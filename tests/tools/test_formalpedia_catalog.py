"""Identity, query and policy regressions using real Lean source syntax."""
import json
from pathlib import Path
import sys

import pytest

TOOLS = Path(__file__).resolve().parents[2] / 'tools'
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from formalpedia_core import cli as fp_cli, source as fp_source, workspace as fp_workspace
from formalpedia_catalog import Catalogue
import lean_source
import lean_style


@pytest.fixture
def library(tmp_path, monkeypatch):
    formal = tmp_path / 'formal'
    (formal / 'Problems').mkdir(parents=True)
    ledger = tmp_path / 'ledger.json'
    ledger.write_text('[]', encoding='utf-8')
    monkeypatch.setattr(fp_workspace, 'ROOT', tmp_path)
    monkeypatch.setattr(fp_workspace, 'FORMAL', formal)
    monkeypatch.setattr(fp_workspace, 'LEDGER', ledger)
    monkeypatch.setattr(fp_workspace, 'INDEX', tmp_path / 'index.json')
    return formal / 'Problems', ledger


def write(folder, name, text):
    path = folder / (name + '.lean')
    path.write_text(text, encoding='utf-8')
    return path


def test_missing_or_stale_export_does_not_control_live_discovery(library):
    folder, _ = library
    write(folder, 'A', 'namespace N\ntheorem first : True := trivial\nend N\n')
    catalogue = Catalogue()
    assert catalogue.status()['local_export'] == {'required': False, 'state': 'missing'}
    fp_workspace.INDEX.write_text('broken JSON')
    assert catalogue.status()['local_export']['state'] == 'unreadable'
    assert catalogue.show('N.first')['status'] == 'found'
    fp_workspace.INDEX.write_text(fp_source.render(fp_source.build()), encoding='utf-8')
    assert catalogue.status()['local_export']['state'] == 'current'
    write(folder, 'A', 'namespace N\ntheorem second : True := trivial\nend N\n')
    assert catalogue.status()['local_export']['state'] == 'stale'
    assert catalogue.show('N.second')['status'] == 'found'
    assert catalogue.show('N.first')['status'] == 'not_found'


def test_unified_lookup_joins_exact_identity_and_preserves_stale_source_view(library):
    from formalpedia_core import semantic_common as sem_common, semantic_query as sem_query, semantic_store as sem_store
    folder, _ = library
    source = write(folder, 'A', 'namespace N\ntheorem first : True := trivial\nend N\n')
    cat = Catalogue()
    missing = cat.show('N.first')
    assert missing['canonical_id'] == 'Problems.A::N.first'
    assert missing['compiled']['freshness']['status'] == 'missing'
    row = {'id': 'Problems.A::N.first', 'name': 'N.first', 'module': 'Problems.A', 'kind': 'theorem',
           'type': 'True', 'type_ast': ['const', 'True', []], 'axioms': [], 'binders': [],
           'type_dependencies': ['True'], 'value_dependencies': ['True.intro']}
    env = {'imports': {'Problems.A': []}, 'inputs': sem_common.inputs(fp_workspace.ROOT),
           'source_modules': ['Problems.A'], 'objects': {}, 'object_modules': {}}
    sem_store.publish(sem_query.SemanticCatalogue(), ['Problems.A'], [row], env)
    joined = cat.show('Problems.A::N.first')
    assert joined['compiled']['declaration']['type_dependencies'] == ['True']
    assert joined['declaration']['qualified_name'] == 'N.first'
    source.write_text(source.read_text() + '-- new research\n')
    stale = cat.show('N.first')
    assert stale['status'] == 'found' and stale['source_status'] == 'found'
    assert stale['compiled']['freshness']['status'] == 'stale'
    with pytest.raises(ValueError, match='conflicts'):
        cat.show('Problems.A::N.first', module='Problems.B')


def test_generated_lookup_never_invents_source_or_private_identity(library):
    from formalpedia_core import semantic_common as sem_common, semantic_query as sem_query, semantic_store as sem_store
    folder, _ = library
    write(folder, 'A', 'namespace N\nstructure Box where\n  x : Nat\n'
                     'private theorem hidden : True := trivial\nend N\n')
    row = {'id': 'Problems.A::N.Box.mk', 'name': 'N.Box.mk', 'module': 'Problems.A',
           'kind': 'constructor', 'type': 'Nat → N.Box', 'type_ast': [], 'axioms': []}
    env = {'imports': {'Problems.A': []}, 'inputs': sem_common.inputs(fp_workspace.ROOT),
           'source_modules': ['Problems.A'], 'objects': {}, 'object_modules': {}}
    other = dict(row, id='Problems.A::M.Box.mk', name='M.Box.mk')
    sem_store.publish(sem_query.SemanticCatalogue(), ['Problems.A'], [row, other], env)
    cat = Catalogue()
    generated = cat.show('Problems.A::N.Box.mk')
    assert generated['status'] == 'found' and generated['declaration'] is None
    assert generated['source_status'] == 'not_indexed' and generated['exact_claims'] == []
    assert generated['source_file'] == 'formal/Problems/A.lean'
    ambiguous = cat.show('mk')
    assert ambiguous['status'] == 'ambiguous' and ambiguous['total_candidates'] == 2
    hidden = cat.show('hidden', include_private=True)
    assert hidden['canonical_id'] is None
    assert hidden['compiled']['status'] == 'unmapped_private'


def test_scoped_search_hides_legacy_results_but_exact_lookup_stays_global(library):
    folder, _ = library
    (folder / 'Juggler').mkdir()
    write(folder / 'Juggler', 'Scope', 'namespace J\n/-- Active result. -/\ntheorem active : True := trivial\nend J\n')
    write(folder, 'Historical', 'namespace Old\n/-- Historical result. -/\ntheorem legacy : True := trivial\nend Old\n')
    catalogue = Catalogue()
    assert {r['id'] for r in catalogue.search('')['results']} == {'J.active'}
    assert {r['id'] for r in catalogue.search('', scope='archive')['results']} == {'Old.legacy'}
    assert catalogue.search('', scope='all')['total'] == 2
    assert catalogue.show('Old.legacy')['scope'] == 'archive'
    with pytest.raises(ValueError, match='scope'):
        catalogue.search('', scope='typo')


def test_namespace_identity_is_not_inferred_from_filename(library):
    folder, _ = library
    write(folder, 'DifferentFile', 'namespace Math\nnamespace First\n'
          '/-- First statement. -/\ntheorem same_name : True := trivial\nend First\n'
          'section Local\nnamespace Second\ntheorem same_name : False → False := id\n'
          'end Second\nend Local\nend Math\n')
    catalogue = Catalogue()
    ambiguous = catalogue.show('same_name')
    assert ambiguous['status'] == 'ambiguous'
    assert {d['id'] for d in ambiguous['candidates']} == {'Math.First.same_name', 'Math.Second.same_name'}
    found = catalogue.show('Math.Second.same_name')
    assert found['declaration']['module'] == 'Problems.DifferentFile'
    assert 'False → False' in found['declaration']['signature']


def test_visibility_root_escapes_and_private_sections(library):
    folder, _ = library
    write(folder, 'Private', 'namespace Outer\nprivate section\n'
          'theorem hidden : True := trivial\npublic theorem visible : True := trivial\n'
          'end\ntheorem _root_.Elsewhere.fact : True := trivial\nend Outer\n')
    catalogue = Catalogue()
    assert catalogue.show('hidden')['status'] == 'not_found'
    private = catalogue.show('hidden', include_private=True)['declaration']
    assert private['qualified_name'] is None and '::private::' in private['id']
    assert catalogue.show('Outer.visible')['status'] == 'found'
    assert catalogue.show('Elsewhere.fact')['status'] == 'found'


def test_unicode_names_nested_docs_and_multiline_attributes():
    text = ('namespace «Math.Space»\n/-- Important /- nested -/ explanation. -/\n'
            '@[simp]\nprotected\ntheorem α_eq_α : True := trivial\nend «Math.Space»\n')
    row, = lean_source.scan(text, 'File', 'formal/File.lean')
    assert row['id'] == '«Math.Space».α_eq_α'
    assert row['doc'] == 'Important /- nested -/ explanation.'
    assert row['attributes'] == ['simp']


def test_complete_header_keeps_default_arguments_and_late_hypotheses():
    text = ('namespace Test\n/-- All hypotheses matter. -/\ntheorem long_result\n'
            '(n : Nat := 0)\n' + '\n'.join(f'(h{i} : n = n)' for i in range(14)) +
            '\n(hLast : False) : False := by\n  exact hLast\nend Test\n')
    row, = lean_source.scan(text, 'Test', 'formal/Test.lean')
    assert '(n : Nat := 0)' in row['signature']
    assert '(hLast : False) : False' in row['signature']
    assert 'exact hLast' not in row['signature']


def test_comments_and_strings_are_not_declarations_or_trust_markers():
    text = ('namespace N\n/-- Mentions sorry and native_decide. -/\n'
            'def message : String := "native_decide\\n theorem fake : True"\n'
            '-- theorem imaginary : False := sorry\n'
            'theorem good : True := by\n  /- sorry -/\n  trivial\nend N\n')
    rows = lean_source.scan(text, 'N', 'formal/N.lean')
    assert [d['name'] for d in rows] == ['message', 'good']
    assert {d['trust'] for d in rows} == {'kernel'}


def test_headers_keep_boolean_and_pipe_operators_but_stop_at_equations():
    rows = lean_source.scan('namespace N\n'
        'theorem bool_law (b : Bool) : (b || true) = true := by simp\n'
        'theorem bool_unparenthesized (b : Bool) : b || true = true := by simp\n'
        'theorem pipeline (n : Nat) : (n |> id) = n := rfl\n'
        'def zero : Nat → Nat\n  | _ => 0\nend N\n', 'N', 'formal/N.lean')
    assert '|| true = true' in rows[1]['signature']
    assert '(n |> id) = n' in rows[2]['signature']
    assert rows[3]['signature'] == 'def zero : Nat → Nat'


def test_search_uses_statements_exact_claims_filters_and_pagination(library):
    folder, ledger = library
    write(folder, 'A', 'namespace Math\n/-- Reciprocal mass growth. -/\n'
          'theorem growth (n : Nat) : n ≤ n := Nat.le_refl n\n'
          '/-- Another result. -/\ntheorem other : True := trivial\nend Math\n')
    ledger.write_text(json.dumps([{'id': 'J-growth', 'tag': 'EXACT — HUMAN PROOF',
        'lean': 'Problems/A.lean', 'decl': 'Math.growth', 'statement': 'Contagion exponent transfer.'}]))
    catalogue = Catalogue()
    assert catalogue.search('contagion transfer')['results'][0]['id'] == 'Math.growth'
    assert catalogue.search('Nat.le_refl')['total'] == 0  # proof bodies are not statements
    assert catalogue.search('', ledger_id='J-growth')['total'] == 1
    assert catalogue.show('other')['exact_claims'] == []
    assert catalogue.show('growth')['exact_claims'][0]['id'] == 'J-growth'
    first = catalogue.search('', namespace='Math', limit=1)
    second = catalogue.search('', namespace='Math', limit=1, offset=first['next_offset'])
    assert first['results'][0]['id'] != second['results'][0]['id']
    assert second['next_offset'] is None


def test_live_search_refreshes_without_writing_saved_artifacts(library):
    folder, _ = library
    path = write(folder, 'Live', 'namespace N\ntheorem old_name : True := trivial\nend N\n')
    catalogue = Catalogue()
    before = catalogue.status()['snapshot']
    path.write_text('namespace N\ntheorem renamed : True := trivial\nend N\n')
    assert catalogue.show('renamed')['status'] == 'found'
    assert catalogue.show('old_name')['status'] == 'not_found'
    assert catalogue.status()['snapshot'] != before
    assert not fp_workspace.INDEX.exists()


def test_claim_does_not_choose_between_same_file_short_names(library):
    folder, ledger = library
    write(folder, 'Two', 'namespace A\ntheorem x : True := trivial\nend A\n'
          'namespace B\ntheorem x : True := trivial\nend B\n')
    ledger.write_text(json.dumps([{'id': 'ambiguous', 'lean': 'Problems/Two.lean',
        'decl': 'x', 'statement': 'A claim.', 'tag': 'EXACT — HUMAN PROOF'}]))
    result = Catalogue().claim('ambiguous')
    assert result['declarations'][0]['status'] == 'ambiguous'
    assert all(not d['ledger_exact'] for d in fp_source.build()['declarations'])


def test_impact_reports_module_granularity_and_path_ambiguity(library):
    folder, _ = library
    write(folder, 'A', 'namespace N\ntheorem fact : True := trivial\nend N\n')
    write(folder, 'B', 'import Problems.A\n')
    result = Catalogue().impact('N.fact')
    assert result['direct_dependents'] == ['Problems.B']
    assert result['granularity'].startswith('module imports')


def test_style_respects_mathlib_camel_tokens_and_prop_definitions():
    rows = lean_source.scan('namespace N\n/-- Mass. -/\ndef logMass : Nat := 1\n'
        '/-- Predicate. -/\ndef FailureBound (n : Nat) : Prop := n > 0\n'
        '/-- A bound. -/\ntheorem logMass_le : logMass ≤ 2 := by decide\nend N\n',
        'N', 'formal/N.lean')
    assert lean_style.violations({'declarations': rows}) == []


def test_style_baseline_does_not_exempt_new_names_or_changed_statements():
    rows = lean_source.scan('namespace N\ntheorem theorem41 : True := trivial\nend N\n',
                            'N', 'formal/N.lean')
    baseline = {'violations': lean_style.violations({'declarations': rows})}
    assert lean_style.report({'declarations': rows}, baseline)['new_count'] == 0
    changed = lean_source.scan('namespace N\ntheorem theorem42 : True := trivial\nend N\n',
                               'N', 'formal/N.lean')
    assert lean_style.report({'declarations': changed}, baseline)['new_count'] == 2
    rows[0]['signature'] = 'theorem theorem41 : False'
    assert lean_style.report({'declarations': rows}, baseline)['new_count'] == 2


@pytest.mark.parametrize('limit,offset', [(0, 0), (101, 0), (20, -1)])
def test_query_limits_are_validated(library, limit, offset):
    with pytest.raises(ValueError):
        Catalogue().search('', limit=limit, offset=offset)


def test_cli_ambiguous_show_returns_candidates_and_nonzero(library, capsys):
    folder, _ = library
    write(folder, 'A', 'namespace A\ntheorem same : True := trivial\nend A\n'
          'namespace B\ntheorem same : True := trivial\nend B\n')
    assert fp_cli.main(['show', 'same']) == 2
    assert json.loads(capsys.readouterr().out)['status'] == 'ambiguous'


def test_same_full_name_in_independent_modules_requires_module_or_id(library):
    folder, _ = library
    write(folder, 'A', 'namespace N\ntheorem fact : True := trivial\nend N\n')
    write(folder, 'B', 'namespace N\ntheorem fact : False → False := id\nend N\n')
    catalogue = Catalogue()
    assert catalogue.show('N.fact')['status'] == 'ambiguous'
    found = catalogue.show('N.fact', module='Problems.B')['declaration']
    assert found['id'] == 'Problems.B::N.fact'
    assert catalogue.show(found['id'])['declaration'] == found
    assert catalogue.search('False')['total'] == 1


def test_symbol_search_does_not_return_every_declaration(library):
    folder, _ = library
    write(folder, 'A', 'namespace N\ntheorem bound (n : Nat) : n ≤ n := by omega\n'
          'theorem reflexive : True := trivial\nend N\n')
    assert Catalogue().search('≤')['total'] == 1
    assert Catalogue().search('∩')['total'] == 0
    with pytest.raises(ValueError, match='2000'):
        Catalogue().search('x' * 2001)


def test_theorem_names_preserve_conventional_uppercase_object_tokens():
    rows = lean_source.scan('namespace N\n/-- An operator. -/\ndef DZ : Nat := 0\n'
        '/-- Its value. -/\ntheorem DZ_eq : DZ = 0 := rfl\n'
        '/-- An interval law. -/\ntheorem Icc_subset_Icc : True := trivial\nend N\n',
        'N', 'formal/N.lean')
    assert all(v['rule'] != 'theorem_case' for v in lean_style.violations({'declarations': rows}))

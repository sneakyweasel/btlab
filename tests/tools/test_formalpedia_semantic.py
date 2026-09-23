"""Semantic discovery must never turn stale metadata into current proof evidence."""
from copy import deepcopy
import json
import os
from pathlib import Path
import sys
import subprocess

import pytest

TOOLS = Path(__file__).resolve().parents[2] / 'tools'
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))
import formalpedia_semantic as sem


def const(name):
    return ['const', name, []]


def declaration(name, *, module='Problems.Demo', ast=None, uses=(), values=(), proof='1'):
    ast = ast or const('True')
    return {'id': module + '::' + name, 'name': name, 'module': module, 'kind': 'theorem',
            'type': 'True', 'type_ast': ast, 'type_sha256': sem.digest(ast),
            'axioms': [], 'binders': [], 'conclusion': 'True', 'value_hash64': proof,
            'type_dependencies': list(uses), 'value_dependencies': list(values)}


def save(cat, rows, *, objects=None, make_current=True, source_modules=None):
    data = {'schema': sem.SCHEMA, 'built_at': 'test',
            'inputs': sem.scoped_inputs(sem.inputs(cat.root), source_modules), 'source_modules': source_modules,
            'objects': objects or {}, 'modules': sorted({r['module'] for r in rows}),
            'coverage': 'selected_modules', 'declarations': rows}
    identifier = sem.digest(data)
    cat.cache.mkdir(parents=True, exist_ok=True)
    (cat.cache / f'{identifier}.json').write_text(json.dumps(data), encoding='utf-8')
    if make_current:
        (cat.cache / 'current').write_text(identifier)
    return identifier


@pytest.fixture
def cat(tmp_path):
    source = tmp_path / 'formal/Problems/Demo.lean'
    source.parent.mkdir(parents=True)
    source.write_text('theorem demo : True := True.intro')
    return sem.SemanticCatalogue(tmp_path)


def test_missing_is_read_only_and_cannot_search(cat):
    assert cat.status()['status'] == 'missing'
    with pytest.raises(ValueError, match='missing'):
        cat.search()
    assert not cat.cache.exists()


def test_content_changes_even_same_size_invalidate_queries(cat):
    save(cat, [declaration('demo')])
    assert cat.status()['status'] == 'current'
    p = cat.root / 'formal/Problems/Demo.lean'
    p.write_text(p.read_text().replace('demo', 'next'))
    assert cat.status()['status'] == 'stale'
    for query in (lambda: cat.show('demo'), lambda: cat.search(), lambda: cat.dependencies('demo')):
        with pytest.raises(ValueError, match='stale'):
            query()


def test_object_replacement_invalidates_queries(cat):
    p = cat.root / 'external.olean'
    p.write_bytes(b'compiled')
    save(cat, [declaration('demo')], objects={str(p): sem.file_stamp(p)})
    p.write_bytes(b'changed object')
    assert cat.status()['changed_object_count'] == 1
    assert cat.status()['status'] == 'stale'


def test_partial_export_tracks_import_closure_but_not_unrelated_research(cat):
    dep = cat.root / 'formal/Problems/Dependency.lean'
    dep.write_text('def helper : Nat := 1')
    save(cat, [declaration('demo')], source_modules=['Problems.Demo', 'Problems.Dependency'])
    unrelated = cat.root / 'formal/Problems/NewResearch.lean'
    unrelated.write_text('-- work in progress')
    assert cat.status()['status'] == 'current'
    dep.write_text('def helper : Nat := 2')
    assert cat.status()['status'] == 'stale'
    assert cat.status()['changed_inputs'] == ['formal/Problems/Dependency.lean']


def test_ambiguity_and_generated_private_names(cat):
    rows = [declaration('N.same'), declaration('M.same'),
            declaration('_private.Problems.Demo.0.hidden'), declaration('N.same', module='Problems.Other')]
    save(cat, rows)
    assert cat.show('same')['candidate_count'] == 3
    assert cat.show('N.same')['status'] == 'ambiguous'
    assert cat.show('Problems.Demo::N.same')['status'] == 'found'
    assert cat.search()['total'] == 3
    assert cat.search(include_private=True)['total'] == 4


def test_named_holes_require_identical_subtrees_and_do_not_unify():
    pattern = ['app', {'hole': 'same'}, {'hole': 'same'}]
    assert sem.structural_match(pattern, ['app', const('Nat'), const('Nat')])
    assert not sem.structural_match(pattern, ['app', const('Nat'), const('Int')])
    assert not sem.structural_match(const('Nat.add'), const('HAdd.hAdd'))


def test_search_constants_shape_and_snapshot_pagination(cat):
    ast = ['forall', 'explicit', const('Nat'), ['app', const('Nat.succ'), ['bvar', 0]]]
    first = declaration('N.first', ast=ast, uses=['Nat', 'Nat.succ'])
    second = declaration('N.second', ast=deepcopy(ast), uses=['Nat', 'Nat.succ'])
    # Same conclusion shape but different premise; returned as structural, never applicable.
    other = declaration('N.other', ast=['forall', 'implicit', const('Int'), ast[3]], uses=['Int', 'Nat.succ'])
    sid = save(cat, [first, second, other])
    assert cat.search(like='N.first')['total'] == 2
    assert cat.search(like='N.first', part='conclusion')['total'] == 3
    assert cat.search(constants=['Nat', 'Nat.succ'])['total'] == 2
    assert cat.search(pattern=['forall', 'implicit', {'hole': 'T'}, {'hole': 'P'}])['total'] == 1
    page = cat.search(limit=1, snapshot=sid)
    assert page['next_offset'] == 1 and len(page['items']) == 1
    with pytest.raises(ValueError, match='snapshot changed'):
        cat.search(snapshot='old')
    assert 'type_ast' not in cat.show('N.first')['declaration']
    assert cat.show('N.first', True)['declaration']['type_ast'] == ast


def test_dependency_edges_distinguish_type_proof_reverse_and_external(cat):
    save(cat, [declaration('P', uses=['Prop']), declaration('lemma', uses=['P'], values=['proof_helper']),
               declaration('proof_helper', values=['True.intro'])])
    typed = cat.dependencies('lemma', edge='type')['items']
    assert len(typed) == 1 and typed[0]['to'].endswith('::P')
    value = cat.dependencies('lemma', edge='value', depth=2)['items']
    assert value[-1]['to'] == 'external:True.intro' and value[-1]['external']
    callers = cat.dependencies('proof_helper', direction='used_by')['items']
    assert callers[0]['to'].endswith('::lemma') and callers[0]['edge'] == 'value'


def test_diff_propagates_definition_changes_without_claiming_strength(cat):
    rows = [declaration('f'), declaration('lemma', uses=['f']), declaration('caller', values=['lemma'])]
    before = save(cat, rows)
    changed = deepcopy(rows)
    changed[0]['value_hash64'] = '2'
    after = save(cat, changed)
    result = cat.diff(before, after)
    by_name = {r['name']: r['changes'] for r in result['items']}
    assert by_name['f'] == ['value_hash64']
    assert by_name['lemma'] == by_name['caller'] == ['transitive_dependency_changed']
    assert result['before'] == before and result['after'] == after
    assert cat.diff(before, before)['total'] == 0


def test_historical_diff_allowed_when_current_sources_are_stale(cat):
    before = save(cat, [declaration('f')])
    (cat.root / 'formal/Problems/Demo.lean').write_text('-- newer source')
    result = cat.diff(before)
    assert result['current_status'] == 'stale'


def test_snapshot_paths_and_corruption_rejected(cat):
    save(cat, [declaration('f')])
    with pytest.raises(ValueError, match='Invalid'):
        cat.diff('../private')
    broken = 'a' * 64
    (cat.cache / f'{broken}.json').write_text('{"schema":1}')
    with pytest.raises(ValueError, match='corrupted'):
        cat.diff(broken)


def test_failed_compile_preserves_last_snapshot(cat, monkeypatch):
    previous = save(cat, [declaration('f')])
    (cat.root / 'formal/lake-manifest.json').write_text('{"packages":[]}')
    monkeypatch.setattr(sem, 'executable', lambda *args: 'lake')
    monkeypatch.setattr(sem, 'environment', lambda *args: {})
    class Failed:
        returncode = 1
    monkeypatch.setattr(sem.subprocess, 'run', lambda *args, **kwargs: Failed())
    with pytest.raises(ValueError, match='previous snapshot preserved'):
        sem.build(root=cat.root)
    assert (cat.cache / 'current').read_text() == previous


def test_source_change_during_build_cannot_publish(cat, monkeypatch):
    previous = save(cat, [declaration('f')])
    (cat.root / 'formal/lake-manifest.json').write_text('{"packages":[]}')
    monkeypatch.setattr(sem, 'executable', lambda *args: 'lake')
    monkeypatch.setattr(sem, 'environment', lambda *args: {})
    monkeypatch.setattr(sem, 'compiled_inventory', lambda *args: {})
    calls = []
    class Passed:
        returncode = 0
    def run(command, **kwargs):
        calls.append(command)
        if len(calls) == 2:
            (cat.root / 'formal/Problems/Demo.lean').write_text('-- concurrent research edit')
        return Passed()
    monkeypatch.setattr(sem.subprocess, 'run', run)
    with pytest.raises(ValueError, match='Sources changed'):
        sem.build(root=cat.root)
    assert calls[0] == ['lake', 'build', '+Problems.Demo']
    assert (cat.cache / 'current').read_text() == previous


def test_import_only_module_can_publish_an_empty_export(cat, monkeypatch):
    (cat.root / 'formal/lake-manifest.json').write_text('{"packages":[]}')
    monkeypatch.setattr(sem, 'executable', lambda *args: 'lake')
    monkeypatch.setattr(sem, 'environment', lambda *args: {})
    monkeypatch.setattr(sem, 'compiled_inventory', lambda *args: {})
    class Passed:
        returncode = 0
    def run(command, **kwargs):
        if '--run' in command:
            Path(command[-1]).write_text(json.dumps({'record': 'environment', 'objects': []}) + '\n')
        return Passed()
    monkeypatch.setattr(sem.subprocess, 'run', run)
    result = sem.build(root=cat.root)
    assert result['declarations'] == 0
    assert cat.status()['status'] == 'current'
    assert cat.search()['items'] == []


@pytest.mark.parametrize('kwargs', [{'limit': 0}, {'offset': -1}, {'part': 'other'},
                                   {'like': 'demo', 'pattern': {}}, {'constants': ['Nat'] * 33}])
def test_invalid_search_inputs(cat, kwargs):
    save(cat, [declaration('demo')])
    with pytest.raises(ValueError):
        cat.search(**kwargs)


def test_compiler_export_preserves_hidden_binders_axioms_and_alpha_types(tmp_path):
    """An actual pinned compiler, independent of optional lab snapshot/cache state."""
    root = TOOLS.parent
    lean = sem.executable('lean', root)
    if not lean:
        pytest.skip('Pinned Lean compiler not installed')
    source = tmp_path / 'SemanticFixture.lean'
    source.write_text('''universe u
namespace SemanticFixture
axiom assumed : True
def seed : Nat := 2
structure Box (α : Type u) where
  val : α
theorem usesAssumption : True := assumed
theorem exposed (n : Nat) (h : n = seed) : n = seed := h
theorem alphaOne {α : Sort u} (x : α) : x = x := rfl
theorem alphaTwo {β : Sort u} (y : β) : y = y := rfl
private theorem hidden : True := True.intro
end SemanticFixture
''', encoding='utf-8')
    env = sem.environment(root)
    env['LEAN_PATH'] = str(tmp_path) + (os.pathsep + env['LEAN_PATH'] if env.get('LEAN_PATH') else '')
    def run(args):
        result = subprocess.run([lean, *args], cwd=tmp_path, env=env, capture_output=True,
                                text=True, encoding='utf-8', timeout=120)
        assert result.returncode == 0, result.stdout + result.stderr
    run(['-o', str(tmp_path / 'SemanticFixture.olean'), str(source)])
    request, output = tmp_path / 'request.json', tmp_path / 'export.jsonl'
    request.write_text(json.dumps({'modules': ['SemanticFixture']}))
    run(['--run', str(TOOLS / 'lean/SemanticExport.lean'), str(request), str(output)])
    records = [json.loads(line) for line in output.read_text(encoding='utf-8').splitlines()]
    assert records[0]['record'] == 'environment' and records[0]['objects']
    rows = {r['name']: r for r in records[1:]}
    assumption = rows['SemanticFixture.usesAssumption']
    assert assumption['axioms'] == ['SemanticFixture.assumed']
    assert 'SemanticFixture.assumed' in assumption['value_dependencies']
    exposed = rows['SemanticFixture.exposed']
    assert 'SemanticFixture.seed' in exposed['type_dependencies']
    assert exposed['binders'][1]['is_proposition']
    one, two = rows['SemanticFixture.alphaOne'], rows['SemanticFixture.alphaTwo']
    assert one['type_ast'] == two['type_ast']
    assert one['binders'][0]['kind'] == 'implicit'
    assert any(name.startswith('_private.') and name.endswith('.hidden') for name in rows)
    assert rows['SemanticFixture.Box.mk']['kind'] == 'constructor'
    assert rows['SemanticFixture.Box.rec']['kind'] == 'recursor'

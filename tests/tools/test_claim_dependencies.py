"""Trust boundaries of recorded proof routes and their compiler overlay."""
import hashlib
import json
from pathlib import Path

import pytest
import lean_source

from formalpedia_core import claim_graph as graph, workspace
from formalpedia_core.claim_query import compiled_overlay
from formalpedia_catalog import Catalogue
from render_theorem_ledger import render

ROOT = Path(__file__).resolve().parents[2]


def row(name, tag='EXACT — HUMAN PROOF', **extra):
    return {'id': name, 'tag': tag, 'statement': name + ' statement', 'source': 'proof.md',
            'lean': '', 'tests': [], **extra}


def route(root, uses=(), *, name='written', coverage='complete'):
    path = root / 'proof.md'
    if not path.exists():
        path.write_text('# Proof\nA proof passage.\n# End\n', encoding='utf-8')
    source = {'path': 'proof.md', 'start': '# Proof', 'end': '# End'}
    text, _ = graph.source_passage(root, source)
    source['sha256'] = hashlib.sha256(text.encode()).hexdigest()
    return {'id': name, 'method': 'written', 'coverage': coverage,
            'source': source, 'uses': [{'claim': n, 'kind': k} for n, k in uses],
            'notes': 'Dependencies at the stated scope; no proof certification.'}


def test_unknown_is_not_a_reviewed_empty_list(tmp_path):
    rows = [row('unknown'), row('leaf', proof_routes=[route(tmp_path)])]
    unknown = graph.build(rows, tmp_path, 'unknown')
    assert unknown['summary']['incomplete_dependencies'] == ['unknown']
    assert not unknown['dependency_coverage_complete']
    leaf = graph.build(rows, tmp_path, 'leaf')
    assert leaf['dependency_coverage_complete']
    assert leaf['summary']['human_proof_claims'] == ['leaf']
    assert leaf['nodes']['leaf']['tag'] == 'EXACT — HUMAN PROOF'


def test_alternative_routes_do_not_conjoin_their_assumptions(tmp_path):
    rows = [row('A', proof_routes=[route(tmp_path, [('H', 'assumption')], name='conditional'),
                                  route(tmp_path, name='independent')]),
            row('H', 'CONJECTURE', claim_kind='hypothesis')]
    undecided = graph.build(rows, tmp_path, 'A')
    assert undecided['nodes']['A']['reason'] == 'route_selection_required'
    assert not undecided['dependency_coverage_complete']
    assert undecided['edges'] == []
    conditional = graph.build(rows, tmp_path, 'A', choices={'A': 'conditional'})
    assert conditional['summary']['assumptions'] == ['H']
    assert conditional['summary']['non_established_claims'] == ['H']
    independent = graph.build(rows, tmp_path, 'A', choices={'A': 'independent'})
    assert independent['summary']['assumptions'] == []
    assert 'H' not in independent['nodes']
    with pytest.raises(ValueError, match='Unknown route'):
        graph.build(rows, tmp_path, 'A', choices={'A': 'invented'})


def test_stale_prose_fails_validation_and_remains_visible(tmp_path):
    rows = [row('A', proof_routes=[route(tmp_path)])]
    assert graph.validate(rows, tmp_path) == []
    before = graph.build(rows, tmp_path, 'A')['snapshot']
    (tmp_path / 'proof.md').write_text('# Proof\nA changed proof.\n# End\n', encoding='utf-8')
    assert any('stale' in e for e in graph.validate(rows, tmp_path))
    changed = graph.build(rows, tmp_path, 'A')
    assert changed['snapshot'] != before
    assert changed['summary']['stale_annotations'] == ['A']
    with pytest.raises(ValueError, match='stale'):
        render(rows, root=tmp_path)


@pytest.mark.parametrize('mutation,expected', [
    (lambda r: r[0]['proof_routes'][0]['uses'].append({'claim': 'absent', 'kind': 'proof'}), 'unknown dependency'),
    (lambda r: r[0]['proof_routes'][0]['uses'].append({'claim': 'A', 'kind': 'proof'}), 'self'),
    (lambda r: r[0]['proof_routes'][0].update(uses=[{'claim': 'B', 'kind': []}]), 'kind must be a string'),
    (lambda r: r[0]['proof_routes'][0].update(coverage=[]), 'invalid coverage'),
    (lambda r: r[0].update(proof_routes=[]), 'nonempty list'),
    (lambda r: r[0]['proof_routes'][0].update(method='compiled'), 'compiled edges are derived'),
    (lambda r: r[0]['proof_routes'][0]['uses'][0].update(kind='computation'), 'computational claim'),
    (lambda r: r[0]['proof_routes'][0].update(source={'path': '../secret', 'start': 'a', 'end': 'b', 'sha256': '0'*64}), 'unavailable'),
])
def test_invalid_metadata_is_rejected(tmp_path, mutation, expected):
    rows = [row('A', proof_routes=[route(tmp_path, [('B', 'proof')])]), row('B')]
    mutation(rows)
    assert any(expected in e for e in graph.validate(rows, tmp_path))


def test_cycles_and_hidden_hypotheses_are_rejected(tmp_path):
    rows = [row('A', proof_routes=[route(tmp_path, [('B', 'proof')])]),
            row('B', proof_routes=[route(tmp_path, [('A', 'proof')])])]
    assert any('Circular' in e for e in graph.validate(rows, tmp_path))
    rows[1] = row('B', 'CONJECTURE', claim_kind='hypothesis')
    assert any('assumption edge' in e for e in graph.validate(rows, tmp_path))


def test_truncation_does_not_turn_unvisited_claims_into_proved_leaves(tmp_path):
    rows = [row('A', proof_routes=[route(tmp_path, [('B', 'proof')])]), row('B')]
    result = graph.build(rows, tmp_path, 'A', max_nodes=1)
    assert result['truncated'] and not result['dependency_coverage_complete']
    assert result['summary']['omitted_claims'] == ['B']


def test_computation_scope_and_local_premises_survive_rendering(tmp_path):
    rows = [row('A', proof_routes=[route(tmp_path, [('finite', 'computation')])], conditions=['N <= 100']),
            row('finite', 'COMPUTATIONALLY VERIFIED', statement='Finite enumeration for 1 <= n <= 100.')]
    result = graph.build(rows, tmp_path, 'A')
    assert result['summary']['finite_computations'] == ['finite']
    assert result['nodes']['finite']['statement'].endswith('100.')
    assert 'N <= 100' in graph.markdown(result)
    assert 'Finite enumeration for 1 <= n <= 100.' in graph.markdown(result)
    assert '```mermaid' in graph.markdown(result)
    assert result['nodes']['A']['tag'] == 'EXACT — HUMAN PROOF'


@pytest.fixture
def claim_catalog(tmp_path, monkeypatch):
    formal = tmp_path / 'formal'
    formal.mkdir()
    ledger_path = tmp_path / 'ledger.json'
    rows = [row('A', proof_routes=[route(tmp_path, [('B', 'proof')])]), row('B')]
    ledger_path.write_text(json.dumps(rows), encoding='utf-8')
    for key, value in {'ROOT': tmp_path, 'FORMAL': formal, 'LEDGER': ledger_path}.items():
        monkeypatch.setattr(workspace, key, value)
    return Catalogue(), tmp_path


def test_pagination_detects_prose_edits_and_queries_are_read_only(claim_catalog):
    catalogue, root = claim_catalog
    def inventory():
        return {p.relative_to(root).as_posix(): p.read_bytes() for p in root.rglob('*') if p.is_file()}
    before = inventory()
    first = catalogue.claim_dependencies('A', limit=1)
    second = catalogue.claim_dependencies('A', limit=1, offset=1, snapshot=first['snapshot'])
    assert first['total'] == 3 and second['items'][0]['id'] == 'B'
    missing = catalogue.claim_dependencies('A', include_compiled=True)
    assert missing['compiled']['status'] == 'missing'
    assert before == inventory()
    (root / 'proof.md').write_text('# Proof\nChanged.\n# End\n')
    with pytest.raises(ValueError, match='snapshot changed'):
        catalogue.claim_dependencies('A', offset=1, snapshot=first['snapshot'])
    with pytest.raises(ValueError, match='limit'):
        catalogue.claim_dependencies('A', limit=101)


def test_compiled_projection_keeps_paths_snapshot_and_unmapped_helpers(tmp_path):
    from formalpedia_core import semantic_common, semantic_query, semantic_store
    file = tmp_path / 'formal/Problems/Example.lean'
    file.parent.mkdir(parents=True)
    file.write_text('namespace Example\ntheorem a : True := trivial\ntheorem b : True := trivial\nend Example\n')
    declarations = lean_source.scan(file.read_text(), 'Problems.Example', 'formal/Problems/Example.lean')
    rows = [row('A', lean='Problems/Example.lean', decl='Example.a'),
            row('B', lean='Problems/Example.lean', decl='Example.b')]
    semantic = semantic_query.SemanticCatalogue(tmp_path)
    records = []
    for name, uses in [('Example.a', ['Example.helper']), ('Example.helper', ['Example.b']), ('Example.b', [])]:
        records.append({'id': 'Problems.Example::'+name, 'name': name, 'module': 'Problems.Example',
            'kind': 'theorem', 'type': 'True', 'type_ast': ['const','True',[]], 'axioms': [], 'binders': [],
            'type_dependencies': ['True'], 'value_dependencies': uses})
    semantic_store.publish(semantic, ['Problems.Example'], records,
        {'inputs': semantic_common.inputs(tmp_path), 'source_modules': ['Problems.Example'],
         'objects': {}, 'imports': {'Problems.Example': []}, 'object_modules': {}})
    written = graph.build(rows, tmp_path, 'A')
    result = compiled_overlay(written, rows, {'declarations': declarations}, semantic)
    edge = next(e for e in result['edges'] if e['to'] == 'B')
    assert edge['origin'] == 'compiled' and edge['export_snapshot']
    assert edge['declaration_path'] == ['Problems.Example::Example.a', 'Problems.Example::Example.helper', 'Problems.Example::Example.b']
    assert result['unmapped_count'] > 0
    assert not written['dependency_coverage_complete']
    file.write_text(file.read_text() + '-- changed\n')
    stale = compiled_overlay(written, rows, {'declarations': declarations}, semantic)
    assert stale['status'] == 'stale' and stale['edges'] == []


def test_paper_scopes_preserve_finite_density_and_contagion_boundaries():
    ledger = json.loads((ROOT / 'docs/theory/theorem_ledger.json').read_text(encoding='utf-8'))
    assert graph.validate(ledger, ROOT) == []
    finite = graph.build(ledger, ROOT, 'J-paper-b-five-step-density-127')
    assert finite['summary']['assumptions'] == []
    assert 'J-paper-b-hypothesis-fd' not in finite['nodes']
    assert 'J-paper-b-oooee-mixed-127' in finite['summary']['human_proof_claims']
    assert not finite['dependency_coverage_complete']  # analytic/external leaves remain unexpanded
    density_one = graph.build(ledger, ROOT, 'J-paper-b-density-one-under-fd')
    assert density_one['summary']['assumptions'] == ['J-paper-b-hypothesis-fd']
    contagion = graph.build(ledger, ROOT, 'J-ooee-contagion-five-eighths')
    assert not contagion['summary']['assumptions']
    assert 'J-ooee-actual-weighted-production' in contagion['nodes']
    tao = graph.build(ledger, ROOT, 'J-ooee-tao-rate-termination')
    assert tao['summary']['assumptions'] == ['J-paper-c-hypothesis-tao-rate']
    pressure = graph.build(ledger, ROOT, 'J-ooee-pressure-rate-termination')
    assert pressure['summary']['assumptions'] == ['J-paper-c-hypothesis-stopped-pressure']
    assert tao['nodes']['J-ooee-tao-rate-termination']['tag'] == 'EXACT — HUMAN PROOF'


def test_cli_refuses_to_certify_incomplete_dependencies(claim_catalog, capsys):
    from formalpedia_core.cli import main
    _, _root = claim_catalog
    assert main(['claim-graph', 'A', '--format', 'markdown', '--require-complete']) == 1
    assert 'incomplete' in capsys.readouterr().out
    assert main(['claim-graph', 'absent']) == 2
    assert 'Unknown ledger claim' in capsys.readouterr().err

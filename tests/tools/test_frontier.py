"""The formalization frontier never calls an unknown, partial, stale or finite input ready."""
import copy
import hashlib
import json
import re
from pathlib import Path

import pytest

from formalpedia_core import blueprint, frontier
from formalpedia_core.claim_graph import source_passage
from research.claims import load_claims

ROOT = Path(__file__).resolve().parents[2]
LEAN, HUMAN = 'EXACT — LEAN VERIFIED', 'EXACT — HUMAN PROOF'


def row(name, tag=HUMAN, **extra):
    return {'id': name, 'tag': tag, 'statement': name + ' statement', 'source': 'proof.md',
            'lean': '', 'tests': [], **extra}


def route(root, uses=(), *, name='written', coverage='complete', stale=False):
    path = root / 'proof.md'
    if not path.exists():
        path.write_text('# Proof\nA proof passage.\n# End\n', encoding='utf-8')
    source = {'path': 'proof.md', 'start': '# Proof', 'end': '# End'}
    text, _ = source_passage(root, source)
    source['sha256'] = hashlib.sha256((text + ('edited' if stale else '')).encode()).hexdigest()
    return {'id': name, 'method': 'written', 'coverage': coverage, 'source': source,
            'uses': [{'claim': n, 'kind': k} for n, k in uses],
            'notes': 'Dependencies at the stated scope; no proof certification.'}


@pytest.fixture
def ledger(tmp_path):
    r = lambda *a, **k: route(tmp_path, *a, **k)
    return [
        row('L', LEAN, decl=['l_thm'], lean='Problems/L.lean', lean_trust='kernel'),
        row('L-bare', LEAN),
        row('H', 'CONJECTURE', claim_kind='hypothesis'),
        row('F', 'COMPUTATIONALLY VERIFIED'),
        row('E'),
        row('ready', proof_routes=[r([('L', 'proof')])]),
        row('conditional', proof_routes=[r([('L', 'proof'), ('H', 'assumption')])]),
        row('finite-input', proof_routes=[r([('F', 'computation')])]),
        row('one-away', proof_routes=[r([('ready', 'proof'), ('L', 'statement')])]),
        row('two-away', proof_routes=[r([('ready', 'proof'), ('E', 'proof')])]),
        row('partial', proof_routes=[r([('L', 'proof')], coverage='partial')]),
        row('stale', proof_routes=[r([('L', 'proof')], stale=True)]),
        row('alternatives', proof_routes=[r([('L', 'proof')], name='sketch', coverage='partial'),
                                          r([('L-bare', 'proof')], name='full')]),
        row('refuted', 'REFUTED'),
    ]


def test_statuses_follow_routes_and_labels(ledger, tmp_path):
    result = frontier.build(ledger, tmp_path)
    status = {name: item['status'] for name, item in result['claims'].items()}
    assert status == {
        'L': 'formalized', 'L-bare': 'formalized', 'H': 'open', 'F': 'finite', 'E': 'unannotated',
        'ready': 'ready', 'conditional': 'ready_conditional', 'finite-input': 'blocked',
        'one-away': 'blocked', 'two-away': 'blocked', 'partial': 'needs_annotation', 'stale': 'stale',
        'alternatives': 'ready', 'refuted': 'not_a_target'}
    assert result['claims']['conditional']['conditional_on'] == ['H']
    assert result['claims']['finite-input']['blockers'] == [
        {'claim': 'F', 'kind': 'computation', 'tag': 'COMPUTATIONALLY VERIFIED', 'status': 'finite'}]
    assert result['claims']['alternatives']['route'] == 'full'
    assert [i['id'] for i in result['ready']] == ['ready', 'alternatives', 'conditional']


def test_known_bad_inputs_are_never_ready(ledger, tmp_path):
    ready = {i['id'] for i in frontier.build(ledger, tmp_path)['ready']}
    assert not ready & {'partial', 'stale', 'finite-input', 'two-away', 'E', 'H', 'F', 'refuted'}


def test_one_blocker_lists_and_unlocks(ledger, tmp_path):
    result = frontier.build(ledger, tmp_path)
    assert {i['id'] for i in result['almost_ready']} == {'one-away', 'finite-input'}
    assert {u['claim']: u['would_become_ready'] for u in result['unlocks']} == {
        'ready': ['one-away'], 'F': ['finite-input']}
    assert [i['id'] for i in result['blocked']] == ['two-away']
    assert [i['id'] for i in result['unannotated_boundary']] == ['E']
    assert result['claims']['ready']['downstream'] == 2


def test_input_coverage_is_advisory_and_missing_declarations_are_flagged(ledger, tmp_path):
    coverage = {'L': {'verdict': 'fresh', 'band': 'doubtful', 'reading': 'claim_broader'}}
    result = frontier.build(ledger, tmp_path, coverage=coverage)
    ready = result['claims']['ready']
    assert ready['status'] == 'ready'
    assert ready['inputs'][0]['coverage'] == {'verdict': 'fresh', 'band': 'doubtful', 'reading': 'claim_broader'}
    assert ready['warnings'] == ['input L English coverage: doubtful']
    bare = result['claims']['alternatives']['inputs'][0]
    assert bare['coverage']['band'] == 'no_declaration'
    assert result['claims']['L-bare']['warnings'] == ['LEAN VERIFIED without a declaration link']
    stale = frontier.build(ledger, tmp_path, coverage={'L': {'verdict': 'stale'}})
    assert stale['claims']['ready']['inputs'][0]['coverage']['band'] == 'stale'


def test_scope_and_no_mutation(ledger, tmp_path):
    before = copy.deepcopy(ledger)
    scoped = frontier.build(ledger, tmp_path, scope='two-away')
    assert ledger == before
    assert scoped['counts']['formalized'] == 1
    assert [i['id'] for i in scoped['ready']] == ['ready']
    assert scoped['unlocks'] == [] and scoped['almost_ready'] == []
    with pytest.raises(ValueError, match='Unknown ledger claim'):
        frontier.build(ledger, tmp_path, scope='missing')
    assert frontier.build(ledger, tmp_path)['snapshot'] == frontier.build(ledger, tmp_path)['snapshot']


def test_next_actions_and_markdown(ledger, tmp_path):
    result = frontier.build(ledger, tmp_path)
    assert result['claims']['conditional']['next_action'].startswith('Formalize conditional from proof.md:1')
    assert 'keep H as explicit hypotheses' in result['claims']['conditional']['next_action']
    assert result['claims']['two-away']['next_action'] == 'Formalize its blockers first: ready, E.'
    text = frontier.markdown(result)
    assert '## Ready (3)' in text and '`E`' in text
    assert frontier.compact(result['claims']['ready'])['next_action']


def test_blueprint_layout_points_down_and_escapes_statements(ledger, tmp_path):
    ledger[4]['statement'] = 'E </script><script>alert(1)</script>'
    result = frontier.build(ledger, tmp_path)
    text = blueprint.render(result, ledger, generated='test')
    assert text.count('</script>') == 2
    payload = re.search(r'id="frontier-data">(.*?)</script>', text, re.S).group(1)
    data = json.loads(payload)
    assert data['claims']['E']['statement'].endswith('</script>')
    nodes, edges = data['graph']['nodes'], data['graph']['edges']
    assert {(n['x'], n['y']) for n in nodes.values()}.__len__() == len(nodes)
    assert all(nodes[e['from']]['y'] < nodes[e['to']]['y'] for e in edges)
    assert set(nodes) == {'ready', 'conditional', 'finite-input', 'one-away', 'two-away', 'partial',
                          'stale', 'alternatives', 'L', 'L-bare', 'H', 'F', 'E'}
    out = tmp_path / 'view' / 'blueprint.html'
    blueprint.write(out, text)
    assert out.read_text(encoding='utf-8') == text


def test_committed_ledger_frontier_invariants():
    ledger = load_claims(ROOT).entries
    result = frontier.build(ledger, ROOT)
    rows = {r['id']: r for r in ledger}
    assert sum(result['counts'].values()) == len(ledger)
    for item in result['ready']:
        chosen = next(r for r in rows[item['id']]['proof_routes'] if r['id'] == item['route'])
        assert chosen['coverage'] == 'complete'
        for edge in chosen['uses']:
            if edge['kind'] != 'assumption':
                assert rows[edge['claim']]['tag'] == LEAN
    for item in result['claims'].values():
        assert item['tag'] == rows[item['id']]['tag']

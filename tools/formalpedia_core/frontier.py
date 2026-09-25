"""Formalization frontier: which human-proved claims have every written input in Lean.

A Blueprint-style reading of the canonical claims. It computes a work queue from
recorded proof routes and evidence labels; it never promotes a label, never
treats an unannotated claim as dependency-free and never counts a finite
computation or an open hypothesis as formalized.
"""
from __future__ import annotations

from collections import defaultdict
from pathlib import Path

from research.claim_dependencies import digest, source_state, validate

LEAN = 'EXACT — LEAN VERIFIED'
TARGET_TAGS = {'EXACT — HUMAN PROOF', 'REPARAMETERIZATION'}
FINITE = 'COMPUTATIONALLY VERIFIED'
STATUSES = ('formalized', 'ready', 'ready_conditional', 'blocked', 'stale', 'needs_annotation',
            'unannotated', 'open', 'finite', 'not_a_target')
"""Every claim gets exactly one. Only the route-evaluated targets can be ready or blocked."""
LIMITATIONS = (
    'Ready means a complete written route whose proof and statement inputs are all LEAN VERIFIED; '
    'it is a work queue, not a proof that the Lean statement is easy or that the English route is correct. '
    'Assumption edges are carried as conditions and never discharged. Computation edges block until the '
    'finite claim itself is formalized. Unannotated or partial routes are unknown, not empty. '
    'Input coverage bands are Jev advisory readings of English-to-Lean coverage, never a review. '
    'Alternative routes are evaluated separately and never combined. No label is promoted.'
)
_RANK = {'ready': 0, 'ready_conditional': 1, 'blocked': 2, 'stale': 3, 'needs_annotation': 4}


def _route_state(root: Path, row: dict, route: dict, rows: dict, formalized: set[str]) -> dict:
    uses = route['uses']
    state = {'route': route['id'], 'coverage': route['coverage'],
             'freshness': source_state(root, route['source']),
             'blockers': [], 'conditional_on': [], 'inputs': []}
    for edge in uses:
        target, kind = edge['claim'], edge['kind']
        if kind == 'assumption':
            state['conditional_on'].append(target)
        elif target in formalized:
            state['inputs'].append({'claim': target, 'kind': kind})
        else:
            state['blockers'].append({'claim': target, 'kind': kind, 'tag': rows[target]['tag']})
    if route['coverage'] != 'complete':
        state['status'] = 'needs_annotation'
    elif state['freshness']['status'] != 'current':
        state['status'] = 'stale'
    elif state['blockers']:
        state['status'] = 'blocked'
    else:
        state['status'] = 'ready_conditional' if state['conditional_on'] else 'ready'
    return state


def _users(ledger: list[dict]) -> dict[str, set[str]]:
    users: dict[str, set[str]] = defaultdict(set)
    for row in ledger:
        for route in row.get('proof_routes', []):
            for edge in route['uses']:
                users[edge['claim']].add(row['id'])
    return users


def _closure(start: str, step) -> set[str]:
    seen, pending = set(), [start]
    while pending:
        name = pending.pop()
        for other in step(name):
            if other not in seen:
                seen.add(other)
                pending.append(other)
    return seen


def build(ledger: list[dict], root: Path, *, coverage: dict[str, dict] | None = None,
          scope: str | None = None) -> dict:
    """Classify every claim; ``scope`` restricts the listed items to one root's inputs.

    ``coverage`` maps LEAN VERIFIED claim IDs to Jev coverage entries (``verdict``,
    ``band``, ``reading``). Missing entries are reported as unasked.
    """
    errors = validate(ledger, root, check_sources=False)
    if errors:
        raise ValueError('Invalid claim dependencies: ' + '; '.join(errors[:10]))
    rows = {row['id']: row for row in ledger}
    if scope is not None and scope not in rows:
        raise ValueError(f'Unknown ledger claim: {scope}')
    coverage = coverage or {}
    formalized = {name for name, row in rows.items() if row['tag'] == LEAN}
    users = _users(ledger)
    uses = {name: {e['claim'] for r in row.get('proof_routes', []) for e in r['uses']}
            for name, row in rows.items()}
    claims: dict[str, dict] = {}
    for name, row in rows.items():
        item = {'id': name, 'tag': row['tag'], 'claim_kind': row.get('claim_kind', 'result'),
                'source': row['source'], 'lean': row.get('lean') or None, 'decl': list(row.get('decl', [])),
                'routes': [], 'warnings': []}
        if row['tag'] == LEAN:
            item['status'] = 'formalized'
            item['coverage'] = _coverage(coverage.get(name))
            if not row.get('decl'):
                # Nothing names the Lean statement, so its coverage cannot even be asked.
                item['coverage'] = {'verdict': 'no_declaration', 'band': 'no_declaration', 'reading': None}
                item['warnings'].append('LEAN VERIFIED without a declaration link')
        elif row.get('claim_kind') == 'hypothesis' or row['tag'] == 'CONJECTURE':
            item['status'] = 'open'
        elif row['tag'] == FINITE:
            item['status'] = 'finite'
        elif row['tag'] not in TARGET_TAGS:
            item['status'] = 'not_a_target'
        elif not row.get('proof_routes'):
            item['status'] = 'unannotated'
        else:
            states = [_route_state(root, row, r, rows, formalized) for r in row['proof_routes']]
            best = min(states, key=lambda s: (_RANK[s['status']], len(s['blockers']), s['route']))
            item['routes'] = states
            item['status'] = best['status']
            item['route'] = best['route']
            item['blockers'] = best['blockers']
            item['conditional_on'] = best['conditional_on']
            item['inputs'] = [{**i, 'decl': list(rows[i['claim']].get('decl', [])),
                               'lean': rows[i['claim']].get('lean') or None,
                               'coverage': (_coverage(coverage.get(i['claim'])) if rows[i['claim']].get('decl')
                                            else {'verdict': 'no_declaration', 'band': 'no_declaration',
                                                  'reading': None})} for i in best['inputs']]
            source = next(r['source'] for r in row['proof_routes'] if r['id'] == best['route'])
            item['proof_source'] = {'path': source['path'], 'start': source['start'],
                                    'line': best['freshness'].get('line'),
                                    'freshness': best['freshness']['status']}
            for i in item['inputs']:
                band = i['coverage']['band']
                if band != 'covered':
                    item['warnings'].append(f"input {i['claim']} English coverage: {band}")
        claims[name] = item
    for name, item in claims.items():
        item['downstream'] = len(_closure(name, lambda n: users.get(n, ())))
        for blocker in item.get('blockers', []):
            blocker['status'] = claims[blocker['claim']]['status']
        item['next_action'] = _next_action(item)
    # A blocker "unlocks" a user when it is that user's only blocker on its best complete route.
    unlocks: dict[str, list[str]] = defaultdict(list)
    for name, item in claims.items():
        if item['status'] == 'blocked' and len(item['blockers']) == 1:
            unlocks[item['blockers'][0]['claim']].append(name)
    in_scope = set(rows) if scope is None else _closure(scope, lambda n: uses.get(n, ())) | {scope}
    listed = [claims[n] for n in sorted(in_scope)]

    def pick(status):
        chosen = [i for i in listed if i['status'] in status]
        return sorted(chosen, key=lambda i: (-i['downstream'], i['id']))

    boundary = [n for n in in_scope if claims[n]['status'] == 'unannotated' and users.get(n)]
    result = {
        'scope': scope,
        'counts': {s: sum(claims[n]['status'] == s for n in in_scope) for s in STATUSES},
        'ready': pick({'ready', 'ready_conditional'}),
        'almost_ready': [i for i in pick({'blocked'}) if len(i['blockers']) == 1],
        'blocked': [i for i in pick({'blocked'}) if len(i['blockers']) > 1],
        'stale': pick({'stale'}),
        'needs_annotation': pick({'needs_annotation'}),
        'unannotated_boundary': sorted((claims[n] for n in boundary), key=lambda i: (-i['downstream'], i['id'])),
        'unlocks': sorted(({'claim': b, 'tag': rows[b]['tag'], 'status': claims[b]['status'],
                            'would_become_ready': sorted(set(u) & in_scope), 'downstream': claims[b]['downstream'],
                            'next_action': claims[b]['next_action']}
                           for b, u in unlocks.items() if set(u) & in_scope),
                          key=lambda x: (-len(x['would_become_ready']), -x['downstream'], x['claim'])),
        'limitations': LIMITATIONS,
    }
    result['snapshot'] = digest([ledger, coverage, scope, result])
    result['claims'] = claims
    return result


def _coverage(entry: dict | None) -> dict:
    if not entry:
        return {'verdict': 'unasked', 'band': 'unasked', 'reading': None}
    verdict = entry.get('verdict', 'unasked')
    return {'verdict': verdict, 'band': entry.get('band') if verdict == 'fresh' else verdict,
            'reading': entry.get('reading')}


def _next_action(item: dict) -> str:
    status, name = item['status'], item['id']
    if status in {'ready', 'ready_conditional'}:
        where = item['proof_source']
        text = f"Formalize {name} from {where['path']}:{where['line']} using the listed Lean inputs"
        if item['conditional_on']:
            text += '; keep ' + ', '.join(item['conditional_on']) + ' as explicit hypotheses'
        return text + '. Then add an axiom check and retag only after English coverage review.'
    if status == 'blocked':
        names = ', '.join(b['claim'] for b in item['blockers'])
        return f'Formalize its blockers first: {names}.'
    if status == 'stale':
        return f"Reread {item['proof_source']['path']} and review route {item['route']} before repinning."
    if status == 'needs_annotation':
        return f"Enumerate the immediate dependencies of {name} in {item['proof_source']['path']} and mark the route complete."
    if status == 'unannotated':
        return f"Record a written proof route for {name} from {item['source']}."
    if status == 'formalized':
        band = item['coverage']['band']
        return 'Formalized.' if band == 'covered' else f'Formalized; English coverage {band}: review before relying on it.'
    return {'open': 'Open hypothesis: carry as an assumption.',
            'finite': 'Finite computation: formalize the check (e.g. by decide) before a proof edge can use it.',
            'not_a_target': 'Not a formalization target.'}[status]


def compact(item: dict) -> dict:
    """Agent-facing item without per-route internals; the full record stays in ``claims``."""
    keep = ('id', 'tag', 'status', 'route', 'proof_source', 'blockers', 'conditional_on', 'inputs',
            'downstream', 'warnings', 'next_action', 'lean', 'source')
    return {k: item[k] for k in keep if k in item}


def markdown(result: dict, *, limit: int = 20) -> str:
    counts = result['counts']
    lines = ['# Formalization frontier', '',
             f"Scope: `{result['scope']}`" if result['scope'] else 'Scope: whole ledger', '',
             ' · '.join(f'{k.replace("_", " ")} {v}' for k, v in counts.items() if v), '',
             result['limitations'], '']

    def section(title, items, extra):
        lines.extend([f'## {title} ({len(items)})', ''])
        if not items:
            lines.extend(['None.', ''])
            return
        for item in items[:limit]:
            lines.append(f"- `{item['id']}` ({item.get('downstream', 0)} downstream) — {extra(item)}")
        if len(items) > limit:
            lines.append(f'- … {len(items) - limit} more; use `--format json`.')
        lines.append('')

    section('Ready', result['ready'], lambda i: i['next_action'] + (
        (' Warnings: ' + '; '.join(i['warnings']) + '.') if i['warnings'] else ''))
    section('Almost ready (one blocker)', result['almost_ready'],
            lambda i: f"needs `{i['blockers'][0]['claim']}` ({i['blockers'][0]['kind']}).")
    lines.extend([f"## Highest-value blockers ({len(result['unlocks'])})", ''])
    for u in result['unlocks'][:limit]:
        lines.append(f"- `{u['claim']}` ({u['status']}) would make ready: "
                     + ', '.join(f'`{n}`' for n in u['would_become_ready']))
    lines.append('')
    section('Blocked', result['blocked'], lambda i: 'needs ' + ', '.join(f"`{b['claim']}`" for b in i['blockers']))
    section('Stale source pins', result['stale'], lambda i: i['next_action'])
    section('Incomplete routes', result['needs_annotation'], lambda i: i['next_action'])
    section('Unannotated claims on the graph boundary', result['unannotated_boundary'], lambda i: i['next_action'])
    return '\n'.join(lines).rstrip() + '\n'

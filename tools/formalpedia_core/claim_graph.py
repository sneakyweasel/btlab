"""Review graphs for canonical claims; shared validation lives in research.claim_dependencies."""
from __future__ import annotations
from html import escape
from pathlib import Path
from research.claim_dependencies import (COVERAGE, EDGE_KINDS, LIMITATIONS, digest,
    source_passage, source_state, validate)

def build(ledger: list[dict], root: Path, claim: str, *, choices: dict[str, str] | None = None,
          max_nodes: int = 100) -> dict:
    """Follow exactly one selected written route per claim, with explicit unknown leaves."""
    if not 1 <= max_nodes <= 200:
        raise ValueError('max_nodes must be between 1 and 200')
    errors = validate(ledger, root, check_sources=False)
    if errors:
        raise ValueError('Invalid claim dependencies: ' + '; '.join(errors[:10]))
    rows = {row['id']: row for row in ledger}
    if claim not in rows:
        raise ValueError(f'Unknown ledger claim: {claim}')
    choices = choices or {}
    for name, route in choices.items():
        if name not in rows or route not in {r['id'] for r in rows[name].get('proof_routes', [])}:
            raise ValueError(f'Unknown route selection: {name}={route}')
    nodes, edges, pending = {}, [], [claim]
    omitted = set()
    while pending:
        name = pending.pop(0)
        if name in nodes:
            continue
        if len(nodes) >= max_nodes:
            omitted.add(name)
            continue
        row = rows[name]
        routes = row.get('proof_routes', [])
        chosen = choices.get(name)
        route = next((r for r in routes if r['id'] == chosen), None) if chosen else routes[0] if len(routes) == 1 else None
        node = {'id': name, 'tag': row['tag'], 'claim_kind': row.get('claim_kind', 'result'),
                'statement': row['statement'][:700], 'statement_truncated': len(row['statement']) > 700,
                'source': row['source'], 'route': route['id'] if route else None,
                'available_routes': [r['id'] for r in routes],
                'coverage': route['coverage'] if route else 'unknown',
                'reason': 'route_selection_required' if len(routes) > 1 and not chosen else
                          'unannotated' if not routes else '',
                'lean_trust': row.get('lean_trust')}
        node['conditions'] = row.get('conditions', [])
        nodes[name] = node
        if route is None:
            continue
        node.update(proof_source=route['source'], freshness=source_state(root, route['source']), notes=route['notes'])
        for edge in route['uses']:
            edges.append({'from': name, 'to': edge['claim'], 'kind': edge['kind'],
                          'origin': 'written', 'route': route['id'], 'source': route['source'],
                          'freshness': node['freshness']['status']})
            pending.append(edge['claim'])
    unrelated = set(choices) - set(nodes)
    if unrelated and not omitted:
        raise ValueError('Route selections outside the selected proof: ' + ', '.join(sorted(unrelated)))
    assumptions = {e['to'] for e in edges if e['kind'] == 'assumption'}
    assumptions |= {n for n, data in nodes.items() if data['claim_kind'] == 'hypothesis'}
    summary = {
        'assumptions': sorted(assumptions),
        'non_established_claims': sorted(n for n, data in nodes.items() if data['tag'] in {'CONJECTURE', 'OBSERVATION', 'REFUTED'}),
        'human_proof_claims': sorted(n for n, data in nodes.items() if data['tag'] == 'EXACT — HUMAN PROOF'),
        'finite_computations': sorted(n for n, data in nodes.items() if data['tag'] == 'COMPUTATIONALLY VERIFIED'),
        'claims_with_local_conditions': sorted(n for n, data in nodes.items() if data['conditions']),
        'incomplete_dependencies': sorted(n for n, data in nodes.items() if data['coverage'] != 'complete' and n not in assumptions),
        'stale_annotations': sorted(n for n, data in nodes.items() if data.get('freshness', {}).get('status', 'current') != 'current'),
        'omitted_claims': sorted(omitted),
    }
    complete = not (summary['incomplete_dependencies'] or summary['stale_annotations'] or omitted)
    return {'root': claim, 'granularity': 'claim', 'nodes': nodes, 'edges': edges, 'summary': summary,
            'dependency_coverage_complete': complete, 'truncated': bool(omitted),
            'snapshot': digest([ledger, choices, nodes, edges]), 'limitations': LIMITATIONS}


def markdown(graph: dict) -> str:
    """Render a bounded review view; this is a view of the ledger, never another source."""
    lines = ['# Claim dependencies', '', f"Root: `{graph['root']}`", '',
             'Dependency coverage: ' + ('complete' if graph['dependency_coverage_complete'] else 'incomplete') + '.',
             '', graph['limitations'], '', '## Review boundary', '']
    for key, values in graph['summary'].items():
        lines.append(f"- {key.replace('_', ' ')}: " + (', '.join(f'`{v}`' for v in values) or 'none recorded'))
    lines += ['', '## Written graph', '',
              'Arrows point from a claim to its inputs. Diamonds are assumptions; blue nodes are finite computations. '
              'Dashed borders mark incomplete or stale annotations, not false statements.', '', '```mermaid', 'flowchart TD']
    names = list(graph['nodes']) + graph['summary']['omitted_claims']
    diagram_ids = {name: f'n{i}' for i, name in enumerate(names)}
    for name in names:
        node = graph['nodes'].get(name)
        label = escape(name + (' (omitted)' if node is None else ''), quote=True)
        assumption = name in graph['summary']['assumptions']
        left, right = ('{', '}') if assumption else ('[', ']')
        lines.append(f'  {diagram_ids[name]}{left}"{label}"{right}')
        if node and node['tag'] == 'COMPUTATIONALLY VERIFIED':
            lines.append(f'  class {diagram_ids[name]} finite')
        if node is None or (not assumption and node['coverage'] != 'complete') or (node and node.get('freshness', {}).get('status', 'current') != 'current'):
            lines.append(f'  class {diagram_ids[name]} incomplete')
    for edge in graph['edges']:
        lines.append(f"  {diagram_ids[edge['from']]} -->|{edge['kind']}| {diagram_ids[edge['to']]}")
    lines += ['  classDef incomplete stroke-dasharray: 5 5',
              '  classDef finite fill:#e1efff,color:#142d4e', '```', '',
              '## Selected proof routes', '', '| Claim | Evidence | Route | Coverage | Source | Statement excerpt |',
              '|---|---|---|---|---|---|']
    for name, node in graph['nodes'].items():
        source = node.get('proof_source', {})
        location = source.get('path', node['source'])
        coverage = node['coverage'] + ' / ' + node.get('freshness', {}).get('status', 'not recorded')
        statement = node['statement'].replace('|', '\\|').replace('\n', ' ')
        if node['statement_truncated']:
            statement += ' [truncated; inspect the ledger claim]'
        lines.append(f"| `{name}` | {node['tag']} | {node['route'] or node['reason']} | {coverage} | {location} | {statement} |")
    lines += ['', '## Written dependencies', '']
    for edge in graph['edges']:
        lines.append(f"- `{edge['from']}` → `{edge['to']}` ({edge['kind']}; route `{edge['route']}`).")
    lines += ['', '## Local mathematical conditions', '',
              'These belong to the theorem statements; this graph does not automatically discharge them.', '']
    for name, node in graph['nodes'].items():
        for condition in node['conditions']:
            lines.append(f'- `{name}`: {condition}')
    return '\n'.join(lines) + '\n'

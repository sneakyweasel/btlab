"""Read-only claim graph queries and a separately labelled compiled overlay."""
from __future__ import annotations

from collections import defaultdict

from . import claim_graph, identities, workspace


def compiled_overlay(graph: dict, ledger: list[dict], index: dict, semantic) -> dict:
    """Project exact declaration links, retaining compiler endpoints and bounded paths.

This overlay never fills holes in the written proof graph. A dependency on a
declaration associated with a claim is not a proof of that English claim.
    """
    by_file = defaultdict(list)
    for declaration in index['declarations']:
        by_file[declaration['file']].append(declaration)
    owners, starts, unresolved = defaultdict(set), [], []
    for row in ledger:
        local = {'declarations': by_file[identities.lean_key(row.get('lean'))]}
        for name in identities.row_decls(row):
            found = identities.resolve_declarations(local, name)
            if len(found) != 1 or not found[0].get('qualified_name'):
                if row['id'] in graph['nodes']:
                    unresolved.append({'claim': row['id'], 'reference': name, 'reason': 'ambiguous or missing source identity'})
                continue
            declaration = found[0]
            key = declaration['module'] + '::' + declaration['qualified_name']
            owners[key].add(row['id'])
            if row['id'] in graph['nodes']:
                starts.append((row['id'], key))
    status = semantic.status()
    result = {'status': status['status'], 'export_snapshot': status.get('snapshot'),
              'query_snapshot': status.get('query_snapshot'), 'edges': [], 'unresolved': unresolved,
              'claims_without_declarations': sorted(row['id'] for row in ledger
                  if row['id'] in graph['nodes'] and not identities.row_decls(row)),
              'unmapped_dependencies': [], 'unmapped_count': 0, 'truncated': len(starts) > 20,
              'selected_declarations': len(starts), 'queried_declarations': 0,
              'limitations': 'At most 20 declarations, depth 3 and 100 declaration edges per declaration. '
                  'Exact recorded associations only; not English proof edges. Unindexed helpers, '
                  'unmapped claims and local premises are not discharged. No axiom audit is run.'}
    if status['status'] not in {'current', 'partial'}:
        return result
    queries = semantic.dependencies_batch([name for _, name in starts[:20]],
        depth=3, limit=100, snapshot=status['query_snapshot']) if starts else {}
    seen = set()
    for claim, name in starts[:20]:
        result['queried_declarations'] += 1
        query = queries[name]
        if 'error' in query:
            result['unresolved'].append({'claim': claim, 'reference': name, 'reason': query['error']})
            continue
        result['truncated'] |= query['truncated'] or query['next_offset'] is not None
        paths = {query['target']: [query['target']]}
        for edge in query['items']:
            path = paths.get(edge['from'], []) + [edge['to']]
            paths.setdefault(edge['to'], path)
            targets = owners.get(edge['to'], set())
            if not targets:
                result['unmapped_count'] += 1
                if len(result['unmapped_dependencies']) < 20:
                    result['unmapped_dependencies'].append(edge['to'])
            for target in sorted(targets - {claim}):
                key = (claim, target, name, edge['from'], edge['to'], edge['edge'])
                if key in seen:
                    continue
                seen.add(key)
                result['edges'].append({'from': claim, 'to': target, 'kind': edge['edge'],
                    'origin': 'compiled', 'root_declaration': name, 'declaration_from': edge['from'],
                    'declaration_to': edge['to'], 'declaration_path': path,
                    'export_snapshot': query['export_snapshot'], 'query_snapshot': query['snapshot']})
    after = semantic.status()
    if after.get('query_snapshot') != status.get('query_snapshot'):
        raise ValueError('Semantic snapshot changed during claim projection; retry')
    return result


def query(catalogue, ledger_id: str, *, choices: dict[str, str] | None = None,
          include_compiled: bool = False, max_nodes: int = 100,
          limit: int = 50, offset: int = 0, snapshot: str | None = None) -> dict:
    """Stable paginated nodes/edges; sources are reread so prose edits invalidate pages."""
    from formalpedia_catalog import page_bounds
    from .semantic_query import SemanticCatalogue

    page_bounds(limit, offset)
    index, ledger, _ = catalogue.snapshot()
    graph = claim_graph.build(ledger, workspace.ROOT, ledger_id, choices=choices, max_nodes=max_nodes)
    compiled = {'status': 'not_requested', 'edges': []}
    if include_compiled:
        if catalogue._semantic is None:
            catalogue._semantic = SemanticCatalogue()
        compiled = compiled_overlay(graph, ledger, index, catalogue._semantic)
    token = claim_graph.digest([graph['snapshot'], compiled])
    if snapshot is not None and snapshot != token:
        raise ValueError('Claim graph snapshot changed; restart pagination')
    items = ([{'item_type': 'node', **node} for node in graph['nodes'].values()]
             + [{'item_type': 'edge', **edge} for edge in graph['edges']]
             + [{'item_type': 'edge', **edge} for edge in compiled['edges']])
    return {'root': ledger_id, 'granularity': 'claim', 'snapshot': token,
            'summary': graph['summary'], 'dependency_coverage_complete': graph['dependency_coverage_complete'],
            'truncated': graph['truncated'], 'compiled': {k: v for k, v in compiled.items() if k != 'edges'},
            'items': items[offset:offset + limit], 'total': len(items), 'offset': offset,
            'next_offset': offset + limit if offset + limit < len(items) else None,
            'limitations': graph['limitations']}

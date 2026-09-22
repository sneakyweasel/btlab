"""Shared, local, read-only discovery API for the CLI and MCP server."""
from __future__ import annotations

from collections import Counter
import hashlib
import json
import re
import threading

import formalpedia as fp
from lab_scope import active_lean_modules, validate_scope

TRUST_NOTICE = ('Source markers are navigation evidence, not an executed Lean check or a '
                'transitive axiom audit. Read the complete hypotheses before using a result.')
STOP = {'a', 'an', 'the', 'of', 'and', 'or', 'for', 'with', 'from', 'that', 'is', 'in'}


def tokens(text: str) -> list[str]:
    text = re.sub(r'([a-z])([A-Z])', r'\1 \2', text).replace('_', ' ')
    return [x for x in re.findall(r'\w+', text.casefold()) if x not in STOP]


def compact(decl: dict) -> dict:
    fields = ('id', 'qualified_name', 'name', 'namespace', 'module', 'file', 'line',
              'kind', 'visibility', 'deprecated', 'trust', 'ledger_exact')
    result = {key: decl.get(key) for key in fields}
    result.update(doc=decl.get('doc', '')[:400],
                  signature=decl.get('signature', '')[:1200],
                  signature_truncated=len(decl.get('signature', '')) > 1200)
    return result


def page_bounds(limit: int, offset: int) -> None:
    if not 1 <= limit <= 100 or offset < 0:
        raise ValueError('limit must be between 1 and 100; offset must be nonnegative')


class Catalogue:
    """Refresh an in-memory snapshot when local sources or the ledger change.

    No request writes generated artifacts, invokes Lean, or sends mathematics to
    another service. A lock keeps concurrent MCP requests on a coherent snapshot.
    """

    def __init__(self):
        self._lock = threading.RLock()
        self._stamp = None
        self._index = None
        self._ledger = []
        self._snapshot = ''
        self._documents = {}

    def _state(self):
        paths = fp.sources() + [fp.LEDGER]
        return tuple((p.relative_to(fp.ROOT).as_posix(), p.stat().st_mtime_ns, p.stat().st_size)
                     for p in paths if p.exists())

    def snapshot(self) -> tuple[dict, list[dict], str]:
        with self._lock:
            before = self._state()
            if self._index is None or before != self._stamp:
                for _ in range(3):
                    index = fp.build()
                    ledger = json.loads(fp.LEDGER.read_text(encoding='utf-8'))
                    after = self._state()
                    if before == after:
                        break
                    before = after
                else:
                    raise RuntimeError('Sources kept changing during indexing; retry after the edits settle')
                by_id = {row['id']: row for row in ledger}
                self._documents = {}
                for d in index['declarations']:
                    fields = [d['source_name'], d['doc'], d['signature'], d['module']]
                    fields += [by_id[r].get('statement', '') for r in d['ledger_exact'] if r in by_id]
                    self._documents[d['id']] = (' '.join(fields).casefold(),
                                                 set(tokens(' '.join(fields))))
                self._index, self._ledger, self._stamp = index, ledger, after
                self._snapshot = hashlib.sha256(fp.render(index).encode()).hexdigest()[:16]
            return self._index, self._ledger, self._snapshot

    def search(self, query: str, *, namespace: str | None = None, module: str | None = None,
               kind: str | None = None, ledger_id: str | None = None,
               include_private: bool = False, include_deprecated: bool = False,
               limit: int = 20, offset: int = 0, scope: str = 'active') -> dict:
        page_bounds(limit, offset)
        validate_scope(scope)
        if len(query) > 2000:
            raise ValueError('query must not exceed 2000 characters; search with a few key terms')
        with self._lock:
            index, _, snapshot = self.snapshot()
            documents = self._documents
        terms, needle = tokens(query), query.strip().casefold()
        active = active_lean_modules(index)
        hits = []
        for d in index['declarations']:
            if scope != 'all' and (d['module'] in active) != (scope == 'active'):
                continue
            if not include_private and d['visibility'] == 'private':
                continue
            if not include_deprecated and d['deprecated']:
                continue
            if namespace and not (d['source_name'].startswith(namespace + '.')
                                  or d['namespace'] == namespace):
                continue
            if module and d['module'] != module:
                continue
            if kind and d['kind'] != kind:
                continue
            if ledger_id and ledger_id not in d['ledger_exact']:
                continue
            text, words = documents[d['id']]
            direct = needle in (d['source_name'].casefold(), d['name'].casefold())
            if terms and not direct and not all(t in words or t in text for t in terms):
                continue
            if needle and not terms and needle not in text:
                continue
            score = (1000 if needle == d['source_name'].casefold() else
                     900 if needle == d['name'].casefold() else
                     700 if needle and d['source_name'].casefold().endswith('.' + needle) else 0)
            if needle and needle in d['source_name'].casefold():
                score += 100
            score += sum(20 for t in terms if t in set(tokens(d['name'])))
            score += sum(5 for t in terms if t in set(tokens(d['doc'])))
            score += int(bool(d['doc'])) + int(bool(d['ledger_exact']))
            hits.append((score, d))
        hits.sort(key=lambda item: (-item[0], item[1]['id'], item[1]['file'], item[1]['line']))
        selected = hits[offset:offset + limit]
        return {'snapshot': snapshot, 'query': query, 'scope': scope, 'total': len(hits), 'offset': offset,
                'next_offset': offset + limit if offset + limit < len(hits) else None,
                'results': [dict(compact(d), score=score, scope='active' if d['module'] in active else 'archive')
                            for score, d in selected],
                'trust_notice': TRUST_NOTICE}

    def show(self, name: str, *, module: str | None = None, include_private: bool = False) -> dict:
        index, ledger, snapshot = self.snapshot()
        found = fp.resolve_declarations(index, name, module=module, include_private=include_private)
        if len(found) != 1:
            return {'status': 'ambiguous' if found else 'not_found', 'query': name,
                    'snapshot': snapshot, 'candidates': [compact(d) for d in found[:100]],
                    'total_candidates': len(found),
                    'hint': 'Use a fully qualified name or the module filter; no candidate was selected.'}
        d = found[0]
        scope = 'active' if d['module'] in active_lean_modules(index) else 'archive'
        reach = fp.reachable(index)
        papers = [paper for paper, root in fp.PAPER_ROOTS.items()
                  if d['module'] in reach.get(root, set()) | {root}]
        return {'status': 'found', 'snapshot': snapshot, 'scope': scope, 'declaration': d,
                'exact_claims': [row for row in ledger if row['id'] in d['ledger_exact']],
                'file_claim_ids': d['ledger'], 'reachable_from_paper_roots': papers,
                'trust_notice': TRUST_NOTICE}

    def claim(self, ledger_id: str) -> dict:
        index, ledger, snapshot = self.snapshot()
        row = next((r for r in ledger if r['id'] == ledger_id), None)
        if row is None:
            return {'status': 'not_found', 'ledger_id': ledger_id, 'snapshot': snapshot}
        declarations = []
        for name in fp.row_decls(row):
            matches = fp.resolve_declarations(index, name, file=fp.lean_key(row.get('lean')))
            declarations.append({'reference': name,
                                 'status': 'resolved' if len(matches) == 1 else
                                           'ambiguous' if matches else 'not_found',
                                 'candidates': matches})
        return {'status': 'found', 'snapshot': snapshot, 'claim': row,
                'declarations': declarations, 'trust_notice': TRUST_NOTICE}

    def impact(self, target: str, *, limit: int = 50, offset: int = 0) -> dict:
        page_bounds(limit, offset)
        index, _, snapshot = self.snapshot()
        needle = target.replace('\\', '/')
        modules = [name for name, data in index['modules'].items()
                   if name == target or data['file'] == needle
                   or data['file'].endswith('/' + needle.lstrip('/'))]
        if not modules:
            matches = fp.resolve_declarations(index, target)
            modules = sorted({d['module'] for d in matches})
        if len(modules) != 1:
            return {'status': 'ambiguous' if modules else 'not_found', 'target': target,
                    'snapshot': snapshot, 'candidates': modules}
        name = modules[0]
        reverse = fp.dependents(index)
        dependents = fp.transitive(reverse, name)
        return {'status': 'found', 'snapshot': snapshot, 'module': name,
                'granularity': 'module imports; not proof-level dependency evidence',
                'imports': index['modules'][name]['imports'],
                'direct_dependents': reverse.get(name, []),
                'total_dependents': len(dependents),
                'dependents': dependents[offset:offset + limit],
                'next_offset': offset + limit if offset + limit < len(dependents) else None,
                'paper_roots_affected': [p for p, root in fp.PAPER_ROOTS.items()
                                         if root == name or root in dependents]}

    def status(self) -> dict:
        index, _, snapshot = self.snapshot()
        active = active_lean_modules(index)
        public = [d for d in index['declarations'] if d['visibility'] == 'public']
        names = Counter(d['name'] for d in public)
        duplicates = Counter(d['qualified_name'] for d in public)
        try:
            disk = json.loads(fp.INDEX.read_text(encoding='utf-8'))
        except (OSError, ValueError):
            disk = None
        return {'schema': index['schema'], 'snapshot': snapshot,
                'source': 'live working tree', 'saved_index_current': disk == index,
                'totals': index['totals'], 'public_declarations': len(public),
                'scope_modules': {'active': len(active), 'archive': len(index['modules']) - len(active)},
                'documented_public_declarations': sum(bool(d['doc']) for d in public),
                'ambiguous_short_spellings': sum(n > 1 for n in names.values()),
                'duplicate_public_identities': [n for n, count in duplicates.items() if count > 1],
                'trust_notice': TRUST_NOTICE}

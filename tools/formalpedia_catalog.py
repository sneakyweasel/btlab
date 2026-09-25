"""Shared, local, read-only discovery API for the CLI and MCP server."""
from __future__ import annotations

from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import re
import threading

from formalpedia_core import (audits as fp_audits, graph as fp_graph, identities as fp_identities,
                              source as fp_source, workspace as fp_workspace)
from lab_scope import active_lean_modules, validate_scope
from research.claims import claim_files, load_claims

TRUST_NOTICE = ('Source markers are navigation evidence, not an executed Lean check or a '
                'transitive axiom audit. axiom_audits quote committed #print axioms output, '
                'current as of the commit that recorded it. Read the complete hypotheses, '
                'including signature_context, before using a result.')
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
                  signature_truncated=len(decl.get('signature', '')) > 1200,
                  signature_complete=decl.get('signature_complete'),
                  signature_context=decl.get('signature_context', []))
    return result


def page_bounds(limit: int, offset: int) -> None:
    if not 1 <= limit <= 100 or offset < 0:
        raise ValueError('limit must be between 1 and 100; offset must be nonnegative')


class Catalogue:
    """Refresh an in-memory snapshot when local sources or the ledger change.

    No request writes generated artifacts, invokes Lean, or sends mathematics to
    another service. A lock keeps concurrent MCP requests on a coherent snapshot.

    ``persist`` names a file that carries the built index between processes, for the
    CLI, which otherwise rebuilds it on every call. It is reused only while every source,
    the ledger, every axiom artifact and the indexing code itself are unchanged.
    """

    def __init__(self, semantic=None, persist: Path | None = None):
        self._persist = persist
        self._lock = threading.RLock()
        self._stamp = None
        self._index = None
        self._ledger = []
        self._claim_locations = {}
        self._snapshot = ''
        self._documents = None
        self._audits = {'by_name': {}, 'artifacts': [], 'problems': []}
        self._semantic = semantic

    def compiled(self, name: str) -> dict:
        """Optional exact compiler view; missing/stale metadata never hides live source."""
        from formalpedia_core.semantic_query import SemanticCatalogue
        with self._lock:
            if self._semantic is None:
                self._semantic = SemanticCatalogue()
            try:
                return self._semantic.show(name)
            except (ValueError, OSError) as exc:
                return {'status': 'unavailable', 'reason': str(exc),
                        'freshness': self._semantic.status()}

    def _state(self):
        paths = fp_source.sources() + list(claim_files(fp_workspace.ROOT))
        paths += [p for check in fp_audits.checks() for p in (check, check.with_suffix('.expected'))]
        return tuple((p.relative_to(fp_workspace.ROOT).as_posix(), p.stat().st_mtime_ns, p.stat().st_size)
                     for p in paths if p.exists())

    @staticmethod
    def _code() -> str:
        """Fingerprint of the code that builds the index: a parser change invalidates the cache."""
        tools = Path(__file__).resolve().parent
        files = sorted((tools / 'formalpedia_core').glob('*.py')) + [
            tools / name for name in ('lean_source.py', 'trust_boundary.py', 'formalpedia_catalog.py')]
        files += [tools.parent / 'src/research' / name for name in ('claims.py', 'claim_dependencies.py')]
        digest = hashlib.sha256()
        for path in files:
            digest.update(path.name.encode() + b'\0' + path.read_bytes())
        return digest.hexdigest()

    def _restore(self, state) -> bool:
        if self._persist is None:
            return False
        try:
            saved = json.loads(self._persist.read_text(encoding='utf-8'))
            if (saved.get('state') != [list(row) for row in state]
                    or saved.get('code') != self._code()
                    or saved.get('root') != str(fp_workspace.ROOT)):
                return False
            claims = load_claims(fp_workspace.ROOT)
            index, audits = saved['index'], saved['audits']
            snapshot = hashlib.sha256(fp_source.render([index, claims.snapshot, audits]).encode()).hexdigest()[:16]
            if snapshot != saved['snapshot'] or self._state() != state:
                return False
            documents = {key: (text, set(words)) for key, (text, words) in saved['documents'].items()}
        except (OSError, ValueError, KeyError, TypeError, AttributeError):
            return False
        self._index, self._audits = index, audits
        self._ledger, self._claim_locations = claims.entries, claims.locations
        self._stamp, self._snapshot = state, snapshot
        self._documents = documents
        return True

    def _save(self) -> None:
        if self._persist is None:
            return
        try:
            self._persist.parent.mkdir(parents=True, exist_ok=True)
            partial = self._persist.with_name(f'{self._persist.name}.{os.getpid()}.tmp')
            partial.write_text(json.dumps({'state': [list(row) for row in self._stamp],
                                           'root': str(fp_workspace.ROOT),
                                           'code': self._code(), 'snapshot': self._snapshot,
                                           'index': self._index, 'audits': self._audits,
                                           'documents': {key: [text, sorted(words)] for key, (text, words)
                                                         in self._search_documents().items()}}),
                                encoding='utf-8')
            os.replace(partial, self._persist)
        except OSError:
            pass  # a cache that cannot be written only costs the next call a rebuild

    def _search_documents(self) -> dict:
        """Search text per declaration, built on first search rather than on every load."""
        if self._documents is None:
            by_id = {row['id']: row for row in self._ledger}
            self._documents = {}
            for d in self._index['declarations']:
                fields = [d['source_name'], d['doc'], d['signature'], d['module']]
                fields += [by_id[r].get('statement', '') for r in d['ledger_exact'] if r in by_id]
                self._documents[d['id']] = (' '.join(fields).casefold(), set(tokens(' '.join(fields))))
        return self._documents

    def snapshot(self) -> tuple[dict, list[dict], str]:
        with self._lock:
            before = self._state()
            if self._index is None and self._restore(before):
                return self._index, self._ledger, self._snapshot
            if self._index is None or before != self._stamp:
                for _ in range(3):
                    claims = load_claims(fp_workspace.ROOT)
                    ledger = claims.entries
                    index = fp_source.build(ledger)
                    audits = fp_audits.scan()
                    after = self._state()
                    if before == after:
                        break
                    before = after
                else:
                    raise RuntimeError('Sources kept changing during indexing; retry after the edits settle')
                self._claim_locations = claims.locations
                self._documents = None
                self._index, self._ledger, self._stamp = index, ledger, after
                self._audits = audits
                self._snapshot = hashlib.sha256(fp_source.render([index, claims.snapshot, audits]).encode()).hexdigest()[:16]
                self._save()
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
            documents = self._search_documents()
        terms, needle = tokens(query), query.strip().casefold()
        active = active_lean_modules(index, fp_workspace.ROOT)
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
        if '::' in name and '::private::' not in name:
            owner, name = name.split('::', 1)
            if module and module != owner:
                raise ValueError('Module filter conflicts with the canonical ID')
            module = owner
        found = fp_identities.resolve_declarations(index, name, module=module, include_private=include_private)
        if not found:
            compiled = self.compiled(module + '::' + name if module else name)
            if compiled['status'] == 'ambiguous':
                return {'status': 'ambiguous', 'query': name, 'snapshot': snapshot,
                        'source_status': 'not_indexed', 'compiled': compiled,
                        'candidates': compiled['candidates'],
                        'total_candidates': compiled['candidate_count'],
                        'hint': 'Use Module.Name::fully.qualified.name; no candidate was selected.'}
            if compiled['status'] == 'found':
                row = compiled['declaration']
                if row['name'].startswith('_private.') and not include_private:
                    compiled = {'status': 'private', 'hint': 'Pass include_private to inspect this compiler identity.'}
                else:
                    reach = fp_graph.reachable(index)
                    source_file = 'formal/' + row['module'].replace('.', '/') + '.lean'
                    file_claims = [r for r in ledger if fp_identities.lean_key(r.get('lean')) == source_file]
                    return {'status': 'found', 'snapshot': snapshot, 'canonical_id': row['id'],
                            'source_status': 'not_indexed', 'declaration': None, 'compiled': compiled,
                            'source_file': source_file,
                            'scope': 'active' if row['module'] in active_lean_modules(index, fp_workspace.ROOT) else 'archive',
                            'exact_claims': [r for r in file_claims if row['name'] in fp_identities.row_decls(r)],
                            'file_claim_ids': [r['id'] for r in file_claims],
                            'reachable_from_paper_roots': [p for p, root in fp_graph.PAPER_ROOTS.items()
                                if row['module'] in reach.get(root, set()) | {root}],
                            'trust_notice': TRUST_NOTICE}
        if len(found) != 1:
            return {'status': 'ambiguous' if found else 'not_found', 'query': name,
                    'snapshot': snapshot, 'candidates': [compact(d) for d in found[:100]],
                    'total_candidates': len(found),
                    **({'compiled': compiled} if not found else {}),
                    'hint': 'Use a fully qualified name or the module filter; no candidate was selected.'}
        d = found[0]
        scope = 'active' if d['module'] in active_lean_modules(index, fp_workspace.ROOT) else 'archive'
        reach = fp_graph.reachable(index)
        papers = [paper for paper, root in fp_graph.PAPER_ROOTS.items()
                  if d['module'] in reach.get(root, set()) | {root}]
        canonical = d['module'] + '::' + d['qualified_name'] if d['qualified_name'] else None
        compiled = self.compiled(canonical) if canonical else {
            'status': 'unmapped_private', 'reason': 'Source private names are not compiler identities.'}
        return {'status': 'found', 'snapshot': snapshot, 'scope': scope, 'declaration': d,
                'canonical_id': canonical, 'source_status': 'found', 'compiled': compiled,
                'axiom_audits': self.axiom_audits(d),
                'exact_claims': [row for row in ledger if row['id'] in d['ledger_exact']],
                'file_claim_ids': d['ledger'], 'reachable_from_paper_roots': papers,
                'trust_notice': TRUST_NOTICE}

    def claim(self, ledger_id: str) -> dict:
        with self._lock:
            index, ledger, snapshot = self.snapshot()
            location = self._claim_locations.get(ledger_id, {}).copy()
        row = next((r for r in ledger if r['id'] == ledger_id), None)
        if row is None:
            return {'status': 'not_found', 'ledger_id': ledger_id, 'snapshot': snapshot}
        declarations = []
        for name in fp_identities.row_decls(row):
            matches = fp_identities.resolve_declarations(index, name, file=fp_identities.lean_key(row.get('lean')))
            declarations.append({'reference': name,
                                 'status': 'resolved' if len(matches) == 1 else
                                           'ambiguous' if matches else 'not_found',
                                 'candidates': matches,
                                 'axiom_audits': self.axiom_audits(matches[0]) if len(matches) == 1 else []})
        resolved = [d for d in declarations if d['status'] == 'resolved']
        audited = [d for d in resolved if d['axiom_audits']]
        return {'status': 'found', 'snapshot': snapshot, 'claim': row,
                'claim_location': location,
                'declarations': declarations,
                'axiom_audit_coverage': {
                    'resolved_declarations': len(resolved), 'audited': len(audited),
                    'all_standard': (all(a['standard'] for d in audited for a in d['axiom_audits'])
                                     if audited else None),
                    'unaudited': [d['reference'] for d in resolved if not d['axiom_audits']]},
                'trust_notice': TRUST_NOTICE}

    def axiom_audits(self, decl: dict) -> list[dict]:
        """Recorded ``#print axioms`` answers for one source declaration, if any artifact asks."""
        name = decl.get('qualified_name')
        return list(self._audits['by_name'].get(name, [])) if name else []

    def audits(self, *, limit: int = 50, offset: int = 0) -> dict:
        """Artifact consistency problems and coverage, readable without a Lean toolchain."""
        page_bounds(limit, offset)
        index, ledger, snapshot = self.snapshot()
        problems = self._audits['problems'] + fp_audits.unresolved(self._audits, index)
        return {'snapshot': snapshot, 'artifacts': len(self._audits['artifacts']),
                'problem_count': len(problems), 'problems': problems[offset:offset + limit],
                'next_offset': offset + limit if offset + limit < len(problems) else None,
                'coverage': self._audit_coverage(index, ledger),
                'limitations': self._audits.get('limitations', '')}

    def _audit_coverage(self, index: dict, ledger: list[dict]) -> dict:
        by_name = self._audits['by_name']
        exact = [d for d in index['declarations'] if d['ledger_exact'] and d.get('qualified_name')]
        audited_exact = [d for d in exact if d['qualified_name'] in by_name]
        return {'audited_declarations': len(by_name),
                'declarations_with_exact_ledger_references': len(exact),
                'of_which_audited': len(audited_exact),
                'nonstandard_audits': sum(not a['standard'] for rows in by_name.values() for a in rows)}

    def frontier(self, **options) -> dict:
        """Formalization work queue from written routes, evidence labels and Jev coverage."""
        from formalpedia_core.claim_query import frontier_query
        with self._lock:
            return frontier_query(self, **options)

    def claim_dependencies(self, ledger_id: str, **options) -> dict:
        """Inspect selected written proof routes and optional compiled associations."""
        from formalpedia_core.claim_query import query
        with self._lock:
            return query(self, ledger_id, **options)

    def impact(self, target: str, *, limit: int = 50, offset: int = 0) -> dict:
        page_bounds(limit, offset)
        index, _, snapshot = self.snapshot()
        needle = target.replace('\\', '/')
        modules = [name for name, data in index['modules'].items()
                   if name == target or data['file'] == needle
                   or data['file'].endswith('/' + needle.lstrip('/'))]
        if not modules:
            matches = fp_identities.resolve_declarations(index, target)
            modules = sorted({d['module'] for d in matches})
        if len(modules) != 1:
            return {'status': 'ambiguous' if modules else 'not_found', 'target': target,
                    'snapshot': snapshot, 'candidates': modules}
        name = modules[0]
        reverse = fp_graph.dependents(index)
        dependents = fp_graph.transitive(reverse, name)
        return {'status': 'found', 'snapshot': snapshot, 'module': name,
                'granularity': 'module imports; not proof-level dependency evidence',
                'imports': index['modules'][name]['imports'],
                'direct_dependents': reverse.get(name, []),
                'total_dependents': len(dependents),
                'dependents': dependents[offset:offset + limit],
                'next_offset': offset + limit if offset + limit < len(dependents) else None,
                'paper_roots_affected': [p for p, root in fp_graph.PAPER_ROOTS.items()
                                         if root == name or root in dependents]}

    def status(self) -> dict:
        index, _, snapshot = self.snapshot()
        active = active_lean_modules(index, fp_workspace.ROOT)
        public = [d for d in index['declarations'] if d['visibility'] == 'public']
        names = Counter(d['name'] for d in public)
        duplicates = Counter(d['qualified_name'] for d in public)
        try:
            disk = json.loads(fp_workspace.INDEX.read_text(encoding='utf-8'))
            export_state = 'current' if disk == index else 'stale'
        except FileNotFoundError:
            disk, export_state = None, 'missing'
        except (OSError, ValueError):
            disk = None
            export_state = 'unreadable'
        return {'schema': index['schema'], 'snapshot': snapshot,
                'source': 'live working tree', 'saved_index_current': disk == index,
                'local_export': {'required': False, 'state': export_state},
                'totals': index['totals'], 'public_declarations': len(public),
                'ledger_links': {
                    'declarations_with_exact_ledger_references':
                        sum(bool(d['ledger_exact']) for d in index['declarations']),
                    'declarations_in_a_ledger_file_only':
                        sum(bool(d['ledger']) and not d['ledger_exact'] for d in index['declarations']),
                    'note': ('totals.declarations_with_a_ledger_row counts file association; '
                             'only exact references name the declaration')},
                'axiom_audits': {'artifacts': len(self._audits['artifacts']),
                                 'problems': len(self._audits['problems']),
                                 **self._audit_coverage(index, self._ledger)},
                'scope_modules': {'active': len(active), 'archive': len(index['modules']) - len(active)},
                'documented_public_declarations': sum(bool(d['doc']) for d in public),
                'ambiguous_short_spellings': sum(n > 1 for n in names.values()),
                'duplicate_public_identities': [n for n, count in duplicates.items() if count > 1],
                'trust_notice': TRUST_NOTICE}

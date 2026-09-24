"""Read-only queries over current compiler metadata and historical snapshots."""
from __future__ import annotations

from collections import deque
import json
from pathlib import Path
import threading
from formalpedia_core import workspace as fp_workspace
from formalpedia_catalog import page_bounds
from .semantic_common import (REBUILD, LIMITATIONS, digest, inputs, file_stamp, known_modules, environment_changes, conclusion, structural_match, compact, locked)
from .semantic_store import SnapshotStore


class SemanticCatalogue:
    """Never runs Lean or writes files. Only current modules enter semantic queries."""

    def __init__(self, root: Path | None = None, cache: Path | None = None):
        self.root = (root or fp_workspace.ROOT).resolve()
        self.cache = cache or self.root / '.cache/formalpedia/semantic'
        self._store = SnapshotStore(self.cache)
        self._loaded: tuple[str, dict] | None = None
        self._lock = threading.RLock()
        self._stale: set[str] = set()

    def _load(self, snapshot: str | None = None) -> dict:
        snapshot, data = self._store.load(snapshot)
        self._loaded = snapshot, data
        return data

    @locked
    def status(self) -> dict:
        base = {'rebuild': REBUILD, 'limitations': LIMITATIONS}
        try:
            data = self._load()
            self._store.check_references(data)
            envs, owners = self._store.environment_records(data)
        except FileNotFoundError:
            return dict(base, status='missing')
        except (OSError, ValueError) as exc:
            return dict(base, status='unreadable', reason=str(exc))
        now = inputs(self.root)
        stamps = {p: file_stamp(Path(p)) for p in {p for env in envs.values() for p in env['objects']}}
        changes = {key: environment_changes(env, now, stamps) for key, env in envs.items()}
        changed = sorted(set().union(*(v[0] for v in changes.values())))
        changed_objects = set().union(*(v[1] for v in changes.values()))
        self._stale = {m for m, key in owners.items() if '*' in changes[key][2] or m in changes[key][2]}
        missing = sorted(set(known_modules(now)) - set(owners))
        state = ('partial' if len(self._stale) < len(owners) else 'stale') if self._stale else 'current'
        # The page token includes live freshness, so a file edit cannot silently remove
        # rows halfway through pagination. Historical diffs still take the export ID.
        token = digest([self._loaded[0], sorted(self._stale), missing])
        counts = self._store.counts(data)
        return dict(base, status=state, query_snapshot=token,
                    snapshot=self._loaded[0], built_at=data['built_at'],
                    declarations=sum(counts.values()), modules=data['modules'][:20],
                    current_declarations=sum(n for m, n in counts.items() if m not in self._stale),
                    storage_schema=data['schema'],
                    module_count=len(data['modules']), modules_truncated=len(data['modules']) > 20,
                    current_module_count=len(owners) - len(self._stale),
                    stale_modules=sorted(self._stale)[:20], stale_module_count=len(self._stale),
                    unindexed_modules=missing[:20], unindexed_module_count=len(missing),
                    coverage=data['coverage'], changed_inputs=changed[:20],
                    changed_input_count=len(changed), changed_object_count=len(changed_objects))

    def _current(self, snapshot: str | None = None, module: str | None = None) -> tuple[dict, dict]:
        status = self.status()
        if status['status'] not in {'current', 'partial'}:
            raise ValueError(f"Semantic index is {status['status']}; run {REBUILD}")
        if snapshot is not None and snapshot != status['query_snapshot']:
            raise ValueError('Semantic snapshot changed; restart pagination')
        data = self._loaded[1]
        modules = (set(data['modules']) if module is None else {module}) - self._stale
        return dict(data, declarations=self._store.index(data, modules)), status

    @staticmethod
    def _query_info(status: dict) -> dict:
        return {'snapshot': status['query_snapshot'], 'export_snapshot': status['snapshot'],
                'freshness': status['status'], 'stale_modules': status['stale_modules'],
                'stale_module_count': status['stale_module_count'],
                'unindexed_modules': status['unindexed_modules'],
                'unindexed_module_count': status['unindexed_module_count']}

    def _query_resolve(self, rows: list[dict], name: str) -> list[dict]:
        # Resolve against all indexed identities first: stale candidates must not make
        # an ambiguous short name look unique or a historical theorem look absent.
        modules = [name.split('::', 1)[0]] if '::' in name else None
        if modules and modules[0] in self._stale:
            raise ValueError(f'Module {modules[0]} is stale; run {REBUILD}')
        found = self._resolve(self._store.index(self._loaded[1], modules), name)
        stale = sorted({r['module'] for r in found if r['module'] in self._stale})
        if stale:
            raise ValueError('Target includes stale modules: ' + ', '.join(stale[:5]) + '; run ' + REBUILD)
        return self._resolve(rows, name)

    @staticmethod
    def _resolve(rows: list[dict], name: str) -> list[dict]:
        exact = [r for r in rows if name in (r['id'], r['name'])]
        return exact or [r for r in rows if r['name'].split('.')[-1] == name]

    @locked
    def axioms(self, identities: list[str]) -> dict:
        """Kernel axiom lists for many ``Module::name`` identities after one freshness check.

        An identity absent from the current export, or in a stale module, maps to None.
        Raises ValueError when no current or partial export exists.
        """
        data, status = self._current()
        rows = {r['id']: r for r in data['declarations']}
        return dict(self._query_info(status), axioms={
            identity: (list(rows[identity].get('axioms') or []) if identity in rows else None)
            for identity in identities})

    @locked
    def show(self, name: str, include_ast: bool = False) -> dict:
        data, status = self._current(module=name.split('::', 1)[0] if '::' in name else None)
        rows = self._query_resolve(data['declarations'], name)
        result = dict(self._query_info(status), limitations=LIMITATIONS)
        if len(rows) != 1:
            return dict(result, status='ambiguous' if rows else 'not_found',
                        candidates=[compact(r) for r in rows[:20]], candidate_count=len(rows))
        row = dict(self._store.detail(self._loaded[1], rows[0]))
        if not include_ast:
            row.pop('type_ast')
        return dict(result, status='found', declaration=row)

    @locked
    def search(self, constants: list[str] | None = None, like: str | None = None,
               pattern: list | dict | None = None, part: str = 'type', kind: str | None = None,
               module: str | None = None, include_private: bool = False, limit: int = 20,
               offset: int = 0, snapshot: str | None = None) -> dict:
        page_bounds(limit, offset)
        if part not in {'type', 'conclusion'}:
            raise ValueError('part must be type or conclusion')
        if like and pattern is not None:
            raise ValueError('Use either like or pattern')
        if len(constants or []) > 32 or len(json.dumps(pattern)) > 20000:
            raise ValueError('Structural query exceeds its size budget')
        data, status = self._current(snapshot, module)
        if module in self._stale:
            raise ValueError(f'Module {module} is stale; run {REBUILD}')
        if like:
            # The comparison declaration may belong to a different module from
            # the requested result scope. Resolve it independently of that filter.
            candidates = self._store.index(self._loaded[1],
                [like.split('::', 1)[0]] if '::' in like else None)
            found = self._query_resolve(candidates, like)
            if len(found) != 1:
                raise ValueError('like must resolve to exactly one declaration; use semantic show')
            pattern = self._store.detail(self._loaded[1], found[0])['type_ast']
            if part == 'conclusion':
                pattern = conclusion(pattern)
        def has_holes(value):
            return isinstance(value, dict) or isinstance(value, list) and any(has_holes(v) for v in value)
        exact = digest(pattern) if pattern is not None and not has_holes(pattern) else None
        rows = []
        for row in data['declarations']:
            if (not include_private and row['name'].startswith('_private.')) or (kind and row['kind'] != kind):
                continue
            if module and row['module'] != module:
                continue
            if not set(constants or []).issubset(row['type_dependencies']):
                continue
            if exact is not None:
                if row['type_sha256' if part == 'type' else 'conclusion_sha256'] != exact:
                    continue
            elif pattern is not None:
                ast = self._store.detail(self._loaded[1], row)['type_ast']
                target = ast if part == 'type' else conclusion(ast)
                if not structural_match(pattern, target):
                    continue
            rows.append(compact(row))
        return {**self._query_info(status), 'match': 'elaborated_structural_syntax',
                'items': rows[offset:offset + limit], 'total': len(rows),
                'next_offset': offset + limit if offset + limit < len(rows) else None,
                'limitations': LIMITATIONS}

    @locked
    def dependencies(self, name: str, direction: str = 'uses', edge: str = 'all',
                     depth: int = 1, limit: int = 30, offset: int = 0,
                     snapshot: str | None = None) -> dict:
        page_bounds(limit, offset)
        if direction not in {'uses', 'used_by'} or edge not in {'type', 'value', 'all'} or not 1 <= depth <= 5:
            raise ValueError('Expected uses/used_by, type/value/all, and depth 1..5')
        data, status = self._current(snapshot)
        rows = data['declarations']
        selected = self._query_resolve(rows, name)
        if len(selected) != 1:
            raise ValueError('Target must resolve uniquely; use semantic show')
        by_name: dict[str, list[dict]] = {}
        for row in rows:
            by_name.setdefault(row['name'], []).append(row)
        graph: dict[str, set[tuple[str, str]]] = {}
        external = set()
        for row in rows:
            for label in ('type', 'value') if edge == 'all' else (edge,):
                for dep in row[label + '_dependencies']:
                    candidates = by_name.get(dep, [])
                    # Import environments reject conflicting names; multiple independent
                    # environments must retain qualified IDs rather than guessed edges.
                    target = candidates[0]['id'] if len(candidates) == 1 else 'external:' + dep
                    if not candidates:
                        external.add(target)
                    a, b = (row['id'], target) if direction == 'uses' else (target, row['id'])
                    graph.setdefault(a, set()).add((b, label))
        start = selected[0]['id']
        queue, seen, found = deque([(start, 0)]), {start}, []
        truncated = False
        while queue:
            node, distance = queue.popleft()
            if distance == depth:
                continue
            for target, label in sorted(graph.get(node, set())):
                found.append({'from': node, 'to': target, 'edge': label,
                              'depth': distance + 1, 'external': target in external})
                if target not in seen:
                    seen.add(target)
                    queue.append((target, distance + 1))
                if len(found) >= 10000:
                    truncated = True
                    break
            if truncated:
                break
        return {**self._query_info(status), 'target': start, 'direction': direction,
                'items': found[offset:offset + limit], 'total': len(found), 'truncated': truncated,
                'next_offset': offset + limit if offset + limit < len(found) else None,
                'limitations': LIMITATIONS + ' Traversal stops at unindexed declarations; '
                'reverse edges exclude stale modules and may be incomplete.'}

    @locked
    def diff(self, before: str, after: str | None = None, limit: int = 20, offset: int = 0) -> dict:
        """Compare historical exports, including callers of changed definitions."""
        page_bounds(limit, offset)
        old, new = self._load(before), self._load(after)
        old_rows = {r['id']: r for r in self._store.index(old)}
        new_rows = {r['id']: r for r in self._store.index(new)}
        items, changed_names = [], set()
        fields = ('type_sha256', 'value_hash64', 'type_dependencies', 'value_dependencies', 'axioms', 'kind')
        for identifier in sorted(old_rows.keys() | new_rows.keys()):
            a, b = old_rows.get(identifier), new_rows.get(identifier)
            if a is None or b is None:
                changes = ['added' if a is None else 'removed']
            else:
                changes = [key for key in fields if a[key] != b[key]]
                if len(a.get('universe_parameters', [])) != len(b.get('universe_parameters', [])):
                    changes.append('universe_arity')
            if changes:
                row = b or a
                items.append({'id': identifier, 'name': row['name'], 'changes': changes})
                changed_names.add(row['name'])
        affected = set(changed_names)
        for _ in range(len(new_rows)):
            added = {r['name'] for r in new_rows.values()
                     if affected.intersection(r['type_dependencies'] + r['value_dependencies'])} - affected
            if not added:
                break
            affected.update(added)
        for row in new_rows.values():
            if row['name'] in affected - changed_names:
                items.append({'id': row['id'], 'name': row['name'], 'changes': ['transitive_dependency_changed']})
        items.sort(key=lambda r: r['id'])
        return {'before': before, 'after': self._loaded[0], 'items': items[offset:offset + limit],
                'total': len(items), 'next_offset': offset + limit if offset + limit < len(items) else None,
                'coverage_changed': old['modules'] != new['modules'], 'current_status': self.status()['status'],
                'limitations': LIMITATIONS + ' Added/removed entries may reflect coverage changes. '
                'A changed type is not automatically stronger or weaker.'}

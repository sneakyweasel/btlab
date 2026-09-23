"""Explicit Lean export builds and read-only, freshness-checked semantic discovery.

Structural matches are syntax matches on elaborated expressions, not unification,
proof applicability, or a judgment about the English claims in the ledger.
"""
from __future__ import annotations

import argparse
from collections import deque
from datetime import datetime, timezone
import hashlib
from functools import wraps
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import threading
from typing import Any

import formalpedia as fp
from formalpedia_catalog import page_bounds
from lab_environment import environment, executable

SCHEMA = 2
REBUILD = 'python tools/formalpedia.py semantic build'
LIMITATIONS = ('Compiled metadata, not an English-claim coverage judgment. Structural matches '
              'are not Lean unification. Dependency edges describe stored types/proof bodies. '
              'Proof hash64 is a change hint, not an equivalence certificate. External object '
              'freshness uses file size/mtime, not cryptographic attestation. No evidence labels change.')


def digest(value: Any) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':'),
                                    ensure_ascii=False).encode()).hexdigest()


def inputs(root: Path) -> dict[str, str]:
    """Hash local mathematical inputs and exporter code; never scan the generated cache."""
    formal = root / 'formal'
    paths = [formal / name for name in ('lean-toolchain', 'lakefile.toml', 'lake-manifest.json')]
    for lib in fp.LIBRARIES:
        paths.extend((formal / lib).rglob('*.lean'))
        paths.append(formal / f'{lib}.lean')
    paths.append(root / 'tools/lean/SemanticExport.lean')
    return {p.relative_to(root).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(set(paths)) if p.is_file()}


def file_stamp(path: Path) -> list[int] | None:
    try:
        s = path.stat()
        return [s.st_size, s.st_mtime_ns]
    except OSError:
        return None


def scoped_inputs(values: dict[str, str], modules: list[str] | None) -> dict[str, str]:
    if modules is None:
        return values
    allowed = {'formal/' + module.replace('.', '/') + '.lean' for module in modules}
    return {p: value for p, value in values.items()
            if not p.startswith('formal/') or not p.endswith('.lean') or p in allowed}


def object_stamps(objects: list[dict]) -> dict[str, list[int] | None]:
    # Lean imports public, server and private object regions depending on the module.
    paths = {str(Path(row['path']).resolve()) for row in objects}
    for path in list(paths):
        paths.update(path + suffix for suffix in ('.server', '.private'))
    return {p: file_stamp(Path(p)) for p in sorted(paths)}


def compiled_inventory(root: Path, lake: str) -> dict[str, list[int] | None]:
    """Record object inputs before import so a concurrent rebuild cannot look current."""
    paths = []
    for directory in (root / 'formal/.lake', Path(lake).parent.parent / 'lib/lean'):
        paths.extend(p for p in directory.rglob('*.olean*') if p.is_file())
    return {str(p.resolve()): file_stamp(p) for p in paths}


def module_path(module: str) -> str:
    return 'formal/' + module.replace('.', '/') + '.lean'


def known_modules(values: dict) -> list[str]:
    return sorted(p[7:-5].replace('/', '.') for p in values
                  if p.startswith('formal/') and p.endswith('.lean'))


def environment_changes(env: dict, now: dict, stamps: dict) -> tuple[set, set, set]:
    """Propagate changed inputs through the compiler's actual import DAG once per batch."""
    current = scoped_inputs(now, env.get('source_modules'))
    changed = {p for p in current.keys() | env['inputs'].keys()
               if current.get(p) != env['inputs'].get(p)}
    objects = {p for p, old in env['objects'].items() if stamps[p] != old}
    graph = env.get('imports')
    if graph is None or any(not p.startswith('formal/') or not p.endswith('.lean') for p in changed):
        return changed, objects, {'*'} if changed or objects else set()
    affected = {p[7:-5].replace('/', '.') for p in changed}
    affected.update(env['object_modules'][p] for p in objects)
    reverse: dict[str, set[str]] = {}
    for module, deps in graph.items():
        for dep in deps:
            reverse.setdefault(dep, set()).add(module)
    queue = deque(affected)
    while queue:
        for consumer in reverse.get(queue.popleft(), set()) - affected:
            affected.add(consumer)
            queue.append(consumer)
    return changed, objects, affected


def environments(data: dict) -> tuple[dict, dict]:
    if data['schema'] == 1:
        # Old exports lack a compiler import DAG: retain them conservatively as one unit.
        legacy = {k: data.get(k) for k in ('inputs', 'objects', 'source_modules')}
        return {'legacy': legacy}, dict.fromkeys(data['modules'], 'legacy')
    return data['environments'], data['module_environments']


def conclusion(ast: list) -> list:
    while ast[0] == 'forall':
        ast = ast[3]
    return ast


def structural_match(pattern: Any, target: Any, bindings: dict | None = None) -> bool:
    """Named holes match repeated subtrees exactly; no binder shifting or metavariables."""
    bindings = {} if bindings is None else bindings
    if isinstance(pattern, dict) and set(pattern) == {'hole'}:
        name = pattern['hole']
        if not isinstance(name, str) or not name or len(name) > 80:
            raise ValueError('A structural hole needs a nonempty name of at most 80 characters')
        if name in bindings:
            return bindings[name] == target
        bindings[name] = target
        return True
    if isinstance(pattern, list):
        return (isinstance(target, list) and len(pattern) == len(target)
                and all(structural_match(p, t, bindings) for p, t in zip(pattern, target)))
    return pattern == target


def compact(row: dict) -> dict:
    result = {key: row[key] for key in ('id', 'name', 'module', 'kind', 'axioms')}
    return dict(result, type=row['type'][:1800], type_truncated=len(row['type']) > 1800)


def locked(method):
    @wraps(method)
    def call(self, *args, **kwargs):
        with self._lock:
            return method(self, *args, **kwargs)
    return call


class SemanticCatalogue:
    """Never runs Lean or writes files. Only current modules enter semantic queries."""

    def __init__(self, root: Path | None = None, cache: Path | None = None):
        self.root = (root or fp.ROOT).resolve()
        self.cache = cache or self.root / '.cache/formalpedia/semantic'
        self._loaded: tuple[str, dict] | None = None
        self._lock = threading.RLock()
        self._stale: set[str] = set()

    def _load(self, snapshot: str | None = None) -> dict:
        if snapshot is None:
            snapshot = (self.cache / 'current').read_text(encoding='utf-8').strip()
        if not re.fullmatch(r'[0-9a-f]{64}', snapshot):
            raise ValueError('Invalid semantic snapshot identifier')
        if self._loaded and self._loaded[0] == snapshot:
            return self._loaded[1]
        data = json.loads((self.cache / f'{snapshot}.json').read_text(encoding='utf-8'))
        if data.get('schema') not in {1, SCHEMA} or digest(data) != snapshot:
            raise ValueError('Unsupported or corrupted semantic snapshot')
        self._loaded = snapshot, data
        return data

    @locked
    def status(self) -> dict:
        base = {'rebuild': REBUILD, 'limitations': LIMITATIONS}
        try:
            data = self._load()
        except FileNotFoundError:
            return dict(base, status='missing')
        except (OSError, ValueError) as exc:
            return dict(base, status='unreadable', reason=str(exc))
        now = inputs(self.root)
        envs, owners = environments(data)
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
        return dict(base, status=state, query_snapshot=token,
                    snapshot=self._loaded[0], built_at=data['built_at'],
                    declarations=len(data['declarations']), modules=data['modules'][:20],
                    current_declarations=sum(r['module'] not in self._stale for r in data['declarations']),
                    module_count=len(data['modules']), modules_truncated=len(data['modules']) > 20,
                    current_module_count=len(owners) - len(self._stale),
                    stale_modules=sorted(self._stale)[:20], stale_module_count=len(self._stale),
                    unindexed_modules=missing[:20], unindexed_module_count=len(missing),
                    coverage=data['coverage'], changed_inputs=changed[:20],
                    changed_input_count=len(changed), changed_object_count=len(changed_objects))

    def _current(self, snapshot: str | None = None) -> tuple[dict, dict]:
        status = self.status()
        if status['status'] not in {'current', 'partial'}:
            raise ValueError(f"Semantic index is {status['status']}; run {REBUILD}")
        if snapshot is not None and snapshot != status['query_snapshot']:
            raise ValueError('Semantic snapshot changed; restart pagination')
        data = self._loaded[1]
        return dict(data, declarations=[r for r in data['declarations']
                                        if r['module'] not in self._stale]), status

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
        found = self._resolve(self._loaded[1]['declarations'], name)
        stale = sorted({r['module'] for r in found if r['module'] in self._stale})
        if stale:
            raise ValueError('Target includes stale modules: ' + ', '.join(stale[:5]) + '; run ' + REBUILD)
        return self._resolve(rows, name)

    @staticmethod
    def _resolve(rows: list[dict], name: str) -> list[dict]:
        exact = [r for r in rows if name in (r['id'], r['name'])]
        return exact or [r for r in rows if r['name'].split('.')[-1] == name]

    @locked
    def show(self, name: str, include_ast: bool = False) -> dict:
        data, status = self._current()
        rows = self._query_resolve(data['declarations'], name)
        result = dict(self._query_info(status), limitations=LIMITATIONS)
        if len(rows) != 1:
            return dict(result, status='ambiguous' if rows else 'not_found',
                        candidates=[compact(r) for r in rows[:20]], candidate_count=len(rows))
        row = dict(rows[0])
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
        data, status = self._current(snapshot)
        if module in self._stale:
            raise ValueError(f'Module {module} is stale; run {REBUILD}')
        if like:
            found = self._query_resolve(data['declarations'], like)
            if len(found) != 1:
                raise ValueError('like must resolve to exactly one declaration; use semantic show')
            pattern = found[0]['type_ast']
            if part == 'conclusion':
                pattern = conclusion(pattern)
        rows = []
        for row in data['declarations']:
            if (not include_private and row['name'].startswith('_private.')) or (kind and row['kind'] != kind):
                continue
            if module and row['module'] != module:
                continue
            if not set(constants or []).issubset(row['type_dependencies']):
                continue
            target = row['type_ast'] if part == 'type' else conclusion(row['type_ast'])
            if pattern is not None and not structural_match(pattern, target):
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
        old_rows = {r['id']: r for r in old['declarations']}
        new_rows = {r['id']: r for r in new['declarations']}
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


def merge_export(previous: dict | None, modules: list[str], rows: list[dict], env: dict,
                 known: list[str]) -> dict:
    """Replace selected modules without erasing unrelated (possibly stale) coverage."""
    envs, owners = environments(previous) if previous else ({}, {})
    owners = {m: key for m, key in owners.items() if m not in modules and m in known}
    key = digest(env)
    owners.update(dict.fromkeys(modules, key))
    envs = {**envs, key: env}
    kept = [r for r in previous['declarations'] if r['module'] in owners and r['module'] not in modules
            ] if previous else []
    return {'schema': SCHEMA, 'built_at': datetime.now(timezone.utc).isoformat(),
            'environments': {k: envs[k] for k in set(owners.values())}, 'module_environments': owners,
            'modules': sorted(owners),
            'coverage': 'full_local_library' if set(owners) == set(known) else 'selected_modules',
            'declarations': sorted(kept + rows, key=lambda r: r['id'])}


def publish(cat: SemanticCatalogue, modules: list[str], rows: list[dict], env: dict) -> dict:
    """Serialize publication only; merge against the latest pointer under an OS lock.

    Advisory locks are released even on process exit. Readers never acquire a lock
    or create this file. Concurrent successful exporters cannot overwrite coverage.
    """
    cat.cache.mkdir(parents=True, exist_ok=True)
    with (cat.cache / 'publish.lock').open('a+b') as lock:
        if os.name == 'nt':
            import msvcrt
            if lock.tell() == 0:
                lock.write(b'\0')
                lock.flush()
            lock.seek(0)
            try:
                msvcrt.locking(lock.fileno(), msvcrt.LK_NBLCK, 1)
            except OSError as exc:
                raise ValueError('Another semantic export is publishing; retry') from exc
        else:
            import fcntl
            try:
                fcntl.flock(lock.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
            except OSError as exc:
                raise ValueError('Another semantic export is publishing; retry') from exc
        try:
            try:
                previous = cat._load()
            except (OSError, ValueError):
                # An explicit build can recover an unreadable cache. Its returned
                # coverage describes what could actually be reconstructed.
                previous = None
            now = inputs(cat.root)
            data = merge_export(previous, modules, rows, env, known_modules(now))
            identifier = digest(data)
            (cat.cache / f'{identifier}.json').write_text(json.dumps(data, ensure_ascii=False), encoding='utf-8')
            # Recheck after writing the immutable file, immediately before publication.
            stamps = {p: file_stamp(Path(p)) for p in env['objects']}
            if any(environment_changes(env, inputs(cat.root), stamps)[:2]):
                raise ValueError('Sources or compiled objects changed before publication; previous snapshot preserved')
            pointer = cat.cache / (identifier + '.current')
            pointer.write_text(identifier, encoding='utf-8')
            os.replace(pointer, cat.cache / 'current')
            return {'status': 'built', 'snapshot': identifier, 'declarations': len(data['declarations']),
                    'exported_declarations': len(rows), 'refreshed_modules': modules,
                    'modules': len(data['modules']), 'coverage': data['coverage']}
        finally:
            if os.name == 'nt':
                lock.seek(0)
                msvcrt.locking(lock.fileno(), msvcrt.LK_UNLCK, 1)
            else:
                fcntl.flock(lock.fileno(), fcntl.LOCK_UN)


def build(modules: list[str] | None = None, *, root: Path | None = None,
          timeout: int = 1800) -> dict:
    """Compile selected sources, export outdated modules, and atomically merge coverage."""
    root = (root or fp.ROOT).resolve()
    formal = root / 'formal'
    if not 10 <= timeout <= 7200:
        raise ValueError('timeout must be between 10 and 7200 seconds')
    original = inputs(root)
    known = known_modules(original)
    modules = sorted(set(modules or known))
    if not modules or any(m not in known for m in modules):
        raise ValueError('Only existing local library modules can be exported')
    lake = executable('lake', root)
    if lake is None:
        raise ValueError('Pinned Lean compiler is not installed; run tools/lab.py doctor')
    lock = json.loads((formal / 'lake-manifest.json').read_text(encoding='utf-8'))
    missing = [p['name'] for p in lock['packages'] if not (formal / '.lake/packages' / p['name']).is_dir()]
    if missing:
        raise ValueError('Install pinned packages explicitly first: ' + ', '.join(missing))
    scratch = root / '.build/formalpedia'
    scratch.mkdir(parents=True, exist_ok=True)
    run = Path(tempfile.mkdtemp(prefix='semantic-', dir=scratch))
    request, output, log = run / 'request.json', run / 'export.jsonl', run / 'build.log'
    cat = SemanticCatalogue(root)
    with log.open('w', encoding='utf-8') as stream:
        def run_command(command):
            result = subprocess.run(command, cwd=formal, env=environment(root),
                                    stdin=subprocess.DEVNULL, stdout=stream, stderr=stream, timeout=timeout)
            stream.flush()
            if result.returncode:
                raise ValueError(f'Lean build/export failed; previous snapshot preserved. See {log}')
        # '+' selects a module, even when its name is also a Lake library target.
        run_command([lake, 'build', *('+' + module for module in modules)])
        state = cat.status()
        if state['status'] in {'current', 'partial', 'stale'} and cat._loaded[1]['schema'] == SCHEMA:
            existing = set(cat._loaded[1]['modules'])
            modules = [m for m in modules if m not in existing or m in cat._stale]
        if not modules:
            if set(cat._loaded[1]['modules']) - set(known):
                env = {'inputs': scoped_inputs(original, []), 'source_modules': [],
                       'objects': {}, 'imports': {}, 'object_modules': {}}
                return dict(publish(cat, [], [], env), log=str(log))
            return {'status': 'unchanged', 'snapshot': state['snapshot'], 'refreshed_modules': [], 'log': str(log)}
        request.write_text(json.dumps({'modules': modules}), encoding='utf-8')
        before_objects = compiled_inventory(root, lake)
        run_command([lake, 'env', 'lean', '--run', str(root / 'tools/lean/SemanticExport.lean'),
                     str(request), str(output)])
    full_coverage = modules == known
    if full_coverage and original != inputs(root):
        raise ValueError(f'Sources changed during export; previous snapshot preserved. See {log}')
    with output.open(encoding='utf-8') as stream:
        metadata = json.loads(next(stream))
        rows = []
        for line in stream:
            row = json.loads(line)
            row['id'] = row['module'] + '::' + row['name']
            row['type_sha256'] = digest(row['type_ast'])
            rows.append(row)
    if metadata.get('record') != 'environment':
        raise ValueError(f'Incomplete Lean export; see {log}')
    objects = object_stamps(metadata['objects'])
    if any(before_objects.get(path) != stamp for path, stamp in objects.items()):
        raise ValueError(f'Compiled objects changed during export; previous snapshot preserved. See {log}')
    latest = inputs(root)
    source_modules = None if full_coverage else sorted(set(modules) | {
        row['module'] for row in metadata['objects']
        if 'formal/' + row['module'].replace('.', '/') + '.lean' in original.keys() | latest.keys()})
    original = scoped_inputs(original, source_modules)
    if original != scoped_inputs(latest, source_modules):
        raise ValueError(f'Sources changed while processing export; previous snapshot preserved. See {log}')
    if any('imports' not in row for row in metadata['objects']):
        raise ValueError('Exporter did not provide the compiler import graph')
    env = {'inputs': original, 'objects': objects, 'source_modules': source_modules,
           'imports': {row['module']: row['imports'] for row in metadata['objects']},
           'object_modules': {str(Path(row['path']).resolve()) + suffix: row['module']
                              for row in metadata['objects'] for suffix in ('', '.server', '.private')}}
    return dict(publish(cat, modules, rows, env), log=str(log))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    p = sub.add_parser('build', help='explicitly compile and export; MCP never builds')
    p.add_argument('--module', action='append', dest='modules')
    p.add_argument('--timeout', type=int, default=1800)
    sub.add_parser('status')
    p = sub.add_parser('show')
    p.add_argument('name')
    p.add_argument('--include-ast', action='store_true')
    p = sub.add_parser('search')
    p.add_argument('--constant', action='append', dest='constants')
    p.add_argument('--like')
    p.add_argument('--pattern', type=json.loads)
    p.add_argument('--part', choices=['type', 'conclusion'], default='type')
    p.add_argument('--kind')
    p.add_argument('--module')
    p.add_argument('--include-private', action='store_true')
    p = sub.add_parser('dependencies')
    p.add_argument('name')
    p.add_argument('--direction', choices=['uses', 'used_by'], default='uses')
    p.add_argument('--edge', choices=['all', 'type', 'value'], default='all')
    p.add_argument('--depth', type=int, default=1)
    p = sub.add_parser('diff')
    p.add_argument('before')
    p.add_argument('--after')
    for name in ('search', 'dependencies', 'diff'):
        p = sub.choices[name]
        p.add_argument('--limit', type=int, default=20)
        p.add_argument('--offset', type=int, default=0)
        if name != 'diff':
            p.add_argument('--snapshot')
    options = vars(parser.parse_args(argv))
    command = options.pop('command')
    try:
        result = build(**options) if command == 'build' else getattr(SemanticCatalogue(), command)(**options)
    except (ValueError, OSError, subprocess.TimeoutExpired) as exc:
        print(json.dumps({'status': 'failed', 'reason': str(exc)}))
        return 1
    print(json.dumps(result, ensure_ascii=False, indent=2))
    return 0 if result.get('status') not in {'missing', 'stale', 'unreadable', 'ambiguous', 'not_found'} else 1


if __name__ == '__main__':
    raise SystemExit(main())

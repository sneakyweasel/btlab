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

SCHEMA = 1
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
    """Never runs Lean or writes files. An absent/stale export fails explicitly."""

    def __init__(self, root: Path | None = None, cache: Path | None = None):
        self.root = (root or fp.ROOT).resolve()
        self.cache = cache or self.root / '.cache/formalpedia/semantic'
        self._loaded: tuple[str, dict] | None = None
        self._lock = threading.RLock()

    def _load(self, snapshot: str | None = None) -> dict:
        if snapshot is None:
            snapshot = (self.cache / 'current').read_text(encoding='utf-8').strip()
        if not re.fullmatch(r'[0-9a-f]{64}', snapshot):
            raise ValueError('Invalid semantic snapshot identifier')
        if self._loaded and self._loaded[0] == snapshot:
            return self._loaded[1]
        data = json.loads((self.cache / f'{snapshot}.json').read_text(encoding='utf-8'))
        if data.get('schema') != SCHEMA or digest(data) != snapshot:
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
        now = scoped_inputs(inputs(self.root), data.get('source_modules'))
        changed = sorted(p for p in now.keys() | data['inputs'].keys()
                         if now.get(p) != data['inputs'].get(p))
        changed_objects = [p for p, stamp in data['objects'].items() if file_stamp(Path(p)) != stamp]
        return dict(base, status='stale' if changed or changed_objects else 'current',
                    snapshot=self._loaded[0], built_at=data['built_at'],
                    declarations=len(data['declarations']), modules=data['modules'][:20],
                    module_count=len(data['modules']), modules_truncated=len(data['modules']) > 20,
                    coverage=data['coverage'], changed_inputs=changed[:20],
                    changed_input_count=len(changed), changed_object_count=len(changed_objects))

    def _current(self, snapshot: str | None = None) -> tuple[dict, dict]:
        status = self.status()
        if status['status'] != 'current':
            raise ValueError(f"Semantic index is {status['status']}; run {REBUILD}")
        if snapshot is not None and snapshot != status['snapshot']:
            raise ValueError('Semantic snapshot changed; restart pagination')
        return self._loaded[1], status

    @staticmethod
    def _resolve(rows: list[dict], name: str) -> list[dict]:
        exact = [r for r in rows if name in (r['id'], r['name'])]
        return exact or [r for r in rows if r['name'].split('.')[-1] == name]

    @locked
    def show(self, name: str, include_ast: bool = False) -> dict:
        data, status = self._current()
        rows = self._resolve(data['declarations'], name)
        result = {'snapshot': status['snapshot'], 'limitations': LIMITATIONS}
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
        if like:
            found = self._resolve(data['declarations'], like)
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
        return {'snapshot': status['snapshot'], 'match': 'elaborated_structural_syntax',
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
        selected = self._resolve(rows, name)
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
        return {'snapshot': status['snapshot'], 'target': start, 'direction': direction,
                'items': found[offset:offset + limit], 'total': len(found), 'truncated': truncated,
                'next_offset': offset + limit if offset + limit < len(found) else None,
                'limitations': LIMITATIONS + ' Traversal stops at unindexed external declarations.'}

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


def build(modules: list[str] | None = None, *, root: Path | None = None,
          timeout: int = 1800) -> dict:
    """Compile selected current sources before exporting; publish only complete snapshots."""
    root = (root or fp.ROOT).resolve()
    formal = root / 'formal'
    if not 10 <= timeout <= 7200:
        raise ValueError('timeout must be between 10 and 7200 seconds')
    original = inputs(root)
    known = sorted('.'.join(Path(p).relative_to('formal').with_suffix('').parts)
                   for p in original if p.endswith('.lean') and p.startswith('formal/'))
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
    request.write_text(json.dumps({'modules': modules}), encoding='utf-8')
    # '+' selects a module, even when its name is also a Lake library target.
    commands = [[lake, 'build', *('+' + module for module in modules)],
                [lake, 'env', 'lean', '--run', str(root / 'tools/lean/SemanticExport.lean'),
                 str(request), str(output)]]
    with log.open('w', encoding='utf-8') as stream:
        before_objects = {}
        for index, command in enumerate(commands):
            if index == 1:
                before_objects = compiled_inventory(root, lake)
            result = subprocess.run(command, cwd=formal, env=environment(root),
                                    stdin=subprocess.DEVNULL, stdout=stream, stderr=stream, timeout=timeout)
            stream.flush()
            if result.returncode:
                raise ValueError(f'Lean build/export failed; previous snapshot preserved. See {log}')
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
    snapshot = {'schema': SCHEMA, 'built_at': datetime.now(timezone.utc).isoformat(),
                'inputs': original, 'objects': objects, 'source_modules': source_modules,
                'modules': modules, 'coverage': 'full_local_library' if full_coverage else 'selected_modules',
                'declarations': sorted(rows, key=lambda r: r['id'])}
    identifier = digest(snapshot)
    cache = root / '.cache/formalpedia/semantic'
    cache.mkdir(parents=True, exist_ok=True)
    # A failed export never changes current. Atomic pointer replacement lets readers finish
    # on the old immutable snapshot while a new one is being written.
    (cache / f'{identifier}.json').write_text(json.dumps(snapshot, ensure_ascii=False), encoding='utf-8')
    pointer = cache / (identifier + '.current')
    pointer.write_text(identifier, encoding='utf-8')
    os.replace(pointer, cache / 'current')
    return {'status': 'built', 'snapshot': identifier, 'declarations': len(rows),
            'modules': len(modules), 'coverage': snapshot['coverage'], 'log': str(log)}


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

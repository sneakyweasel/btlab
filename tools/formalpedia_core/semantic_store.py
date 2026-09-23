"""Content-addressed semantic manifests, module records and compact search indexes.

Reads never create directories or locks. Only explicit publication/migration writes.
Old monolithic exports remain readable; conversion never changes their provenance.
"""
from __future__ import annotations

from collections import OrderedDict
from contextlib import contextmanager
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import tempfile

from .semantic_common import SCHEMA, conclusion, digest, environments, environment_changes, file_stamp, inputs, known_modules

CACHE_BYTES = 64 * 1024**2


def encoded(value) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=False).encode('utf-8')


def summary(row: dict) -> dict:
    """Enough for name/constant lookup, dependency traversal and historical differences."""
    fields = ('id', 'name', 'module', 'kind', 'axioms', 'type_dependencies', 'value_dependencies',
              'type_sha256', 'value_hash64', 'universe_parameters', 'value_available')
    result = {k: row[k] for k in fields if k in row}
    ast = row.get('type_ast', [])
    result.setdefault('type_sha256', digest(ast))
    result['conclusion_sha256'] = digest(conclusion(ast) if ast else ast)
    return dict(result, type=row['type'][:1800], type_truncated=len(row['type']) > 1800)


@contextmanager
def publication_lock(cache: Path):
    """Nonblocking process lock; the OS releases it on exit, including crashes."""
    cache.mkdir(parents=True, exist_ok=True)
    with (cache / 'publish.lock').open('a+b') as stream:
        if os.name == 'nt':
            import msvcrt
            if stream.tell() == 0:
                stream.write(b'\0')
                stream.flush()
            stream.seek(0)
            try:
                msvcrt.locking(stream.fileno(), msvcrt.LK_NBLCK, 1)
            except OSError as exc:
                raise ValueError('Another semantic export is publishing; retry') from exc
        else:
            import fcntl
            try:
                fcntl.flock(stream.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
            except OSError as exc:
                raise ValueError('Another semantic export is publishing; retry') from exc
        try:
            yield
        finally:
            if os.name == 'nt':
                stream.seek(0)
                msvcrt.locking(stream.fileno(), msvcrt.LK_UNLCK, 1)
            else:
                fcntl.flock(stream.fileno(), fcntl.LOCK_UN)


def atomic_write(path: Path, data: bytes):
    path.parent.mkdir(parents=True, exist_ok=True)
    handle, name = tempfile.mkstemp(prefix='.publishing-', dir=path.parent)
    temporary = Path(name)
    try:
        with os.fdopen(handle, 'wb') as stream:
            stream.write(data)
        os.replace(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)


class SnapshotStore:
    """Lazy verified object reader; bounded caches avoid retaining the whole AST corpus."""

    def __init__(self, cache: Path):
        self.cache = cache
        self._cache = OrderedDict()
        self._bytes = 0
        self._manifest = None

    def path(self, kind: str, identifier: str) -> Path:
        if kind not in {'', 'modules', 'indexes', 'environments'} or not re.fullmatch(r'[0-9a-f]{64}', identifier):
            raise ValueError('Invalid semantic snapshot identifier')
        return self.cache / kind / (identifier + '.json')

    def read(self, kind: str, ref: dict) -> dict:
        path = self.path(kind, ref['sha256'])
        stamp = file_stamp(path)
        if stamp is None:
            raise ValueError(f'Missing semantic {kind or "manifest"} object: {ref["sha256"]}')
        if 'bytes' in ref and stamp[0] != ref['bytes']:
            raise ValueError(f'Semantic {kind} object is corrupted: size changed')
        key = (kind, ref['sha256'])
        if key in self._cache and self._cache[key][0] == stamp:
            self._cache.move_to_end(key)
            return self._cache[key][1]
        raw = path.read_bytes()
        value = json.loads(raw)
        # Legacy snapshots used noncanonical whitespace; IDs always hash canonical JSON.
        if digest(value) != ref['sha256']:
            raise ValueError(f'Semantic {kind or "snapshot"} object is corrupted')
        if key in self._cache:
            self._bytes -= self._cache.pop(key)[2]
        # A single giant module remains queryable but is not retained in this cache.
        if len(raw) <= CACHE_BYTES:
            self._cache[key] = (stamp, value, len(raw))
            self._bytes += len(raw)
            while self._bytes > CACHE_BYTES:
                self._bytes -= self._cache.popitem(last=False)[1][2]
        return value

    def load(self, identifier: str | None = None) -> tuple[str, dict]:
        if identifier is None:
            identifier = (self.cache / 'current').read_text(encoding='utf-8').strip()
        path = self.path('', identifier)
        stamp = file_stamp(path)
        if self._manifest and self._manifest[:2] == (identifier, stamp):
            return identifier, self._manifest[2]
        data = self.read('', {'sha256': identifier})
        if data.get('schema') not in {1, 2, SCHEMA}:
            raise ValueError('Unsupported or corrupted semantic snapshot')
        self._manifest = identifier, stamp, data
        return identifier, data

    def environment_records(self, data: dict) -> tuple[dict, dict]:
        if data['schema'] < SCHEMA:
            return environments(data)
        return ({key: self.read('environments', ref) for key, ref in data['environments'].items()},
                data['module_environments'])

    def check_references(self, data: dict):
        """Cheap availability check. Content hashes are verified when records are read."""
        if data['schema'] < SCHEMA:
            return
        refs = [('environments', ref) for ref in data['environments'].values()]
        refs += [(kind, value[key]) for value in data['shards'].values()
                 for kind, key in (('modules', 'records'), ('indexes', 'index'))]
        for kind, ref in refs:
            stamp = file_stamp(self.path(kind, ref['sha256']))
            if stamp is None or stamp[0] != ref['bytes']:
                raise ValueError(f'Missing or corrupted semantic {kind} object: {ref["sha256"]}')

    def counts(self, data: dict) -> dict[str, int]:
        if data['schema'] == SCHEMA:
            return {m: s['count'] for m, s in data['shards'].items()}
        counts = dict.fromkeys(data['modules'], 0)
        for row in data['declarations']:
            counts[row['module']] += 1
        return counts

    def index(self, data: dict, modules=None) -> list[dict]:
        selected = set(data['modules'] if modules is None else modules)
        if data['schema'] < SCHEMA:
            return sorted((summary(r) for r in data['declarations'] if r['module'] in selected), key=lambda r: r['id'])
        rows = []
        for module in sorted(selected):
            if module in data['shards']:
                rows.extend(self.read('indexes', data['shards'][module]['index'])['declarations'])
        return sorted(rows, key=lambda r: r['id'])

    def records(self, data: dict, module: str) -> list[dict]:
        if data['schema'] < SCHEMA:
            return [r for r in data['declarations'] if r['module'] == module]
        return self.read('modules', data['shards'][module]['records'])['declarations']

    def detail(self, data: dict, row: dict) -> dict:
        return next(r for r in self.records(data, row['module']) if r['id'] == row['id'])

    def write(self, kind: str, value: dict) -> dict:
        raw = encoded(value)
        identifier = hashlib.sha256(raw).hexdigest()
        path = self.path(kind, identifier)
        if not path.exists() or path.read_bytes() != raw:
            atomic_write(path, raw)
        return {'sha256': identifier, 'bytes': len(raw)}

    def shard(self, module: str, rows: list[dict]) -> dict:
        rows = sorted(rows, key=lambda r: r['id'])
        if any(r['module'] != module or r['id'] != module + '::' + r['name'] for r in rows):
            raise ValueError('Exported declarations do not match their module identity')
        return {'records': self.write('modules', {'module': module, 'declarations': rows}),
                'index': self.write('indexes', {'module': module, 'declarations': [summary(r) for r in rows]}),
                'count': len(rows)}

    def sharded(self, data: dict) -> dict:
        if data['schema'] == SCHEMA:
            return data
        envs, owners = environments(data)
        refs = {key: self.write('environments', env) for key, env in envs.items()}
        rows = {m: [] for m in data['modules']}
        for row in data['declarations']:
            rows[row['module']].append(row)
        return {'schema': SCHEMA, 'built_at': data['built_at'], 'coverage': data['coverage'],
                'modules': data['modules'], 'module_environments': owners, 'environments': refs,
                'shards': {m: self.shard(m, r) for m, r in rows.items()}}

    def commit(self, data: dict, validate=lambda: None) -> str:
        ref = self.write('', data)
        self.check_references(data)
        validate()
        atomic_write(self.cache / 'current', ref['sha256'].encode('ascii'))
        return ref['sha256']

    def migrate(self) -> dict:
        with publication_lock(self.cache):
            before, data = self.load()
            if data['schema'] == SCHEMA:
                return {'status': 'unchanged', 'snapshot': before}
            converted = self.sharded(data)
            return {'status': 'migrated', 'before': before, 'snapshot': self.commit(converted),
                    'modules': len(converted['modules']), 'built_at': data['built_at']}


def publish(cat, modules: list[str], rows: list[dict], env: dict) -> dict:
    """Merge a verified compiler export against the latest manifest under a process lock."""
    store = SnapshotStore(cat.cache)
    with publication_lock(cat.cache):
        try:
            _, old = store.load()
        except (OSError, ValueError):
            old = None
        if old is None:
            old = {'schema': SCHEMA, 'shards': {}, 'environments': {}, 'module_environments': {}}
        else:
            old = store.sharded(old)
        known = set(known_modules(inputs(cat.root)))
        owners = {m: key for m, key in old['module_environments'].items() if m in known and m not in modules}
        key = digest(env)
        owners.update(dict.fromkeys(modules, key))
        envs = {**old['environments'], key: store.write('environments', env)}
        grouped = {m: [] for m in modules}
        for row in rows:
            grouped[row['module']].append(row)
        shards = {m: value for m, value in old['shards'].items() if m in owners and m not in modules}
        shards.update({m: store.shard(m, records) for m, records in grouped.items()})
        data = {'schema': SCHEMA, 'built_at': datetime.now(timezone.utc).isoformat(),
                'modules': sorted(owners), 'module_environments': owners, 'shards': shards,
                'environments': {key: envs[key] for key in set(owners.values())},
                'coverage': 'full_local_library' if set(owners) == known else 'selected_modules'}

        def validate():
            stamps = {p: file_stamp(Path(p)) for p in env['objects']}
            if any(environment_changes(env, inputs(cat.root), stamps)[:2]):
                raise ValueError('Sources or compiled objects changed before publication; previous snapshot preserved')

        identifier = store.commit(data, validate)
        return {'status': 'built', 'snapshot': identifier, 'declarations': sum(s['count'] for s in shards.values()),
                'exported_declarations': len(rows), 'refreshed_modules': modules,
                'modules': len(owners), 'coverage': data['coverage']}

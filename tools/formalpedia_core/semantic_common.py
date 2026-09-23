"""Semantic identities, structural matching and module freshness inputs."""
from __future__ import annotations

from collections import deque
import hashlib
from functools import wraps
import json
from pathlib import Path
from typing import Any
from formalpedia_core import workspace as fp_workspace


SCHEMA = 3


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
    for lib in fp_workspace.LIBRARIES:
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
    return dict(result, type=row['type'][:1800],
                type_truncated=row.get('type_truncated', len(row['type']) > 1800))


def locked(method):
    @wraps(method)
    def call(self, *args, **kwargs):
        with self._lock:
            return method(self, *args, **kwargs)
    return call

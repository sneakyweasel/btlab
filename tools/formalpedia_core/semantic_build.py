"""Explicit Lean build/export orchestration. Never called by MCP queries."""
from __future__ import annotations

import json
from pathlib import Path
import subprocess
import tempfile
from formalpedia_core import workspace as fp_workspace
from lab_environment import environment, executable
from .semantic_common import (SCHEMA, digest, inputs, scoped_inputs, object_stamps, compiled_inventory, known_modules)
from .semantic_query import SemanticCatalogue
from .semantic_store import publish


def build(modules: list[str] | None = None, *, root: Path | None = None,
          timeout: int = 1800) -> dict:
    """Compile selected sources, export outdated modules, and atomically merge coverage."""
    root = (root or fp_workspace.ROOT).resolve()
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
        if state['status'] in {'current', 'partial', 'stale'}:
            existing = set(cat._loaded[1]['modules'])
            modules = [m for m in modules if m not in existing or m in cat._stale]
        if not modules:
            if set(cat._loaded[1]['modules']) - set(known):
                env = {'inputs': scoped_inputs(original, []), 'source_modules': [],
                       'objects': {}, 'imports': {}, 'object_modules': {}}
                return dict(publish(cat, [], [], env), log=str(log))
            if cat._loaded[1]['schema'] < SCHEMA:
                migration = cat._store.migrate()
                return dict(migration, refreshed_modules=[], log=str(log))
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

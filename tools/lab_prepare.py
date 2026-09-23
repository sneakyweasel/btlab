"""Explicit, checkout-local dependency preparation and reproducible readiness receipts."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import uuid

from lab_environment import ROOT, environment, executable
from lab_dependencies import inside, math_inputs, package_state, prepare_packages

LOCK = 'tools/requirements-lab.lock'
LOCK_META = 'tools/requirements-lab.json'
RECEIPT = '.build/preparation/ready.json'
LOCK_INPUTS = ('pyproject.toml', 'tools/requirements-formalpedia.txt')
INVENTORY_SCRIPT = (
    'import importlib.metadata as m,json,platform,sys; '
    'print(json.dumps({"version":platform.python_version(),"cache_tag":sys.implementation.cache_tag,'
    '"packages":sorted((d.metadata["Name"].lower().replace("_","-"),d.version) for d in m.distributions())}))'
)


def text_hash(path: Path) -> str:
    return hashlib.sha256(path.read_text(encoding='utf-8').encode()).hexdigest()


def lock_inputs(root: Path) -> dict:
    return {name: text_hash(root / name) for name in LOCK_INPUTS}


def lock_state(root: Path) -> dict:
    try:
        metadata = json.loads((root / LOCK_META).read_text(encoding='utf-8'))
        valid = metadata['inputs'] == lock_inputs(root) and metadata['sha256'] == text_hash(root / LOCK)
        return {'status': 'current' if valid else 'stale', 'sha256': text_hash(root / LOCK)}
    except (OSError, ValueError, KeyError) as exc:
        return {'status': 'missing', 'reason': str(exc)}


def managed_python(root: Path) -> Path:
    directory = inside(root, root / '.build/python' / ('Scripts' if os.name == 'nt' else 'bin'))
    # POSIX venv launchers legitimately symlink to their base interpreter.
    return directory / ('python.exe' if os.name == 'nt' else 'python')


def python_inventory(python: Path) -> dict:
    result = subprocess.run([str(python), '-I', '-c', INVENTORY_SCRIPT], capture_output=True,
        text=True, encoding='utf-8', errors='replace', stdin=subprocess.DEVNULL, timeout=30)
    if result.returncode:
        raise ValueError('Managed Python inventory failed: ' + result.stderr[-1000:])
    return json.loads(result.stdout)


def runtime_python(root: Path = ROOT) -> str:
    """Use a prepared interpreter when present; reject stale locks instead of falling back."""
    python = managed_python(root)
    if python.exists():
        state = readiness(root, probe=False, lean=False)
        if state['python']['status'] != 'recorded':
            raise ValueError('Managed Python is unprepared or stale; run python tools/lab.py prepare --apply')
        return str(python)
    return sys.executable


def readiness(root: Path = ROOT, *, probe: bool = False, lean: bool = True) -> dict:
    root = root.resolve()
    lock = lock_state(root)
    python = managed_python(root)
    try:
        receipt = json.loads((root / RECEIPT).read_text(encoding='utf-8'))
    except (OSError, ValueError):
        receipt = {}
    py = {'status': 'unprepared', 'interpreter': str(python), 'inventory_checked': False}
    if python.is_file() and lock['status'] == 'current' and receipt.get('lock_sha256') == lock['sha256']:
        py['status'] = 'recorded'
        if probe:
            try:
                py.update(status='ready' if python_inventory(python) == receipt.get('python') else 'drifted', inventory_checked=True)
            except (ValueError, OSError, subprocess.SubprocessError) as exc:
                py.update(status='unavailable', reason=str(exc))
    elif python.exists():
        py['status'] = 'stale'
    checks = []
    build = {'status': 'not_requested'}
    if lean:
        try:
            checks = package_state(root, probe=probe)
            recorded = receipt.get('lean_build', {})
            build = {'status': 'unbuilt'}
            if recorded:
                same = recorded.get('inputs') == math_inputs(root)
                outputs = recorded.get('outputs', {})
                same &= bool(outputs) and all(inside(root, root / p).is_file() and
                    hashlib.sha256(inside(root, root / p).read_bytes()).hexdigest() == digest for p, digest in outputs.items())
                build['status'] = 'ready' if same else 'stale'
        except (OSError, ValueError, KeyError, subprocess.SubprocessError) as exc:
            build = {'status': 'unavailable', 'reason': str(exc)}
    ready = py['status'] == 'ready' and (not lean or (all(p['status'] == 'ready' for p in checks) and build['status'] == 'ready'))
    return {'status': 'ready' if ready else 'not_ready', 'root': str(root), 'lock': lock,
        'python': py, 'lean_packages': checks, 'lean_build': build,
        'mcp_command': [str(python), str(root / 'tools/formalpedia_mcp.py'), '--root', str(root)],
        'limitations': 'Readiness covers the recorded environment and local build only. It is not a theorem audit or a passing test suite. Cache copies never establish proof status.'}


def atomic_json(root: Path, path: Path, data: dict):
    path = inside(root, path)
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + '.' + uuid.uuid4().hex + '.tmp')
    temporary.write_text(json.dumps(data, indent=2, ensure_ascii=False) + '\n', encoding='utf-8', newline='\n')
    temporary.replace(path)


def prepare(root: Path = ROOT, *, apply=False, donor: Path | None = None, offline=False,
            profile='full', timeout=1800) -> dict:
    root = root.resolve()
    if donor:
        donor = donor.resolve()
        if donor == root or not (donor / 'formal/lake-manifest.json').is_file():
            raise ValueError('Cache donor must be a different laboratory checkout')
    if profile not in {'python', 'full'}:
        raise ValueError('Expected python or full profile')
    lock = lock_state(root)
    if lock['status'] != 'current':
        raise ValueError('Python lock is absent or stale; refresh it explicitly with prepare --refresh-lock')
    result = {'status': 'planned', 'root': str(root), 'profile': profile,
        'offline': offline, 'donor': str(donor) if donor else None,
        'actions': ['Create an independent .build/python environment and sync the hash-pinned lock'] +
            (['Materialize exact Lake package revisions, copying compatible caches as independent files',
              'Run the local Lean build and refresh compiled discovery records'] if profile == 'full' else []),
        'before': readiness(root, lean=profile == 'full')}
    if not apply:
        return result
    uv = shutil.which('uv')
    if not uv:
        raise ValueError('uv is required for preparation; install tools/requirements-formalpedia.txt first')
    if profile == 'full' and not executable('lake', root):
        raise ValueError('The pinned Lean toolchain is not installed; preparation will not silently select another compiler')
    run_dir = inside(root, root / '.build/preparation' / uuid.uuid4().hex[:12])
    run_dir.mkdir(parents=True)
    env = environment(root)
    env['UV_CACHE_DIR'] = str(inside(root, root / '.cache/uv'))
    env['UV_PYTHON_DOWNLOADS'] = 'never'
    steps = []

    def run(argv, cwd=root):
        log = run_dir / f'{len(steps):02d}.log'
        print(f'Preparing: {argv[0]} {argv[1] if len(argv) > 1 else ""} (log {log.relative_to(root)})', file=sys.stderr, flush=True)
        with log.open('wb') as output:
            process = subprocess.run(argv, cwd=cwd, env=env, stdin=subprocess.DEVNULL,
                stdout=output, stderr=subprocess.STDOUT, timeout=timeout)
        steps.append({'argv': argv, 'log': log.relative_to(root).as_posix(), 'exit_code': process.returncode})
        if process.returncode:
            raise ValueError(f'Preparation command failed; see {log}')

    initial = lock_inputs(root)
    python = managed_python(root)
    receipt = {'schema': 'btlab-ready/v1', 'created_utc': datetime.now(timezone.utc).isoformat(),
        'lock_sha256': lock['sha256']}
    try:
        if not python.exists():
            run([uv, 'venv', '--no-managed-python', '--no-python-downloads', '--python', sys.executable, str(root / '.build/python')])
        run([uv, 'pip', 'sync', '--strict', '--require-hashes', '--no-python-downloads', '--no-managed-python',
             '--python', str(python), str(root / LOCK), *(['--offline'] if offline else [])])
        receipt['python'] = python_inventory(python)
        if profile == 'python':
            # Retain a still-valid build across a Python-only dependency sync.
            previous = readiness(root, lean=True)
            if previous['lean_build']['status'] == 'ready':
                saved = json.loads((root / RECEIPT).read_text(encoding='utf-8'))
                receipt['lean_build'] = saved['lean_build']
        if profile == 'full':
            receipt['packages'] = prepare_packages(root, donor, run, offline=offline)
            inputs = math_inputs(root)
            # This invokes the existing compiler/exporter; a copied cache alone cannot pass.
            run([str(python), 'tools/lab.py', 'build', '--timeout', str(timeout)])
            if inputs != math_inputs(root):
                raise ValueError('Lean sources changed during preparation; no build receipt was issued')
            outputs = list((root / 'formal/.lake/build/lib/lean').rglob('*.olean'))
            if not outputs:
                raise ValueError('Build reported success without any local Lean objects')
            receipt['lean_build'] = {'inputs': inputs, 'outputs': {
                p.relative_to(root).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest() for p in outputs}}
        if initial != lock_inputs(root) or lock != lock_state(root):
            raise ValueError('Dependency lock inputs changed during preparation')
        atomic_json(root, root / RECEIPT, receipt)
        result.update(status='ready', after=readiness(root, probe=True, lean=profile == 'full'))
        if result['after']['status'] != 'ready':
            result['status'] = 'not_ready'
    except (OSError, ValueError, subprocess.SubprocessError) as exc:
        result.update(status='failed', reason=str(exc))
    result.update(steps=steps, report=(run_dir / 'report.json').relative_to(root).as_posix())
    atomic_json(root, root / result['report'], result)
    return result


def refresh_lock(root: Path = ROOT):
    uv = shutil.which('uv')
    if not uv:
        raise ValueError('uv is required to resolve the declared dependencies')
    before = lock_inputs(root)
    subprocess.run([uv, 'pip', 'compile', *LOCK_INPUTS, '--extra', 'dev', '--universal', '--generate-hashes',
        '--no-emit-index-url', '--output-file', LOCK, '--cache-dir', '.cache/uv', '--no-python-downloads',
        '--custom-compile-command', 'python tools/lab.py prepare --refresh-lock',
        '--no-managed-python', '--python', sys.executable, '--python-version', '3.11', '--quiet'], cwd=root, check=True)
    if before != lock_inputs(root):
        raise ValueError('Inputs changed during dependency resolution')
    atomic_json(root, root / LOCK_META, {'schema': 'btlab-python-lock/v1', 'inputs': before,
        'sha256': text_hash(root / LOCK), 'profile': 'project dependencies, dev extra and local MCP requirements',
        'resolution': 'universal, Python >=3.11; package archives verified by SHA-256 during sync'})
    return {'status': 'locked', 'lock': LOCK, 'metadata': LOCK_META}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--apply', action='store_true')
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--refresh-lock', action='store_true')
    parser.add_argument('--from', dest='donor', type=Path, help='compatible checkout to copy caches from; never shared writable trees')
    parser.add_argument('--offline', action='store_true')
    parser.add_argument('--profile', choices=['python', 'full'], default='full')
    parser.add_argument('--timeout', type=int, default=1800)
    args = parser.parse_args(argv)
    try:
        if args.timeout <= 0:
            raise ValueError('timeout must be positive')
        result = refresh_lock() if args.refresh_lock else readiness(probe=True, lean=args.profile == 'full') if args.check else prepare(
            apply=args.apply, donor=args.donor, offline=args.offline, profile=args.profile, timeout=args.timeout)
    except (OSError, ValueError, subprocess.SubprocessError) as exc:
        result = {'status': 'failed', 'reason': str(exc)}
    print(json.dumps(result, indent=2, ensure_ascii=False))
    return 0 if result['status'] in {'planned', 'ready', 'locked'} else 1


if __name__ == '__main__':
    raise SystemExit(main())

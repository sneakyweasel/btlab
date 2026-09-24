"""Checkout-scoped runtime discovery; no installation or global configuration writes."""
from __future__ import annotations

import importlib.metadata
import json
import os
from pathlib import Path
import shutil
import sqlite3
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'src'))
from research.repository import environment as repository_environment


def elan_home() -> Path | None:
    candidates = []
    if os.environ.get('ELAN_HOME'):
        candidates.append(Path(os.environ['ELAN_HOME']))
    lake = shutil.which('lake')
    if lake:
        candidates.append(Path(lake).parent.parent)
    candidates.extend([Path(os.environ.get('USERPROFILE', str(Path.home()))) / '.elan', Path.home() / '.elan'])
    return next((p for p in candidates if (p / 'toolchains').is_dir()), None)


def executable(name: str, root: Path = ROOT) -> str | None:
    """Prefer the installed pinned Lean binaries to shims that may download a toolchain."""
    if name in {'lean', 'lake'}:
        home = elan_home()
        pin = root / 'formal/lean-toolchain'
        if home and pin.is_file():
            version = pin.read_text(encoding='utf-8').strip().replace('/', '--').replace(':', '---')
            candidate = home / 'toolchains' / version / 'bin' / (name + ('.exe' if os.name == 'nt' else ''))
            if candidate.is_file():
                return str(candidate)
            return None
        if pin.is_file():
            return None
        found = shutil.which(name)
        # An elan shim is not an installed pinned compiler. Do not trigger installation.
        if found and Path(found).parent.name == 'bin' and Path(found).parent.parent.name == '.elan':
            return None
        return found
    found = shutil.which(name)
    if found:
        return found
    if os.name == 'nt':
        candidates = {
            'pandoc': [Path(os.environ.get('PROGRAMFILES', 'C:/Program Files')) / 'Pandoc/pandoc.exe'],
            'xelatex': [Path(os.environ.get('LOCALAPPDATA', '')) / 'Programs/MiKTeX/miktex/bin/x64/xelatex.exe'],
        }.get(name, [])
        return next((str(p) for p in candidates if p.is_file()), None)
    return None


def environment(root: Path = ROOT) -> dict[str, str]:
    """Bind imports and Git ownership exceptions to this checkout for child processes."""
    root = root.resolve()
    env = repository_environment()
    inherited = env.get('PYTHONPATH')
    env['PYTHONPATH'] = str(root / 'src') + (os.pathsep + inherited if inherited else '')
    home = elan_home()
    if home:
        env.setdefault('ELAN_HOME', str(home))
    lake = executable('lake', root)
    if lake:
        env['PATH'] = str(Path(lake).parent) + os.pathsep + env.get('PATH', '')
    # Subprocess Git commands need the same narrow exception as our own Git reads.
    # Preserve caller configuration and never set safe.directory=* or edit global config.
    count = int(env.get('GIT_CONFIG_COUNT', '0'))
    env[f'GIT_CONFIG_KEY_{count}'] = 'core.longpaths'
    env[f'GIT_CONFIG_VALUE_{count}'] = 'true'
    count += 1
    paths = [root]
    packages = root / 'formal/.lake/packages'
    if packages.is_dir():
        paths.extend(p.resolve() for p in packages.iterdir()
                     if p.is_dir() and p.resolve().is_relative_to(root))
    for path in paths:
        env[f'GIT_CONFIG_KEY_{count}'] = 'safe.directory'
        env[f'GIT_CONFIG_VALUE_{count}'] = path.as_posix()
        count += 1
    env['GIT_CONFIG_COUNT'] = str(count)
    return env


def doctor(root: Path = ROOT, *, probe: bool = False) -> dict:
    """Inspect local prerequisites. Optional bounded version probes perform no installs."""
    root = root.resolve()
    checks = [{'id': 'python', 'status': 'passed' if sys.version_info >= (3, 11) else 'failed',
               'required': True, 'version': sys.version.split()[0], 'executable': sys.executable}]
    for package in ('pytest', 'ruff', 'mpmath', 'python-flint', 'mcp'):
        try:
            version = importlib.metadata.version(package)
            checks.append({'id': package, 'status': 'passed', 'required': package != 'mcp', 'version': version})
        except importlib.metadata.PackageNotFoundError:
            checks.append({'id': package, 'status': 'failed' if package != 'mcp' else 'skipped',
                           'required': package != 'mcp', 'reason': 'Package not installed in this interpreter.',
                           'remedy': 'python -m pip install -e ".[dev]" -r tools/requirements-formalpedia.txt'})
    env = environment(root)
    for name in ('git', 'lean', 'lake', 'pandoc', 'xelatex'):
        try:
            path = executable(name, root)
        except OSError as exc:
            checks.append({'id': name, 'required': name == 'git', 'status': 'failed',
                           'version_probe': 'not_checked', 'reason': str(exc)[:500]})
            continue
        row = {'id': name, 'required': name == 'git', 'executable': path,
               'status': 'passed' if path else 'failed' if name == 'git' else 'skipped',
               'version_probe': 'not_checked'}
        if not path:
            row['reason'] = 'Executable or pinned Lean toolchain not installed locally; no installation attempted.'
        elif probe:
            try:
                argv = [path, *(['--no-lazy-fetch'] if name == 'git' else []), '--version']
                result = subprocess.run(argv, cwd=root, env=env, capture_output=True,
                                        text=True, encoding='utf-8', errors='replace', timeout=10,
                                        stdin=subprocess.DEVNULL)
                row['version_probe'] = 'passed' if result.returncode == 0 else 'failed'
                row['status'] = row['version_probe']
                row['detail'] = (result.stdout or result.stderr)[:500].strip()
            except (OSError, subprocess.TimeoutExpired) as exc:
                row.update(status='failed', version_probe='failed', detail=str(exc)[:500])
        checks.append(row)
    lock = root / 'formal/lake-manifest.json'
    if lock.is_file():
        missing = [p['name'] for p in json.loads(lock.read_text(encoding='utf-8')).get('packages', [])
                   if not (root / 'formal/.lake/packages' / p['name']).is_dir()]
        checks.append({'id': 'lean_packages', 'status': 'skipped' if missing else 'passed',
                       'required': False, 'missing': missing,
                       'verification': 'Directory presence only; compilation and axiom checks not run.'})
    database = Path(os.environ.get('OEIS_DATABASE', str(root / 'data/external/oeis/catalog.sqlite3')))
    row = {'id': 'oeis_database', 'required': False, 'path': str(database), 'status': 'skipped'}
    if database.is_file():
        try:
            with sqlite3.connect(database.resolve().as_uri() + '?mode=ro', uri=True, timeout=2) as connection:
                connection.execute('SELECT name FROM sqlite_master LIMIT 1').fetchall()
            row.update(status='passed', verification='Read-only open; corpus coverage and integrity not checked.')
        except sqlite3.Error as exc:
            row.update(status='failed', reason=str(exc))
    else:
        row['reason'] = 'Optional local OEIS index is absent; see docs/architecture/oeis_discovery.md.'
    checks.append(row)
    from lab_prepare import readiness
    prepared = readiness(root, probe=probe)
    return {'status': 'failed' if any(c['status'] == 'failed' and c['required'] for c in checks) else 'passed',
            'root': str(root), 'checks': checks,
            'preparation': prepared,
            'limitations': 'Local prerequisite discovery, not a successful build or proof audit. No secrets or client configuration are inspected; no packages are installed.'}

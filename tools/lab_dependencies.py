"""Materialize pinned Lean dependencies and copy disposable caches without shared writes."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import uuid

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'src'))
from research.claims import claim_files

GIT = ['git', '-c', 'core.longpaths=true']


def linked(path: Path) -> bool:
    return path.is_symlink() or bool(getattr(path.lstat(), 'st_file_attributes', 0) & 0x400)


def inside(root: Path, path: Path) -> Path:
    path = path.resolve()
    if not path.is_relative_to(root.resolve()) or path == root.resolve():
        raise ValueError(f'Managed path escapes the checkout: {path}')
    return path


def git(path: Path, *args: str) -> str:
    result = subprocess.run([*GIT, '-c', f'safe.directory={path.resolve().as_posix()}', *args],
        cwd=path, capture_output=True, text=True, encoding='utf-8', errors='replace',
        stdin=subprocess.DEVNULL, timeout=120)
    if result.returncode:
        raise ValueError(result.stderr.strip()[-2000:])
    return result.stdout.strip()


def packages(root: Path) -> list[dict]:
    data = json.loads((root / 'formal/lake-manifest.json').read_text(encoding='utf-8'))
    if data.get('packagesDir') != '.lake/packages':
        raise ValueError('Preparation requires the checkout-local .lake/packages directory')
    result = data['packages']
    seen = set()
    for row in result:
        if (row.get('type') != 'git' or not re.fullmatch(r'[A-Za-z][A-Za-z0-9_-]*', row.get('name', ''))
                or not re.fullmatch(r'[0-9a-f]{40}', row.get('rev', '')) or row['name'] in seen
                or not isinstance(row.get('url'), str) or not row['url'].startswith('https://')):
            raise ValueError('Unsupported or ambiguous Lean package lock entry')
        seen.add(row['name'])
    return result


def package_state(root: Path, *, probe: bool = False) -> list[dict]:
    result = []
    for row in packages(root):
        path = inside(root, root / 'formal/.lake/packages' / row['name'])
        item = {'name': row['name'], 'expected_revision': row['rev'], 'status': 'missing'}
        if path.is_dir():
            item['status'] = 'present_unverified'
            if probe:
                try:
                    revision = git(path, 'rev-parse', 'HEAD')
                    dirty = bool(git(path, 'status', '--porcelain', '--untracked-files=normal'))
                    item.update(revision=revision, dirty=dirty,
                        status='ready' if revision == row['rev'] and not dirty else 'mismatch')
                except (OSError, ValueError, subprocess.SubprocessError) as exc:
                    item.update(status='unavailable', reason=str(exc))
        result.append(item)
    return result


def math_inputs(root: Path) -> dict[str, str]:
    """Source inventory for a completed local build; exclude all generated Lake state."""
    formal = root / 'formal'
    paths = []
    if formal.is_dir():
        for child in formal.iterdir():
            if child.name == '.lake':
                continue
            paths.extend(child.rglob('*.lean') if child.is_dir() else [child] if child.suffix == '.lean' else [])
    paths += [formal / n for n in ('lean-toolchain', 'lakefile.toml', 'lakefile.lean', 'lake-manifest.json')]
    paths += [root / n for n in ('tools/lab.py', 'tools/lab_scope.py', 'tools/lab_environment.py',
        'tools/lab_prepare.py', 'tools/lab_dependencies.py',
        'src/research/claims.py', 'src/research/claim_dependencies.py',
        'tools/formalpedia_core/semantic_build.py', 'tools/lean/SemanticExport.lean')]
    paths += list(claim_files(root))  # Claim associations participate in the active Lean build graph.
    return {p.relative_to(root).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(set(paths)) if p.is_file()}


def tree_state(path: Path) -> dict[str, tuple[int, int]]:
    """A race detector for disposable cache copying, not a proof attestation."""
    result = {}
    for p in path.rglob('*'):
        if linked(p):
            raise ValueError(f'Cache contains a link; refusing shared mutable build state: {p}')
        if p.is_file():
            s = p.stat()
            result[p.relative_to(path).as_posix()] = (s.st_size, s.st_mtime_ns)
    return result


def copy_cache(source: Path, target: Path, root: Path) -> bool:
    """Copy bytes into a new local tree. Never hardlink, overwrite, or trust as a build."""
    target = inside(root, target)
    if target.exists() or not source.is_dir():
        return False
    if linked(source):
        raise ValueError('The cache donor must be a real directory')
    before = tree_state(source)
    needed = sum(size for size, _ in before.values())
    if shutil.disk_usage(root).free < needed + 256 * 1024**2:
        raise ValueError(f'Insufficient space to copy {needed} cache bytes independently')
    stage = inside(root, root / '.build/preparation' / ('cache-' + uuid.uuid4().hex))
    stage.parent.mkdir(parents=True, exist_ok=True)
    shutil.copytree(source, stage)
    if tree_state(source) != before:
        raise ValueError(f'Donor cache changed during copying; unpromoted copy retained at {stage}')
    target.parent.mkdir(parents=True, exist_ok=True)
    stage.rename(target)
    return True


def prepare_packages(root: Path, donor: Path | None, run, *, offline: bool = False) -> list[dict]:
    expected = packages(root)
    compatible = bool(donor and (donor / 'formal/lean-toolchain').read_bytes() ==
        (root / 'formal/lean-toolchain').read_bytes() and
        json.loads((donor / 'formal/lake-manifest.json').read_text()) ==
        json.loads((root / 'formal/lake-manifest.json').read_text()))
    result = []
    for row in expected:
        target = inside(root, root / 'formal/.lake/packages' / row['name'])
        source = donor / 'formal/.lake/packages' / row['name'] if compatible else None
        if not target.exists():
            target.parent.mkdir(parents=True, exist_ok=True)
            if source is None or not source.is_dir():
                if offline:
                    raise ValueError(f'{row["name"]}: no compatible local donor; offline preparation cannot fetch it')
                clone_source = row['url']
            else:
                clone_source = str(source)
            run([*GIT, 'clone', '--no-hardlinks', '--no-checkout', '--', clone_source, str(target)])
            run([*GIT, '-C', str(target), 'checkout', '--detach', row['rev']])
            # Preserve the declared upstream rather than a fragile worktree-local origin.
            run([*GIT, '-C', str(target), 'remote', 'set-url', 'origin', row['url']])
        if git(target, 'rev-parse', 'HEAD') != row['rev'] or git(target, 'status', '--porcelain', '--untracked-files=normal'):
            raise ValueError(f'{row["name"]}: existing package differs from its pin; it was not reset or replaced')
        copied = False
        if source and source.is_dir() and git(source, 'rev-parse', 'HEAD') == row['rev'] and not git(source, 'status', '--porcelain', '--untracked-files=normal'):
            copied = copy_cache(source / '.lake/build', target / '.lake/build', root)
        result.append({'name': row['name'], 'revision': row['rev'], 'cache_copied': copied})
    if compatible:
        # Lake must still validate traces/rebuild; this never counts as a successful build.
        copy_cache(donor / 'formal/.lake/build', root / 'formal/.lake/build', root)
    return result

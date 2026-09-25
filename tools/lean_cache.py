"""Shared Lean build cache: fetch compiled modules and the formalpedia snapshot, or publish them.

The laboratory's compiled Lean library (formal/, about 550 modules) and its formalpedia
semantic snapshot are published by CI, on pushes to main, to a public S3 bucket through
Lake's own remote cache (`lake cache put`/`get`). Agents fetch instead of compiling:

    python tools/lean_cache.py fetch      # Mathlib, then this library, then the snapshot
    python tools/lean_cache.py status     # configuration and URLs; no network writes
    python tools/lean_cache.py publish    # CI only: needs LAKE_CACHE_KEY

Downloads are anonymous. Lake re-hashes every downloaded artifact and rebuilds any module
whose inputs differ, so a fetch only saves compile time. Cached artifacts are not proof:
evidence still comes from the axiom audits and `formalpedia.py ledger-check`.
See docs/architecture/lean_build_cache.md.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import shutil
import stat
import subprocess
import sys
import tarfile
import tempfile
import tomllib
import urllib.error
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
from lab_environment import environment, executable  # noqa: E402

CONFIG = ROOT / 'tools/lean/lake-cache.toml'
SERVICE = 'btlab'
REPO = 'sneakyweasel/btlab'
SNAPSHOT = Path('.cache/formalpedia')
WORK = Path('.build/lean-cache')
MAX_REVS = 200


def load_service(path: Path = CONFIG) -> dict:
    """Read the one S3 service and check that both endpoints stay under the public prefix."""
    data = tomllib.loads(path.read_text(encoding='utf-8'))
    services = [s for s in data.get('cache', {}).get('service', []) if s.get('name') == SERVICE]
    if len(services) != 1:
        raise ValueError(f'{path}: expected exactly one [[cache.service]] named {SERVICE!r}')
    service = services[0]
    if service.get('kind') != 's3':
        raise ValueError(f'{path}: service {SERVICE!r} must have kind = "s3"')
    for key in ('artifactEndpoint', 'revisionEndpoint'):
        url = service.get(key, '')
        if not url.startswith('https://') or '/lean/' not in url:
            raise ValueError(f'{path}: {key} must be an https URL under the public lean/ prefix')
    if service['artifactEndpoint'].rsplit('/', 1)[0] != service['revisionEndpoint'].rsplit('/', 1)[0]:
        raise ValueError(f'{path}: artifact and revision endpoints must share one base')
    return service


def public_base(service: dict) -> str:
    """The lean/ prefix URL, parent of both Lake endpoints."""
    return service['artifactEndpoint'].rsplit('/', 1)[0]


def region(service: dict) -> str:
    """The bucket region from a virtual-hosted AWS endpoint, e.g. us-east-1."""
    host = service['artifactEndpoint'].split('/')[2]
    parts = host.split('.')
    if len(parts) >= 5 and parts[1] == 's3' and parts[-2:] == ['amazonaws', 'com']:
        return parts[2]
    raise ValueError(f'cannot read an AWS region from {host}')


def snapshot_url(service: dict, rev: str) -> str:
    return f'{public_base(service)}/formalpedia/{rev}.tgz'


def lake_env(base: dict[str, str] | None = None) -> dict[str, str]:
    """Child environment: this checkout's config, local artifact cache, outputs restored to .lake/build."""
    env = dict(base) if base is not None else environment(ROOT)
    env['LAKE_CONFIG'] = str(CONFIG)
    env['LAKE_ARTIFACT_CACHE'] = 'true'
    env['LAKE_RESTORE_ARTIFACTS'] = 'true'
    return env


def parse_key(key: str | None) -> tuple[str, str]:
    """LAKE_CACHE_KEY is ACCESS_KEY_ID:SECRET_ACCESS_KEY, as curl's --user expects."""
    if not key or key.count(':') != 1:
        raise ValueError('LAKE_CACHE_KEY must be set to ACCESS_KEY_ID:SECRET_ACCESS_KEY')
    ident, secret = (part.strip() for part in key.split(':'))
    if not ident or not secret:
        raise ValueError('LAKE_CACHE_KEY must be set to ACCESS_KEY_ID:SECRET_ACCESS_KEY')
    return ident, secret


def first_available(revs: list[str], exists) -> str | None:
    """The first revision (newest first) whose snapshot exists."""
    return next((rev for rev in revs if exists(rev)), None)


def url_exists(url: str) -> bool:
    request = urllib.request.Request(url, method='HEAD')
    try:
        with urllib.request.urlopen(request, timeout=30) as response:
            return response.status == 200
    except urllib.error.HTTPError as exc:
        if exc.code in (403, 404):  # without s3:ListBucket a missing key is 403
            return False
        raise


def mapping_count(path: Path) -> int:
    return sum(1 for line in path.read_text(encoding='utf-8').splitlines() if line.strip())


def check_mappings(count: int, modules: int) -> None:
    """A publish that recorded fewer mappings than modules would upload a partial cache."""
    if modules <= 0:
        raise ValueError('no build targets')
    if count < modules:
        raise ValueError(f'lake build -o recorded {count} mappings for {modules} modules; '
                         'refusing to publish a partial cache')


def safe_members(archive: tarfile.TarFile) -> list[tarfile.TarInfo]:
    """Regular files and directories with relative paths inside the archive root only."""
    members = []
    for member in archive.getmembers():
        path = PurePosixPath(member.name)
        if path.is_absolute() or '..' in path.parts or not (member.isfile() or member.isdir()):
            raise ValueError(f'unsafe snapshot member: {member.name}')
        members.append(member)
    return members


def extract_snapshot(archive_path: Path, dest: Path) -> None:
    """Replace dest with the archive's contents, only after every member passes the checks."""
    staging = Path(tempfile.mkdtemp(prefix='snapshot-', dir=dest.parent))
    try:
        with tarfile.open(archive_path, 'r:gz') as archive:
            members = safe_members(archive)
            archive.extractall(staging, members=members, filter='data')
        if dest.exists():
            shutil.rmtree(dest)
        staging.rename(dest)
    finally:
        if staging.exists():
            shutil.rmtree(staging)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1 << 20), b''):
            digest.update(block)
    return digest.hexdigest()


def curl_shim(directory: Path, real_curl: str, aws_region: str) -> Path:
    """A curl wrapper for `lake cache put`: Lake signs with region `auto`, which AWS rejects."""
    if os.name == 'nt':
        raise ValueError('publishing is supported from Linux CI only')
    shim = directory / 'curl'
    shim.write_text(
        '#!/bin/sh\n'
        '# Rewrites the SigV4 region Lake passes (auto) to the bucket region.\n'
        'for a do\n'
        '  shift\n'
        f'  if [ "$a" = "aws:amz:auto:s3" ]; then a="aws:amz:{aws_region}:s3"; fi\n'
        '  set -- "$@" "$a"\n'
        'done\n'
        f'exec "{real_curl}" "$@"\n', encoding='utf-8')
    shim.chmod(shim.stat().st_mode | stat.S_IXUSR | stat.S_IXGRP | stat.S_IXOTH)
    return shim


def run(argv: list[str], *, cwd: Path, env: dict[str, str]) -> None:
    print('lean_cache:', ' '.join(argv), file=sys.stderr, flush=True)
    subprocess.run(argv, cwd=cwd, env=env, check=True, stdin=subprocess.DEVNULL)


def git_revs(limit: int = MAX_REVS) -> list[str]:
    out = subprocess.run(['git', 'rev-list', '--first-parent', '-n', str(limit), 'HEAD'], cwd=ROOT,
                         env=environment(ROOT), check=True, capture_output=True, text=True).stdout
    return out.split()


def require_lake() -> str:
    lake = executable('lake', ROOT)
    if lake is None:
        raise ValueError('the pinned Lean toolchain (formal/lean-toolchain) is not installed')
    return lake


def fetch(*, mathlib: bool = True, library: bool = True, build: bool = True, snapshot: bool = True) -> dict:
    service = load_service()
    lake, env, formal = require_lake(), lake_env(), ROOT / 'formal'
    result: dict = {'service': SERVICE, 'repo': REPO}
    if mathlib:
        run([lake, 'exe', 'cache', 'get'], cwd=formal, env=env)
        result['mathlib'] = 'fetched'
    if library:
        run([lake, 'cache', 'get', '--service', SERVICE, '--repo', REPO, f'--max-revs={MAX_REVS}'],
            cwd=formal, env=env)
        result['library'] = 'fetched into the local Lake cache'
    if build:
        # Restores cached outputs into formal/.lake/build; compiles only modules whose inputs differ.
        from lab import build_targets
        from lab_lock import build_lock_path, exclusive
        # It may compile changed modules, so it takes the machine-wide build lock.
        with exclusive(build_lock_path(), purpose='lean_cache.py fetch', root=ROOT):
            run([lake, 'build', *('+' + m for m in build_targets())], cwd=formal, env=env)
        result['build'] = 'restored; changed modules compiled locally'
    if snapshot:
        rev = first_available(git_revs(), lambda r: url_exists(snapshot_url(service, r)))
        if rev is None:
            result['snapshot'] = f'none published within the last {MAX_REVS} first-parent commits'
        else:
            work = ROOT / WORK
            work.mkdir(parents=True, exist_ok=True)
            archive = work / f'formalpedia-{rev}.tgz'
            urllib.request.urlretrieve(snapshot_url(service, rev), archive)
            with urllib.request.urlopen(snapshot_url(service, rev) + '.sha256', timeout=30) as response:
                expected = response.read().decode('ascii').split()[0]
            if sha256(archive) != expected:
                archive.unlink()
                raise ValueError(f'formalpedia snapshot for {rev} does not match its published sha256')
            (ROOT / SNAPSHOT).parent.mkdir(parents=True, exist_ok=True)
            extract_snapshot(archive, ROOT / SNAPSHOT)
            result['snapshot'] = {'revision': rev, 'sha256': expected}
    return result


def put_object(path: Path, url: str, key: str, aws_region: str, content_type: str) -> None:
    """Signed PUT with curl; the key is passed on the command line only to curl, never printed."""
    parse_key(key)
    process = subprocess.run(
        ['curl', '-sS', '--fail-with-body', '--aws-sigv4', f'aws:amz:{aws_region}:s3', '--user', key,
         '-X', 'PUT', '-T', str(path), '-H', f'Content-Type: {content_type}', url],
        capture_output=True, text=True, stdin=subprocess.DEVNULL)
    if process.returncode:
        raise ValueError(f'upload of {url} failed: {(process.stdout + process.stderr).replace(key, "***")[-500:]}')


def publish(*, snapshot: bool = True) -> dict:
    service = load_service()
    key = os.environ.get('LAKE_CACHE_KEY')
    parse_key(key)
    dirty = subprocess.run(['git', 'status', '--porcelain', '--untracked-files=no'], cwd=ROOT,
                           env=environment(ROOT), capture_output=True, text=True, check=True).stdout
    if dirty.strip():
        raise ValueError('refusing to publish from a checkout with tracked changes')
    rev = git_revs(1)[0]
    lake, formal = require_lake(), ROOT / 'formal'
    from lab import build_targets
    modules = build_targets()
    work = ROOT / WORK
    work.mkdir(parents=True, exist_ok=True)
    mappings = work / f'map-{rev}.jsonl'
    env = lake_env()
    from lab_lock import build_lock_path, exclusive
    with exclusive(build_lock_path(), purpose='lean_cache.py publish', root=ROOT):
        run([lake, 'build', '-o', str(mappings), *('+' + m for m in modules)], cwd=formal, env=env)
    count = mapping_count(mappings)
    check_mappings(count, len(modules))
    aws_region = region(service)
    with tempfile.TemporaryDirectory() as shim_dir:
        real_curl = shutil.which('curl')
        if real_curl is None:
            raise ValueError('curl is required to publish')
        curl_shim(Path(shim_dir), real_curl, aws_region)
        put_env = dict(env, PATH=shim_dir + os.pathsep + env.get('PATH', ''), LAKE_CACHE_KEY=key)
        run([lake, 'cache', 'put', str(mappings), '--service', SERVICE, '--repo', REPO], cwd=formal, env=put_env)
    result = {'revision': rev, 'modules': len(modules), 'mappings': count}
    if snapshot:
        source = ROOT / SNAPSHOT
        if not source.is_dir():
            raise ValueError(f'{SNAPSHOT} does not exist; run lab.py build first')
        archive = work / f'formalpedia-{rev}.tgz'
        with tarfile.open(archive, 'w:gz') as tar:
            for path in sorted(source.rglob('*')):
                if path.is_file():
                    tar.add(path, arcname=path.relative_to(source).as_posix(), recursive=False)
        digest = sha256(archive)
        sidecar = work / f'formalpedia-{rev}.tgz.sha256'
        sidecar.write_text(f'{digest}  {rev}.tgz\n', encoding='ascii')
        url = snapshot_url(service, rev)
        put_object(archive, url, key, aws_region, 'application/gzip')
        put_object(sidecar, url + '.sha256', key, aws_region, 'text/plain')
        result['snapshot'] = {'url': url, 'sha256': digest}
    return result


def status() -> dict:
    service = load_service()
    return {'config': str(CONFIG.relative_to(ROOT)), 'service': SERVICE, 'repo': REPO,
            'artifact_endpoint': service['artifactEndpoint'], 'revision_endpoint': service['revisionEndpoint'],
            'snapshot_prefix': public_base(service) + '/formalpedia/', 'region': region(service),
            'lake': executable('lake', ROOT), 'upload_key_present': bool(os.environ.get('LAKE_CACHE_KEY')),
            'limitations': 'Cached artifacts save compile time only; they are not proof status.'}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split('\n\n')[0])
    commands = parser.add_subparsers(dest='command', required=True)
    get = commands.add_parser('fetch', help='download Mathlib, this library and the formalpedia snapshot')
    get.add_argument('--no-mathlib', action='store_true')
    get.add_argument('--no-library', action='store_true')
    get.add_argument('--no-build', action='store_true', help='download only; do not restore into formal/.lake/build')
    get.add_argument('--no-snapshot', action='store_true')
    put = commands.add_parser('publish', help='CI only: upload this commit (needs LAKE_CACHE_KEY)')
    put.add_argument('--no-snapshot', action='store_true')
    commands.add_parser('status', help='print configuration; no network writes')
    args = parser.parse_args(argv)
    try:
        if args.command == 'fetch':
            result = fetch(mathlib=not args.no_mathlib, library=not args.no_library, build=not args.no_build,
                           snapshot=not args.no_snapshot)
        elif args.command == 'publish':
            result = publish(snapshot=not args.no_snapshot)
        else:
            result = status()
    except (ValueError, OSError, subprocess.CalledProcessError, urllib.error.URLError) as exc:
        print(json.dumps({'status': 'failed', 'reason': str(exc)}, indent=2))
        return 1
    print(json.dumps({'status': 'ok', **result}, indent=2))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())

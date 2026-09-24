"""Checkout-bound Git queries shared by discovery, provenance and validation.

Query commands are fixed by their callers, never loaded from saved research data.
This is a cooperative read API, not a sandbox for arbitrary Git arguments/config.
Explicit repository mutations belong to preparation/publication orchestration.
"""
from __future__ import annotations

import os
from pathlib import Path
import subprocess

# Repository-local selectors must not redirect a query to a caller's checkout,
# alternate index, object store or namespace. Keep ordinary caller configuration
# (including narrow safe.directory entries and credentials) without printing it.
SELECTORS = frozenset({
    'GIT_ALTERNATE_OBJECT_DIRECTORIES', 'GIT_OBJECT_DIRECTORY', 'GIT_DIR', 'GIT_WORK_TREE',
    'GIT_IMPLICIT_WORK_TREE', 'GIT_GRAFT_FILE', 'GIT_INDEX_FILE', 'GIT_REPLACE_REF_BASE',
    'GIT_NO_REPLACE_OBJECTS', 'GIT_PREFIX', 'GIT_SHALLOW_FILE', 'GIT_COMMON_DIR', 'GIT_NAMESPACE',
    'GIT_LITERAL_PATHSPECS', 'GIT_GLOB_PATHSPECS', 'GIT_NOGLOB_PATHSPECS', 'GIT_ICASE_PATHSPECS',
})
QUERIES = frozenset({'rev-parse', 'rev-list', 'status', 'diff', 'ls-files', 'ls-tree', 'cat-file',
                     'show', 'log', 'for-each-ref', 'merge-base', 'archive'})


def environment(base: dict[str, str] | None = None) -> dict[str, str]:
    """Copy the caller environment, removing checkout overrides and optional locks.

Also suitable for explicitly requested child mutations: mandatory Git locks are
unaffected. No process-global environment or persistent Git config is changed.
"""
    env = dict(os.environ if base is None else base)
    for key in list(env):
        if key.upper() in SELECTORS:
            env.pop(key)
    env['GIT_OPTIONAL_LOCKS'] = '0'
    return env


def query_command(root: Path, *args: str) -> list[str]:
    if not args or args[0] not in QUERIES:
        raise ValueError('Expected a fixed, read-only Git query command')
    # Do not let a later flag re-enable helper execution or write a query to disk.
    # Callers supply literal revisions/paths after their appropriate -- separator.
    flags = args[1:args.index('--')] if '--' in args else args[1:]
    forbidden = {'--output', '-o', '--remote', '--exec', '--ext-diff', '--textconv', '--filters'}
    if any(arg.split('=', 1)[0] in forbidden or arg.startswith('-o') and arg != '-o' for arg in flags):
        raise ValueError('Git query cannot write output files or invoke external helpers')
    root = root.resolve()
    command = ['git', '--no-pager', '--no-optional-locks', '--no-replace-objects', '--no-lazy-fetch',
               '-c', f'safe.directory={root.as_posix()}', '-c', 'core.longpaths=true',
               '-c', 'core.fsmonitor=false', '-c', 'diff.autoRefreshIndex=false',
               '-c', 'gc.auto=0', '-C', str(root)]
    extra = ['--no-ext-diff', '--no-textconv'] if args[0] in {'diff', 'show', 'log'} else []
    return [*command, args[0], *extra, *args[1:]]


def query_environment(root: Path) -> dict[str, str]:
    env = environment()
    # A requested directory without its own repository must not silently discover
    # an ancestor checkout. Worktree gitfiles and explicitly selected bare repos
    # still resolve through Git itself.
    env['GIT_CEILING_DIRECTORIES'] = str(root.resolve().parent)
    return env


def query(root: Path, *args: str, timeout: float = 60, text: bool = False,
          input: bytes | str | None = None, check: bool = False) -> subprocess.CompletedProcess:
    options = {'encoding': 'utf-8', 'errors': 'replace'} if text else {}
    return subprocess.run(query_command(root, *args), cwd=root.resolve(), env=query_environment(root),
                          capture_output=True, input=input, timeout=timeout, check=check,
                          **({'stdin': subprocess.DEVNULL} if input is None else {}), **options)


def blobs(root: Path, revision: str, paths: list[str]) -> dict[str, bytes | None]:
    """Read exact committed blobs in one batch; None means a missing path.

    Invalid/missing history and a malformed response fail explicitly. Git archive
    attributes and worktree line endings cannot alter these committed bytes.
    NUL-delimited requests support paths containing spaces, tabs and newlines.
    """
    if any(not isinstance(p, str) or not p or '\0' in p for p in paths) or len(set(paths)) != len(paths):
        raise ValueError('Expected distinct nonempty Git paths without NUL characters')
    commit = query(root, 'rev-parse', '--verify', '--end-of-options', revision + '^{commit}',
                   text=True, check=True).stdout.strip()
    if not paths:
        return {}
    tree = query(root, 'ls-tree', '-r', '-t', '-z', '--full-tree', commit, check=True).stdout
    objects = {}
    selected = set(paths)
    for entry in tree.split(b'\0'):
        if not entry:
            continue
        header, name = entry.split(b'\t', 1)
        name = name.decode('utf-8')
        if name in selected:
            _, kind, identifier = header.split()
            if kind != b'blob':
                raise ValueError('Expected a Git blob, not a directory or submodule')
            objects[name] = identifier
    result = dict.fromkeys(paths)
    if not objects:
        return result
    requests = b''.join(identifier + b'\0' for identifier in objects.values())
    raw = query(root, 'cat-file', '--batch', '-Z', input=requests, check=True).stdout
    position = 0
    for name in objects:
        end = raw.find(b'\0', position)
        if end < 0:
            raise ValueError('Truncated Git blob response')
        header = raw[position:end]
        position = end + 1
        if header.endswith(b' missing'):
            raise ValueError(f'Committed blob is not available locally: {name}')
        fields = header.split()
        if len(fields) != 3 or fields[1] != b'blob' or not fields[2].isdigit():
            raise ValueError('Expected a Git blob, not a directory or malformed response')
        size = int(fields[2])
        if position + size >= len(raw) or raw[position + size:position + size + 1] != b'\0':
            raise ValueError('Truncated Git blob contents')
        result[name] = raw[position:position + size]
        position += size + 1
    if position != len(raw):
        raise ValueError('Unexpected trailing Git blob response')
    return result

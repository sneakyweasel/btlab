"""Build the active Juggler/Collatz Lean graph without changing paper-pinned Lake files."""
from __future__ import annotations

import argparse
import os
from pathlib import Path
import shutil
import subprocess

import formalpedia as fp
from lab_scope import active_lean_modules


def build_targets() -> list[str]:
    paths = fp.sources()
    known = {fp.module_of(p) for p in paths}
    graph = {'modules': {fp.module_of(p): {'imports': fp.imports(p, known)} for p in paths}}
    active = active_lean_modules(graph)
    # Build every application module, including modules not imported by the paper barrels.
    return sorted(n for n in active if n.startswith(('Problems.Juggler', 'Problems.Collatz.')))


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=['build'])
    parser.add_argument('--include-archive', action='store_true')
    parser.add_argument('--list', action='store_true', help='show targets without building')
    args = parser.parse_args(argv)
    targets = [] if args.include_archive else build_targets()
    if not args.include_archive and not targets:
        parser.error('No Juggler/Collatz modules found; refusing a historical default build')
    if args.list:
        print('\n'.join(targets) if targets else 'Lake historical default targets')
        return 0
    lake = shutil.which('lake')
    if not lake:
        candidate = Path(os.environ.get('USERPROFILE', str(Path.home()))) / '.elan/bin/lake.exe'
        lake = str(candidate) if candidate.is_file() else 'lake'
    return subprocess.run([lake, 'build', *targets], cwd=fp.FORMAL, stdin=subprocess.DEVNULL).returncode


if __name__ == '__main__':
    raise SystemExit(main())

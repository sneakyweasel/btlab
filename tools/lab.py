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
    # Include standalone application and ledger-cited modules, not only paper barrels.
    return sorted(active)


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=['build'])
    parser.add_argument('--list', action='store_true', help='show targets without building')
    args = parser.parse_args(argv)
    targets = build_targets()
    if not targets:
        parser.error('No Juggler/Collatz modules found; check the source checkout')
    if args.list:
        print('\n'.join(targets))
        return 0
    lake = shutil.which('lake')
    if not lake:
        candidate = Path(os.environ.get('USERPROFILE', str(Path.home()))) / '.elan/bin/lake.exe'
        lake = str(candidate) if candidate.is_file() else 'lake'
    return subprocess.run([lake, 'build', *targets], cwd=fp.FORMAL, stdin=subprocess.DEVNULL).returncode


if __name__ == '__main__':
    raise SystemExit(main())

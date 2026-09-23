"""Run research, tests and Lean builds against this checkout, including in worktrees."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess
import sys

import formalpedia as fp
from lab_scope import active_lean_modules
from lab_environment import environment, executable


def build_targets() -> list[str]:
    paths = fp.sources()
    known = {fp.module_of(p) for p in paths}
    graph = {'modules': {fp.module_of(p): {'imports': fp.imports(p, known)} for p in paths}}
    active = active_lean_modules(graph)
    # Include standalone application and ledger-cited modules, not only paper barrels.
    return sorted(active)


def run_python(arguments: list[str], root: Path | None = None) -> int:
    """Prefer this checkout's sources over any other editable installation."""
    root = fp.ROOT if root is None else root.resolve()
    env = environment(root)
    if len(arguments) >= 2 and arguments[0] == '-m' and arguments[1] != 'pytest':
        env['BTLAB_RUN_COMMAND'] = json.dumps(['python', 'tools/lab.py', 'run', *arguments[1:]])
    else:
        env.pop('BTLAB_RUN_COMMAND', None)
    return subprocess.run([sys.executable, *arguments], cwd=root, env=env).returncode


def main(argv=None) -> int:
    arguments = list(sys.argv[1:] if argv is None else argv)
    if arguments and arguments[0] in {'doctor', 'impact', 'verify'}:
        from lab_verify import main as workflow_main
        return workflow_main(arguments)
    if arguments and arguments[0] in {'search', 'context', 'check', 'manifest'}:
        from research_catalog import main as research_main
        return research_main(arguments)
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='command', required=True)
    build = commands.add_parser('build', help='build every retained Lean application and dependency')
    build.add_argument('--list', action='store_true', help='show targets without building')
    run = commands.add_parser('run', help='run a Python module from this checkout')
    run.add_argument('module', help='for example research.juggler_sequence.branch_index')
    run.add_argument('args', nargs=argparse.REMAINDER)
    test = commands.add_parser('test', help='run pytest using this checkout\'s source tree')
    test.add_argument('args', nargs=argparse.REMAINDER)
    for name in ('doctor', 'impact', 'verify'):
        commands.add_parser(name, add_help=False, help={
            'doctor': 'inspect local prerequisites',
            'impact': 'trace changed files to modules, claims, papers and tests',
            'verify': 'plan or run change-aware validation',
        }[name])
    for name in ('search', 'context', 'check', 'manifest'):
        command = commands.add_parser(name, add_help=False, help={
            'search': 'search Juggler and Collatz research dossiers',
            'context': 'read one bounded research context section',
            'check': 'validate research references and output manifests',
            'manifest': 'record provenance for a newly completed experiment',
        }[name])
        command.add_argument('args', nargs=argparse.REMAINDER)
    args = parser.parse_args(argv)
    if args.command in {'run', 'test'}:
        forwarded = args.args[1:] if args.args[:1] == ['--'] else args.args
        module = args.module if args.command == 'run' else 'pytest'
        return run_python(['-m', module, *forwarded])
    targets = build_targets()
    if not targets:
        parser.error('No Juggler/Collatz modules found; check the source checkout')
    if args.list:
        print('\n'.join(targets))
        return 0
    lake = executable('lake', fp.ROOT)
    if not lake:
        parser.error('Pinned Lean toolchain is not installed locally; run lab.py doctor')
    return subprocess.run([lake, 'build', *targets], cwd=fp.FORMAL,
                          env=environment(fp.ROOT), stdin=subprocess.DEVNULL).returncode


if __name__ == '__main__':
    raise SystemExit(main())

"""Command line entry point for the Juggler–Collatz laboratory."""
from __future__ import annotations

import argparse
from pathlib import Path

from research.collatz.cli import add_collatz_subparser, run_collatz
from research.open_problems import list_problems


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog='btlab', description='Juggler–Collatz Mathematical Laboratory')
    commands = parser.add_subparsers(dest='command', required=True)
    add_collatz_subparser(commands)
    commands.add_parser('status', help='show active applications and verification commands')
    commands.add_parser('formal', help='show the Lean toolchain and build command')
    args = parser.parse_args(argv)
    if args.command == 'collatz':
        return run_collatz(args)
    if args.command == 'status':
        print('Active applications: ' + ', '.join(p.id for p in list_problems()))
        print('Python checks: pytest')
        print('Juggler probes: python -m research.juggler_sequence.<branch>')
        print('Juggler atlas: juggler-atlas --help')
    toolchain = Path(__file__).resolve().parents[2] / 'formal/lean-toolchain'
    if toolchain.is_file():
        print('Lean toolchain: ' + toolchain.read_text(encoding='utf-8').strip())
    print('Lean build: python tools/lab.py build')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())

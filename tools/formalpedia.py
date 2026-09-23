"""Formalpedia CLI and the small read-only surface used by publication probes."""
from formalpedia_core.source import build as build
from formalpedia_core.graph import reachable as reachable, paper_surface as paper_surface


def main(argv=None):
    from formalpedia_core.cli import main as cli_main
    return cli_main(argv)


if __name__ == '__main__':
    raise SystemExit(main())

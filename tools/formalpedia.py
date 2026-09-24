"""Formalpedia CLI and the small read-only surface used by publication probes."""
from formalpedia_core import source as _source
from formalpedia_core.graph import reachable as reachable, paper_surface as paper_surface


def build():
    """The source index in the schema released papers' pinned probes consume.

    Paper C's formal-layer checker is a hash-pinned release input and tests
    ``trust == "kernel"``. The catalogue, CLI and MCP call that value ``unmarked``,
    since it only means no sorry, admit, axiom or native_decide appears in the source;
    this surface keeps the released label until those probes are rebuilt.
    """
    index = _source.build()
    for decl in index['declarations']:
        if decl['trust'] == 'unmarked':
            decl['trust'] = 'kernel'
    return index


def main(argv=None):
    from formalpedia_core.cli import main as cli_main
    return cli_main(argv)


if __name__ == '__main__':
    raise SystemExit(main())

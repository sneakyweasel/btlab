"""Start the pinned Lean MCP with this repository's project and elan environment.

Install uv in the invoking Python environment. The server itself lives in uv's
isolated tool cache, separate from laboratory and formalpedia dependencies.
"""
from __future__ import annotations

import os
from pathlib import Path
import subprocess
import sys


def main() -> None:
    project = Path(__file__).resolve().parents[1] / 'formal'
    elan = Path(os.environ.get('ELAN_HOME', Path.home() / '.elan'))
    os.environ.setdefault('ELAN_HOME', str(elan))
    os.environ['PATH'] = str(elan / 'bin') + os.pathsep + os.environ.get('PATH', '')
    os.environ.setdefault('LEAN_LOG_LEVEL', 'NONE')
    argv = [sys.executable, '-m', 'uv', 'tool', 'run',
        '--from', 'lean-lsp-mcp==0.30.0', 'lean-lsp-mcp',
        '--lean-project-path', str(project), *sys.argv[1:]]
    if os.name == 'nt':
        # Windows has no in-place exec: os.execv starts a new process and exits
        # this one, and Node-based MCP clients then close the server's stdin.
        raise SystemExit(subprocess.call(argv))
    os.execv(sys.executable, argv)


if __name__ == '__main__':
    main()

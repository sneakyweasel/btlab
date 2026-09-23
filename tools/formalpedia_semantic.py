"""Explicit semantic CLI; the MCP uses formalpedia_core.semantic_query directly."""
from __future__ import annotations

import argparse
import json
import subprocess
from formalpedia_core.semantic_query import SemanticCatalogue


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    p = sub.add_parser('build', help='explicitly compile and export; MCP never builds')
    p.add_argument('--module', action='append', dest='modules')
    p.add_argument('--timeout', type=int, default=1800)
    sub.add_parser('status')
    sub.add_parser('migrate', help='convert the current snapshot to module files without rebuilding Lean')
    p = sub.add_parser('show')
    p.add_argument('name')
    p.add_argument('--include-ast', action='store_true')
    p = sub.add_parser('search')
    p.add_argument('--constant', action='append', dest='constants')
    p.add_argument('--like')
    p.add_argument('--pattern', type=json.loads)
    p.add_argument('--part', choices=['type', 'conclusion'], default='type')
    p.add_argument('--kind')
    p.add_argument('--module')
    p.add_argument('--include-private', action='store_true')
    p = sub.add_parser('dependencies')
    p.add_argument('name')
    p.add_argument('--direction', choices=['uses', 'used_by'], default='uses')
    p.add_argument('--edge', choices=['all', 'type', 'value'], default='all')
    p.add_argument('--depth', type=int, default=1)
    p = sub.add_parser('diff')
    p.add_argument('before')
    p.add_argument('--after')
    for name in ('search', 'dependencies', 'diff'):
        p = sub.choices[name]
        p.add_argument('--limit', type=int, default=20)
        p.add_argument('--offset', type=int, default=0)
        if name != 'diff':
            p.add_argument('--snapshot')
    options = vars(parser.parse_args(argv))
    command = options.pop('command')
    try:
        if command == 'build':
            from formalpedia_core.semantic_build import build
            result = build(**options)
        elif command == 'migrate':
            result = SemanticCatalogue()._store.migrate()
        else:
            result = getattr(SemanticCatalogue(), command)(**options)
    except (ValueError, OSError, subprocess.TimeoutExpired) as exc:
        print(json.dumps({'status': 'failed', 'reason': str(exc)}))
        return 1
    print(json.dumps(result, ensure_ascii=False, indent=2))
    return 0 if result.get('status') not in {'missing', 'stale', 'unreadable', 'ambiguous', 'not_found'} else 1


if __name__ == "__main__":
    raise SystemExit(main())

"""Reproducible, opt-in paper examples through the real OEIS MCP stdio transport.

Requires the local full index and optional MCP dependencies. No network or source
edits. Terms come from integer arithmetic, not from the index being tested.
"""
from __future__ import annotations

import argparse
import asyncio
from datetime import datetime, timezone
import json
from math import isqrt
import os
from pathlib import Path
import re
import sys
from time import perf_counter

from mcp import ClientSession, StdioServerParameters
from mcp.client.stdio import stdio_client

ROOT = Path(__file__).resolve().parents[1]


def juggler(n: int) -> int:
    return isqrt(n if n % 2 == 0 else n ** 3)


def orbit(n: int) -> list[int]:
    values = [n]
    while n > 1:
        n = juggler(n)
        values.append(n)
        if len(values) > 1000:
            raise ValueError('Audit orbit exceeded its fixed budget')
    return values


def survivor_rows(depth: int) -> list[list[int]]:
    rows = [[1]]
    for length in range(1, depth + 1):
        previous = rows[-1]
        rows.append([(previous[o] if o < len(previous) else 0) +
                     (previous[o - 1] if o else 0)
                     if 3 ** o >= 2 ** length else 0 for o in range(length + 1)])
    return rows


def examples() -> list[dict]:
    rows = survivor_rows(80)
    totals = list(map(sum, rows))
    certificates = [2 * totals[d - 1] - totals[d] for d in range(1, 81)]
    nonzero = [v for v in certificates if v]
    dropping = [0] + [next(i for i, v in enumerate(orbit(2 * n + 1)) if v < 2 * n + 1)
                      for n in range(1, 40)]
    definitions = [
        ('juggler_map', 'A094683', [juggler(n) for n in range(40)], 'prefix'),
        ('juggler_stopping_time', 'A007320', [len(orbit(n)) - 1 for n in range(1, 41)], 'prefix'),
        ('juggler_height', 'A094716', [max(orbit(n)) for n in range(40)], 'prefix'),
        ('juggler_dropping_time', 'A094778', dropping, 'prefix'),
        ('survivor_counts', 'A076227', totals[:40], 'prefix'),
        ('powers_three_binary_lengths', 'A020914', [(3 ** n).bit_length() for n in range(40)], 'prefix'),
        ('free_lengths_with_endpoint', 'A054414', [1] + [d for d, v in enumerate(certificates, 1) if v == 0][:25], 'prefix'),
        ('nonzero_certificates', 'A186009', nonzero[:30], 'prefix'),
        ('admissible_counts_shifted', 'A100982', nonzero[1:31], 'prefix'),
        ('terminal_odd_words', 'A260591', [0] + certificates[1:40], 'prefix'),
        ('selected_semiconvergents', 'A206788', [1, 2, 7, 12, 53, 359, 665, 16266, 31867, 111202], 'subsequence'),
    ]
    return [{'case': case, 'expected': expected, 'terms': list(map(str, values)), 'mode': mode}
            for case, expected, values, mode in definitions]


async def audit() -> dict:
    report = {'created_at': datetime.now(timezone.utc).isoformat(), 'checks': []}
    params = StdioServerParameters(command=sys.executable, args=[str(ROOT / 'tools/oeis_mcp.py')],
                                  cwd=str(ROOT), env=dict(os.environ, PYTHONUTF8='1'))
    async with stdio_client(params) as (read, write):
        async with ClientSession(read, write) as session:
            await session.initialize()
            available = {t.name for t in (await session.list_tools()).tools}

            async def call(name, arguments):
                started = perf_counter()
                result = await asyncio.wait_for(session.call_tool(name, arguments), timeout=30)
                if result.isError:
                    raise AssertionError(str(result.content))
                return result.structuredContent, round(perf_counter() - started, 4)

            report['status'], _ = await call('oeis_status', {})
            required = {'oeis_status', 'oeis_get', 'oeis_terms', 'oeis_search', 'oeis_match_terms',
                        'oeis_compare_terms', 'oeis_neighbors', 'oeis_bfile', 'oeis_lab_links'}
            report['checks'].append({'case': 'tool_availability', 'passed': required <= available})
            result, seconds = await call('oeis_terms', {'identifier': 'A007320', 'limit': 40})
            report['checks'].append({'case': 'terms_offsets', 'passed':
                result['terms'] == [{'position': n - 1, 'n': n, 'value': str(len(orbit(n)) - 1)}
                                    for n in range(1, 41)], 'seconds': seconds})
            for example in examples():
                arguments = {k: example[k] for k in ('terms', 'mode')} | {'limit': 50}
                results, seconds = await call('oeis_match_terms', arguments)
                matches = list(results['results'])
                pages = 1
                while results['next_cursor'] and pages < 20:
                    results, elapsed = await call('oeis_match_terms', arguments | {'cursor': results['next_cursor']})
                    seconds += elapsed
                    matches.extend(results['results'])
                    pages += 1
                found = [r for r in matches if r['aid'] == example['expected']]
                report['checks'].append({'case': example['case'], 'passed': bool(found),
                    'expected': example['expected'], 'input_terms': example['terms'],
                    'mode': example['mode'], 'matches': [r['aid'] for r in matches],
                    'alignment': found[0] if found else None, 'seconds': round(seconds, 4),
                    'exhausted': results['exhausted']})

            short = [str(juggler(n)) for n in range(6)]
            result, seconds = await call('oeis_match_terms', {'terms': short, 'mode': 'prefix', 'limit': 50})
            ids = [r['aid'] for r in result['results']]
            report['checks'].append({'case': 'short_juggler_ambiguity',
                'passed': {'A094683', 'A094685'} <= set(ids), 'matches': ids, 'seconds': seconds})
            triangle = [str(v) for row in survivor_rows(14)[1:] for v in reversed(row) if v]
            triangle_position = None
            for length, expected in [(24, True), (len(triangle), False)]:
                result, seconds = await call('oeis_match_terms', {'terms': triangle[:length], 'limit': 50})
                ids = [r['aid'] for r in result['results']]
                if expected:
                    triangle_position = next(r['first_match_positions'][0] for r in result['results']
                                             if r['aid'] == 'A214494')
                report['checks'].append({'case': f'triangle_{length}_terms',
                    'passed': ('A214494' in ids) == expected, 'matches': ids, 'seconds': seconds,
                    'exhausted': result['exhausted']})
            for query, target in [('surviving Collatz residues', 'A076227'), ('dropping juggler', 'A094778')]:
                result, seconds = await call('oeis_search', {'query': query})
                ids = [r['aid'] for r in result['results']]
                report['checks'].append({'case': f'text_{target}', 'passed': target in ids,
                                        'matches': ids, 'seconds': seconds})
            result, seconds = await call('oeis_get', {'identifier': 'A076227', 'fields': ['comments', 'formulas']})
            report['checks'].append({'case': 'published_fields', 'passed': bool(result['fields']),
                                    'entry_revision': result['entry_revision'], 'seconds': seconds})
            result, seconds = await call('oeis_neighbors', {'identifier': 'A076227', 'explicit_only': False})
            report['checks'].append({'case': 'cross_references', 'passed': result['total'] > 0, 'seconds': seconds})
            result, seconds = await call('oeis_bfile', {'identifier': 'A094683'})
            report['checks'].append({'case': 'bfile_coverage', 'passed': result['status'] == 'lfs_pointer',
                                    'status': result['status'], 'seconds': seconds})
            result, seconds = await call('oeis_lab_links', {'identifier': 'A076227', 'limit': 50})
            report['checks'].append({'case': 'lean_ledger_links',
                'passed': bool(result['lean_declarations']) and bool(result['ledger_claims']),
                'total_mentions': result['total_mentions'], 'seconds': seconds})
            result, seconds = await call('oeis_get', {'identifier': 'A076227', 'fields': ['examples'], 'limit': 50})
            table_rows = []
            for field in result['fields']:
                match = re.fullmatch(r'\s*n\s*=\s*(\d+)\s*\|([\d\s]+)\|\s*(\d+)\s*', field['text'])
                if match:
                    n = int(match[1])
                    values = list(map(int, match[2].split()))
                    row = survivor_rows(n)[-1]
                    table_rows.append(values == [v for v in row if v] and int(match[3]) == sum(row))
            report['checks'].append({'case': 'triangle_in_example_text',
                'passed': len(table_rows) == 10 and all(table_rows), 'rows_verified': len(table_rows), 'seconds': seconds})
            if 'oeis_compare_terms' in available:
                survivor_terms = list(map(str, map(sum, survivor_rows(45))))
                free = [1] + [d for d in range(2, 170) if d not in {(3 ** n).bit_length() for n in range(110)}]
                for case, target, terms, position, status in [
                    ('juggler_candidate_disagreement', 'A094685', [str(juggler(n)) for n in range(40)], 0, 'mismatch'),
                    ('triangle_candidate_disagreement', 'A214494', triangle, triangle_position, 'mismatch'),
                    ('beatty_candidate_disagreement', 'A136616', list(map(str, free[:55])), 0, 'mismatch'),
                    ('survivor_storage_limit', 'A076227', survivor_terms, 0, 'insufficient_data'),
                ]:
                    result, seconds = await call('oeis_compare_terms',
                        {'identifier': target, 'terms': terms, 'start_position': position})
                    report['checks'].append({'case': case, 'passed': result['status'] == status,
                        'comparison': result, 'seconds': seconds})
                result, seconds = await call('oeis_lab_links', {'identifier': 'A076227', 'kinds': ['paper'], 'limit': 50})
                files = {m['file'] for m in result['mentions']}
                report['checks'].append({'case': 'latex_manuscript_links', 'passed':
                    {'docs/theory/cochin-juggler.tex', 'docs/theory/juggler_parity_discrepancy_note.tex'} <= files,
                    'files': sorted(files), 'mention_counts': result['mention_counts'], 'seconds': seconds})
            report['available_tools'] = sorted(available)
    if len({c['case'] for c in report['checks']}) != len(report['checks']):
        raise AssertionError('Audit case names must be unique')
    report['passed'] = sum(c['passed'] for c in report['checks'])
    report['total'] = len(report['checks'])
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = asyncio.run(audit())
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')
    print(json.dumps({'passed': result['passed'], 'total': result['total'],
                      'failed': [c['case'] for c in result['checks'] if not c['passed']]}))
    return 0 if result['passed'] == result['total'] else 1


if __name__ == '__main__':
    raise SystemExit(main())

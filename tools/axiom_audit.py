"""Rerun the recorded Lean axiom checks and compare them with their committed output.

Each ``formal/AxiomCheck*.lean`` prints ``#print axioms`` for the declarations a paper or
proof map cites; ``AxiomCheck*.expected`` is its recorded output, which formalpedia quotes as
``axiom_audits``.  Without this runner nothing re-derives most of those artifacts, so a proof
change could leave a committed answer describing an older proof.

    python tools/axiom_audit.py --check          # static: artifacts answer their checks
    python tools/axiom_audit.py --run            # Lean: rerun every check and compare
    python tools/axiom_audit.py --run --write    # Lean: record the fresh output

``--run`` needs the pinned toolchain and a built ``formal/`` graph (``python tools/lab.py
build``).  Nonstandard axioms fail the run as well as differences.
"""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
import difflib
import json
from pathlib import Path
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))

from formalpedia_core import audits as fp_audits, workspace as fp_workspace  # noqa: E402


def _lake() -> str | None:
    from lab_environment import executable
    return executable('lake', fp_workspace.ROOT)


def run_check(check: Path, lake: str, timeout: float) -> tuple[Path, int, str]:
    from lab_environment import environment
    proc = subprocess.run([lake, 'env', 'lean', check.name], cwd=check.parent,
                          capture_output=True, text=True, encoding='utf-8', timeout=timeout,
                          env=environment(fp_workspace.ROOT))
    return check, proc.returncode, proc.stdout + proc.stderr


def _normalise(text: str) -> str:
    return '\n'.join(line.rstrip() for line in text.strip().splitlines()) + '\n'


def rerun(checks: list[Path], *, write: bool, workers: int, timeout: float) -> list[dict]:
    lake = _lake()
    if lake is None:
        raise SystemExit('lake not found: install the toolchain pinned in formal/lean-toolchain')
    problems = []
    with ThreadPoolExecutor(max_workers=workers) as pool:
        for check, code, output in pool.map(lambda c: run_check(c, lake, timeout), checks):
            rel = check.relative_to(fp_workspace.ROOT).as_posix()
            expected = check.with_suffix('.expected')
            fresh = _normalise(output)
            if code != 0:
                problems.append({'kind': 'lean_failed', 'check': rel, 'exit_code': code,
                                 'output_head': fresh[:2000]})
                continue
            for row in fp_audits.parse_expected(fresh):
                if not row['standard']:
                    problems.append({'kind': 'nonstandard_axioms', 'check': rel, 'name': row['name'],
                                     'axioms': row['axioms']})
            recorded = _normalise(expected.read_text(encoding='utf-8')) if expected.is_file() else None
            if write:
                expected.write_text(fresh, encoding='utf-8')
            elif recorded != fresh:
                diff = ''.join(difflib.unified_diff(
                    (recorded or '').splitlines(keepends=True), fresh.splitlines(keepends=True),
                    fromfile=f'{rel} (recorded)', tofile=f'{rel} (fresh)', n=1))
                if recorded is None and rel in fp_audits.KNOWN_MISSING_EXPECTED:
                    continue  # the ratchet in formalpedia_core.audits; still reported by --check
                problems.append({'kind': 'missing_expected' if recorded is None else 'stale_expected',
                                 'check': rel, 'diff_head': diff[:4000]})
    return problems


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split('\n\n')[0])
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument('--check', action='store_true', help='static consistency, no Lean')
    mode.add_argument('--run', action='store_true', help='rerun every check with Lean')
    ap.add_argument('--write', action='store_true', help='with --run: record fresh output')
    ap.add_argument('--only', nargs='*', help='check file names, e.g. AxiomCheckPaperC.lean')
    ap.add_argument('--workers', type=int, default=2)
    ap.add_argument('--timeout', type=float, default=1800)
    args = ap.parse_args(argv)
    if args.workers < 1 or args.timeout <= 0:
        ap.error('--workers and --timeout must be positive')
    if args.write and not args.run:
        ap.error('--write requires --run')
    if args.check:
        problems = [p for p in fp_audits.scan()['problems'] if not p.get('known')]
    else:
        checks = fp_audits.checks()
        if args.only is not None:
            unknown = set(args.only) - {c.name for c in checks}
            if unknown or not args.only:
                ap.error('--only requires existing check names: ' + ', '.join(sorted(unknown)))
            checks = [c for c in checks if c.name in set(args.only)]
        problems = rerun(checks, write=args.write, workers=args.workers, timeout=args.timeout)
    print(json.dumps({'problems': problems, 'count': len(problems)}, indent=2, ensure_ascii=False))
    return 1 if problems else 0


if __name__ == '__main__':
    raise SystemExit(main())

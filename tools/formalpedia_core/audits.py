"""Recorded Lean axiom audits: what each ``AxiomCheck*.expected`` artifact says.

The artifacts are the output of ``lake env lean AxiomCheckX.lean`` from ``formal/``, committed
beside the file that produced them.  They are the only per-declaration kernel evidence that
exists without a local Lean build, so discovery reports them next to the source view.  A
recorded artifact is evidence about the commit that recorded it: reading it here does not
rerun Lean, and :func:`problems` only checks that each artifact still matches the questions
its check file asks.  ``tools/axiom_audit.py --run`` regenerates and compares them with Lean.
"""
from __future__ import annotations

import re
from pathlib import Path
from typing import Any

from . import workspace as _fp_workspace


STANDARD = ('propext', 'Classical.choice', 'Quot.sound')

"""Mathlib's three foundational axioms; anything else in a list is reported, not judged."""


KNOWN_MISSING_EXPECTED = frozenset({'formal/AxiomCheckJugglerCollatzPaper.lean'})

"""Checks recorded without output when the audit gate was introduced (24 September 2026).

A ratchet: the set may only shrink.  Record the check's output with
``python tools/axiom_audit.py --run --write --only <file>`` rather than adding a name here.
"""


PRINT = re.compile(r'^[ \t]*#print[ \t]+axioms[ \t]+(?P<name>\S+)', re.MULTILINE)

RESULT = re.compile(
    r"^'(?P<name>[^\n]+?)' (?:depends on axioms: \[(?P<axioms>[^\]]*)\]"
    r"|(?P<none>does not depend on any axioms))",
    re.MULTILINE)

"""One ``#print axioms`` answer.  Lists wrap across lines, and a name may end in a prime:
``'foo'' depends`` is the name ``foo'``, which the lazy name group reaches by extending past
the first quote that is not followed by `` depends``."""


def checks(formal: Path | None = None) -> list[Path]:
    formal = formal or _fp_workspace.FORMAL
    return sorted(formal.glob('AxiomCheck*.lean'))


def parse_expected(text: str) -> list[dict[str, Any]]:
    rows = []
    for match in RESULT.finditer(text):
        axioms = [] if match['none'] else [a.strip() for a in match['axioms'].split(',') if a.strip()]
        rows.append({'name': match['name'], 'axioms': axioms,
                     'standard': set(axioms) <= set(STANDARD)})
    return rows


def _asked(printed: str, answered: str) -> bool:
    """A check file may print a name relative to an ``open`` namespace; Lean answers in full."""
    printed = printed.removeprefix('_root_.')
    return answered == printed or answered.endswith('.' + printed)


def scan(root: Path | None = None) -> dict[str, Any]:
    """Every recorded answer, keyed by the full name Lean reported, plus artifact problems."""
    root = root or _fp_workspace.ROOT
    formal = root / 'formal'
    by_name: dict[str, list[dict[str, Any]]] = {}
    artifacts, problems = [], []
    for check in checks(formal):
        expected = check.with_suffix('.expected')
        asked = [m['name'] for m in PRINT.finditer(check.read_text(encoding='utf-8'))]
        rel_check = check.relative_to(root).as_posix()
        if not expected.is_file():
            problems.append({'kind': 'missing_expected', 'check': rel_check, 'asked': len(asked),
                             'known': rel_check in KNOWN_MISSING_EXPECTED,
                             'detail': 'no recorded output; run the check and commit its .expected'})
            artifacts.append({'check': rel_check, 'expected': None, 'asked': len(asked), 'answered': 0})
            continue
        rel_expected = expected.relative_to(root).as_posix()
        answered = parse_expected(expected.read_text(encoding='utf-8'))
        artifacts.append({'check': rel_check, 'expected': rel_expected,
                          'asked': len(asked), 'answered': len(answered)})
        if len(asked) != len(answered) or not all(map(_asked, asked, [r['name'] for r in answered])):
            first = next((i for i, (a, r) in enumerate(zip(asked, answered)) if not _asked(a, r['name'])),
                         min(len(asked), len(answered)))
            problems.append({'kind': 'stale_expected', 'check': rel_check, 'expected': rel_expected,
                             'asked': len(asked), 'answered': len(answered), 'first_difference': first,
                             'detail': 'the recorded output does not answer the questions the check asks'})
        for row in answered:
            if not row['standard']:
                problems.append({'kind': 'nonstandard_axioms', 'expected': rel_expected,
                                 'name': row['name'],
                                 'axioms': [a for a in row['axioms'] if a not in STANDARD]})
            by_name.setdefault(row['name'], []).append(
                {'expected': rel_expected, 'axioms': row['axioms'], 'standard': row['standard']})
    return {'by_name': by_name, 'artifacts': artifacts, 'problems': problems,
            'limitations': ('Recorded Lean output read from committed artifacts; not rerun here. '
                            'A stale_expected problem means the artifact no longer matches its '
                            'check file. Freshness against the current proofs needs '
                            'python tools/axiom_audit.py --run with a Lean toolchain.')}


def unresolved(audits: dict[str, Any], index: dict[str, Any]) -> list[dict[str, Any]]:
    """Recorded names that no source declaration carries: renamed, removed, or generated."""
    known = {d['qualified_name'] for d in index['declarations'] if d.get('qualified_name')}
    return [{'kind': 'unresolved_name', 'name': name, 'expected': rows[0]['expected'],
             'detail': 'not a source declaration: renamed, deleted, generated or external'}
            for name, rows in sorted(audits['by_name'].items()) if name not in known]

"""Section 11 constants of the OEOEE production recompute from T1--T5."""

from __future__ import annotations

from fractions import Fraction as F
from math import pi, sqrt
from pathlib import Path

from research.juggler_sequence.oeoee_audit import (
    CLASS_FALSIFIED,
    DATA_DIR,
    NOTE,
    PRINTED,
    all_checks,
    assembly,
    bookkeeping,
    half_a_prefactor,
    half_b_leading,
    half_b_log_coeff,
    summary,
    t3_prefactor,
)


HEADINGS = (
    "## Problem",
    "## Exact statement",
    "## Current literature",
    "## Branch budget",
    "## Balanced-ternary formulation",
    "## Why BT may be relevant",
    "## Candidate operations / invariants",
    "## Experiments",
    "## Conjectures",
    "## Counterexamples",
    "## Formalization",
    "## Results",
    "## Open questions",
    "## Decision",
    "## Publication assessment",
)


LAMBDA3_ROW = "Half A pairing Lambda3 0.89 m'^{14/9}"
LAMBDA3_HONEST_ROW = (
    "Half A pairing Lambda3 honest (2/3)m'^{17/9} + (8/9)m'^{14/9}"
)


def test_every_section_11_constant_recomputes_except_the_known_failure() -> None:
    """One printed constant is false on data; everything else recomputes.

    The Lambda_3 pairing bound 0.89 m'^{14/9} omits the V Delta / 2 term of
    (T5) and is exceeded on J_2^sm at m'=80 and m'=200.  It is pinned by name
    rather than tolerated, so any *other* constant that stops recomputing
    still fails this test.
    """

    checks = all_checks()
    assert checks
    bad = [(c["name"], c["printed"], c["computed"]) for c in checks if not c["ok"]]
    assert [name for name, _p, _c in bad] == [LAMBDA3_ROW], bad


def test_t3_is_four_over_sqrt_pi() -> None:
    row = t3_prefactor()
    assert 4 / sqrt(pi) <= PRINTED["t3_prefactor"]
    assert row["ok"]


def test_half_b_leading_is_exactly_64_over_9() -> None:
    assert 4 * F(8, 3) * F(2, 3) == F(64, 9)
    assert half_b_leading()["ok"]


def test_half_b_log_is_64_over_3_pi() -> None:
    assert abs(64 / (3 * pi) - PRINTED["half_b_log"]) < 1e-3
    assert half_b_log_coeff()["ok"]


def test_half_a_prefactor_from_t3() -> None:
    derived = (4 / 3) * 2.26 * sqrt(8 / 3) * 2
    assert abs(derived - PRINTED["half_a_prefactor"]) < 0.02
    assert half_a_prefactor()["ok"]


def test_assembly_has_room() -> None:
    assert 8 * 8.9 + 4 * 6.3 <= 100
    assert assembly()["ok"]


def test_bookkeeping_is_one_twenty_seventh() -> None:
    assert F(1, 3) * F(1, 3) - F(2, 9) * F(1, 3) == F(1, 27)
    assert bookkeeping()["ok"]


def test_summary_reports_the_one_false_constant() -> None:
    """Was test_summary_is_clean, and asserted CLASS_CONSISTENT.

    It passed because the three Half A pairing rows compared each printed
    constant to itself with ok=True hardcoded.  With those rows evaluated on
    data the section is falsified by exactly one of them.
    """

    result = summary()
    assert result["classification"]["name"] == CLASS_FALSIFIED
    assert result["classification"]["failures"] == 1
    assert result["classification"]["failing_names"] == [LAMBDA3_ROW]
    assert result["classification"]["total_checks"] >= 20
    assert not result["classification"]["all_printed_constants_recompute"]
    # The replacement the docstring names was prose until 14 September 2026:
    # only the false printed constant was evaluated.  total_checks is a floor,
    # not a pin, so this row is named here -- deleting it must break something.
    honest = [r for r in _rows(result) if r["name"] == LAMBDA3_HONEST_ROW]
    assert len(honest) == 1, [r["name"] for r in _rows(result)]
    assert honest[0]["ok"], honest[0]
    assert result["classification"]["power_saving"] == "P^{-1/8}"


def _rows(result):
    """Every check row in the summary, wherever it is nested."""
    def walk(o):
        if isinstance(o, dict):
            if "name" in o and "ok" in o:
                yield o
            for v in o.values():
                yield from walk(v)
        elif isinstance(o, list):
            for v in o:
                yield from walk(v)
    return list(walk(result))


def test_note_and_dossier_exist() -> None:
    assert NOTE.is_file()
    root = Path(__file__).resolve().parents[3]
    dossier = (root / "docs" / "problems" / "juggler_oeoee_production.md").read_text(
        encoding="utf-8"
    )
    for heading in HEADINGS:
        assert heading in dossier
    ledger = root / "docs" / "theory" / "oeoee_audit_ledger.md"
    assert ledger.is_file()
    text = ledger.read_text(encoding="utf-8")
    assert "2.26" in text and "0.4801" in text and "P^{-1/8}" in text


def test_stored_summary_matches_a_fresh_run() -> None:
    stored = DATA_DIR / "summary.json"
    if not stored.is_file():
        return
    import json

    data = json.loads(stored.read_text(encoding="utf-8"))
    fresh = summary()["classification"]
    assert data["classification"]["failures"] == fresh["failures"]
    assert data["classification"]["failing_names"] == fresh["failing_names"]
    assert data["classification"]["name"] == fresh["name"]

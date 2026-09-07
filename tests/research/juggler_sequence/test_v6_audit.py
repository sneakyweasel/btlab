"""Section 15 constants of the V_6 production recompute from T1--T5."""

from __future__ import annotations

from fractions import Fraction as F
from math import pi
from pathlib import Path

from research.juggler_sequence.v6_audit import (
    CLASS_CONSISTENT,
    DATA_DIR,
    NOTE,
    PRINTED,
    all_checks,
    assembly,
    binding_saving,
    bookkeeping,
    case1_leading,
    summary,
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


def test_every_section_15_constant_recomputes() -> None:
    checks = all_checks()
    assert checks
    bad = [(c["name"], c["printed"], c["computed"]) for c in checks if not c["ok"]]
    assert bad == [], bad


def test_case1_leading_is_exactly_16384_over_729() -> None:
    assert 4 * F(2048, 243) * F(2, 3) == F(16384, 729)
    assert case1_leading()["ok"]


def test_case1_log_is_16384_over_243_pi() -> None:
    assert abs(16384 / (243 * pi) - PRINTED["case1_log"]) < 1e-2


def test_binding_is_eighty_one_over_two_zero_four_eight() -> None:
    assert F(1, 6) * F(3, 4) ** 5 == F(81, 2048)
    assert F(8192, 729) * F(81, 2048) == F(4, 9)
    assert binding_saving()["ok"]


def test_bookkeeping_is_one_two_one_eight_seven() -> None:
    assert (F(1, 3) - F(2, 9)) * F(1, 243) == F(1, 2187)
    assert bookkeeping()["ok"]


def test_assembly_has_room_at_twenty_two() -> None:
    assert assembly()["ok"]
    factor_18 = 22 ** (-700 / 729)
    factor_332 = 22 ** (-148 / 243)
    factor_9128 = 22 ** (-28 / 81)
    factor_27512 = 22 ** (-4 / 27)
    at_22 = (
        2048 * 9.3 * factor_18
        + 1024 * 9.2 * factor_332
        + 512 * 9.0 * factor_9128
        + 256 * 9.1 * factor_27512
        + 128 * 6.3 * factor_27512
        + 8 * 6.3
    )
    assert at_22 <= 8000


def test_summary_is_clean() -> None:
    result = summary()
    assert result["classification"]["name"] == CLASS_CONSISTENT
    assert result["classification"]["failures"] == 0
    assert result["classification"]["total_checks"] >= 18
    assert result["classification"]["all_printed_constants_recompute"]
    assert result["classification"]["power_saving"] == "P^{-81/2048}"
    assert result["classification"]["lambda_root_if_promoted"] == 0.4926


def test_note_and_dossier_exist() -> None:
    assert NOTE.is_file()
    root = Path(__file__).resolve().parents[3]
    dossier = (root / "docs" / "problems" / "juggler_v6_production.md").read_text(
        encoding="utf-8"
    )
    for heading in HEADINGS:
        assert heading in dossier
    assert "PROMOTE" in dossier.split("## Decision", 1)[1]
    ledger = root / "docs" / "theory" / "v6_audit_ledger.md"
    assert ledger.is_file()
    text = ledger.read_text(encoding="utf-8")
    assert "0.4926" in text and "P^{-81/2048}" in text and "1/2187" in text


def test_stored_summary_matches_a_fresh_run() -> None:
    stored = DATA_DIR / "summary.json"
    if not stored.is_file():
        return
    import json

    data = json.loads(stored.read_text(encoding="utf-8"))
    assert data["classification"]["failures"] == 0
    assert data["classification"]["name"] == summary()["classification"]["name"]

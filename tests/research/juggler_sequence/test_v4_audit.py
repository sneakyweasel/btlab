"""Section 13 constants of the V_4 production recompute from T1--T5."""

from __future__ import annotations

from fractions import Fraction as F
from math import pi
from pathlib import Path

from research.juggler_sequence.v4_audit import (
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


def test_every_section_13_constant_recomputes() -> None:
    checks = all_checks()
    assert checks
    bad = [(c["name"], c["printed"], c["computed"]) for c in checks if not c["ok"]]
    assert bad == [], bad


def test_case1_leading_is_exactly_1024_over_81() -> None:
    assert 4 * F(128, 27) * F(2, 3) == F(1024, 81)
    assert case1_leading()["ok"]


def test_case1_log_is_1024_over_27_pi() -> None:
    assert abs(1024 / (27 * pi) - PRINTED["case1_log"]) < 1e-2


def test_binding_is_nine_over_one_twenty_eight() -> None:
    assert F(1, 6) * F(3, 4) ** 3 == F(9, 128)
    assert F(512, 81) * F(9, 128) == F(4, 9)
    assert binding_saving()["ok"]


def test_bookkeeping_is_one_two_forty_three() -> None:
    assert (F(1, 3) - F(2, 9)) * F(1, 27) == F(1, 243)
    assert bookkeeping()["ok"]


def test_assembly_has_room_at_sixteen() -> None:
    assert assembly()["ok"]
    factor_18 = 16 ** (-28 / 81)
    factor_332 = 16 ** (-4 / 27)
    at_16 = 128 * 9.0 * factor_18 + 64 * 9.1 * factor_332 + 32 * 6.3 * factor_332 + 8 * 6.3
    assert at_16 <= 1600


def test_summary_is_clean() -> None:
    result = summary()
    assert result["classification"]["name"] == CLASS_CONSISTENT
    assert result["classification"]["failures"] == 0
    assert result["classification"]["total_checks"] >= 18
    assert result["classification"]["all_printed_constants_recompute"]
    assert result["classification"]["power_saving"] == "P^{-9/128}"
    assert result["classification"]["lambda_root_if_promoted"] == 0.4916


def test_note_and_dossier_exist() -> None:
    assert NOTE.is_file()
    root = Path(__file__).resolve().parents[3]
    dossier = (root / "docs" / "problems" / "juggler_v4_production.md").read_text(
        encoding="utf-8"
    )
    for heading in HEADINGS:
        assert heading in dossier
    assert "PROMOTE" in dossier.split("## Decision", 1)[1]
    ledger = root / "docs" / "theory" / "v4_audit_ledger.md"
    assert ledger.is_file()
    text = ledger.read_text(encoding="utf-8")
    assert "0.4916" in text and "P^{-9/128}" in text and "1/243" in text


def test_stored_summary_matches_a_fresh_run() -> None:
    stored = DATA_DIR / "summary.json"
    if not stored.is_file():
        return
    import json

    data = json.loads(stored.read_text(encoding="utf-8"))
    assert data["classification"]["failures"] == 0
    assert data["classification"]["name"] == summary()["classification"]["name"]

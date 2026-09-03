"""Printed leftovers of Paper B Theorem 5.3 against OOOEE / OOEOE fibers."""

from __future__ import annotations

from fractions import Fraction
from pathlib import Path

from research.juggler_sequence.kernel_localize import (
    CELL_MIN,
    LEMMA39,
    PASSENGER,
    SAVING,
    T_MIN,
    Y_ASSESSED,
    Y_FIBER,
    Y_TRIPLE,
    effective_measure_leftover,
    evaluate_at,
    exceeds_target,
    summary,
    target_exponent,
    v_retune_assessed,
)

DOSSIER = Path(__file__).resolve().parents[3] / "docs" / "problems" / "juggler_kernel_localize.md"
SUMMARY = (
    Path(__file__).resolve().parents[3]
    / "data"
    / "research"
    / "juggler"
    / "kernel_localize"
    / "summary.json"
)


def test_oooee_fiber_is_shorter_than_ooeee_and_below_triple() -> None:
    assert Y_FIBER == Fraction(5, 32)
    assert Y_ASSESSED == Fraction(23, 32)
    assert Y_FIBER < Y_TRIPLE < Y_ASSESSED
    assert Y_FIBER < CELL_MIN
    assert Y_FIBER < T_MIN


def test_fiber_target_is_eleven_over_ninety_six() -> None:
    assert target_exponent(Y_FIBER) == Fraction(11, 96)
    assert target_exponent(Y_ASSESSED) == Fraction(65, 96)


def test_lemma39_is_the_whole_interval_at_both_lengths() -> None:
    assert effective_measure_leftover(Y_FIBER) == Y_FIBER
    assert effective_measure_leftover(Y_ASSESSED) == Y_ASSESSED
    assert exceeds_target(Y_FIBER, Y_FIBER)
    assert exceeds_target(Y_ASSESSED, Y_ASSESSED)
    assert exceeds_target(LEMMA39, Y_ASSESSED)
    assert exceeds_target(PASSENGER, Y_FIBER)
    assert not exceeds_target(PASSENGER, Y_ASSESSED)


def test_v_retune_constraints_conflict() -> None:
    row = v_retune_assessed()
    assert row["constraints_compatible"] is False
    assert row["gap_exponent"] == "7/16"  # 21/48 reduced
    assert row["y_needed_for_printed_omega"] == "31/32"


def test_evaluate_flags_both_intervals() -> None:
    fiber = evaluate_at(Y_FIBER, "fiber")
    assessed = evaluate_at(Y_ASSESSED, "assessed")
    assert fiber["falsifier_fires"] is True
    assert assessed["falsifier_fires"] is True
    lemma39_fiber = next(r for r in fiber["leftovers"] if r["id"] == "lemma39_trivial")
    lemma39_assessed = next(r for r in assessed["leftovers"] if r["id"] == "lemma39_trivial")
    assert lemma39_fiber["exceeds_target"] is True
    assert lemma39_assessed["exceeds_target"] is True


def test_summary_closes() -> None:
    data = summary()
    assert data["classification"]["decision"] == "CLOSE"
    assert data["classification"]["true_fiber_is_p_5_32"] is True
    assert data["classification"]["section_7_4_used_wrong_y"] is True
    assert data["classification"]["v_retune_impossible_at_assessed_y"] is True
    assert data["anti"]["kernel_retagged"] is False
    assert data["anti"]["forty_estimates_rederived"] is False


def test_dossier_headings_and_close() -> None:
    dossier = DOSSIER.read_text(encoding="utf-8")
    for heading in (
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
    ):
        assert heading in dossier
    decision = dossier.split("## Decision", 1)[1].split("## ", 1)[0]
    assert "CLOSE" in decision


def test_summary_artifact_exists() -> None:
    assert SUMMARY.is_file()
    import json

    data = json.loads(SUMMARY.read_text(encoding="utf-8"))
    assert data["classification"]["decision"] == "CLOSE"
    assert data["classification"]["lemma39_exceeds_fiber_target"] is True

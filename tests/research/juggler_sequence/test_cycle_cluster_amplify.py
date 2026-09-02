"""Cheap-cluster Amplify versus surplus. Not a halt test."""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path

from research.conjectures import get_conjecture
from research.juggler_sequence.cycle_cluster_amplify import (
    K_MAX,
    exact_k1_row,
    exact_linear_exponent,
    exponent_row,
    gap_invariant_holds,
    inductive_step_adds_eight_ninths,
    last_cubic_over_linear_exponent,
    ooe_cluster,
    surplus_exponent,
)
from research.juggler_sequence.defect_lower_bound import amplify_from_first, formal_surplus
from research.juggler_sequence.global_defect import follows_itinerary

REPO = Path(__file__).resolve().parents[3]
SUMMARY = (
    REPO
    / "data"
    / "research"
    / "juggler"
    / "cycle_finance"
    / "cluster_amplify"
    / "summary.json"
)


def test_n3_gap_is_invariant_through_k25():
    assert gap_invariant_holds(K_MAX)
    for k in range(K_MAX):
        assert inductive_step_adds_eight_ninths(k)
    row = exponent_row(25)
    assert row["gap_rho1_is_three"]
    assert row["gap_rhomax_is_three_halves"]
    assert surplus_exponent(25) - 3 == 717897987691852588770246


def test_closed_form_matches_exact_walk():
    for k in (1, 2, 7, 25):
        word = ooe_cluster(k)
        top = surplus_exponent(k)
        assert exact_linear_exponent(word, 0, Fraction(0)) == top - 3
        assert exact_linear_exponent(word, 0, Fraction(3, 2)) == top - Fraction(3, 2)


def test_cubics_stay_behind_the_linear_term():
    assert last_cubic_over_linear_exponent(1) == -3
    assert last_cubic_over_linear_exponent(25) == -3
    assert last_cubic_over_linear_exponent(25, Fraction(3, 2)) == Fraction(-3, 2)


def test_realized_ooe_amplify_loses_to_surplus():
    for seed in (365, 1517, 1000057):
        assert follows_itinerary(seed, "OOE")
        assert amplify_from_first(seed, "OOE") < formal_surplus(seed, "OOE")
        row = exact_k1_row(seed)
        assert row["amplify_lt_surplus"]
        assert row["amplify_le_delta"]


def test_artifact_records_the_refutation():
    payload = json.loads(SUMMARY.read_text(encoding="utf-8"))
    assert payload["gap_invariant"] is True
    assert payload["rhomax_gap_invariant"] is True
    assert payload["inductive_steps"] is True
    assert payload["cubic_behind_by_three"] is True
    assert payload["any_linear_beats"] is False
    assert payload["exact_k1_all_lose"] is True
    assert payload["slogan_false"] is True
    assert payload["exponents"][0]["gap_rho1"] == "3"
    assert payload["exponents"][-1]["k"] == 25
    assert payload["exponents"][-1]["gap_rho1"] == "3"


def test_dossier_and_conjecture_record_close():
    dossier = (
        REPO / "docs" / "problems" / "juggler_cycle_cluster_amplify.md"
    ).read_text(encoding="utf-8")
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "## Publication assessment" in dossier
    decision = dossier.split("## Decision", 1)[1].split("## ", 1)[0]
    assert "CLOSE" in decision
    rec = get_conjecture("juggler_cycle_cluster_amplify")
    assert rec["status"] == "REFUTED"
    assert rec["counterexamples"]

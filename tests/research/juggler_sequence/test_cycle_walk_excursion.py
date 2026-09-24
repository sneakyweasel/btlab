"""Walk-excursion Phase 0. Not a halt test and not a floor raise."""

from __future__ import annotations

import json
import math
from pathlib import Path

from research.juggler_sequence.cycle_christoffel import christoffel_word
from research.juggler_sequence.cycle_walk_charge import (
    brute_force_budget,
    walk_budget,
)
from research.juggler_sequence.cycle_walk_excursion import (
    LATTICE_GENERATORS,
    NAMED_TYPES,
    SURVEY_PATH,
    analyze_word,
    reconstruct_maximizer,
    replay_charge,
    semi_convergents_alpha,
    survey_charge_density,
)

DOSSIER = Path("docs/problems/juggler_cycle_walk_excursion.md")
CONJECTURE = Path("conjectures/active/juggler_walk_excursion_optimum.json")
ARTIFACT = Path("data/research/juggler/cycle_walk_excursion/summary.json")


def test_semi_convergents_are_certified_past_the_float_horizon():
    # A float expansion of MU goes wrong near denominator 5e7: up to 1e9 it produced
    # 290141713 in place of the convergent denominator 397573379 of log2(3).
    types = set(semi_convergents_alpha(10**9))
    assert (397573379, 232565518) in types
    assert (290141713, 169722022) not in types


def test_named_pairs_are_semi_convergents_of_alpha():
    types = set(semi_convergents_alpha())
    for pair in NAMED_TYPES:
        assert pair in types
    for pair in LATTICE_GENERATORS:
        assert pair in types
    assert (12, 7) in types
    assert (29, 17) in types
    assert (41, 24) in types
    assert (53, 31) in types


def test_traceback_matches_brute_force_and_walk_budget():
    for length, odd_count in [(5, 4), (8, 6), (11, 7), (12, 8)]:
        rec = reconstruct_maximizer(length, odd_count, 1000)
        assert rec["feasible"] is True
        dp = walk_budget(length, odd_count, 1000)["walk_sum"]
        bf = brute_force_budget(length, odd_count, 1000)
        replayed = replay_charge(rec["word"], 1000)
        assert math.isclose(rec["walk_sum"], dp, rel_tol=1e-12)
        assert math.isclose(rec["walk_sum"], bf, rel_tol=1e-12)
        assert math.isclose(replayed, dp, rel_tol=1e-12)
        assert rec["word"].count("O") == odd_count
        assert len(rec["word"]) == length


def test_ooe_is_the_first_closed_near_return():
    analysis = analyze_word("OOE")
    assert analysis["n_closed"] == 1
    assert analysis["blocks"][0]["type"] == (2, 1)
    assert analysis["all_closed_cf"] is True


def test_leftover_maximizer_is_the_christoffel_word():
    for length, odd_count in [(19, 12), (84, 53)]:
        rec = reconstruct_maximizer(length, odd_count, 1000)
        assert rec["word"] == christoffel_word(length, odd_count)


def test_survey_charge_per_letter_is_constant():
    assert SURVEY_PATH.is_file()
    density = survey_charge_density()
    assert density["n_rows"] == 19
    assert density["relative_spread"] < 1e-2
    assert density["uniform_ratio_false"] is True
    assert 0.04 < density["C_median"] < 0.06


def test_anti_overclaim_and_dossier_headings():
    dossier = DOSSIER.read_text(encoding="utf-8")
    for heading in (
        "## Problem",
        "## Exact statement",
        "## Current literature",
        "## Branch budget",
        "## Decision",
        "## Publication assessment",
    ):
        assert heading in dossier
    assert "not claimed" in dossier
    assert "PROMOTE" in dossier or "PARK" in dossier or "CLOSE" in dossier
    record = json.loads(CONJECTURE.read_text(encoding="utf-8"))
    assert record["id"] == "juggler_walk_excursion_optimum"
    assert record["status"] == "ACTIVE"
    payload = json.loads(ARTIFACT.read_text(encoding="utf-8"))
    assert payload["not_a_halt_theorem"] is True
    assert payload["no_cycle_all_lengths"] is False
    assert payload["not_a_uniform_ratio_theorem"] is True
    assert payload["classification"]["label"] == "WALK_EXCURSION_GREEN"
    assert all(row["equals_christoffel"] for row in payload["cf_lengths"])

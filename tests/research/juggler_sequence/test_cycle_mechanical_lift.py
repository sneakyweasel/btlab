"""Mechanical-lift Phase 0. Not a halt test and not a floor raise."""

from __future__ import annotations

import json
from pathlib import Path

from research.juggler_sequence.cycle_finance import o_min_and_theta
from research.juggler_sequence.cycle_mechanical_lift import (
    iet_hug_prefix,
    xi_exact,
)
from research.juggler_sequence.cycle_remainder_finance import cell_record
from research.juggler_sequence.cycle_walk_greedy import hug_word
from research.juggler_sequence.power_itineraries import floor_power

DOSSIER = Path("docs/problems/juggler_cycle_mechanical_lift.md")
CONJECTURE = Path("conjectures/refuted/juggler_mechanical_lift_obstruction.json")
ARTIFACT = Path("data/research/juggler/cycle_mechanical_lift/summary.json")


def test_xi_matches_cell_record_and_stays_in_unit_interval():
    for n in (13, 15, 365, 1000057, 1016445):
        rec = xi_exact(n)
        cell = cell_record(n)
        assert rec["rho"] == cell["rho"]
        assert rec["width"] == cell["width"]
        assert rec["xi"] == cell["pos"]
        assert 0.0 <= rec["xi"] < 1.0
        image = floor_power(n)
        power = n * n * n if n % 2 else n
        assert rec["rho"] == power - image * image
        assert rec["width"] == 2 * image + 1


def test_hug_equals_iet_on_leftover_nineteen():
    odd_count, _ = o_min_and_theta(19)
    assert odd_count == 12
    word = hug_word(19, 12)
    assert word == iet_hug_prefix(19)
    assert word == "OOEOOEOOEOEOOEOOEOE"
    assert "OOEOE" in word


def test_oe_collision_is_not_a_function_of_xi():
    left = xi_exact(1_000_001)
    right = xi_exact(1_000_003)
    assert left["xi"] != right["xi"]
    mid_left = floor_power(1_000_001)
    mid_right = floor_power(1_000_003)
    assert mid_left % 2 == 0 and mid_right % 2 == 0
    landing_left = floor_power(mid_left)
    landing_right = floor_power(mid_right)
    assert landing_left == landing_right == 31_622
    landing = xi_exact(31_622)
    assert 0.0 <= landing["xi"] < 1.0


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
    decision = dossier.split("## Decision", 1)[1].split("## ", 1)[0]
    assert "CLOSE" in decision
    assert "PROMOTE" not in decision
    assert "not claimed" in dossier
    record = json.loads(CONJECTURE.read_text(encoding="utf-8"))
    assert record["id"] == "juggler_mechanical_lift_obstruction"
    assert record["status"] == "REFUTED"
    assert record["not_a_halt_theorem"] is True
    assert record["counterexamples"]
    payload = json.loads(ARTIFACT.read_text(encoding="utf-8"))
    assert payload["not_a_halt_theorem"] is True
    assert payload["no_cycle_all_lengths"] is False
    assert payload["no_new_period_bound"] is True
    assert payload["no_floor_raise"] is True
    assert payload["no_paper_a_edit"] is True
    assert payload["iet_identity"]["all_match"] is True
    assert payload["distinction"]["relaxed_mechanical_feasibility"] is True
    assert payload["distinction"]["exact_integer_liftability"] is False
    cls = payload["classification"]
    assert cls["label"] == "MECHANICAL_LIFT_CLOSED"
    assert cls["decision"] == "CLOSE"
    assert cls["transport_new"] is False
    assert cls["scale_stable_phi"] is False
    assert cls["uncorrelated"] is True
    assert cls["composition_skipped"] is True
    assert cls["n_complete_integer_lifts"] == 0
    for tag in (
        "INERT_EVEN",
        "UNIQUE_ODD",
        "UNCORRELATED",
        "SCALE_HUG",
        "LOCAL_CELL",
    ):
        assert tag in cls["tags"]
    assert "TRANSPORT_NEW" not in cls["tags"]
    assert payload["cocycle"]["OOE"]["uncorrelated"] is True
    assert payload["cocycle"]["OE"]["uncorrelated"] is True
    assert payload["inert_even"]["inert"] is True
    assert payload["unique_odd"]["unique"] is True
    assert payload["scale_hug"]["fires"] is True
    assert payload["scale_hug"]["landings"]
    assert all(row["below_oe_start"] for row in payload["scale_hug"]["landings"])
    assert payload["three_classes"]["cell_feasible"]["local_cell"] is True
    assert payload["hypothesis3"]["better_approx_shrinks_xi_set"] is False
    fans = {row["tag"]: row for row in payload["fans"]}
    assert fans["fanA_k1"]["length"] == 478_245
    assert fans["fanB_k0"]["walk_feasible"] is True
    assert fans["fanB_k0"]["n_other"] == 0

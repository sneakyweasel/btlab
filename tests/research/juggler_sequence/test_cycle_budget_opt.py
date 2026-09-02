"""Run-type cycle-finance packing. Not a halt test."""

from __future__ import annotations

import json
from pathlib import Path

from research.juggler_sequence.cycle_budget_opt import (
    budget_excludes,
    budget_rhs,
    budget_row,
    climb_fits_tau1,
    first_odd_image,
    oe_start_min,
    run_type_counts,
)
from research.juggler_sequence.cycle_finance import (
    PUBLISHED_FLOOR,
    o_min_and_theta,
    parity_rhs,
    sha256_int_list,
)

REPO = Path(__file__).resolve().parents[3]

BUDGET_KILLS = [56347 + 1054 * k for k in range(42)]


def test_oe_start_min_is_least_odd_with_image_ge_sq():
    assert oe_start_min(12) == 29
    assert first_odd_image(29) >= 12 * 12
    assert first_odd_image(27) < 12 * 12
    assert oe_start_min(261) == 1669
    assert first_odd_image(1669) >= 261 * 261
    assert first_odd_image(1667) < 261 * 261
    start = PUBLISHED_FLOOR + 1
    assert oe_start_min(start) == 100000135
    assert first_odd_image(100000135) >= start * start
    assert first_odd_image(100000133) < start * start


def test_run_type_counts_at_25781():
    oo_count, oe_count = run_type_counts(16266, 9515)
    assert oo_count == 6751
    assert oe_count == 2764
    assert climb_fits_tau1(16266, 9515)


def test_budget_25781_strictly_below_parity_but_lives():
    odd_count, theta = o_min_and_theta(25781)
    start = PUBLISHED_FLOOR + 1
    packed = budget_rhs(start, 25781, odd_count)
    parity = parity_rhs(start, 25781, odd_count)
    assert packed < parity
    assert not budget_excludes(25781, odd_count, theta, PUBLISHED_FLOOR)
    row = budget_row(25781)
    assert row["oo_count"] == 6751
    assert row["oe_count"] == 2764
    assert row["strictly_below_parity"]
    assert not row["budget_excludes"]
    assert not row["drop_max_excludes"]
    assert row["budget_rhs_drop_max"] <= row["budget_rhs"] < row["parity_rhs"]


def test_budget_scan_shrinks_leftover_set():
    payload = json.loads(
        (
            REPO / "data" / "research" / "juggler" / "cycle_finance"
            / "budget_opt.json"
        ).read_text(encoding="utf-8")
    )
    assert payload["leftover_count"] == 141
    assert payload["killed_by_parity"] == []
    assert payload["killed_by_budget"] == BUDGET_KILLS
    assert payload["killed_count"] == 42
    assert payload["remaining_count"] == 99
    assert payload["not_strictly_below_parity"] == []
    assert payload["climb_fits_tau1_failures"] == []
    assert payload["max_unbounded_changes_extremum"] is False
    assert payload["killed_by_drop_max"] == BUDGET_KILLS
    assert payload["sha256_killed"] == sha256_int_list(BUDGET_KILLS)
    assert payload["oe_start"] == 100000135
    spot = payload["spotlight_25781"]
    assert spot["L"] == 25781
    assert not spot["budget_excludes"]
    assert 25781 not in payload["killed_by_budget"]
    assert 55293 not in payload["killed_by_budget"]
    assert 56347 in payload["killed_by_budget"]


def test_dossier_boundary():
    dossier = (
        REPO / "docs" / "problems" / "juggler_cycle_budget_opt.md"
    ).read_text(encoding="utf-8")
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "## Publication assessment" in dossier
    assert "**PROMOTE**" in dossier
    assert "theorem no_cycle_itinerary_any_length" not in dossier
    assert "budget_opt.json" in dossier

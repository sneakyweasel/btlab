"""Fast checks for the odd-inverse width calibration."""

from __future__ import annotations

import json
from pathlib import Path

from research.juggler_sequence.empty_odd_cell import odd_cell_kind
from research.juggler_sequence.odd_inverse_width import (
    CLASS_REPARAM,
    EXISTING_LEAN,
    FORBIDDEN_THEOREMS,
    JSON_PATH,
    ODD_HITS,
    lean_api_present,
    mvt_width,
    real_width,
    width_lt_one_elementary,
    width_row,
)
from research.juggler_sequence.power_words import floor_power

CONJECTURE = Path("conjectures/refuted/juggler_odd_inverse_width.json")
DOSSIER = Path("docs/problems/juggler_odd_inverse_width.md")


def test_width_at_one_already_below_one() -> None:
    width = real_width(1)
    assert 0.58 < width < 0.59
    assert width < 1.0
    assert width < mvt_width(1)
    row = width_row(1)
    assert row["kind"] == 2
    assert row["occupants"] == [1]


def test_elementary_width_lt_one() -> None:
    cert = width_lt_one_elementary()
    assert cert["discriminant"] == -32
    assert cert["always_positive"] is True
    assert all(val > 0 for val in cert["samples"])


def test_mvt_ratio_approaches_one() -> None:
    assert width_row(10**2)["ratio"] > 0.99
    assert width_row(10**6)["ratio"] > 0.999999
    assert width_row(10**12)["width"] < 1e-4
    assert width_row(10**12)["occupant_count"] <= 1


def test_odd_step_is_type2_self_preimage() -> None:
    for x in ODD_HITS:
        image = floor_power(x)
        assert odd_cell_kind(image) == 2


def test_artifact_is_reparameterization() -> None:
    summary = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert summary["classification"] == CLASS_REPARAM
    assert summary["finite_width"]["all_lt_one"] is True
    assert summary["finite_width"]["first_ge_one"] is None
    assert summary["elementary"]["always_positive"] is True
    assert summary["odd_step_type2"]["all_type2"] is True
    assert summary["odd_step_type2"]["all_self_preimage"] is True
    assert summary["ambient_types"]["type0_share"] > 0.9
    assert summary["ambient_types"]["mismatches"] == 0
    assert summary["hug_flow"]["net_oe_positive"] is True
    assert summary["hug_flow"]["net_ooe_positive"] is True
    assert summary["fan_concat"]["end_odd_19"] == 17
    assert summary["fan_concat"]["glue_19_to_19"] == 0
    assert all(row["occupant_count"] <= 1 for row in summary["power_grid"])
    assert all(row["width_lt_one"] for row in summary["power_grid"])
    anti = summary["anti_overclaim"]
    assert anti["halt_theorem"] is False
    assert anti["paper_a_modified"] is False
    assert anti["cycle_inverse_width_reopened"] is False
    assert anti["n_window_raised"] is False


def test_lean_boundaries() -> None:
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in EXISTING_LEAN:
        assert lean[name] is True, name
    for name in FORBIDDEN_THEOREMS:
        assert lean[f"has_{name}"] is False, name
    assert lean["new_lean_file"] is False


def test_conjecture_and_dossier() -> None:
    conj = json.loads(CONJECTURE.read_text(encoding="utf-8"))
    assert conj["id"] == "juggler_odd_inverse_width"
    assert conj["status"] == "REFUTED"
    dossier = DOSSIER.read_text(encoding="utf-8")
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "CLOSE" in dossier
    assert "odd_cell_unique" in dossier
    assert "Paper A" in dossier

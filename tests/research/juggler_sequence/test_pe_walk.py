"""Anchor-relative PE-block walk. Not an OE-contracts or empty-cell test."""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path

from research.juggler_sequence.cycle_itinerary import follows_itinerary, image_after
from research.juggler_sequence.pe_walk import (
    CLASS_PARK,
    EXISTING_LEAN,
    FORBIDDEN_NEW_API,
    FORBIDDEN_THEOREMS,
    JSON_PATH,
    block_multiplier,
    classify,
    lean_api_present,
    pe_blocks,
    render_markdown,
    run_probe,
    third_ooe_alpha,
    walk_row,
    write_artifacts,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM


def test_block_multipliers():
    assert block_multiplier(1, 1) == Fraction(3, 4)
    assert block_multiplier(2, 1) == Fraction(9, 8)
    assert block_multiplier(3, 1) == Fraction(27, 16)
    assert block_multiplier(0, 1) == Fraction(1, 2)


def test_365_is_four_ooe_then_oe_then_e():
    row = walk_row(365)
    assert row["words"] == ["OOE", "OOE", "OOE", "OOE", "OE", "E"]
    assert row["landings"] == [763, 1749, 4447, 12707, 1196, 34]
    assert row["ratio_monotone"] is False
    assert row["rem_monotone"] is False
    assert row["alphas"][2] == "729/512"
    assert row["final_below_anchor"] is True


def test_1517_splits_after_the_same_envelope():
    row = walk_row(1517)
    assert row["words"][:4] == ["OOE", "OOE", "OOE", "OE"]
    assert 33811 in row["landings"]
    assert 2493 in row["landings"]
    assert 2493 > 1517
    assert row["any_block_below_entrance_above_anchor"] is True
    split = third_ooe_alpha()
    assert split["365_alpha3"] == split["1517_alpha3"] == "729/512"
    assert split["365_after_three"] == "OOE"
    assert split["1517_after_three"] == "OE"
    assert split["same_alpha_different_next"] is True


def test_oe_contracts_state_but_not_the_anchor():
    assert follows_itinerary(33811, "OE")
    assert image_after(33811, "OE") == 2493
    assert 2493 < 33811
    assert 2493 > 1517
    assert pe_blocks(6187)[-1]["word"] == "OE"
    assert pe_blocks(6187)[-1]["below_anchor"] is True


def test_501_and_6187_are_pe_walks_not_lyapunov():
    row_501 = walk_row(501)
    row_6187 = walk_row(6187)
    assert row_501["ratio_monotone"] is False
    assert row_6187["ratio_monotone"] is False
    assert row_501["final_below_anchor"] is True
    assert row_6187["final_below_anchor"] is True
    assert "L" != row_501["words"][0]
    assert row_501["words"][:2] == ["OOE", "OOOE"]


def test_probe_parks_without_new_lean():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_PARK
    assert scan["summary"]["any_ratio_monotone"] is False
    assert scan["third_ooe"]["same_alpha_different_next"] is True
    assert scan["oe_contracts_33811"] is True
    assert scan["halt_theorem"] is False
    assert scan["oe_contracts_reopened"] is False
    assert scan["empty_cell_reopened"] is False
    assert scan["episode_rank_reopened"] is False


def test_lean_boundaries():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in EXISTING_LEAN:
        assert lean[name] is True, name
    for name in FORBIDDEN_NEW_API:
        assert lean[f"has_{name}"] is False, name
    for name in FORBIDDEN_THEOREMS:
        assert lean[f"has_{name}"] is False, name
    assert lean["new_lean_file"] is False
    assert lean["paper_a_has_new_api"] is False


def test_classify_render_and_artifacts():
    payload = write_artifacts()
    text = render_markdown(payload)
    assert CLASS_PARK in text
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_pe_walk"
    assert data["decision"]["classification"] == CLASS_PARK
    assert dict(ANTI_OVERCLAIM)["global_termination"] is False
    assert payload["anti_overclaim"]["envelope_predicts_next_block"] is False
    assert payload["anti_overclaim"]["oe_contracts_implies_halt"] is False


def test_dossier_boundary():
    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_pe_walk.md").read_text(
        encoding="utf-8"
    )
    note = (repo / "docs" / "theory" / "juggler_finite_dynamics_note.md").read_text(
        encoding="utf-8"
    )
    paper = (repo / "formal" / "Problems" / "JugglerPaper.lean").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "PARK" in dossier
    assert "729/512" in dossier
    assert "PEWalk" not in paper
    assert "theorem juggler_reaches_one" not in note

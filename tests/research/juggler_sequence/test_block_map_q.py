"""Maximal odd-run block map Q. Not a residue-automaton test."""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path

from research.juggler_sequence.block_map_q import (
    CLASS_PARK,
    COLLISION_INDEX,
    EXISTING_LEAN,
    FORBIDDEN_NEW_API,
    FORBIDDEN_THEOREMS,
    JSON_PATH,
    a_of,
    block_map,
    block_mu,
    classify,
    collision_state,
    first_odd_defect,
    lean_api_present,
    q_blocks,
    render_markdown,
    run_probe,
    write_artifacts,
)
from research.juggler_sequence.odd_run_itinerary import prefix_lambda
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM


def test_convention_and_leftover_orbits():
    assert a_of(365) == 2
    assert block_map(365) == 763
    assert block_mu(1) == Fraction(3, 4)
    assert block_mu(2) == Fraction(9, 8)
    starts_365 = [row["x"] for row in q_blocks(365)]
    starts_1517 = [row["x"] for row in q_blocks(1517)]
    assert starts_365 == [365, 763, 1749, 4447, 12707]
    assert starts_1517 == [1517, 3789, 10613, 33811, 2493]
    assert [row["a"] for row in q_blocks(365)] == [2, 2, 2, 2, 1]
    assert [row["a"] for row in q_blocks(1517)] == [2, 2, 2, 1, 3]
    assert q_blocks(365)[4]["Q"] == 1196
    assert q_blocks(1517)[3]["Q"] == 2493
    assert q_blocks(501)[3]["x"] == 763


def test_collision_is_the_integer_landing():
    row_365 = q_blocks(365)[COLLISION_INDEX]
    row_1517 = q_blocks(1517)[COLLISION_INDEX]
    assert row_365["x"] == 4447
    assert row_1517["x"] == 33811
    assert row_365["a"] == 2
    assert row_1517["a"] == 1
    assert row_365["prev"] == 1749
    assert row_1517["prev"] == 10613
    assert row_365["first_def"] == first_odd_defect(4447)
    assert row_1517["first_def"] == first_odd_defect(33811)
    assert row_365["first_def"] != row_1517["first_def"]
    assert row_365["rem"] != row_1517["rem"]
    assert row_365["Q_minus_x"] != row_1517["Q_minus_x"]
    assert prefix_lambda([2, 2, 2]) == Fraction(729, 512)
    collision = collision_state()
    assert collision["any_intrinsic_shared"] is False
    assert collision["minimal_predictor"] == "the integer landing Q^3(n)"


def test_contraction_is_not_progress():
    row = q_blocks(1517)[3]
    assert row["x"] == 33811
    assert row["Q"] == 2493
    assert 2493 >= 1517
    assert q_blocks(1517)[4]["Q"] == 539470
    later = q_blocks(365)[4]
    assert later["x"] == 12707
    assert later["Q"] == 1196
    assert 1196 >= 365


def test_probe_parks_without_new_lean():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_PARK
    window = scan["window"]
    assert window["repeated_endpoints_on_orbit"] == 0
    assert window["a1_expands"] == 0
    assert window["contract_stay_then_q2_stay"] >= 1
    assert window["expand_then_q2_gt_q"] >= 1
    assert window["prefix_222_branching"] is True
    assert 1 in window["next_from_2_expand"]
    assert 2 in window["next_from_2_expand"]
    assert window["a_sign_ambiguous"] >= 1
    assert window["pair_a_ambiguous"] >= 1
    assert window["first_def_ambiguous_a"] >= 1
    assert window["rem_ambiguous_next_a"] >= 1
    assert scan["summary"]["no_repeated_endpoint"] is True
    assert scan["halt_theorem"] is False
    assert scan["residue_automaton"] is False
    assert scan["run_length_graph"] is False


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
    assert data["experiment"] == "juggler_block_map_q"
    assert data["decision"]["classification"] == CLASS_PARK
    assert dict(ANTI_OVERCLAIM)["global_termination"] is False
    assert payload["anti_overclaim"]["finite_q_descriptor"] is False
    assert payload["anti_overclaim"]["two_block_return_law"] is False
    assert payload["anti_overclaim"]["block_transition_theorem"] is False


def test_dossier_boundary():
    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_block_map_q.md").read_text(
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
    assert "4447" in dossier
    assert "33811" in dossier
    assert "BlockMapQ" not in paper
    assert "theorem juggler_reaches_one" not in note

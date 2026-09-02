"""Empty-odd-cell geometry of leftover PE landings."""

from __future__ import annotations

import json
from pathlib import Path

from research.juggler_sequence.empty_odd_cell import (
    CLASS_PARK,
    EXISTING_LEAN,
    FORBIDDEN_NEW_API,
    FORBIDDEN_THEOREMS,
    JSON_PATH,
    ceil_cbrt,
    cell_pair,
    classify,
    control_row,
    criterion_scan,
    icbrt,
    lean_api_present,
    odd_cell_empty,
    odd_cell_kind,
    odd_pred_empty,
    pe_landings,
    render_markdown,
    run_probe,
    write_artifacts,
)
from research.juggler_sequence.floor_cells import odd_cell_integers
from research.juggler_sequence.minimal_anchor_closure import trajectory_until_drop
from research.juggler_sequence.power_words import ANTI_OVERCLAIM, floor_power


def test_cube_criterion_matches_occupancy():
    scan = criterion_scan(4000)
    assert scan["mismatches"] == 0
    assert scan["counts"][0] + scan["counts"][1] + scan["counts"][2] == 4000
    assert scan["type0_share"] > 0.9


def test_types_on_named_landings():
    assert odd_cell_kind(763) == 0
    assert odd_cell_integers(763) == []
    assert odd_cell_empty(763) is True
    assert odd_pred_empty(763) is True
    assert odd_cell_kind(117) == 1
    assert odd_cell_integers(117) == [24]
    assert odd_pred_empty(117) is True
    assert odd_cell_kind(70) == 2
    assert odd_cell_integers(70) == [17]
    assert odd_pred_empty(70) is False
    assert ceil_cbrt(763 * 763) ** 3 >= 764 * 764
    a, b = cell_pair(763)
    assert a == b == icbrt(763 * 763)


def test_odd_step_makes_type2_regardless_of_emptiness():
    assert odd_cell_kind(763) == 0
    nxt = floor_power(763)
    assert nxt == 21075
    assert odd_cell_kind(nxt) == 2
    assert odd_cell_integers(nxt) == [763]
    assert odd_cell_integers(floor_power(365)) == [365]
    assert odd_cell_kind(floor_power(365)) == 2


def test_365_pe_landings_are_type0_with_mixed_exit():
    row = control_row(365)
    assert row["word"] == "OOEOOEOOEOOEOEE"
    assert row["kinds"] == [0, 0, 0, 0, 0]
    assert [item["landing"] for item in row["landings"]] == [
        763,
        1749,
        4447,
        12707,
        1196,
    ]
    assert row["mixed_next_parity"] is True
    assert row["odd_next_parities"] == [1, 1, 1, 0]
    assert row["offset_min"] < 0.1
    assert row["offset_max"] > 0.8
    assert row["odd_landing_next_is_type2"] is True


def test_1517_and_501_and_6187():
    row_1517 = control_row(1517)
    assert row_1517["all_type0"] is True
    assert row_1517["mixed_next_parity"] is True
    row_501 = control_row(501)
    assert 582916 in [item["landing"] for item in row_501["landings"]]
    assert 763 in trajectory_until_drop(501)
    assert row_501["all_type0"] is True
    row_6187 = control_row(6187)
    assert row_6187["all_type0"] is True


def test_69_and_89_are_not_all_type0():
    assert control_row(69)["kinds"] == [1, 0]
    assert control_row(89)["kinds"] == [0, 1, 2]


def test_pe_landing_of_365_has_no_square_subinterval():
    path = trajectory_until_drop(365)
    rows = pe_landings(path)
    ratios = [row["offset"] / row["width"] for row in rows]
    assert min(ratios) < 0.1
    assert max(ratios) > 0.8


def test_probe_parks_without_new_lean():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_PARK
    assert scan["criterion"]["mismatches"] == 0
    assert scan["summary"]["all_type0"] is True
    assert scan["summary"]["mixed_next_parity"] is True
    assert scan["summary"]["763_kind"] == 0
    assert scan["summary"]["763_next_kind"] == 2
    assert scan["ambient"]["type0_share"] > 0.8
    assert scan["halt_theorem"] is False
    assert scan["predclosure_reopened"] is False


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
    assert data["experiment"] == "juggler_empty_odd_cell"
    assert data["decision"]["classification"] == CLASS_PARK
    assert dict(ANTI_OVERCLAIM)["global_termination"] is False
    assert payload["anti_overclaim"]["empty_forces_next_parity"] is False
    assert payload["anti_overclaim"]["empty_persists_along_orbit"] is False


def test_dossier_boundary():
    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_empty_odd_cell.md").read_text(
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
    assert "OddPredEmpty" in dossier
    assert "OddPredEmpty" not in paper
    assert "theorem juggler_reaches_one" not in note

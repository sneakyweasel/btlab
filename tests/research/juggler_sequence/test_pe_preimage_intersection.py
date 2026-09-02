"""PE-envelope versus odd-cell intersection at leftover landings."""

from __future__ import annotations

import json
from pathlib import Path

from research.juggler_sequence.cycle_itinerary import follows_itinerary, image_after
from research.juggler_sequence.empty_odd_preimage import odd_preimage_kind
from research.juggler_sequence.pe_preimage_intersection import (
    CLASS_PARK,
    CONTROLS,
    EXISTING_LEAN,
    FORBIDDEN_NEW_API,
    FORBIDDEN_THEOREMS,
    JSON_PATH,
    TYPE_I,
    TYPE_II,
    TYPE_III,
    classify,
    control_rows,
    intersection_type,
    lean_api_present,
    ooe_scan,
    render_markdown,
    run_probe,
    write_artifacts,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power


def test_even_predecessor_never_meets_odd_interval():
    row = intersection_type(763, 582276)
    assert row["type"] == TYPE_I
    assert row["z_even"] is True
    assert row["z_in_even_cell"] is True
    assert row["z_in_odd_interval"] is False
    assert row["odd_preds"] == []
    assert row["scale_gap"] > 0


def test_type_ii_witness_199():
    assert follows_itinerary(199, "OOE")
    y = image_after(199, "OOE")
    z = floor_power(floor_power(199))
    row = intersection_type(y, z)
    assert y == 385
    assert row["type"] == TYPE_II
    assert row["odd_preds"] == [53]
    assert 53 != z
    assert row["z_in_odd_interval"] is False
    assert row["z_in_even_cell"] is True


def test_first_overshoot_is_not_a_pe_landing():
    """n itself occupies the odd cell of T(n). That is not a PE reset."""
    row = intersection_type(6973, 365)
    assert row["type"] == TYPE_III
    assert row["odd_preds"] == [365]
    assert odd_preimage_kind(6973) == 2


def test_365_pe_landings_are_type_i():
    rows = control_rows(365)
    assert [item["y"] for item in rows] == [763, 1749, 4447, 12707]
    assert all(item["type"] == TYPE_I for item in rows)
    assert all(item["word"] == "OOE" for item in rows)
    assert all(item["z_in_even_cell"] and not item["z_in_odd_interval"] for item in rows)


def test_69_and_89_type_i_with_optional_even_cube():
    trap = control_rows(69)
    short = control_rows(89)
    assert [item["y"] for item in trap] == [117]
    assert trap[0]["type"] == TYPE_I
    assert trap[0]["even_cubes"] == [24]
    assert [item["y"] for item in short] == [155, 291]
    assert all(item["type"] == TYPE_I for item in short)
    assert short[1]["even_cubes"] == [44]


def test_ooe_scan_has_type_ii_and_no_type_iii():
    scan = ooe_scan(4000)
    assert scan["counts"][TYPE_I] > 100
    assert scan["counts"][TYPE_II] >= 8
    assert scan["counts"][TYPE_III] == 0
    assert scan["any_type_iii"] is False
    assert any(item["n"] == 199 for item in scan["type_ii_samples"])


def test_leftover_controls_are_type_i():
    for n in CONTROLS:
        rows = control_rows(n)
        assert rows
        assert all(item["type"] == TYPE_I for item in rows)
        assert all(item["z_even"] for item in rows)


def test_probe_parks_without_new_lean():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_PARK
    assert scan["summary"]["all_type_i"] is True
    assert scan["summary"]["scale_mismatch"] is True
    assert scan["summary"]["any_type_iii"] is False
    assert scan["ooe_scan"]["any_type_iii"] is False
    assert scan["halt_theorem"] is False
    assert scan["predclosure_reopened"] is False
    assert scan["forward_law_retested"] is False
    assert scan["rbc_reopened"] is False


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
    assert data["experiment"] == "juggler_pe_preimage_intersection"
    assert data["decision"]["classification"] == CLASS_PARK
    assert dict(ANTI_OVERCLAIM)["global_termination"] is False
    assert payload["anti_overclaim"]["iy_meets_jn_new_obstruction"] is False
    assert payload["anti_overclaim"]["n0_empty_pe_cells"] is False
    assert payload["anti_overclaim"]["rbc_reopened"] is False


def test_dossier_boundary():
    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_pe_preimage_intersection.md").read_text(
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
    assert "PredClosure" in dossier
    assert "PECellIntersection" not in paper
    assert "theorem juggler_reaches_one" not in note
    assert "theorem no_juggler_cycle" not in note

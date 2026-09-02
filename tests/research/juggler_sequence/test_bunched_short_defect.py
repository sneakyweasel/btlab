"""Exact short-cluster closure via defect. Not a halt or Z5 test."""

from __future__ import annotations

import json

from research.juggler_sequence.bunched_short_defect import (
    CLASS_PARK,
    FORBIDDEN_THEOREMS,
    LEAN_THEOREMS,
    SHORT_PAIRS,
    classify,
    ee_delta,
    ee_state,
    last_odd_hits,
    lean_api_present,
    render_markdown,
    run_probe,
    tiny_gap_min,
    write_artifacts,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power


def test_ee_identity_and_tiny_gap():
    assert SHORT_PAIRS[0] == (0, 0)
    assert SHORT_PAIRS[-1] == (2, 1)
    n, eps, eta = 13, 1, 0
    y = ee_state(n, eps, eta)
    assert y - n**4 == ee_delta(n, eps, eta) == 339
    assert floor_power(floor_power(y)) == n
    assert tiny_gap_min(13) == 2 * 13 * 13 + 1 == 339
    assert tiny_gap_min(15) == 451


def test_last_odd_defects_are_ordinary():
    rows = last_odd_hits(13)
    assert len(rows) == 1
    row = rows[0]
    assert row["z"] == 31
    assert row["delta"] % 2 == 1
    assert row["delta"] <= 2 * row["q"]
    assert row["tiny_relative_n4"] is False
    assert row["gap_from_n4"] == 1023


def test_probe_and_classify_park():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_PARK
    assert scan["tiny_gap_possible_odd_n"] is False
    assert scan["ee_signatures_unrestricted"] is True
    assert scan["required_defect_ordinary"] is True
    assert scan["parity_mismatch"] is False
    assert scan["leftover_cell_rewrite"] is True
    assert scan["last_odd"]["hit_count"] == 15
    assert scan["last_odd"]["all_delta_odd"] is True
    assert scan["last_odd"]["tiny_n4_hits"] == 0
    assert scan["ee13"]["count"] == 2366
    assert scan["ee13"]["pair_count"] == 16
    assert scan["ee15"]["count"] == 3600
    assert scan["ee15"]["pair_count"] == 16
    assert scan["preimage_enumerator"] is False
    assert scan["length_eleven_census"] is False
    assert scan["z5_cells"] is False


def test_lean_api_without_halt_or_z5():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    for name in FORBIDDEN_THEOREMS:
        assert lean[f"has_{name}"] is False, name
    assert lean["not_in_paper_barrel"] is True
    assert lean["no_new_lean"] is True


def test_classify_render_and_artifacts():
    payload = write_artifacts()
    text = render_markdown(payload)
    assert CLASS_PARK in text
    assert "n^4 + 2 eps n^2" in text
    from research.juggler_sequence.bunched_short_defect import JSON_PATH

    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_bunched_short_defect"
    assert data["decision"]["classification"] == CLASS_PARK
    assert data["anti_overclaim"]["cycles_impossible"] is False
    assert dict(ANTI_OVERCLAIM)["global_termination"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_bunched_short_defect.md").read_text(
        encoding="utf-8"
    )
    ret = (repo / "docs" / "problems" / "juggler_bunched_short_return.md").read_text(
        encoding="utf-8"
    )
    note = (repo / "docs" / "theory" / "juggler_finite_dynamics_note.md").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "PARK" in dossier
    assert "defect" in dossier.lower()
    assert "juggler_bunched_short_defect" in ret
    assert "theorem no_cycle_itinerary_length_eleven" not in note
    assert "theorem no_juggler_cycle" not in note

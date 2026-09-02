"""First-E transport at four evens. Not an engine-control or halt test."""

from __future__ import annotations

import json

from research.juggler_sequence.first_e_e4 import (
    CLASS_REPARAM,
    CLASSES,
    FORBIDDEN_THEOREMS,
    LEAN_THEOREMS,
    classify,
    classify_leftover,
    leftover_params,
    probe_payload,
    remainder_shapes,
    render_markdown,
    word_e4,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM

_PAYLOAD = None


def payload() -> dict:
    global _PAYLOAD
    if _PAYLOAD is None:
        _PAYLOAD = probe_payload()
    return _PAYLOAD


def test_leftover_classes_and_partition():
    assert classify_leftover(2, 0, 4, 0) == "gapped_last_cluster"
    assert classify_leftover(2, 0, 3, 1) == "gapped_last_cluster"
    assert classify_leftover(2, 6, 0, 0) == "bunched_remainder"
    assert classify_leftover(2, 5, 1, 0) == "bunched_remainder"
    assert classify_leftover(2, 5, 0, 0) == "short_bunched_remainder"
    assert classify_leftover(2, 4, 1, 0) == "short_bunched_remainder"
    assert classify_leftover(7, 0, 0, 0) == "leading_even"
    assert classify_leftover(6, 1, 0, 0) == "leading_OE"
    assert word_e4(2, 6, 0, 0) == "OOEOOOOOOEEE"
    assert word_e4(7, 0, 0, 0) == "OOOOOOOEEEE"
    shapes = remainder_shapes()
    assert len(shapes) == 30
    assert all(row["first_expanding_a0"] is not None for row in shapes)
    kinds = {row["kind"] for row in shapes}
    assert kinds == {"leading_even", "leading_OE", "short_bunched_remainder"}
    params = leftover_params()
    assert len(params) == 1185
    assert all(classify_leftover(*row) in CLASSES for row in params)
    assert not any(
        classify_leftover(*row) == "bunched_remainder"
        for row in params
        if sum(row) == 7
    )
    assert any(
        classify_leftover(*row) == "bunched_remainder"
        for row in params
        if sum(row) == 8
    )


def test_probe_is_reparameterization():
    data = payload()
    scan = data["scan"]
    lean = data["lean"]
    decision = data["decision"]
    assert classify(scan, lean)["classification"] == CLASS_REPARAM
    assert decision["classification"] == CLASS_REPARAM
    assert scan["leftover_count"] == 1185
    assert scan["remainder_count"] == 300
    assert scan["remainder_shape_count"] == 30
    assert scan["class_counts"]["gapped_last_cluster"] == 570
    assert scan["class_counts"]["bunched_remainder"] == 315
    assert scan["class_counts"]["short_bunched_remainder"] == 160
    assert scan["class_counts"]["leading_OE"] == 70
    assert scan["class_counts"]["leading_even"] == 70
    assert scan["first_bunched_remainder_odd"] == 8
    assert scan["z_monotone"] is True
    assert scan["all_bunched_tails_hold"] is True
    assert scan["unclassified"] == 0
    assert scan["length_eight_census"] is False
    assert scan["length_nine_census"] is False
    assert scan["four_even_bunched_attack"] is False


def test_lean_api_has_no_e4_or_census_theorem():
    lean = payload()["lean"]
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    for name in FORBIDDEN_THEOREMS:
        assert lean[name] is True, name
    assert lean["length_eight_open_in_census"] is True
    assert lean["no_all_cycles_impossible"] is True


def test_classify_render_and_artifacts():
    data = payload()
    text = render_markdown(data)
    assert CLASS_REPARAM in text
    assert "30 short-first-gap" in text
    from research.juggler_sequence.first_e_e4 import JSON_PATH

    assert JSON_PATH.is_file()
    stored = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert stored["experiment"] == "juggler_first_e_e4"
    assert stored["decision"]["classification"] == CLASS_REPARAM
    assert stored["anti_overclaim"]["cycles_impossible"] is False
    assert stored["anti_overclaim"]["first_e_e4_lean"] is False
    assert stored["anti_overclaim"]["four_even_bunched_attack"] is False
    assert stored["lean"]["no_cycle_itinerary_four_even"] is True
    assert stored["lean"]["no_cycle_itinerary_length_eight"] is True
    assert stored["scan"]["length_eight_census"] is False
    assert dict(ANTI_OVERCLAIM)["global_termination"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_first_e_e4.md").read_text(
        encoding="utf-8"
    )
    note = (repo / "docs" / "theory" / "juggler_finite_dynamics_note.md").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "CLOSE" in dossier
    assert "REPARAMETERIZATION" in dossier
    assert "no_cycle_itinerary_length_eight" in dossier
    assert "no_cycle_itinerary_length_nine" in dossier
    assert "not a length-8" in dossier or "not a length-8/9" in dossier
    assert "theorem no_cycle_itinerary_four_even" not in note
    assert "theorem no_cycle_itinerary_length_eight" not in note
    assert "theorem no_cycle_itinerary_length_nine" not in note

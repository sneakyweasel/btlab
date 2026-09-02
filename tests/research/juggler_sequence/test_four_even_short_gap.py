"""Four-even short-first-gap prefix-cell. Not an engine-control or halt test."""

from __future__ import annotations

import json

from research.juggler_sequence.first_e_e4 import remainder_shapes, word_e4
from research.juggler_sequence.four_even_short_gap import (
    CLASS_PARK,
    FORBIDDEN_THEOREMS,
    LEAN_THEOREMS,
    N0_PLUS1_MAX,
    N0_PLUS2_MAX,
    classify,
    first_n0,
    log_z4,
    probe_payload,
    render_markdown,
    tail_holds_log,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM

_PAYLOAD = None


def payload() -> dict:
    global _PAYLOAD
    if _PAYLOAD is None:
        _PAYLOAD = probe_payload()
    return _PAYLOAD


def test_thirty_length_eleven_words_and_cell():
    shapes = remainder_shapes()
    assert len(shapes) == 30
    words = {word_e4(shape["first_expanding_a0"], shape["a1"], shape["a2"], shape["a3"]) for shape in shapes}
    assert len(words) == 30
    assert all(len(word) == 11 for word in words)
    assert "OOOOOOOEEEE" in words
    assert "OOEOOOOOEEE" in words
    assert log_z4(10, 0, 0, 0) > 0
    assert tail_holds_log(37, 8, 0, 0, 0) is True
    assert tail_holds_log(10, 7, 0, 0, 0) is False
    assert first_n0(7, 0, 0, 0) is None
    assert first_n0(8, 0, 0, 0) == 37
    assert first_n0(9, 0, 0, 0) == 11


def test_probe_is_park_after_first_expanding():
    data = payload()
    scan = data["scan"]
    decision = data["decision"]
    assert classify(scan, data["lean"])["classification"] == CLASS_PARK
    assert decision["classification"] == CLASS_PARK
    assert scan["shape_count"] == 30
    assert scan["all_first_expanding_length_eleven"] is True
    assert scan["all_miss_first_expanding_window"] is True
    assert scan["plus1_bounded"] is True
    assert scan["plus2_bounded"] is True
    assert scan["max_n0_plus1"] == N0_PLUS1_MAX
    assert scan["max_n0_plus2"] == N0_PLUS2_MAX
    assert scan["all_large_n0_huge"] is True
    assert scan["length_eight_census"] is False
    assert scan["length_nine_census"] is False
    assert scan["length_eleven_census"] is False
    assert scan["four_even_lean"] is False


def test_lean_api_has_no_four_even_or_census_theorem():
    lean = payload()["lean"]
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    for name in FORBIDDEN_THEOREMS:
        assert lean[name] is True, name
    assert lean["length_eight_open_in_census"] is True


def test_classify_render_and_artifacts():
    data = payload()
    text = render_markdown(data)
    assert CLASS_PARK in text
    assert "OOOOOOOEEEE" in text
    from research.juggler_sequence.four_even_short_gap import JSON_PATH

    assert JSON_PATH.is_file()
    stored = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert stored["experiment"] == "juggler_four_even_short_gap"
    assert stored["decision"]["classification"] == CLASS_PARK
    assert stored["anti_overclaim"]["cycles_impossible"] is False
    assert stored["anti_overclaim"]["four_even_lean"] is False
    assert stored["anti_overclaim"]["length_eleven_census"] is False
    assert stored["lean"]["no_cycle_itinerary_four_even"] is True
    assert stored["lean"]["no_cycle_itinerary_length_eight"] is True
    assert dict(ANTI_OVERCLAIM)["global_termination"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_four_even_short_gap.md").read_text(
        encoding="utf-8"
    )
    note = (repo / "docs" / "theory" / "juggler_finite_dynamics_note.md").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "PARK" in dossier
    assert "no_cycle_itinerary_length_eight" in dossier
    assert "no_cycle_itinerary_length_nine" in dossier
    assert "not a length-8" in dossier or "not a length-8/9" in dossier
    assert "theorem no_cycle_itinerary_four_even" not in note
    assert "theorem no_cycle_itinerary_length_eleven" not in note
    assert "theorem no_cycle_itinerary_length_eight" not in note

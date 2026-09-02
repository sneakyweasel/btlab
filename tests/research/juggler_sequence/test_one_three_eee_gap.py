"""(1,3) EEE +1-chain gap. Not a length-11 census or halt test."""

from __future__ import annotations

import json
from pathlib import Path

from research.juggler_sequence.one_three_eee_gap import (
    CELL_BITS,
    CLASS_PROVED,
    FAMILY,
    FORBIDDEN_THEOREMS,
    LEAN_THEOREMS,
    PIN_MAX,
    SLACK,
    SURPLUS,
    classify,
    eee_cell_hi,
    elementary_comparisons,
    first_prefix_start,
    follows_itinerary,
    fudge_exp,
    lean_api_present,
    leading_beats_v,
    left_plus,
    master_beats,
    pin_family,
    prefix,
    render_markdown,
    itinerary,
    write_artifacts,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM


def test_family_identity_and_elementary():
    assert SURPLUS == 3**7 == 2187
    assert CELL_BITS == 2**11 == 2048
    assert SLACK == 139
    assert len(FAMILY) == 5
    assert [member.a0 + member.a1 for member in FAMILY] == [7] * 5
    assert itinerary(6, 1) == "OOOOOOEOEEE"
    assert itinerary(2, 5) == "OOEOOOOOEEE"
    assert left_plus(6) == (1995, 1266, 64)
    assert left_plus(2) == (15, 6, 4)
    assert fudge_exp(6, 1) == 384
    assert fudge_exp(2, 5) == 5064
    assert 12 * 163 >= 3 * 164
    elem = elementary_comparisons()
    assert all(elem.values()), elem


def test_first_starts_and_prefix_above_cell():
    expected = {6: 163, 5: 241, 4: 37, 3: 113, 2: 173}
    for member in FAMILY:
        assert first_prefix_start(member.a0, member.a1) == expected[member.a0]
        z = follows_itinerary(member.first, prefix(member.a0, member.a1))
        assert z is not None
        assert z >= eee_cell_hi(member.first)
        assert leading_beats_v(member.first, member.a0, member.v_lb)
        assert master_beats(member.first, member.v_lb, fudge_exp(member.a0, member.a1))


def test_pin_empty():
    pins = pin_family()
    assert len(pins) == 5
    for row, member in zip(pins, FAMILY, strict=True):
        assert row["first"] == member.first
        assert row["misses"] == []
        assert row["count"] == member.pin_count
        assert row["above_cell"] == member.pin_count
        assert row["min_n"] == member.min_n
        assert row["min_ratio"] > member.min_ratio_floor
        assert row["n_hi"] == PIN_MAX


def test_lean_has_o7_and_no_family_census():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    for name in FORBIDDEN_THEOREMS:
        assert lean[name] is True, name
    assert lean["no_nonunique_family_cycle_itinerary"] is True
    assert lean["paper_a_has_no_family"] is True


def test_classify_render_and_artifacts():
    from research.juggler_sequence.one_three_eee_gap import JSON_PATH, probe_payload

    data = probe_payload()
    assert classify(data["scan"], data["lean"])["classification"] == CLASS_PROVED
    text = render_markdown(data)
    assert CLASS_PROVED in text
    assert "OOOOOOEOEEE" in text
    assert "OOEOOOOOEEE" in text
    write_artifacts(data)
    stored = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert stored["experiment"] == "juggler_one_three_eee_gap"
    assert stored["decision"]["classification"] == CLASS_PROVED
    assert stored["anti_overclaim"]["length_eleven_census"] is False
    assert stored["scan"]["twenty_three_word_scan"] is False
    assert dict(ANTI_OVERCLAIM)["global_termination"] is False
    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_one_three_eee_gap.md").read_text(
        encoding="utf-8"
    )
    assert "PROMOTE" in dossier
    assert "OOOOOOEOEEE" in dossier
    assert "no_cycle_itinerary_length_eleven" in dossier

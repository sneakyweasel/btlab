"""Isolated-odd prefixes versus short-tail fibres. Not a halt or Z5 test."""

from __future__ import annotations

import json

from research.juggler_sequence.isolated_odd_return import (
    CLASS_CLOSE,
    FORBIDDEN_THEOREMS,
    LEAN_THEOREMS,
    N_CYCLEMIN,
    SHORT_PAIRS,
    block_map,
    classify,
    cyclemin_image,
    in_return_fibre,
    is_isolated_odd,
    iso_odd_prefixes,
    lean_api_present,
    render_markdown,
    write_artifacts,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power


def test_block_map_contracts_and_family_is_isolated():
    assert block_map(13) == 6
    assert block_map(27) == 11
    assert 6 < 13 and 11 < 27
    assert block_map(5) is None
    assert floor_power(5) % 2 == 1
    words = list(iso_odd_prefixes())
    assert "" in words
    assert "O" in words
    assert "OE" in words
    assert "OEE" in words
    assert all(is_isolated_odd(word) for word in words)
    assert "OO" not in words
    assert "OOE" not in words


def test_empty_and_single_o_are_the_only_cyclemin_prefixes():
    assert cyclemin_image(13, "") == 13
    assert cyclemin_image(13, "O") == 46
    assert cyclemin_image(13, "OE") is None
    assert cyclemin_image(13, "OEE") is None
    assert cyclemin_image(13, "OEOE") is None
    assert in_return_fibre(13, 13, 0, 0) is False
    assert in_return_fibre(13, 46, 0, 0) is False
    for b, c in SHORT_PAIRS:
        assert in_return_fibre(13, 13, b, c) is False
        assert in_return_fibre(13, 46, b, c) is False


def test_probe_and_classify_close():
    payload = write_artifacts()
    scan = payload["scan"]
    lean = payload["lean"]
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_CLOSE
    assert scan["block"]["always_contracts"] is True
    assert scan["block"]["expands"] == 0
    assert scan["block"]["fixed"] == 0
    assert scan["block"]["follows"] == 43
    assert scan["census"]["admissible_words"] == ["", "O"]
    assert scan["census"]["extra_cyclemin_prefixes"] == 0
    assert scan["census"]["hit_count"] == 0
    assert scan["census"]["landing_count"] == 52
    assert scan["census"]["n_max"] == N_CYCLEMIN
    assert scan["short"]["empty_hits"] == 0
    assert scan["short"]["single_o_hits"] == 0
    assert scan["length_eleven_census"] is False
    assert scan["z5_cells"] is False
    assert scan["four_even_assembler"] is False
    assert scan["interval_census"] is False
    assert scan["fibre_enumeration"] is False


def test_lean_api_without_halt_or_z5():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    for name in FORBIDDEN_THEOREMS:
        assert lean[f"has_{name}"] is False, name
    assert lean["not_in_paper_barrel"] is True
    assert lean["no_global_termination_theorem"] is True
    assert lean["FloorPower_not_rewritten"] is True


def test_classify_render_and_artifacts():
    from research.juggler_sequence.isolated_odd_return import JSON_PATH

    payload = write_artifacts()
    text = render_markdown(payload)
    assert CLASS_CLOSE in text
    assert "oe_block_contracts" in text
    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_isolated_odd_return"
    assert data["decision"]["classification"] == CLASS_CLOSE
    assert data["anti_overclaim"]["cycles_impossible"] is False
    assert data["engine_control_layer_modified"] is False
    assert dict(ANTI_OVERCLAIM)["global_termination"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_isolated_odd_return.md").read_text(
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
    assert "CLOSE" in dossier
    assert "isolated-odd" in dossier.lower()
    assert "juggler_isolated_odd_return" in ret
    assert "theorem no_cycle_itinerary_length_eleven" not in note
    assert "theorem no_cycleMin_four_even" not in note
    assert "theorem no_juggler_cycle" not in note

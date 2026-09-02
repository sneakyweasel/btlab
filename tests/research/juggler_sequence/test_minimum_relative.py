"""Shared AboveAnchor layer for CycleMin and MinimalNonTerm."""

from __future__ import annotations

import json

from research.juggler_sequence.cycle_itinerary import follows_itinerary, image_after
from research.juggler_sequence.minimum_relative import (
    CLASS_GREEN,
    FORBIDDEN_THEOREMS,
    LEAN_THEOREMS,
    above_anchor,
    classify,
    even_below_square_gives_drop,
    first_drop_index,
    isolated_prefix_word,
    lean_api_present,
    remaining_gap,
    render_markdown,
    run_probe,
    write_artifacts,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power


def test_trivial_cycle_is_above_anchor():
    assert floor_power(1) == 1
    assert above_anchor(1, "")
    assert above_anchor(1, "O")
    assert follows_itinerary(1, "O")


def test_ooe_at_five_is_above_anchor():
    word = isolated_prefix_word(2, 0)
    assert word == "OOE"
    assert follows_itinerary(5, word)
    assert image_after(5, word) == 6
    assert above_anchor(5, word)


def test_ooeoe_at_nine_is_not_above_anchor():
    word = isolated_prefix_word(2, 1)
    assert word == "OOEOE"
    assert follows_itinerary(9, word)
    assert image_after(9, word) < 9
    assert above_anchor(9, word) is False


def test_even_square_trap_on_69():
    assert follows_itinerary(69, "OOEOOE")
    x = image_after(69, "OOEOOE")
    assert x == 212
    assert even_below_square_gives_drop(x, 69)
    assert above_anchor(69, "OOEOOE") is True
    assert above_anchor(69, "OOEOOEE") is False


def test_501_and_6187_prefixes_before_drop():
    for n in (501, 6187):
        drop = first_drop_index(n, 400)
        assert drop is not None
        assert drop > 1
        current = n
        word = ""
        for _ in range(drop - 1):
            word += "O" if current % 2 else "E"
            current = floor_power(current)
            assert current >= n
        assert above_anchor(n, word)
        current = floor_power(current)
        assert current < n


def test_remaining_gap_is_unbounded_escape():
    gap = remaining_gap()
    assert gap["coincide"] is False
    assert "odd-landing" in gap["leftover"]
    assert 365 in gap["examples"]


def test_leftover_word_has_cube_not_square_gap():
    """OOEOOEOOEOEOO: 3^9 < 3·2^13 (cube) and not 3^9 < 2·2^13 (square)."""
    assert 3**9 < 3 * 2**13
    assert not (3**9 < 2 * 2**13)


def test_probe_and_classify_green():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_GREEN
    assert scan["negative"]["above_anchor"] is False
    assert scan["ooe_five"]["above_anchor"] is True
    assert scan["even_trap_69"]["drop"] is True
    assert scan["remaining_gap"]["coincide"] is False


def test_lean_api_without_halt():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    for name in FORBIDDEN_THEOREMS:
        assert lean[f"has_{name}"] is False, name
    assert lean["in_laboratory_barrel"] is True
    assert lean["not_in_paper_barrel"] is True


def test_classify_render_and_artifacts():
    payload = write_artifacts()
    text = render_markdown(payload)
    assert CLASS_GREEN in text
    from research.juggler_sequence.minimum_relative import JSON_PATH

    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_minimum_relative"
    assert data["decision"]["classification"] == CLASS_GREEN
    assert dict(ANTI_OVERCLAIM)["global_termination"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_minimum_relative.md").read_text(
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
    assert "PROMOTE" in dossier
    assert "AboveAnchor" in dossier
    assert "MinimumRelative" not in paper
    assert "theorem no_juggler_cycle" not in note
    assert "theorem juggler_reaches_one" not in note

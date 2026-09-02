"""Minimal-anchor closure on leftover odd-escape corridors."""

from __future__ import annotations

import json
from pathlib import Path

from research.juggler_sequence.cycle_itinerary import follows_itinerary, image_after
from research.juggler_sequence.minimal_anchor_closure import (
    CLASS_PARK,
    CONTROLS,
    EXISTING_LEAN,
    FORBIDDEN_NEW_API,
    FORBIDDEN_THEOREMS,
    JSON_PATH,
    WORD_L,
    classify,
    corridor_rank,
    episode_row,
    lean_api_present,
    render_markdown,
    run_probe,
    structured_from,
    write_artifacts,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power


def test_corridor_rank_bands():
    assert corridor_rank(365, 365) == 2
    assert corridor_rank(364, 365) == 1
    assert corridor_rank(365 * 365, 365) == 3
    assert corridor_rank(365 * 365 - 1, 365) == 2


def test_365_is_a_generator_spine():
    row = episode_row(365)
    assert row["word"] == "OOEOOEOOEOOEOEE"
    assert row["drop"] == 34
    assert row["first_overshoot"] == 6973
    assert row["first_overshoot_odd"] is True
    assert row["above_anchor_before_drop"] is True
    assert row["high_merge"] is None
    assert row["smaller_full_word"] == []
    assert row["high_odd_preds"]["smaller"] == []
    assert row["high_odd_preds"]["first_overshoot_unique_odd_pred"] is True
    assert row["high_odd_preds"]["empty_odd_high"] == [763, 1749, 4447, 12707]
    assert row["any_high_structured_return"] is False
    assert row["ranks"]["max_rank"] == 4
    assert row["ranks"]["monotone_nonincreasing"] is False
    reset = row["ranks"]["first_reset"]
    assert reset is not None
    assert reset["state"] == 582276
    assert reset["next"] == 763
    assert reset["next_below_anchor"] is False


def test_first_overshoot_oe_stays_on_all_leftovers():
    expected = {365: 763, 501: 1089, 1517: 3789, 6187: 18425}
    for n, image in expected.items():
        overshoot = floor_power(n)
        struct = structured_from(overshoot, n)
        assert overshoot % 2 == 1
        assert struct["E"]["follows"] is False
        assert struct["OOE"]["follows"] is False
        assert struct["OOOE"]["follows"] is False
        assert struct["OE"]["follows"] is True
        assert struct["OE"]["image"] == image
        assert image > n
        assert struct["OE"]["below_anchor"] is False


def test_501_inherits_365_at_763():
    row = episode_row(501)
    assert row["follows_L"] is True
    assert image_after(501, WORD_L) == 763
    merge = row["high_merge"]
    assert merge is not None
    assert merge["state"] == 763
    assert merge["m"] == 365
    assert merge["steps_from_m"] == 3
    assert merge["path_index"] == 11


def test_1517_is_a_generator_spine():
    row = episode_row(1517)
    assert row["word"] == "OOEOOEOOEOEOOOEE"
    assert row["high_merge"] is None
    assert row["smaller_full_word"] == []
    assert row["high_odd_preds"]["smaller"] == []
    assert row["any_high_structured_return"] is False
    assert row["ranks"]["monotone_nonincreasing"] is False


def test_6187_exits_by_oe_from_l_image():
    row = episode_row(6187)
    assert follows_itinerary(6187, WORD_L)
    assert image_after(6187, WORD_L) == 11189
    assert 11189 > 6187
    assert row["high_merge"] is None
    assert row["smaller_full_word"] == []
    assert row["high_odd_preds"]["smaller"] == []
    assert row["any_high_structured_return"] is True
    oe = structured_from(11189, 6187)["OE"]
    assert oe["follows"] is True
    assert oe["image"] == 1087
    assert oe["below_anchor"] is True
    assert follows_itinerary(501, "OOEOOOEOOEEO")


def test_89_is_square_trap_contrast_not_leftover():
    row = episode_row(89)
    assert row["word"] == "OOEOOEOE"
    assert row["drop"] == 70
    assert row["even_below_square_before_last"] is False or row["path"][-2] < 89 * 89
    assert row["path"][-2] == 4964
    assert 4964 % 2 == 0
    assert 4964 < 89 * 89


def test_probe_parks_without_new_lean():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_PARK
    assert scan["summary"]["generators"] == [365, 1517, 6187]
    assert scan["summary"]["inherited"] == [501]
    assert scan["summary"]["501_merges_365"] is True
    assert scan["summary"]["short_structured_return"] is False
    assert scan["summary"]["6187_L_image_OE_drop"] is True
    assert scan["summary"]["6187_L_image"] == 11189
    assert scan["summary"]["rank_is_potential"] is False
    assert scan["contrast_69"]["shared_square_trap"] is True
    assert scan["contrast_69"]["landing"] == 212
    assert scan["contrast_89"]["word"] == "OOEOOEOE"
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
    assert data["experiment"] == "juggler_minimal_anchor_closure"
    assert data["decision"]["classification"] == CLASS_PARK
    assert dict(ANTI_OVERCLAIM)["global_termination"] is False
    assert payload["anti_overclaim"]["smaller_bad_descent"] is False
    assert payload["anti_overclaim"]["predclosure_reopened"] is False


def test_dossier_boundary():
    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_minimal_anchor_closure.md").read_text(
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
    assert "EscapeEpisode" not in paper
    assert "MinimalBad" not in paper
    assert "theorem juggler_reaches_one" not in note
    assert "theorem no_juggler_cycle" not in note

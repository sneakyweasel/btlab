"""Gapped three-even CycleItinerary leftovers. Not an engine-control or halt test."""

from __future__ import annotations

import json

from research.juggler_sequence.gapped_cycle_itinerary import (
    ALLOWED,
    CLASS_GREEN,
    FORBIDDEN,
    LEAN_THEOREMS,
    classify,
    classify_word,
    lean_api_present,
    render_markdown,
    rotate,
    run_probe,
)
from research.juggler_sequence.first_e_transport import (
    word_gapped_ee,
    word_gapped_eoe,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM


def test_rotation_classes_and_probe():
    assert classify_word("OOEOOOOEE") == "gapped_ee"
    assert classify_word("OOEOOOEOE") == "gapped_eoe"
    assert classify_word(rotate(word_gapped_ee(2, 4), 3)) == "bootstrap_oo"
    assert classify_word(rotate(word_gapped_ee(3, 4), 4)) == "bootstrap_ooo"
    assert classify_word(rotate(word_gapped_ee(2, 4), 8)) == "starts_even"
    assert classify_word(rotate(word_gapped_eoe(2, 3), 7)) == "starts_OE"
    assert classify_word("OEOOOOEEO") == "ends_odd"
    assert "bunched_ee" in FORBIDDEN
    assert "gapped_ee" in ALLOWED
    scan = run_probe()
    assert scan["row_count"] == 1099
    assert scan["forbidden_count"] == 0
    assert scan["all_allowed"] is True
    assert scan["originals_are_gapped"] is True
    assert scan["has_bootstrap_oo"] is True
    assert scan["has_bootstrap_ooo"] is True
    assert scan["length_eight_census"] is False
    assert scan["length_nine_census"] is False
    assert scan["first_e_at_four"] is False
    assert scan["class_counts"].get("bunched_ee", 0) == 0
    assert scan["class_counts"].get("other", 0) == 0


def test_lean_api_and_classify():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_GREEN
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    assert lean["no_cycle_itinerary_gapped_three_even_ee"] is True
    assert lean["no_cycle_itinerary_gapped_three_even_eoe"] is True
    assert lean["no_length_eight_theorem"] is True
    assert lean["no_length_nine_theorem"] is True
    assert lean["length_eight_open_in_census"] is True
    assert lean["no_bunched_tail_theorem"] is True


def test_classify_render_and_artifacts():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    text = render_markdown(
        {
            "decision": decision,
            "scan": scan,
            "lean": lean,
            "engine_control_layer_modified": False,
            "anti_overclaim": {
                **dict(ANTI_OVERCLAIM),
                "cycles_impossible": False,
                "three_even_cycles_impossible": False,
                "gapped_cycle_itinerary_lean": True,
                "length_eight_census": False,
                "length_nine_census": False,
                "first_e_at_four": False,
            },
        }
    )
    assert CLASS_GREEN in text
    assert "no_cycle_itinerary_gapped_three_even_ee" in text
    from research.juggler_sequence.gapped_cycle_itinerary import JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_gapped_cycle_itinerary"
    assert data["decision"]["classification"] == CLASS_GREEN
    assert data["anti_overclaim"]["cycles_impossible"] is False
    assert data["anti_overclaim"]["gapped_cycle_itinerary_lean"] is True
    assert data["lean"]["no_cycle_itinerary_gapped_three_even_ee"] is True
    assert data["lean"]["no_cycle_itinerary_gapped_three_even_eoe"] is True
    assert data["scan"]["length_eight_census"] is False
    assert data["scan"]["length_nine_census"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_gapped_cycle_word.md").read_text(
        encoding="utf-8"
    )
    note = (repo / "docs" / "theory" / "juggler_finite_dynamics_note.md").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "PROMOTE" in dossier
    assert "no_cycle_itinerary_gapped_three_even_ee" in dossier
    assert "no_cycle_itinerary_gapped_three_even_eoe" in dossier
    assert "no_cycle_itinerary_length_eight" in dossier
    assert "no_cycle_itinerary_length_nine" in dossier
    assert "not a length-8" in dossier or "not a length-8/9" in dossier
    assert "Theorem 3.21" in note
    assert "no_cycle_itinerary_gapped_three_even_ee" in note
    assert "remain open" not in note
    assert "theorem no_cycle_itinerary_length_eight" not in note
    assert "theorem no_cycle_itinerary_length_nine" not in note
    flat = " ".join(note.split())
    assert (
        "Theorems 3.12--3.21 assemble into an even-count exclusion: no "
        "cycle itinerary has fewer than four even letters, so a nontrivial "
        "cycle has period at least eleven (Theorem 3.22). Section 4 "
        "excludes later periods by financing."
    ) in flat

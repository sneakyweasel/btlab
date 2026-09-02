"""Front overshoot versus short-cluster undershoot. Not a halt or Z5 test."""

from __future__ import annotations

import json

from research.juggler_sequence.front_overshoot import (
    CLASS_PARK,
    DIAGNOSTIC_LEAKS,
    FORBIDDEN_THEOREMS,
    LEAN_THEOREMS,
    N_A,
    N_EEE,
    SHORT_PAIRS,
    cell_depth,
    classify,
    lean_api_present,
    locate_front,
    remaining_after_oo,
    render_markdown,
    run_probe,
    weak_floor_compatible_with_all_tails,
    write_artifacts,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM


def test_cells_and_weak_floor():
    assert SHORT_PAIRS == (
        (0, 0),
        (1, 0),
        (2, 0),
        (3, 0),
        (0, 1),
        (1, 1),
        (2, 1),
    )
    assert remaining_after_oo(0, 0) == "EEE"
    assert remaining_after_oo(3, 0) == "EOOOEE"
    assert remaining_after_oo(2, 1) == "EOOEOE"
    assert cell_depth(12, 13) == -1
    assert cell_depth(169, 13) == 0
    assert cell_depth(196, 13) == 1
    assert weak_floor_compatible_with_all_tails(13) is True


def test_diagnostic_leaks_locate():
    expected = {
        37: ("A", 76, True),
        103: ("inside_tail", 1674, False),
        113: ("A", 1942, True),
        205: ("B", 598, True),
    }
    later = 0
    for row in DIAGNOSTIC_LEAKS:
        located = locate_front(row["n"], row["word"])
        assert located is not None
        case, img, later_oo = expected[row["n"]]
        assert located["image"] == img
        assert located["oo"] is not None
        assert located["oo"]["case"] == case
        assert located["cycle"] is False
        assert located["interval"] is True
        if later_oo:
            later += 1
    assert later == 3


def test_probe_and_classify_park():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_PARK
    assert scan["weak_floor_compatible_all_tails"] is True
    assert scan["case_a"]["oo_count"] == 11
    assert scan["case_a"]["ee"] == {"above": 1, "below": 10}
    assert scan["case_a"]["eee"] == {"below": 11}
    assert scan["case_a"]["never_inside_ee"] is True
    assert scan["case_a"]["never_inside_eee"] is True
    assert scan["case_a"]["raises_above_eee_uniform"] is False
    assert scan["case_a"]["exact_remaining"] == []
    assert scan["eee"]["oo_count"] == 31
    assert scan["eee"]["eee"] == {"below": 27, "above": 4}
    assert scan["eee"]["never_inside_eee"] is True
    assert scan["words_a"]["cycle_count"] == 0
    assert scan["words_a"]["interval_count"] == 1
    assert scan["words_a"]["interval"][0]["n"] == 113
    assert scan["words_b"]["cycle_count"] == 0
    assert scan["leaks"]["later_oo"] == 3
    assert scan["leaks"]["inside_tail"] == 1
    assert scan["leaks"]["cycle_count"] == 0
    assert scan["leaks"]["shared_geometry"] is False
    assert scan["witnesses"]["count"] == 18
    assert scan["witnesses"]["all_start_below_square"] is True
    assert scan["length_eleven_census"] is False
    assert scan["z5_cells"] is False
    assert scan["four_even_assembler"] is False
    assert scan["leftover_suffix_retest"] is False
    assert scan["n_a"] == N_A
    assert scan["n_eee"] == N_EEE


def test_lean_api_without_halt_or_z5():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    for name in FORBIDDEN_THEOREMS:
        assert lean[f"has_{name}"] is False, name
    assert lean["not_in_paper_barrel"] is True
    assert lean["no_global_termination_theorem"] is True
    assert lean["no_new_lean"] is True


def test_classify_render_and_artifacts():
    payload = write_artifacts()
    text = render_markdown(payload)
    assert CLASS_PARK in text
    assert "OOOOEOOOEEOOEE" in text
    assert "(n+2)^2" in text
    from research.juggler_sequence.front_overshoot import JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_front_overshoot"
    assert data["decision"]["classification"] == CLASS_PARK
    assert data["anti_overclaim"]["cycles_impossible"] is False
    assert data["scan"]["words_a"]["cycle_count"] == 0
    assert data["scan"]["leaks"]["later_oo"] == 3
    assert dict(ANTI_OVERCLAIM)["global_termination"] is False


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_front_overshoot.md").read_text(
        encoding="utf-8"
    )
    parked = (repo / "docs" / "problems" / "juggler_bunched_short.md").read_text(
        encoding="utf-8"
    )
    pred = (repo / "docs" / "problems" / "juggler_bunched_short_front.md").read_text(
        encoding="utf-8"
    )
    note = (repo / "docs" / "theory" / "juggler_finite_dynamics_note.md").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "PARK" in dossier
    assert "first-even" in dossier.lower()
    assert "juggler_front_overshoot" in parked
    assert "juggler_front_overshoot" in pred
    assert "theorem no_cycle_itinerary_length_eleven" not in note
    assert "theorem no_cycleMin_four_even" not in note
    assert "theorem no_juggler_cycle" not in note

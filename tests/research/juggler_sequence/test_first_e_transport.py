"""First-E transport of the two-even tail. Not an engine-control or halt test."""

from __future__ import annotations

import json

from research.juggler_sequence.first_e_transport import (
    B_EE_MIN,
    B_EOE_MIN,
    CLASS_GREEN,
    K_MAX,
    LEAN_THEOREMS,
    bunched_ee_pairs,
    bunched_eoe_pairs,
    classify,
    gapped_ee_pairs,
    gapped_eoe_pairs,
    lean_api_present,
    remaining_ee,
    remaining_eoe,
    render_markdown,
    run_probe,
    seven_odd_covers_small_n,
    small_n_route,
    transport_contradiction,
    word_gapped_ee,
    word_gapped_eoe,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM
from research.juggler_sequence.uniform_two_even import shared_tail_holds


def test_gapped_vs_bunched_split():
    assert gapped_ee_pairs(9) == [(2, 4)]
    assert gapped_eoe_pairs(9) == [(2, 3)]
    assert word_gapped_ee(2, 4) == "OOEOOOOEE"
    assert word_gapped_eoe(2, 3) == "OOEOOOEOE"
    assert remaining_ee(4) == "OOOOEE"
    assert remaining_eoe(3) == "OOOEOE"
    assert bunched_ee_pairs(9) == [(3, 3), (4, 2), (5, 1), (6, 0)]
    assert bunched_eoe_pairs(9) == [(3, 2), (4, 1), (5, 0)]
    for b in range(B_EE_MIN, 10):
        assert remaining_ee(b) == "O" * b + "EE"
    for b in range(B_EOE_MIN, 10):
        assert remaining_eoe(b) == "O" * b + "EOE"
    assert seven_odd_covers_small_n(16) is False
    assert seven_odd_covers_small_n(17) is True
    for k in range(17, K_MAX + 1):
        for a, b in gapped_ee_pairs(k) + gapped_eoe_pairs(k):
            assert a >= 7 or b >= 7


def test_transport_chain_requires_y_ge_n():
    assert shared_tail_holds(256, 6) is True
    assert transport_contradiction(256, 256, 6) is True
    assert transport_contradiction(205, 256, 6) is True
    assert transport_contradiction(256, 200, 6) is False
    assert transport_contradiction(100, 80, 6) is False
    assert small_n_route(3, 7, 4) == "seven_odds_prefix"
    assert small_n_route(3, 2, 7) in {"prefix_unrealized", "seven_odds_remaining", "tail_at_y"}


def test_finite_window_empty_and_classify():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_GREEN
    assert scan["finite_count"] > 0
    assert scan["all_finite_tables_empty"] is True
    assert scan["large_k_small_n_sealed"] is True
    assert scan["length_eight_census"] is False
    assert scan["length_nine_census"] is False
    assert scan["bunched_attack"] is False
    for row in scan["finite_rows"]:
        assert row["table"]["hit_count"] == 0


def test_lean_api_without_census_or_transport_theorem():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    assert lean["no_first_e_transport_theorem"] is False
    assert lean["no_cycleMin_gapped_three_even_ee"] is True
    assert lean["no_cycleMin_gapped_three_even_eoe"] is True
    assert lean["no_length_eight_theorem"] is True
    assert lean["no_length_nine_theorem"] is True
    assert lean["length_eight_open_in_census"] is True


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
                "length_nine_census": False,
                "first_e_transport_lean": True,
            },
        }
    )
    assert CLASS_GREEN in text
    assert "OOEOOOOEE" in text
    from research.juggler_sequence.first_e_transport import JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_first_e_transport"
    assert data["decision"]["classification"] == CLASS_GREEN
    assert data["anti_overclaim"]["cycles_impossible"] is False
    assert data["lean"]["no_first_e_transport_theorem"] is False
    assert data["anti_overclaim"]["first_e_transport_lean"] is True
    assert data["lean"]["no_cycleMin_gapped_three_even_ee"] is True
    assert data["lean"]["no_cycleMin_gapped_three_even_eoe"] is True


def test_dossier_boundary():
    from pathlib import Path

    repo = Path(__file__).resolve().parents[3]
    dossier = (repo / "docs" / "problems" / "juggler_first_e_transport.md").read_text(
        encoding="utf-8"
    )
    note = (repo / "docs" / "theory" / "juggler_finite_dynamics_note.md").read_text(
        encoding="utf-8"
    )
    assert "## Branch budget" in dossier
    assert "## Decision" in dossier
    assert "PROMOTE" in dossier
    assert "no_cycleMin_gapped_three_even_ee" in dossier
    assert "no_cycle_itinerary_length_eight" in dossier
    assert "no_cycle_itinerary_length_nine" in dossier
    assert "not a length-8" in dossier or "not a length-8/9" in dossier
    assert "theorem no_cycle_itinerary_length_eight" not in note
    assert "theorem no_cycle_itinerary_length_nine" not in note

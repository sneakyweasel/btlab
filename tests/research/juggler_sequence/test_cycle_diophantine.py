"""Cycle Diophantine peak defects. Not an engine-control or halt test."""

from __future__ import annotations

from research.juggler_sequence.cycle_diophantine import (
    CLASS_R,
    CLASS_REPACK,
    FORBIDDEN_ENGINES,
    HARD_STARTS,
    LEAN_THEOREMS,
    classify,
    diophantine_of_orbit,
    lean_api_present,
    peak_defects,
    render_markdown,
    run_probe,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM


def test_nine_composition_and_slack():
    nine = diophantine_of_orbit(9)
    assert nine["pred"] == 27
    assert nine["maximum"] == 140
    assert nine["landing"] == 11
    assert nine["top_r"] == 1
    assert nine["delta"] == 83
    assert nine["eps"] == 19
    assert nine["compose_holds"] is True
    assert nine["slack_holds"] is True
    assert nine["delta_odd"] is True
    assert nine["eps_odd"] is True
    assert nine["landing_in_R"] is True
    defects = peak_defects(27, 140, 11, 1)
    assert defects["slack"] == 2 * 19 * 121 + 19 * 19 + 83


def test_hard_starts_compose_and_odd():
    for start in HARD_STARTS + (9, 77):
        row = diophantine_of_orbit(start)
        assert row["compose_holds"] is True
        assert row["slack_holds"] is True
        assert row["delta_odd"] is True
        assert row["eps_odd"] is True
        assert row["delta_pos"] is True
        assert row["eps_pos"] is True


def test_transient_can_land_in_R():
    three = diophantine_of_orbit(3)
    seven = diophantine_of_orbit(7)
    assert three["landing_in_R"] is True
    assert seven["landing_in_R"] is True


def test_lean_api_diophantine_without_engine():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    assert lean["no_all_cycles_impossible"] is True
    assert lean["no_cycle_engine"] is True
    assert lean["no_remainder_dynamics"] is True
    assert lean["no_energy"] is True
    assert lean["no_mordell_solver"] is True
    assert lean["CycleItinerary_not_rewritten"] is True
    assert lean["FloorPower_not_rewritten"] is True
    assert lean["orbit_min_not_used"] is True
    assert lean["PowerBoundEq_not_used_as_cycle_attack"] is True
    from research.juggler_sequence.cycle_diophantine import LEAN_PATH

    src = LEAN_PATH.read_text(encoding="utf-8")
    assert "sorry" not in src
    assert "admit" not in src
    assert "theorem juggler_reaches_one" not in src
    assert "theorem peak_diophantine_compose" in src
    assert "theorem peak_diophantine_slack" in src
    assert "theorem cycle_top_landing_ge_thirteen" in src
    assert "PowerBoundEq" not in src
    assert "MinimalNonTerm" not in src
    assert "PowerHeight" not in src
    assert "Mordell" not in src
    for name in FORBIDDEN_ENGINES:
        assert name not in src


def test_classify_diophantine_repackaging():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_REPACK
    assert CLASS_R in decision["secondary"]
    assert scan["n_search"] is False
    assert scan["cycle_itinerary_census"] is False
    assert scan["remainder_dynamics"] is False
    assert scan["mordell_solver"] is False
    assert scan["compose_fails"] == 0
    assert scan["residues"]["envelope_only_residues"] is True
    assert scan["landing_in_R"] >= 1
    text = render_markdown(
        {
            "decision": decision,
            "scan": scan,
            "lean": lean,
            "engine_control_layer_modified": False,
            "anti_overclaim": {
                **dict(ANTI_OVERCLAIM),
                "cycles_impossible": False,
                "stronger_than_envelope_slack": False,
            },
        }
    )
    assert CLASS_REPACK in text
    assert "slack" in text
    assert scan["basin"] == [1]


def test_committed_artifacts_schema():
    import json

    from research.juggler_sequence.cycle_diophantine import JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_cycle_diophantine"
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_REPACK
    assert data["anti_overclaim"]["cycles_impossible"] is False
    assert data["anti_overclaim"]["stronger_than_envelope_slack"] is False
    assert data["lean"]["sorry_free"] is True
    assert data["lean"]["peak_diophantine_slack"] is True
    assert data["scan"]["n_search"] is False
    assert data["scan"]["remainder_dynamics"] is False

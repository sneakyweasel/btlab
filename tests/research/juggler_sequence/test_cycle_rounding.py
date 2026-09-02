"""Cyclic rounding. Not an engine-control or halt test."""

from __future__ import annotations

from research.juggler_sequence.cycle_rounding import (
    CLASS_GREEN,
    CLASS_NEW,
    CLASS_RIGID,
    FORBIDDEN_ENGINES,
    HARD_STARTS,
    LEAN_THEOREMS,
    classify,
    lean_api_present,
    path_identity,
    path_remainders,
    remainder,
    render_markdown,
    rounding_of_orbit,
    run_probe,
)
from research.juggler_sequence.cycle_top_pred import floor_power, orbit_until_one
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM


def test_nine_remainders_and_no_amplification():
    states = orbit_until_one(9)
    rhos = path_remainders(states)
    assert remainder(9) == 0
    assert remainder(27) == 83
    assert remainder(140) == 19
    assert rhos[0] == 0
    assert rhos[1] == 83
    assert rhos[2] == 19
    assert rhos[2] < rhos[1]
    nine = rounding_of_orbit(9)
    assert nine["later_remainder_grows"] is False
    assert nine["rho_o_pos"] is True
    assert nine["rho_o"] == 83
    assert nine["rho_top_pos"] is True


def test_path_identity_and_off_cycle_correction():
    states = orbit_until_one(9)
    ident = path_identity(states)
    assert ident["rho_sum"] == ident["pows_minus_next_sq"]
    assert ident["rho_sum"] != ident["pows_minus_squares"]
    assert ident["closure_correction"] == states[0] ** 2 - states[-1] ** 2
    assert ident["balance_off_cycle"] != 0


def test_trivial_one_cycle_balance():
    ident = path_identity([1, 1])
    assert ident["rho_sum"] == 0
    assert ident["closure_correction"] == 0
    assert ident["balance_off_cycle"] == 0


def test_peak_odd_remainder_positive_on_hard_starts():
    for start in HARD_STARTS + (9, 77):
        row = rounding_of_orbit(start)
        assert row["rho_o_pos"] is True
        assert row["rho_o_odd"] is True
        assert row["path_identity_holds"] is True
        pred = row["pred"]
        maximum = row["maximum"]
        assert floor_power(pred) == maximum
        assert maximum * maximum < pred**3


def test_lean_api_rounding_without_engine():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    assert lean["no_all_cycles_impossible"] is True
    assert lean["no_cycle_engine"] is True
    assert lean["no_remainder_dynamics"] is True
    assert lean["no_energy"] is True
    assert lean["FloorPower_no_cycle_itinerary"] is True
    assert lean["orbit_min_not_used"] is True
    assert lean["PowerBoundEq_not_used_as_cycle_attack"] is True
    from research.juggler_sequence.cycle_rounding import LEAN_PATH

    src = LEAN_PATH.read_text(encoding="utf-8")
    assert "sorry" not in src
    assert "admit" not in src
    assert "theorem juggler_reaches_one" not in src
    assert "theorem cycle_remainder_balance" in src
    assert "theorem cycle_exists_pos_remainder" in src
    assert "PowerBoundEq" not in src
    assert "MinimalNonTerm" not in src
    assert "PowerHeight" not in src
    for name in FORBIDDEN_ENGINES:
        assert name not in src
    assert "theorem no_cycle_itinerary_length_six" not in src


def test_classify_rounding_green():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_GREEN
    assert CLASS_NEW in decision["secondary"]
    assert CLASS_RIGID in decision["secondary"]
    assert scan["n_search"] is False
    assert scan["cycle_itinerary_census"] is False
    assert scan["remainder_dynamics"] is False
    assert scan["local_fails"] == 0
    assert scan["nine_later_grows"] is False
    text = render_markdown(
        {
            "decision": decision,
            "scan": scan,
            "lean": lean,
            "engine_control_layer_modified": False,
            "anti_overclaim": {
                **dict(ANTI_OVERCLAIM),
                "cycles_impossible": False,
                "remainder_amplification": False,
                "remainder_dynamics": False,
            },
        }
    )
    assert CLASS_GREEN in text
    assert "remainder" in text
    assert scan["basin"] == [1]


def test_committed_artifacts_schema():
    import json

    from research.juggler_sequence.cycle_rounding import JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_cycle_rounding"
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_GREEN
    assert data["anti_overclaim"]["cycles_impossible"] is False
    assert data["anti_overclaim"]["remainder_amplification"] is False
    assert data["lean"]["sorry_free"] is True
    assert data["lean"]["cycle_remainder_balance"] is True
    assert data["scan"]["n_search"] is False
    assert data["scan"]["remainder_dynamics"] is False

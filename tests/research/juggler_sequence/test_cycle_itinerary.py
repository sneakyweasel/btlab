"""Fixed cycle-word size bounds. Not an engine-control or halt test."""

from __future__ import annotations

from research.juggler_sequence.cycle_itinerary import (
    CLASS_BOUND,
    CLASS_EXCLUDED,
    LEAN_THEOREMS,
    classify,
    expanding,
    exponent_gap,
    floor_power,
    follows_itinerary,
    image_after,
    lean_api_present,
    n_le_from_pow,
    render_markdown,
    run_probe,
    search_cycles,
    word_row,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM
from research.juggler_sequence.uniform_superquadratic import lower_denom


def test_short_expanding_classification():
    assert expanding("O") is True
    assert expanding("E") is False
    assert expanding("OE") is False
    assert expanding("OO") is True
    assert expanding("OOE") is True
    assert expanding("OEO") is True
    assert expanding("EOO") is True


def test_lower_denom_and_tight_bounds():
    assert lower_denom("O") == 4
    assert lower_denom("OO") == 1024
    assert lower_denom("OOE") == 262144
    assert n_le_from_pow(4, 1) == 4
    assert n_le_from_pow(1024, 5) == 4
    assert n_le_from_pow(262144, 1) == 262144
    assert n_le_from_pow(2**38, 1) == 2**38
    assert exponent_gap("OOE") == 1


def test_no_small_cycles_on_excluded_words():
    assert search_cycles("O", 4) == []
    assert search_cycles("OO", 4) == []
    assert search_cycles("OOO", 4) == []
    assert follows_itinerary(3, "O")
    assert image_after(3, "O") == 5
    assert follows_itinerary(2, "EOO")
    assert image_after(2, "EOO") == 1


def test_ooe_no_cycle_on_small_prefix():
    assert search_cycles("OOE", 200) == []
    row = word_row("OOE", search_cap=200)
    assert row["hits"] == []
    assert row["n_le"] == 262144


def test_lean_api_no_universal_cycle_ban():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    assert lean["no_all_cycles_impossible"] is True
    assert lean["no_cycle_engine"] is True
    assert lean["FloorPower_not_rewritten"] is True
    assert lean["PowerBoundEq_not_used_as_cycle_attack"] is True
    from research.juggler_sequence.cycle_itinerary import LEAN_PATH

    src = LEAN_PATH.read_text(encoding="utf-8")
    assert "sorry" not in src
    assert "admit" not in src
    assert "theorem juggler_reaches_one" not in src
    assert "def CycleItinerary" in src
    assert "theorem cycle_pow_le_lowerDenom" in src
    assert "PowerBoundEq" not in src


def test_classify_cycle_bound_green():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_BOUND
    assert CLASS_EXCLUDED in decision["secondary"]
    text = render_markdown(
        {
            "decision": decision,
            "scan": scan,
            "lean": lean,
            "engine_control_layer_modified": False,
            "anti_overclaim": {
                **dict(ANTI_OVERCLAIM),
                "cycles_impossible": False,
                "cycle_is_envelope_equality": False,
            },
        }
    )
    assert CLASS_BOUND in text
    assert "cycle_is_envelope_equality" in text
    assert scan["basin"] == [1]


def test_committed_artifacts_schema():
    import json

    from research.juggler_sequence.cycle_itinerary import JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_cycle_itinerary"
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_BOUND
    assert data["anti_overclaim"]["cycles_impossible"] is False
    assert data["anti_overclaim"]["cycle_is_envelope_equality"] is False
    assert data["anti_overclaim"]["global_termination"] is False
    assert data["lean"]["sorry_free"] is True


def test_floor_power_unchanged():
    assert floor_power(1) == 1
    assert floor_power(3) == 5
    assert floor_power(9) == 27
    assert floor_power(36) == 6

"""Exact cycle-word arithmetic. Not an engine-control or halt test."""

from __future__ import annotations

from research.juggler_sequence.cycle_arith import (
    CLASS_OEO,
    CLASS_OOE,
    CLASS_STRUCT,
    LEAN_THEOREMS,
    classify,
    even_descends,
    floor_power,
    follows_itinerary,
    image_after,
    last_even_cell,
    last_even_is_exact_square,
    lean_api_present,
    render_markdown,
    rotate_itinerary,
    run_probe,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM


def test_last_even_is_a_cell_not_a_square():
    lo, hi = last_even_cell(5)
    assert lo == 25
    assert hi == 36
    assert last_even_is_exact_square(3, "OOE") is None
    assert follows_itinerary(3, "OO")
    assert image_after(3, "OO") == 11
    assert 11 % 2 == 1
    for n in range(3, 40, 2):
        assert last_even_is_exact_square(n, "OOE") is not True


def test_oeo_rotates_onto_eoo():
    assert rotate_itinerary("OEO") == "EOO"
    assert rotate_itinerary("OOE") == "OEO"
    assert rotate_itinerary("EOO") == "OOE"


def test_even_states_descend():
    assert even_descends(2)
    assert even_descends(12)
    assert even_descends(144)
    assert floor_power(2) == 1
    assert not even_descends(3)
    assert not even_descends(1)


def test_no_small_ooe_or_oeo_cycle():
    scan = run_probe()
    assert scan["ooe_hits"] == []
    assert scan["oeo_hits"] == []
    assert scan["ooe_three_follows"] is False
    assert scan["oeo_rotates_to_eoo"] is True
    assert scan["last_even_exact_square_hits"] == []


def test_lean_api_excludes_ooe_oeo_without_engine():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    assert lean["no_all_cycles_impossible"] is True
    assert lean["no_cycle_engine"] is True
    assert lean["FloorPower_not_rewritten"] is True
    assert lean["MinimalNonTerm_not_rewritten"] is True
    assert lean["PowerBoundEq_not_used_as_cycle_attack"] is True
    assert lean["no_exact_square_identity"] is True
    from research.juggler_sequence.cycle_arith import LEAN_PATH

    src = LEAN_PATH.read_text(encoding="utf-8")
    assert "sorry" not in src
    assert "admit" not in src
    assert "theorem juggler_reaches_one" not in src
    assert "theorem no_cycle_itinerary_ooe" in src
    assert "theorem no_cycle_itinerary_oeo" in src
    assert "theorem exists_cycle_min_odd" in src
    assert "PowerBoundEq" not in src
    assert "MinimalNonTerm" not in src


def test_classify_ooe_excluded():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_OOE
    assert CLASS_OEO in decision["secondary"]
    assert CLASS_STRUCT in decision["secondary"]
    text = render_markdown(
        {
            "decision": decision,
            "scan": scan,
            "lean": lean,
            "engine_control_layer_modified": False,
            "anti_overclaim": {
                **dict(ANTI_OVERCLAIM),
                "cycles_impossible": False,
                "last_even_is_exact_square": False,
            },
        }
    )
    assert CLASS_OOE in text
    assert "last_even_is_exact_square" in text
    assert scan["basin"] == [1]


def test_committed_artifacts_schema():
    import json

    from research.juggler_sequence.cycle_arith import JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_cycle_arith"
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_OOE
    assert data["anti_overclaim"]["cycles_impossible"] is False
    assert data["anti_overclaim"]["last_even_is_exact_square"] is False
    assert data["anti_overclaim"]["global_termination"] is False
    assert data["lean"]["sorry_free"] is True
    assert data["lean"]["no_cycle_itinerary_ooe"] is True
    assert data["lean"]["no_cycle_itinerary_oeo"] is True

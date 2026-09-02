"""E-terminating threshold inventory. Not an engine-control or halt test."""

from __future__ import annotations

from research.juggler_sequence.cycle_e_threshold import (
    CLASS_COVER,
    CLASS_INHERIT,
    CLASS_LEN5,
    INVENTORY,
    LEAN_THEOREMS,
    classify,
    expanding,
    lean_api_present,
    length5_e_words,
    render_markdown,
    run_probe,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM


def test_inventory_separates_exact_eventual_and_cell():
    kinds = {row["kind"] for row in INVENTORY}
    assert kinds == {"exact", "inherited", "eventual", "cell-specific"}
    exact = [row for row in INVENTORY if row["kind"] == "exact"]
    assert {row["suffix"] for row in exact} == {"OO", "OOO"}
    assert any(row["suffix"] == "O^a (a≥3)" for row in INVENTORY)


def test_only_ooooe_is_expanding_among_length5_e():
    words = length5_e_words()
    assert len(words) == 16
    assert all(w.endswith("E") and len(w) == 5 for w in words)
    assert expanding("OOOOE") is True
    assert expanding("OOOEE") is False
    assert expanding("OOEOE") is False
    assert [w for w in words if expanding(w)] == ["OOOOE"]


def test_lean_api_inheritance_and_length5():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    assert lean["no_all_cycles_impossible"] is True
    assert lean["no_cycle_engine"] is True
    assert lean["no_length_six"] is True
    assert lean["FloorPower_not_rewritten"] is True
    assert lean["MinimalNonTerm_not_rewritten"] is True
    assert lean["PowerBoundEq_not_used_as_cycle_attack"] is True
    from research.juggler_sequence.cycle_e_threshold import LEAN_PATH

    src = LEAN_PATH.read_text(encoding="utf-8")
    assert "sorry" not in src
    assert "admit" not in src
    assert "theorem juggler_reaches_one" not in src
    assert "theorem threshold_inherits_odd_append" in src
    assert "theorem no_cycle_itinerary_length_five_ends_even" in src
    assert "PowerBoundEq" not in src
    assert "MinimalNonTerm" not in src


def test_classify_coverage_green():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_COVER
    assert CLASS_INHERIT in decision["secondary"]
    assert CLASS_LEN5 in decision["secondary"]
    assert scan["unique_expanding_is_ooooe"] is True
    text = render_markdown(
        {
            "decision": decision,
            "scan": scan,
            "lean": lean,
            "engine_control_layer_modified": False,
            "anti_overclaim": {
                **dict(ANTI_OVERCLAIM),
                "cycles_impossible": False,
                "useful_uniform_Q0": False,
            },
        }
    )
    assert CLASS_COVER in text
    assert "useful_uniform_Q0" in text
    assert scan["basin"] == [1]


def test_committed_artifacts_schema():
    import json

    from research.juggler_sequence.cycle_e_threshold import JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_cycle_e_threshold"
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_COVER
    assert data["anti_overclaim"]["cycles_impossible"] is False
    assert data["anti_overclaim"]["useful_uniform_Q0"] is False
    assert data["anti_overclaim"]["O_terminating_cycles_impossible"] is False
    assert data["lean"]["sorry_free"] is True
    assert data["lean"]["no_cycle_itinerary_length_five_ends_even"] is True
    assert data["scan"]["length5_expanding"] == ["OOOOE"]

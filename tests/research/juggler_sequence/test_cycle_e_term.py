"""E-terminating cycle exclusion. Not an engine-control or halt test."""

from __future__ import annotations

from research.juggler_sequence.cycle_e_term import (
    CLASS_LAST,
    CLASS_LEN4,
    LEAN_THEOREMS,
    classify,
    classify_words,
    expanding,
    lean_api_present,
    length4_e_words,
    render_markdown,
    run_probe,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM


def test_only_oooe_is_expanding_among_length4_e():
    words = length4_e_words()
    assert len(words) == 8
    assert all(w.endswith("E") and len(w) == 4 for w in words)
    assert expanding("OOOE") is True
    assert expanding("OEOE") is False
    assert expanding("OOEE") is False
    assert expanding("OEEE") is False
    expanding_words = [w for w in words if expanding(w)]
    assert expanding_words == ["OOOE"]
    rows = classify_words()
    assert [row["word"] for row in rows if row["expanding"]] == ["OOOE"]


def test_lean_api_generic_threshold_and_length4():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True, name
    assert lean["no_all_cycles_impossible"] is True
    assert lean["no_cycle_engine"] is True
    assert lean["FloorPower_not_rewritten"] is True
    assert lean["MinimalNonTerm_not_rewritten"] is True
    assert lean["PowerBoundEq_not_used_as_cycle_attack"] is True
    assert lean["O_terminating_not_claimed"] is True
    from research.juggler_sequence.cycle_e_term import LEAN_PATH

    src = LEAN_PATH.read_text(encoding="utf-8")
    assert "sorry" not in src
    assert "admit" not in src
    assert "theorem juggler_reaches_one" not in src
    assert "theorem no_cycle_append_even_of_suffix_threshold" in src
    assert "theorem no_cycle_itinerary_oooe" in src
    assert "theorem no_cycle_itinerary_length_four_ends_even" in src
    assert "PowerBoundEq" not in src
    assert "MinimalNonTerm" not in src


def test_classify_last_even_class():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_LAST
    assert CLASS_LEN4 in decision["secondary"]
    assert scan["unique_expanding_is_oooe"] is True
    text = render_markdown(
        {
            "decision": decision,
            "scan": scan,
            "lean": lean,
            "engine_control_layer_modified": False,
            "anti_overclaim": {
                **dict(ANTI_OVERCLAIM),
                "cycles_impossible": False,
                "O_terminating_cycles_impossible": False,
            },
        }
    )
    assert CLASS_LAST in text
    assert "O_terminating_cycles_impossible" in text
    assert scan["basin"] == [1]


def test_committed_artifacts_schema():
    import json

    from research.juggler_sequence.cycle_e_term import JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_cycle_e_term"
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_LAST
    assert data["anti_overclaim"]["cycles_impossible"] is False
    assert data["anti_overclaim"]["O_terminating_cycles_impossible"] is False
    assert data["anti_overclaim"]["global_termination"] is False
    assert data["lean"]["sorry_free"] is True
    assert data["lean"]["no_cycle_itinerary_oooe"] is True
    assert data["scan"]["expanding"] == ["OOOE"]

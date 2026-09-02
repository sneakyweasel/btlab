"""Superquadratic suffix thresholds. Not an engine-control test."""

from __future__ import annotations

from research.juggler_sequence.lean_paths import juggler_text

from research.juggler_sequence.compensated_contraction import follows_itinerary, image_after
from research.juggler_sequence.superquadratic_suffixes import (
    CLASS_EVENTUAL,
    LEAN_THEOREMS,
    classify,
    is_superquadratic,
    lean_api_present,
    render_markdown,
    run_probe,
    scan_suffix,
    superquadratic_words,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, LEAN_PATH, floor_power


def test_superquadratic_predicate_and_short_q():
    assert is_superquadratic("OO")
    assert is_superquadratic("OOO")
    assert is_superquadratic("EOOOO")
    assert not is_superquadratic("O")
    assert not is_superquadratic("EO")
    assert not is_superquadratic("EOO")
    oo = scan_suffix("OO", q_max=40)
    ooo = scan_suffix("OOO", q_max=40)
    assert oo["Q"] == [1, 3]
    assert ooo["Q"] == [1]
    assert follows_itinerary(5, "OO")
    assert image_after(5, "OO") >= 36


def test_scan_has_no_large_contracting_q():
    words = superquadratic_words(k_max=5)
    assert "OO" in words and "EOOOO" in words
    scan = run_probe(k_max=5, q_max=40, q_max_heavy=40)
    for item in scan["suffixes"]:
        q = item["largest_contracting_q"]
        assert q is None or q <= 3


def test_examples_and_lean_api():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    assert lean["LowerPowerBound"] is True
    for name in LEAN_THEOREMS:
        if name == "LowerPowerBound":
            continue
        assert lean[name] is True
    text = juggler_text()
    assert "PowerHeight" not in text
    assert "sorry" not in text
    assert "admit" not in text
    assert "structure LowerEnvelope" not in text


def test_classify_eventual_on_small_probe():
    scan = run_probe(k_max=4, q_max=40, q_max_heavy=40)
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_EVENTUAL
    payload = {
        "decision": decision,
        "scan": scan,
        "lean": lean,
        "engine_control_layer_modified": False,
        "anti_overclaim": dict(ANTI_OVERCLAIM),
    }
    text = render_markdown(payload)
    assert CLASS_EVENTUAL in text
    assert "global_termination" in text


def test_committed_artifacts_schema():
    import json

    from research.juggler_sequence.superquadratic_suffixes import JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_superquadratic_suffixes"
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_EVENTUAL
    assert data["lean"]["sorry_free"] is True
    assert data["lean"]["eventually_no_first_even_contraction"] is True


def test_floor_power_unchanged():
    assert floor_power(3) == 5
    assert floor_power(5) == 11
    assert floor_power(2) == 1

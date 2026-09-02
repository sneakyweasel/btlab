"""First-even suffix thresholds. Not an engine-control test."""

from __future__ import annotations

from research.juggler_sequence.lean_paths import juggler_text

from research.juggler_sequence.compensated_contraction import follows_itinerary, image_after
from research.juggler_sequence.first_even_thresholds import (
    CLASS_FINITE,
    LEAN_THEOREMS,
    cell_bounds,
    classify,
    formal_alpha,
    lean_api_present,
    regime,
    render_markdown,
    run_probe,
    scan_suffix,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, LEAN_PATH, floor_power


def test_integer_any_contraction_is_off_by_one():
    lo, hi = cell_bounds(3)
    assert (lo, hi) == (9, 16)
    assert regime(3, 11) == "mixed"
    assert regime(3, 15) == "all_expand"
    assert 15 < 16
    assert not (15 + 1 < 16)


def test_oo_and_ooo_finite_q():
    oo = scan_suffix("OO", q_max=40)
    ooo = scan_suffix("OOO", q_max=40)
    assert formal_alpha("OO")["gt_two"] is True
    assert formal_alpha("OOO")["gt_two"] is True
    assert oo["Q"] == [1, 3]
    assert ooo["Q"] == [1]
    assert oo["mono_breaks"] == []
    assert ooo["mono_breaks"] == []
    assert image_after(1, "OO") == 1
    assert image_after(3, "OO") == 11
    assert image_after(3, "OOO") == 36
    assert follows_itinerary(3, "OO")
    assert follows_itinerary(3, "OOO")


def test_o_is_infinite_but_not_positive_drift():
    odd = scan_suffix("O", q_max=40)
    assert formal_alpha("O")["gt_two"] is False
    assert odd["Q"] == [q for q in range(1, 41, 2)]
    assert formal_alpha("EO")["ev_positive_drift"] is False


def test_examples_and_lean_api():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True
    assert lean["certificate_present"] is True
    text = juggler_text()
    assert "PowerHeight" not in text
    assert "sorry" not in text
    assert "admit" not in text


def test_classify_finite_on_small_probe():
    scan = run_probe(q_max=40)
    lean = lean_api_present()
    decision = classify(scan, lean)
    assert decision["classification"] == CLASS_FINITE
    payload = {
        "decision": decision,
        "scan": scan,
        "lean": lean,
        "engine_control_layer_modified": False,
        "anti_overclaim": dict(ANTI_OVERCLAIM),
    }
    text = render_markdown(payload)
    assert CLASS_FINITE in text
    assert "global_termination" in text


def test_committed_artifacts_schema():
    import json

    from research.juggler_sequence.first_even_thresholds import JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_first_even_thresholds"
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_FINITE
    assert data["lean"]["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert data["lean"][name] is True


def test_floor_power_unchanged():
    assert floor_power(3) == 5
    assert floor_power(5) == 11
    assert floor_power(11) == 36

"""Uniform superquadratic thresholds. Not an engine-control test."""

from __future__ import annotations

from research.juggler_sequence.lean_paths import juggler_text

from research.juggler_sequence.compensated_contraction import follows_itinerary, image_after
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, LEAN_PATH, floor_power
from research.juggler_sequence.uniform_superquadratic import (
    CLASS_COUNTER,
    LEAN_THEOREMS,
    classify,
    collapse_family,
    collapse_q,
    even_tower_odd_tail,
    is_superquadratic,
    lean_api_present,
    lower_denom,
    q_contracts,
    render_markdown,
    run_probe,
)


def test_short_word_q_max_not_controlled_by_margin_alone():
    assert is_superquadratic("OO")
    assert is_superquadratic("EOOOO")
    assert q_contracts(3, "OO")
    assert q_contracts(2, "EOOOO")
    assert not q_contracts(5, "OO")
    assert follows_itinerary(3, "OO")
    assert image_after(3, "OO") == 11


def test_same_r_o_order_changes_q_max_and_D():
    eoooo = lower_denom("EOOOO")
    ooooe = lower_denom("OOOOE")
    assert eoooo.bit_length() > ooooe.bit_length()
    assert q_contracts(2, "EOOOO")
    assert not q_contracts(2, "OOOOE")


def test_even_tower_collapse_family():
    for k in (2, 3, 4):
        o = 3 * k
        word = even_tower_odd_tail(k, o)
        q = collapse_q(k)
        assert is_superquadratic(word)
        assert follows_itinerary(q, word)
        assert image_after(q, word) == 1
        assert q_contracts(q, word)
        assert q == 2 ** (2 ** (k - 1))
    family = collapse_family(k_max=4)
    assert family[0]["q"] == 4
    assert family[-1]["q"] == 256
    assert family[-1]["q"] > family[0]["q"]


def test_examples_and_lean_api():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True
    text = juggler_text()
    assert "PowerHeight" not in text
    assert "sorry" not in text
    assert "admit" not in text
    assert "structure LowerEnvelope" not in text
    assert "theorem uniform_first_even_threshold" not in text
    assert "theorem changing_suffix_unbounded_contraction" in text
    assert "theorem eventually_no_first_even_contraction" in text


def test_classify_counterexample():
    scan = run_probe(k_max=4, q_max=20, family_k_max=4)
    lean = lean_api_present()
    decision = classify(scan["collapse_family"], lean)
    assert decision["classification"] == CLASS_COUNTER
    payload = {
        "decision": decision,
        "scan": scan,
        "lean": lean,
        "engine_control_layer_modified": False,
        "anti_overclaim": dict(ANTI_OVERCLAIM),
    }
    text = render_markdown(payload)
    assert CLASS_COUNTER in text
    assert "global_termination" in text


def test_committed_artifacts_schema():
    import json

    from research.juggler_sequence.uniform_superquadratic import JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_uniform_thresholds"
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_COUNTER
    assert data["lean"]["sorry_free"] is True
    assert data["lean"]["changing_suffix_unbounded_contraction"] is True
    assert data["lean"]["eventually_no_first_even_contraction"] is True


def test_floor_power_unchanged():
    assert floor_power(3) == 5
    assert floor_power(5) == 11
    assert floor_power(2) == 1
    assert floor_power(16) == 4

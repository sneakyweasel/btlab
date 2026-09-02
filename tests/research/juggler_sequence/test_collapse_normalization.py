"""Collapse normalization. Not an engine-control test."""

from __future__ import annotations

from research.juggler_sequence.lean_paths import juggler_text

from research.juggler_sequence.collapse_normalization import (
    CLASS_WEAK,
    LEAN_THEOREMS,
    classify,
    collapse_on_pow_two,
    even_tower_residuals,
    initial_even_run,
    is_superquadratic,
    lean_api_present,
    max_even_run,
    odd_internal_collapse,
    q_contracts,
    render_markdown,
    run_probe,
    strip_initial_even,
)
from research.juggler_sequence.compensated_contraction import follows_itinerary, image_after
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, LEAN_PATH, floor_power


def test_decomposition_and_pow_two_identity():
    assert initial_even_run("EEEOO") == 3
    assert strip_initial_even("EEEOO") == "OO"
    assert initial_even_run("OEEE") == 0
    assert strip_initial_even("OEEE") == "OEEE"
    assert "E" * 3 + "OO" == "EEEOO"
    row = collapse_on_pow_two(2, 3, "")
    assert row["q"] == 2 ** 8
    assert row["follows_q"] is True
    assert row["image_q"] == row["image_a"] == 2
    row_e = collapse_on_pow_two(2, 2, "E")
    assert row_e["q"] == 2 ** 4
    assert row_e["follows_q"] is True
    assert row_e["image_q"] == row_e["image_a"] == 1


def test_even_tower_is_residual_one():
    rows = even_tower_residuals(k_max=4)
    assert rows[0]["q"] == 4
    assert rows[0]["residual_state"] == 1
    assert rows[-1]["q"] == 256
    assert all(row["residual_state"] == 1 and row["contracts"] for row in rows)


def test_internal_collapse_has_initial_run_zero():
    assert is_superquadratic("OEEE" + "O" * 9)
    assert initial_even_run("OEEE" + "O" * 9) == 0
    assert max_even_run("OEEE" + "O" * 9) == 3
    assert q_contracts(7, "OEEE" + "O" * 9)
    assert image_after(7, "OEEE" + "O" * 9) == 1
    assert follows_itinerary(7, "OEEE" + "O" * 9)
    internal = odd_internal_collapse(q_max=400)
    ks = {row["k"] for row in internal}
    assert 3 in ks and 4 in ks
    assert all(row["initial_even_run"] == 0 for row in internal)
    assert internal[-1]["q"] > internal[0]["q"]


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
    assert "theorem bounded_collapse_eventual_noncontraction" not in text
    assert "theorem collapse_on_pow_two" in text
    assert "theorem eventually_no_first_even_contraction" in text


def test_classify_too_weak():
    scan = run_probe(q_max=400)
    lean = lean_api_present()
    decision = classify(scan["identity_ok"], scan["internal_collapse"], lean)
    assert decision["classification"] == CLASS_WEAK
    payload = {
        "decision": decision,
        "scan": scan,
        "lean": lean,
        "engine_control_layer_modified": False,
        "anti_overclaim": dict(ANTI_OVERCLAIM),
    }
    text = render_markdown(payload)
    assert CLASS_WEAK in text
    assert "global_termination" in text


def test_committed_artifacts_schema():
    import json

    from research.juggler_sequence.collapse_normalization import JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_collapse_normalization"
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_WEAK
    assert data["lean"]["sorry_free"] is True
    assert data["lean"]["collapse_on_pow_two"] is True
    assert data["scan"]["identity_ok"] is True


def test_floor_power_unchanged():
    assert floor_power(7) == 18
    assert floor_power(18) == 4
    assert floor_power(2) == 1
    assert floor_power(16) == 4

"""Internal even-run collapse. Not an engine-control test."""

from __future__ import annotations

from research.juggler_sequence.lean_paths import juggler_text

from research.juggler_sequence.compensated_contraction import follows_itinerary, image_after
from research.juggler_sequence.internal_collapse import (
    CLASS_RUN,
    LEAN_THEOREMS,
    classify,
    collapse_events,
    is_superquadratic,
    lean_api_present,
    max_even_run,
    nested_r3_family,
    q_contracts,
    render_markdown,
    run_probe,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, LEAN_PATH, floor_power


def test_internal_run_factors_and_basin_one():
    word = "EEOEEE" + "O" * 12
    assert max_even_run(word) == 3
    assert is_superquadratic(word)
    assert q_contracts(2500, word)
    assert image_after(2500, word) == 1
    events = collapse_events(2500, word)
    assert events[0]["entry"] == 2500
    assert events[0]["exit"] == 7
    assert events[1]["entry"] == 18
    assert events[1]["exit"] == 1
    assert image_after(1, "O" * 12) == 1


def test_nested_family_grows_at_fixed_max_run():
    family = nested_r3_family()
    assert family[0]["q"] == 7
    assert family[1]["q"] == 2500
    assert family[2]["q"] == 6_250_000
    assert family[3]["q_bit_length"] == 121
    assert all(row["max_even_run"] == 3 and row["T"] == 1 and row["contracts"] for row in family)
    assert follows_itinerary(7, "OEEE" + "O" * 9)


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
    assert "theorem nested_even_collapse_2500" in text
    assert "theorem eventually_no_first_even_contraction" in text


def test_classify_bounded_run():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan["nested_family"], lean)
    assert decision["classification"] == CLASS_RUN
    payload = {
        "decision": decision,
        "scan": scan,
        "lean": lean,
        "engine_control_layer_modified": False,
        "anti_overclaim": dict(ANTI_OVERCLAIM),
    }
    text = render_markdown(payload)
    assert CLASS_RUN in text
    assert "global_termination" in text


def test_committed_artifacts_schema():
    import json

    from research.juggler_sequence.internal_collapse import JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_internal_collapse"
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_RUN
    assert data["lean"]["sorry_free"] is True
    assert data["lean"]["internal_even_collapse"] is True
    assert data["scan"]["nested_family"][1]["q"] == 2500


def test_floor_power_unchanged():
    assert floor_power(2500) == 50
    assert floor_power(50) == 7
    assert floor_power(7) == 18
    assert floor_power(2) == 1

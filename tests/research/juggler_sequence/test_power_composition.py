"""One-sided floor-power composition. Not an engine-control test."""

from __future__ import annotations

from research.juggler_sequence.lean_paths import juggler_text

from research.juggler_sequence.power_composition import (
    CLASS_GREEN,
    LEAN_CONTRACTS,
    LEAN_EMPTY,
    LEAN_EVEN,
    LEAN_FOLLOWS,
    LEAN_ODD,
    append_even_algebra,
    append_odd_algebra,
    classify,
    gap_record,
    itinerary,
    lean_api_present,
    power_bound_holds,
    render_markdown,
    run_near_equality,
    square_towers,
    word_of,
)
from research.juggler_sequence.power_itineraries import (
    ANTI_OVERCLAIM,
    LEAN_PATH,
    WORD_OOOEE,
    cmp_pow,
    floor_power,
)


def test_square_tower_equality_is_non_strict():
    assert 4 in square_towers(20)
    assert 16 in square_towers(20)
    rec = gap_record(4, "E", 2)
    assert rec["equality"] is True
    assert rec["onesided_holds"] is True
    rec16 = gap_record(16, "EE", floor_power(floor_power(16)))
    assert rec16["equality"] is True


def test_append_algebra_on_realized_states():
    assert append_even_algebra(4, 4, 0, 0) is True
    assert append_odd_algebra(3, 3, 0, 0) is True
    assert append_even_algebra(4, 4, 1, 0) is True


def test_oooee_and_oe_weak_bounds():
    assert power_bound_holds(3, WORD_OOOEE) is True
    path = itinerary(3, 5)
    assert word_of(path) == WORD_OOOEE
    assert cmp_pow(path[-1], 32, 3, 27) <= 0
    assert power_bound_holds(11, "OE") is True
    assert power_bound_holds(2, "EO") is True


def test_n1_equality_not_strict_contraction():
    rec = gap_record(1, "OOO", 1)
    assert rec["equality"] is True
    assert rec["onesided_holds"] is True


def test_near_equality_focus_has_no_onesided_failure():
    near = run_near_equality(n_max=400, k_max=5)
    assert near["onesided_failure_count"] == 0
    assert near["mixed_equalities"] == []
    assert near["above_tower_onesided"] is True
    assert near["append_even_check"] is True
    assert near["append_odd_check"] is True


def test_lean_api_and_instances_present():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    assert lean[LEAN_EMPTY] is True
    assert lean[LEAN_EVEN] is True
    assert lean[LEAN_ODD] is True
    assert lean[LEAN_FOLLOWS] is True
    assert lean[LEAN_CONTRACTS] is True
    assert lean["oooee_intact"] is True
    assert lean["oooeeeoo_intact"] is True
    text = juggler_text()
    assert "theorem floorPower_oooee_of_follows" in text
    assert "theorem floorPower_oooeeeoo_of_follows" in text
    assert "sorry" not in text


def test_committed_artifacts_schema():
    import json
    from research.juggler_sequence.power_composition import JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_GREEN
    assert data["near_equality"]["onesided_failure_count"] == 0
    assert data["near_equality"]["mixed_equalities"] == []
    assert data["lean"]["power_bound_follows"] is True
    assert data["anti_overclaim"]["global_termination"] is False


def test_payload_anti_overclaim_and_classification_when_lean_present():
    near = run_near_equality(n_max=80, k_max=4)
    lean = lean_api_present()
    decision = classify(near, lean)
    assert decision["classification"] == CLASS_GREEN
    payload = {
        "decision": decision,
        "near_equality": near,
        "lean": lean,
        "engine_control_layer_modified": False,
        "anti_overclaim": dict(ANTI_OVERCLAIM),
    }
    text = render_markdown(payload)
    assert CLASS_GREEN in text
    assert "global_termination" in text
    assert all(v is False for v in ANTI_OVERCLAIM.values())

"""Finite-progress coverage. Not an engine-control test and not a halt test."""

from __future__ import annotations

from research.juggler_sequence.compensated_contraction import follows_itinerary, image_after
from research.juggler_sequence.oo_descent_density import window_census
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power
from research.juggler_sequence.progress_coverage import (
    CLASS_FRONTIER,
    CLASS_RESIDUAL,
    CLASS_SPINE,
    LEAN_THEOREMS,
    classify,
    coverage_bucket,
    coverage_census,
    first_even_residual,
    is_odd_odd,
    lean_api_present,
    render_markdown,
    run_probe,
)


def test_even_and_oe_are_automatic_progress():
    assert coverage_bucket(2) == "EVEN_PROGRESS"
    assert floor_power(2) == 1
    assert coverage_bucket(13) == "OE_PROGRESS"
    assert follows_itinerary(13, "OE")
    assert image_after(13, "OE") == 6
    assert 6 < 13
    assert coverage_bucket(7) == "OE_PROGRESS"


def test_odd_odd_is_the_leftover_class():
    assert is_odd_odd(3)
    assert is_odd_odd(5)
    assert is_odd_odd(25)
    assert not is_odd_odd(13)
    assert not is_odd_odd(2)
    assert coverage_bucket(3) == "ODD_ODD"
    assert floor_power(3) == 5
    assert 5 > 3


def test_first_even_from_odd_odd_stays_above_start():
    row = first_even_residual(5)
    assert row is not None
    assert row["a"] == 2
    assert row["xa"] == 36
    assert row["y"] == 6
    assert row["kind"] == "FIRST_EVEN_STAYS_ABOVE_START"
    row25 = first_even_residual(25)
    assert row25 is not None
    assert row25["a"] == 3
    assert row25["y"] == 228
    assert 228 >= 25


def test_census_odd_odd_never_descends_at_first_even():
    census = coverage_census()
    assert census["even_progress"] == 40
    assert census["oe_progress"] == 21
    assert census["odd_odd"] == 18
    assert census["first_even_descent"] == 0
    assert census["stay_above_start"] == 18
    assert census["no_even_horizon"] == 0
    assert 2 in census["a_values"]


def test_lean_api_no_halt():
    lean = lean_api_present()
    assert lean["sorry_free"] is True
    for name in LEAN_THEOREMS:
        assert lean[name] is True
    assert lean["no_global_termination_theorem"] is True
    assert lean["no_all_finiteProgress_proved"] is True
    assert lean["FloorPower_not_rewritten"] is True
    from research.juggler_sequence.progress_coverage import LEAN_PATH

    src = LEAN_PATH.read_text(encoding="utf-8")
    assert "sorry" not in src
    assert "admit" not in src
    assert "theorem reachesOne_of_all_finiteProgress" in src
    assert "theorem juggler_reaches_one" not in src


def test_classify_odd_odd_frontier():
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan["census"], lean)
    assert decision["classification"] == CLASS_FRONTIER
    assert CLASS_SPINE in decision["secondary"]
    assert CLASS_RESIDUAL in decision["secondary"]
    text = render_markdown(
        {
            "decision": decision,
            "scan": scan,
            "lean": lean,
            "engine_control_layer_modified": False,
            "anti_overclaim": {
                **dict(ANTI_OVERCLAIM),
                "finite_progress_for_all": False,
            },
        }
    )
    assert CLASS_FRONTIER in text
    assert "finite_progress_for_all" in text
    assert scan["basin"] == [1]


def test_committed_artifacts_schema():
    import json

    from research.juggler_sequence.progress_coverage import JSON_PATH

    assert JSON_PATH.is_file()
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["experiment"] == "juggler_progress_coverage"
    assert data["engine_control_layer_modified"] is False
    assert data["decision"]["classification"] == CLASS_FRONTIER
    assert data["anti_overclaim"]["finite_progress_for_all"] is False
    assert data["anti_overclaim"]["global_termination"] is False
    assert data["lean"]["sorry_free"] is True


def test_floor_power_unchanged():
    assert floor_power(1) == 1
    assert floor_power(2) == 1
    assert floor_power(3) == 5
    assert floor_power(13) == 46
    assert floor_power(46) == 6


def test_horizon20_first_return_n1000_exact_census():
    """Check the exact census path against a direct implementation."""

    def first_return(n: int, horizon: int) -> int | None:
        x = n
        for _ in range(horizon):
            x = floor_power(x)
            if x < n:
                return True
        return None

    oo = 0
    oo_drop = 0
    all_drop = 0
    for n in range(2, 1001):
        is_oo = n % 2 == 1 and floor_power(n) % 2 == 1
        if is_oo:
            oo += 1
        dropped = first_return(n, 20) is not None
        if dropped:
            all_drop += 1
            if is_oo:
                oo_drop += 1
    assert oo == 252
    assert oo_drop == 221
    assert all_drop == 968
    row = window_census(1_000, snapshots=(1_000,))[0]
    assert (row["oo"], row["oo_return_20"], row["all_return_20"]) == (
        oo,
        oo_drop,
        all_drop,
    )
    assert row["unresolved_through_20"] == 0

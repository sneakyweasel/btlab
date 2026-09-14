"""Tests for ``barrier_collapse``: the barrier word, its value, and the deficit."""

from __future__ import annotations

import json
import math

from research.juggler_sequence.barrier_collapse import (
    LOG2_3,
    N0_LEAN,
    SUMMARY,
    barrier_depth,
    composite,
    floor_power,
    itinerary,
    level_weights,
    min_prefix_walk,
    odd_share,
    scale_L,
    survey,
    value_range,
    witness,
)
from research.juggler_sequence.lean_paths import BRANCHES_ROOT


def test_dossier_exists() -> None:
    assert (BRANCHES_ROOT / "juggler_barrier_collapse.md").is_file()


def test_barrier_word_is_bad_and_maximal() -> None:
    """`O E^{t-1}` is `L(y)`-bad at the chosen depth and crosses at the next one."""
    for k in (7, 25, 100, 1000):
        L = scale_L(k)
        t = barrier_depth(k)
        assert min_prefix_walk(t) > -L
        assert min_prefix_walk(t + 1) <= -L


def test_barrier_depth_is_inside_the_window() -> None:
    for k in (7, 25, 100, 1000, 20000):
        assert barrier_depth(k) < math.ceil(19.0 * scale_L(k))


def test_composite_is_the_map_on_the_cylinder() -> None:
    """Where the word holds, the composite agrees with iterating the map."""
    n, t = 10**7 + 1, 3
    if itinerary(n, t) == "O" + "E" * (t - 1):
        m = n
        for _ in range(t):
            m = floor_power(m)
        assert composite(n, t) == m
    # and the composite is monotone, which is what makes the level sets intervals
    prev = 0
    for n in range(10**6 + 1, 10**6 + 400, 2):
        v = composite(n, 3)
        assert v >= prev
        prev = v


def test_value_stays_in_the_floor_band() -> None:
    """The barrier value lies strictly between the floor and its square, at every scale."""
    for k in (7, 15, 25, 100, 435, 2000, 20000):
        t = barrier_depth(k)
        v_lo, v_hi = value_range(10**k, t)
        assert N0_LEAN < v_lo <= v_hi < N0_LEAN * N0_LEAN


def test_level_weights_partition_the_range() -> None:
    y, t = 10**7, barrier_depth(7)
    ws = level_weights(y, t)
    assert sum(ws) == y  # the level sets tile (y, 2y]
    assert all(w >= 0 for w in ws)
    share = odd_share(y, t)
    assert 0.0 <= share <= 1.0


def test_witness_has_the_barrier_word() -> None:
    k = 435
    t = barrier_depth(k)
    v_lo, _ = value_range(10**k, t)
    n = witness(v_lo, t)
    assert n is not None
    assert itinerary(n, t) == "O" + "E" * (t - 1)
    m = n
    for _ in range(t):
        m = floor_power(m)
    assert m == v_lo


def test_survey_fields() -> None:
    row = survey(7)
    assert row["t"] == 3 and row["bad"] and row["in_floor_band"]
    assert math.isclose(row["fair_share"], 2.0**-3)
    assert row["deficit_orders"] > 0


def test_recorded_summary_is_consistent() -> None:
    summary = json.loads(SUMMARY.read_text(encoding="utf-8"))
    assert summary["branch"] == "barrier_collapse"
    for row in summary["rows"]:
        assert row["bad"] and row["in_floor_band"]
        assert row["t"] < row["d_C19"]
        # the deficit the hypothesis demands only grows with the scale
        assert row["deficit_orders"] > 20
    orders = [row["deficit_orders"] for row in summary["rows"]]
    assert orders == sorted(orders)
    # at the largest scale the cylinder carries a single value and is parity-constant
    last = summary["rows"][-1]
    assert last["values"] == 1
    assert last["odd_share"] in (0.0, 1.0)
    w = summary["witness"]
    assert w is not None and w["word"] == "O" + "E" * (last["t"] - 1)

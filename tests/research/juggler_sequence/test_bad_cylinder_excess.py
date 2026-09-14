"""Tests for ``bad_cylinder_excess``: the excess of the `L(y)`-bad cylinders, exactly."""

from __future__ import annotations

import json
import math

from research.juggler_sequence.bad_cylinder_excess import (
    LOG2_3,
    N0_LEAN,
    SUMMARY,
    _depth_row,
    depth_of,
    fair_max_z,
    floor_power,
    measure,
    odd_starts,
    scale_L,
    verdict,
)
from research.juggler_sequence.lean_paths import BRANCHES_ROOT


def test_dossier_exists() -> None:
    assert (BRANCHES_ROOT / "juggler_bad_cylinder_excess.md").is_file()


def test_floor_power_is_the_map() -> None:
    assert floor_power(4) == 2
    assert floor_power(3) == 5
    assert floor_power(37) == 225
    assert floor_power(1) == 1


def test_scale_and_depth() -> None:
    assert math.isclose(scale_L(10**5, N0_LEAN), 1.1343, abs_tol=1e-3)
    assert depth_of(10**4, 19.0, N0_LEAN) == 16
    assert depth_of(10**4, 30.0, N0_LEAN) == 25


def test_fair_baseline() -> None:
    assert fair_max_z(1) == 0.0
    assert math.isclose(fair_max_z(1000), math.sqrt(2 * math.log(1000)))


def test_depth_row_arithmetic() -> None:
    # two cylinders: one of 10 members all odd, one of 4 members with 1 odd
    words = {0b01: [10, 10], 0b10: [4, 1]}
    row = _depth_row(words, y=10**4, t=3, n_starts=100, values={1, 2, 3},
                     pairs={(0b01, 1), (0b10, 2), (0b10, 3)}, shares=(0.5,))
    assert row["words"] == 2
    assert row["values"] == 3
    assert row["word_value_pairs"] == 3
    assert math.isclose(row["values_per_word"], 1.5)
    assert row["max_cylinder"] == 10
    assert math.isclose(row["bad_mass_fraction"], 0.14)
    # the fully biased cylinder has z = |10 - 5| / sqrt(10/4) = sqrt(10)
    assert math.isclose(row["z_max"], math.sqrt(10.0))
    # excess at q = 1/2 is 10 - 5 = 5 (the other cylinder gives 1 - 2 = -1)
    exc = row["excess"]["0.5"]
    assert math.isclose(exc["max_excess"], 5.0)
    # 10^4 (log 10^4)^{-A} = 5 at A = log(2000)/log(log 10^4)
    assert math.isclose(exc["A_required"], math.log(2000.0) / math.log(math.log(10**4)))


def test_badness_matches_the_walk_definition() -> None:
    """A start survives to depth ``t`` exactly when its walk never reached ``-L(y)``."""
    y, depth = 2000, 10
    L = scale_L(y, N0_LEAN)
    res = measure(y, depth)
    for t in range(depth + 1):
        expected = 0
        for n in odd_starts(y):
            m, walk, bad = n, 0.0, True
            for s in range(t):
                walk += (LOG2_3 if m % 2 == 1 else 0.0) - 1.0
                if walk <= -L:
                    bad = False
                    break
                m = floor_power(m)
            if bad:
                expected += 1
        assert abs(res["rows"][t]["bad_mass_fraction"] * res["starts"] - expected) < 0.5


def test_measure_shape_on_a_small_scale() -> None:
    res = measure(2000, depth=12)
    assert res["starts"] == 1000
    assert len(res["rows"]) == 13
    prev_mass = 1.1
    for row in res["rows"]:
        assert row["values_per_word"] >= 1.0 - 1e-12 or row["words"] == 0
        assert row["word_value_pairs"] >= row["words"]
        assert row["bad_mass_fraction"] <= prev_mass + 1e-12
        prev_mass = row["bad_mass_fraction"]
    # depth 0: one cylinder, every start odd, so the bias is the whole mass
    assert res["rows"][0]["words"] == 1
    assert math.isclose(res["rows"][0]["bad_mass_fraction"], 1.0)


def test_recorded_summary_is_consistent() -> None:
    summary = json.loads(SUMMARY.read_text(encoding="utf-8"))
    assert summary["branch"] == "bad_cylinder_excess"
    assert [res["y"] for res in summary["scales"]] == [10**4, 10**5, 10**6, 10**7]
    for res in summary["scales"]:
        assert res["floor"] == N0_LEAN
    for v in summary["verdicts"]["19"]:
        # at the top of the hypothesis's own window the bad cylinders are parity-constant
        assert v["values_per_word_at_d_minus_one"] < 1.2
        # the permitted exponent stays far below the C the criteria need
        assert v["A_required_min"] < 5.0
        # and never beats the fair-coin baseline on the same cylinder sizes
        assert v["A_gap"] <= 0.0
    # the shortfall against a fair coin grows with the scale
    gaps = [v["A_gap"] for v in summary["verdicts"]["19"]]
    assert gaps[0] > gaps[-1]
    ratios = [v["z_ratio_at_d_minus_one"] for v in summary["verdicts"]["19"]]
    assert ratios[0] < ratios[-1]

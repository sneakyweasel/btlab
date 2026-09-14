"""Tests for ``cylinder_energy_measure``: the exact bias energy of the cylinders."""

from __future__ import annotations

import json
import math

from research.juggler_sequence.cylinder_energy_measure import (
    LOG2_3,
    N0_LEAN,
    SUMMARY,
    calibration,
    cylinder_statistics,
    depth_of,
    floor_power,
    measure,
    odd_starts,
    parity_word,
    scale_L,
)
from research.juggler_sequence.lean_paths import BRANCHES_ROOT


def test_dossier_exists() -> None:
    assert (BRANCHES_ROOT / "juggler_cylinder_energy_measure.md").is_file()


def test_floor_power_is_the_map() -> None:
    assert floor_power(4) == 2
    assert floor_power(3) == 5  # floor(3 sqrt 3) = floor(5.196)
    assert floor_power(37) == 225  # the classic start
    assert floor_power(1) == 1


def test_parity_word_bits_and_times() -> None:
    # 37 -> 225 -> 3375 -> 196069 -> 86818724 -> 9317 -> 899319 -> ...; all odd until 86818724
    word, floor_time, cross_time = parity_word(37, 4, L=10.0, n0=1)
    assert word == 0b11110  # 37, 225, 3375, 196069 odd; 86818724 even
    assert floor_time == 6  # no iterate is at or below the floor 1: the sentinel depth + 2
    assert cross_time == 6  # with L = 10 the walk never reaches -10 within five letters
    # an odd start below the floor is dead at time 0 and its walk stays above -L for one step
    word, floor_time, _ = parity_word(101, 2, L=0.5, n0=N0_LEAN)
    assert floor_time == 0
    assert word >> 2 == 1


def test_walk_crossing_matches_definition() -> None:
    L = scale_L(10**5, N0_LEAN)
    for n in list(odd_starts(10**5))[:2000]:
        word, _, cross = parity_word(n, 12, L, N0_LEAN)
        walk = 0.0
        expected = 14
        for s in range(13):
            bit = (word >> (12 - s)) & 1
            walk += (LOG2_3 if bit else 0.0) - 1.0
            if walk <= -L:
                expected = s + 1
                break
        assert cross == expected


def test_identity_and_lemma_8_1_on_a_small_scale() -> None:
    res = measure(2000, depth=12)
    assert res["starts"] == 1000
    for row in res["rows"]:
        for variant in ("all", "bad", "live"):
            r = row[variant]
            # 4 E_t = 2 C_{t+1} - C_t is asserted inside; the ratios are consistent with it
            assert abs(4 * r["E_t"] - (2 * r["C_next"] - r["C_t"])) < 1e-6
            assert 0.0 <= r["worst_ratio"] <= 1.0 + 1e-12
        # live starts are bad (Lemma 8.1), so the live mass is at most the bad mass
        assert row["live"]["mass_fraction"] <= row["bad"]["mass_fraction"] + 1e-12
    # depth 0: every odd start is odd, one fully biased cylinder
    r0 = res["rows"][0]["all"]
    assert r0["cylinders"] == 1 and abs(r0["worst_ratio"] - 1.0) < 1e-12


def test_violators_are_counted_on_both_sides() -> None:
    words = [(0b1101, 20, 20), (0b1100, 20, 20), (0b1110, 20, 20), (0b1001, 20, 20)]
    rows = cylinder_statistics(words, depth=3, shares=(0.55,))
    # depth 2: words 11 (three starts, next letters E, E, O) and 10 (one start, next letter E)
    r = rows[2]["all"]
    assert r["cylinders"] == 2
    v = r["violators"]["0.55"]
    assert v["odd_atoms"] == 0 and v["even_atoms"] == 2
    assert abs(v["odd_mass_fraction"] - 0.0) < 1e-12
    assert abs(v["even_mass_fraction"] - 1.0) < 1e-12
    # 4 E_2 = (2 - 3)^2 + (0 - 1)^2 = 2
    assert abs(4 * r["E_t"] - 2.0) < 1e-12


def test_calibration_constants() -> None:
    cal = calibration(24.0, 0.55)
    assert 0.20 < cal["chernoff_exponent_e_Cq"] < 0.22
    assert 9.4 < cal["B_min"] < 9.5
    assert 42 < cal["two_B_plus_C"] < 44
    crossings = cal["log10_y_where_fair_splitting_meets_the_bound"]
    assert crossings["260"] > 60 and crossings["350000000"] > 50
    assert depth_of(10**5, 24.0, N0_LEAN) == 28
    assert math.isclose(scale_L(10**5, N0_LEAN), 1.1343, abs_tol=1e-3)


def test_recorded_summary_is_consistent() -> None:
    summary = json.loads(SUMMARY.read_text(encoding="utf-8"))
    assert summary["branch"] == "cylinder_energy_measure"
    scales = [res["y"] for res in summary["scales"]]
    assert scales == [10**4, 10**5, 10**6, 10**7]
    for res in summary["scales"]:
        rows = res["rows"]
        assert len(rows) == res["depth"] + 1
        # the unrestricted energy reaches the worst case by the last recorded depth
        assert rows[-1]["all"]["worst_ratio"] > 0.999
        # the bad mass decays with depth: at most half of it is left by depth 20
        assert rows[20]["bad"]["mass_fraction"] < 0.5

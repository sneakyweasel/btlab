"""The walk mod 1 is a rotation orbit, and the log-log clock defect is negligible."""

from __future__ import annotations

import json
import math
from pathlib import Path

from research.juggler_sequence.lachesis_loglog_clock import (
    ALPHA,
    clock,
    cycle_clock_defect_bound,
    etree_density,
    evidence_depth,
    odd_count_of_period,
    orbit_clock_trace,
    rotation_gap,
    survival_log2_by_depth,
)
from research.juggler_sequence.tao_reduction import LOG2_3, N0_CERTIFIED, scale_L

ROOT = Path(__file__).resolve().parents[3]
DOSSIER = ROOT / "docs" / "problems" / "juggler_lachesis_loglog_clock.md"
SUMMARY = ROOT / "data" / "research" / "juggler" / "lachesis_loglog_clock" / "summary.json"


def test_alpha_is_log2_three_halves() -> None:
    assert abs(ALPHA - math.log2(1.5)) < 1e-15


def test_walk_mod_one_is_the_rotation_orbit() -> None:
    """u_t = o_t log2(3) - t is congruent mod 1 to o_t * alpha, exactly."""

    for o in range(0, 400):
        for t in (o, o + 1, 2 * o + 3, 5 * o + 11):
            u = o * LOG2_3 - t
            assert abs(((u % 1.0) - ((o * ALPHA) % 1.0) + 0.5) % 1.0 - 0.5) < 1e-9


def test_clock_defect_is_negligible_on_real_orbits() -> None:
    worst = 0.0
    seen = 0
    for n in range(10**12 + 1, 10**12 + 401, 2):
        for _t, _o, eps in orbit_clock_trace(n, N0_CERTIFIED, 200):
            worst = max(worst, abs(eps))
            seen += 1
    assert seen > 100
    assert worst < 1e-8


def test_cycle_defect_bound_is_far_below_one() -> None:
    row = cycle_clock_defect_bound(3.5e8, 780239)
    assert row["Delta_max"] < 1e-2
    assert row["abs_eps_u_units"] < 1e-3


def test_rotation_gap_matches_brute_force() -> None:
    for o in (7, 53, 1000):
        pts = sorted((j * ALPHA) % 1.0 for j in range(o))
        gaps = [pts[i + 1] - pts[i] for i in range(o - 1)] + [pts[0] + 1.0 - pts[-1]]
        assert abs(rotation_gap(o) - max(gaps)) < 1e-15


def test_certified_period_covers_the_clock_circle() -> None:
    o = odd_count_of_period(780239)
    assert o == 492276
    assert rotation_gap(20000) < 1e-3  # already fine; the full orbit is 5.1e-6


def test_single_seed_etree_density_is_one_over_m() -> None:
    row = etree_density(101, 1)
    assert row["count"] == 101
    assert abs(row["density"] - row["one_over_m"]) < 0.05 * row["one_over_m"]


def test_survival_dp_matches_brute_force() -> None:
    L = scale_L(12 * math.log(10.0), N0_CERTIFIED)  # scale_L wants the natural log of y
    d = 12
    logp = survival_log2_by_depth(L, d)
    alive = 0
    for bits in range(2 ** (d - 1)):
        o, live = 1, True
        for s in range(2, d + 1):
            o += (bits >> (s - 2)) & 1
            if o * LOG2_3 - s <= -L:
                live = False
                break
        alive += live
    assert abs(2.0 ** logp[d] - alive / 2 ** (d - 1)) < 1e-12


def test_evidence_depth_grows_with_the_sample() -> None:
    shallow = evidence_depth(100, 1e6)
    deep = evidence_depth(100, 1e12)
    assert shallow is not None and deep is not None
    assert shallow < deep


def test_clock_is_monotone_in_the_state() -> None:
    assert clock(10**12) < clock(10**24) < clock(10**48)


def test_dossier_and_summary_agree() -> None:
    assert DOSSIER.is_file()
    data = json.loads(SUMMARY.read_text(encoding="utf-8"))
    flags = data["classification"]
    assert flags["decision"] == "PARK"
    assert flags["clock_defect_is_negligible"]
    assert flags["cycle_defect_below_one"]
    assert flags["basin_covers_every_block"]
    assert flags["single_seed_density_is_one_over_m"]
    assert flags["deep_census_dominated_by_floor_raise"]

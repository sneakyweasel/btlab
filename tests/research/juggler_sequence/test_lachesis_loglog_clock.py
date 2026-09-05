"""The walk mod 1 is a rotation orbit, and the log-log clock defect is negligible."""

from __future__ import annotations

import json
import math
from pathlib import Path

from research.juggler_sequence.lachesis_loglog_clock import (
    ALPHA,
    basin_block_density_bounds,
    clock,
    clotho_coverage_threshold,
    flight_gate_passages,
    gap_profile,
    cycle_clock_defect_bound,
    etree_density,
    evidence_depth,
    inverse_sum_bounds,
    odd_count_of_period,
    orbit_clock_trace,
    rotation_gap,
    survival_log2_by_depth,
    theta_of_period,
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


def test_theta_matches_paper_a_gap() -> None:
    """theta(780239) = 1 - 2^L/3^o with o = 492276: the walk-charge blocker's gap."""

    th = theta_of_period(780239)
    o = odd_count_of_period(780239)
    assert abs(th - (1.0 - 2.0 ** (-(o * LOG2_3 - 780239)))) < 1e-15
    assert 3.4e-6 < th < 3.5e-6


def test_inverse_sum_sandwich_and_finance_kill() -> None:
    """Floor theta ln n from the Lean inv-sum form; cap L/n; floor > cap is the finance kill."""

    live = inverse_sum_bounds(3.5e8, 780239)
    assert live["inv_sum_floor"] < live["inv_sum_cap"]
    assert not live["finance_kills"]
    dead = inverse_sum_bounds(1e10, 780239)
    assert dead["finance_kills"]


def test_finance_floor_beats_the_single_seed_bound() -> None:
    row = basin_block_density_bounds(3.5e8, 780239, 68)
    assert row["density_low"] > row["single_seed_two_over_n"]
    assert row["density_low"] < row["density_high"]
    assert abs(row["K_low"] - 1.0) < 1e-12
    assert abs(row["K_high"] - 3.0) < 1e-12


def test_gap_profile_matches_rotation_gap_and_is_monotone() -> None:
    gaps = gap_profile(600)
    for O in (7, 53, 300, 600):
        assert abs(gaps[O - 1] - rotation_gap(O)) < 1e-15
    assert all(gaps[i + 1] <= gaps[i] + 1e-15 for i in range(len(gaps) - 1))


def test_clotho_threshold_is_a_narrow_window_above_q_star() -> None:
    gaps = gap_profile(2000)
    q = math.log(2.0) / math.log(3.0)
    row12 = clotho_coverage_threshold(12, gaps=gaps)
    row100 = clotho_coverage_threshold(100, gaps=gaps)
    assert row12["O_star"] == 40 and row100["O_star"] == 358
    for row in (row12, row100):
        assert 0.0 < row["s_star"] - q < 0.01
        # the hug near-return rate escapes slowly enough; the all-odd rate does not
        assert (12 * LOG2_3 - 19) / 12 < row["walk_gain_per_odd_step"] < LOG2_3 - 1.0


def test_flight_gate_passages_shape_and_high_flyer_speed() -> None:
    """A realised flight passes its decades far above the gate: the first high-flyer reaches
    10^20 with a gain per odd step two orders of magnitude above u/O*."""

    gaps = gap_profile(2000)
    rows = flight_gate_passages(48443, gaps, decades=tuple(range(6, 21)))
    assert rows and all(set(r) >= {"decade", "t", "O", "O_star", "gate_met", "gain_per_odd"} for r in rows)
    assert [r["decade"] for r in rows] == sorted(r["decade"] for r in rows)
    assert all(r["decade"] <= 20 for r in rows)
    assert not any(r["gate_met"] for r in rows)
    last = rows[-1]
    assert last["gate_gain"] is not None and last["gain_per_odd"] > 10 * last["gate_gain"]


def test_lean_layer_is_registered_and_names_its_theorems() -> None:
    from research.juggler_sequence.lean_paths import LAYERS, has_named

    path = LAYERS["LogLogClock"]
    assert path.is_file()
    text = path.read_text(encoding="utf-8")
    for name in ("fract_walk_eq_fract_rotation", "fract_walk_depends_only_on_odd_count",
                 "even_chain_mem_burst", "even_chain_log_offset",
                 "hug_band_step_exists", "narrow_band_dead", "dead_zone_nonempty",
                 "odd_steps_below_one_le_one", "half_lt_alphaClock",
                 "band_step_forced_odd", "band_step_forced_even", "band_successor_unique",
                 "not_reachesOne_ge", "not_reachesOne_even_chain_ge"):
        assert has_named(text, name), name
    assert "import Problems.Juggler.Dynamics" in text


def test_record_gain_is_the_shortest_near_return() -> None:
    """The minimum walk gain per record over the high-flyers is theta_19, not an artefact."""

    from research.juggler_sequence.lachesis_loglog_clock import HIGH_FLYERS, record_structure

    gains = [record_structure(n)["min_walk_gain"] for n in HIGH_FLYERS]
    gains = [g for g in gains if g is not None]
    assert len(gains) == len(HIGH_FLYERS)
    assert abs(min(gains) - (12 * LOG2_3 - 19)) < 1e-9


def test_bounded_record_gaps_force_the_gate_to_fail() -> None:
    """O(y) = O(log log y) against O*(y) >= ln y: the gate fails past the crossover."""

    from research.juggler_sequence.lachesis_loglog_clock import lacunarity_crossover

    theta19 = 12 * LOG2_3 - 19
    near = lacunarity_crossover(90, theta19, 1000)
    far = lacunarity_crossover(90, theta19, 100000)
    assert not near["gate_provably_fails"]
    assert far["gate_provably_fails"]
    assert far["O_upper_bound"] < far["O_star_lower_bound"]
    # the bound grows like log log y, the gate at least like log y
    assert far["O_upper_bound"] / near["O_upper_bound"] < 3.0
    assert far["O_star_lower_bound"] / near["O_star_lower_bound"] > 90.0


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

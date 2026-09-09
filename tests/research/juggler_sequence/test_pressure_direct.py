"""Fair-coin suffix DP and the two direct-attack identities for P_θ / M_{θ,q}."""

from __future__ import annotations

import math
from pathlib import Path

from research.juggler_sequence.pressure_direct import (
    Q_CRIT,
    cylinder_image_stats,
    reset_worst_case_q,
    walsh_generating_function_budget,
)
from research.juggler_sequence.tao_reduction import (
    LOG2_3,
    fair_tilted_live,
    fair_tilted_live_suffix_odd_mass,
    p_of_C,
    scale_L,
    theta_of_C,
)

DOSSIER = Path(__file__).resolve().parents[3] / "docs" / "problems" / "juggler_pressure_direct.md"
SUMMARY = Path(__file__).resolve().parents[3] / "data" / "research" / "juggler" / "pressure_direct" / "summary.json"


def test_theta_19_matches_census_value() -> None:
    assert abs(theta_of_C(19) - 0.396) < 5e-3
    assert 0.59 < p_of_C(19) < 0.61
    assert abs(Q_CRIT - math.log(2.0) / math.log(3.0)) < 1e-12


def test_suffix_mass_matches_brute_force() -> None:
    L, t, theta, k = 1.3, 8, 0.5, 3
    num = 0.0
    den = 0.0
    for bits in range(2 ** (t - 1)):
        o, live, run = 1, True, 1
        for s in range(2, t + 1):
            bit = (bits >> (s - 2)) & 1
            if bit:
                o += 1
                run += 1
            else:
                run = 0
            if o * LOG2_3 - s <= -L:
                live = False
                break
        if live:
            wt = math.exp(theta * o) / 2 ** (t - 1)
            den += wt
            if run >= k:
                num += wt
    assert den > 0
    assert abs(fair_tilted_live_suffix_odd_mass(L, t, theta, k) - num / den) < 1e-12


def test_suffix_mass_edge_cases() -> None:
    L = 1.3
    assert fair_tilted_live_suffix_odd_mass(L, 3, 0.4, 4) == 0.0  # t < k
    # t = k = 1: the unique odd-start word is O
    assert fair_tilted_live_suffix_odd_mass(2.0, 1, 0.4, 1) == 1.0
    # tilt θ = 0 reduces the denominator to the odd-start live probability
    assert fair_tilted_live(L, 8, 0.0) > 0
    mu1 = fair_tilted_live_suffix_odd_mass(L, 8, 0.0, 1)
    assert 0.0 < mu1 < 1.0


def test_reset_worst_case_q_is_half_plus_half_mu() -> None:
    assert reset_worst_case_q(0.0) == 0.5
    assert abs(reset_worst_case_q(0.26) - 0.63) < 1e-12
    assert reset_worst_case_q(0.18) < p_of_C(19)


def test_high_walk_E_image_is_sparse() -> None:
    # OOOE at y = 10^5: u = 3 log2 3 - 4 > 0, last letter E.  Image is sparse
    # in its landing range (not a dyadic interval).  Paper B does not apply.
    row = cylinder_image_stats(10**5, (1, 1, 1, 0))
    assert row["ends_E"] and row["high_walk"] and row["members"] > 0
    assert row["density"] is not None and row["density"] < 0.05
    # OEE is contracted (u < 0); the image can fill a short landing interval.
    contracted = cylinder_image_stats(10**5, (1, 0, 0))
    assert contracted["ends_E"] and not contracted["high_walk"]
    assert contracted["density"] is not None and contracted["density"] > 0.2


def test_walsh_tail_is_exponential_in_d() -> None:
    theta = theta_of_C(19)
    budget = walsh_generating_function_budget(49, theta, k0=4)
    assert budget["log_full_over_d"] > 0.15  # log(1+ρ) ≈ 0.179
    assert budget["log_partial"] < budget["log_full"]
    # fixed-order partial is polynomial in d, hence o(d) in the exponent as d → ∞
    small = walsh_generating_function_budget(8, theta, k0=4)
    assert small["partial_k0"] < small["full_1_plus_rho_pow_d"]


def test_tao_depth_suffix_dp_runs() -> None:
    L = scale_L(12 * math.log(10.0), 350_000_000)
    d = math.ceil(19 * L)
    mu4 = fair_tilted_live_suffix_odd_mass(L, d, theta_of_C(19), 4)
    assert 0.0 <= mu4 <= 1.0


def test_exact_even_and_odd_perfect_power_towers() -> None:
    """Finite fixtures for the two sparse towers used in the gauge obstruction."""

    floor = 350_000_000
    even_base = floor + 2
    odd_base = floor + 1
    for depth in range(1, 6):
        even_start = even_base ** (2**depth)
        x = even_start
        for _ in range(depth):
            assert x % 2 == 0
            x = math.isqrt(x)
            assert x > floor
        assert x == even_base

        odd_start = odd_base ** (2**depth)
        x = odd_start
        for _ in range(depth):
            assert x % 2 == 1
            x = math.isqrt(x**3)
            assert x > floor
        assert x == odd_base ** (3**depth)

        # These are exact integer checks, kept deliberately tiny; they are not
        # evidence that either sparse family has positive dyadic mass.
        assert max(even_start.bit_length(), odd_start.bit_length()) < 1_000


def test_log_order_gauge_minimax_is_the_critical_drift() -> None:
    """The E/O tower constraints meet at exp(theta log(2)/log(3))."""

    theta = theta_of_C(19)
    log2 = math.log(2.0)
    log3 = math.log(3.0)
    log_three_halves = math.log(1.5)
    s_critical = -theta / log3
    critical_log_R = theta * Q_CRIT

    even_constraint = -s_critical * log2
    odd_constraint = theta + s_critical * log_three_halves
    assert math.isclose(even_constraint, critical_log_R, rel_tol=0.0, abs_tol=1e-14)
    assert math.isclose(odd_constraint, critical_log_R, rel_tol=0.0, abs_tol=1e-14)

    # On either side of the crossing, one of the two exact-tower constraints
    # is at least the critical value.  The asymptotic theorem uses k-step
    # iteration; these sample points only regress the minimax algebra.
    for offset in (-4.0, -1.0, -0.1, 0.0, 0.1, 1.0, 4.0):
        s = s_critical + offset
        log_R_lower_bound = max(-s * log2, theta + s * log_three_halves)
        assert log_R_lower_bound >= critical_log_R - 1e-14


def test_critical_gauge_bound_exceeds_optimized_pressure_base() -> None:
    """At the useful fair and biased depths, a pointwise gauge is too costly."""

    for C, q, expected_gap in ((19, 0.5, 0.03237248), (41, 0.55, 0.01293665)):
        p = p_of_C(C)
        theta = math.log(p * (1.0 - q) / (q * (1.0 - p)))
        log_pressure_base = math.log(1.0 - q + q * math.exp(theta))
        log_pointwise_lower_bound = theta * Q_CRIT
        assert q < p < Q_CRIT
        assert theta > 0.0
        assert log_pointwise_lower_bound > log_pressure_base
        assert abs((log_pointwise_lower_bound - log_pressure_base) - expected_gap) < 1e-8


def test_log_order_oscillation_bound_and_necessary_widths() -> None:
    """Regress (P5) and the oscillation widths needed to reach the target rate."""

    log2 = math.log(2.0)
    log3 = math.log(3.0)
    cases = ((19, 0.5, 0.0467036177), (41, 0.55, 0.0186636371))
    for C, q, expected_delta in cases:
        p = p_of_C(C)
        theta = math.log(p * (1.0 - q) / (q * (1.0 - p)))
        log_pressure_base = math.log(1.0 - q + q * math.exp(theta))
        delta = (theta * Q_CRIT - log_pressure_base) / log2
        assert abs(delta - expected_delta) < 5e-11

        # For fixed width delta = s_+ - s_-, the two affine tower bounds
        # meet at s_+ = delta - theta/log(3), attaining (P5).
        equality_s_plus = delta - theta / log3
        for offset in (-2.0, -0.2, 0.0, 0.2, 2.0):
            s_plus = equality_s_plus + offset
            s_minus = s_plus - delta
            log_R_lower_bound = max(
                -s_plus * log2,
                theta + s_minus * log3 - s_plus * log2,
            )
            p5_lower_bound = theta * Q_CRIT - delta * log2
            assert log_R_lower_bound >= p5_lower_bound - 1e-14
            if offset == 0.0:
                assert math.isclose(log_R_lower_bound, p5_lower_bound, abs_tol=1e-14)
                assert math.isclose(p5_lower_bound, log_pressure_base, abs_tol=1e-14)


def test_dossier_headings_and_close() -> None:
    dossier = DOSSIER.read_text(encoding="utf-8")
    for heading in (
        "## Problem",
        "## Exact statement",
        "## Current literature",
        "## Branch budget",
        "## Balanced-ternary formulation",
        "## Why BT may be relevant",
        "## Candidate operations / invariants",
        "## Experiments",
        "## Conjectures",
        "## Counterexamples",
        "## Formalization",
        "## Results",
        "## Open questions",
        "## Decision",
        "## Publication assessment",
    ):
        assert heading in dossier
    decision = dossier.split("## Decision", 1)[1].split("## ", 1)[0]
    assert "CLOSE" in decision


def test_summary_artifact_exists() -> None:
    assert SUMMARY.is_file()
    import json

    data = json.loads(SUMMARY.read_text(encoding="utf-8"))
    assert data["classification"]["decision"] == "CLOSE"
    assert data["classification"]["reset_is_H_q_at_unbounded_depth"] is True
    assert data["classification"]["S_sampling_is_S_fairness"] is True

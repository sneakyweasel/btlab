"""Scale-average sufficiency and its finite algebraic regression checks.

These scalar fixtures do not establish a bound on actual Juggler moments.
The conditional asymptotic implication is a human proof in the dossier.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import accumulate
import math
from pathlib import Path

from research.juggler_sequence.tao_reduction import p_of_C

DOSSIER = (
    Path(__file__).resolve().parents[3]
    / "docs"
    / "problems"
    / "juggler_pressure_external_average.md"
)
NEGATIVE = Path(__file__).resolve().parents[3] / "docs" / "negative_knowledge.md"


def test_dossier_headings_and_conditional_promotion() -> None:
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
    assert "PROMOTE" in decision
    assert "Not a halt theorem" in dossier or "not a halt theorem" in dossier


def test_identity_a_is_cylinder_weighted_nested_phase() -> None:
    dossier = DOSSIER.read_text(encoding="utf-8")
    assert "completed single sum" in dossier.lower() or "Completed single sum" in dossier
    assert "cylinder-weighted nested" in dossier
    assert "Vaaler" in dossier
    assert "§10.4(e)" in dossier or "10.4(e)" in dossier
    assert "cC<1" in dossier or "cC < 1" in dossier


def test_scale_average_sufficiency_is_recorded_with_the_existing_limits() -> None:
    dossier = DOSSIER.read_text(encoding="utf-8")
    assert "J-pressure-scale-average-suffices" in dossier
    assert "conditional" in dossier.lower()
    assert "J-tao-free-term-is-live-mass" in dossier
    assert "S-fairness" in dossier or "$S$-fairness" in dossier


def test_parseval_is_pointed_at_not_rederived() -> None:
    dossier = DOSSIER.read_text(encoding="utf-8")
    assert "J-tao-cylinder-forms-reparameterization" in dossier
    assert "Not re-derived" in dossier or "not re-derived" in dossier
    assert "J-pressure-direct-routes" in dossier


def test_negative_knowledge_records_the_sufficiency_correction() -> None:
    text = NEGATIVE.read_text(encoding="utf-8")
    assert "juggler_pressure_external_average" in text
    assert "J-pressure-external-average" in text
    assert "J-pressure-scale-average-suffices" in text


def test_abel_summation_identity_for_nonnegative_spiky_sequences() -> None:
    """Exact finite summation by parts: Markov factors can be averaged."""

    sequences = (
        [0] * 17,
        [1] * 17,
        [0] * 16 + [10_000],
        [1 + k if k & (k - 1) == 0 else 1 for k in range(1, 65)],
    )
    for rho in sequences:
        cumulative = list(accumulate(rho))
        for exponent in (1, 2):
            weights = [Fraction(1, (k + 1) ** exponent) for k in range(len(rho))]
            direct = sum((value * weight for value, weight in zip(rho, weights)), Fraction(0))
            abel = cumulative[-1] * weights[-1] + sum(
                (
                    cumulative[k] * (weights[k] - weights[k + 1])
                    for k in range(len(rho) - 1)
                ),
                Fraction(0),
            )
            assert direct == abel
            assert all(weight >= 0 for weight in weights)
            assert all(a >= b for a, b in zip(weights, weights[1:]))


def test_linear_cesaro_bound_allows_non_subpower_pointwise_spikes() -> None:
    """A scalar separator, not a claimed realization by Juggler orbits."""

    cumulative = 0
    for k in range(1, 4097):
        is_power_of_two = k & (k - 1) == 0
        rho = 1 + k if is_power_of_two else 1
        cumulative += rho
        assert cumulative <= 3 * k
        if is_power_of_two:
            # Infinitely many such exact spikes would violate rho_k=k^{o(1)}.
            assert rho >= k
            if k >= 2:
                assert math.log(rho) / math.log(k) >= 1.0


def test_dyadic_grouping_bounds_the_weighted_spiky_sum() -> None:
    """The finite dyadic bound covers positive, zero, and negative exponents."""

    for exponent in (0.5269265491091455, 0.5194493967422041, 1.0, 1.2):
        for depth in (1, 3, 7, 11):
            K = 2**depth - 1
            weighted = math.fsum(
                (1 + k if k & (k - 1) == 0 else 1) * k ** (-exponent)
                for k in range(1, K + 1)
            )
            # On [2^j, 2^(j+1)), use k^(-r) <= 2^(-jr) and
            # the cumulative bound A(2^(j+1)-1) <= 3*2^(j+1).
            block_bound = 6.0 * math.fsum(
                2.0 ** (j * (1.0 - exponent)) for j in range(depth)
            )
            assert weighted <= block_bound


def test_optimized_scale_average_rates_and_allowed_growth_surplus() -> None:
    """The admissible eta is positive at both quoted elementary depths."""

    for C, q, expected_rate, expected_surplus in (
        (19, 0.5, 0.5269265491091455, 0.01952654910914542),
        (41, 0.55, 0.5194493967422041, 0.012049396742204177),
    ):
        p = p_of_C(C)
        theta = math.log(p * (1.0 - q) / (q * (1.0 - p)))
        log_base = math.log(1.0 - q + q * math.exp(theta))
        rate = C * (theta * p - log_base) / math.log(2.0)
        kl = p * math.log(p / q) + (1.0 - p) * math.log((1.0 - p) / (1.0 - q))
        assert math.isclose(rate, C * kl / math.log(2.0), abs_tol=1e-13)
        assert math.isclose(rate, expected_rate, abs_tol=1e-13)
        assert math.isclose(rate + 0.4926 - 1.0, expected_surplus, abs_tol=1e-13)
        eta = expected_surplus / 2.0
        beta_floor = max(1.0 + eta - rate, 0.0)
        beta = (beta_floor + 0.4926) / 2.0
        contagion_exponent = (beta + 0.4926) / 2.0
        assert 0.0 <= eta < expected_surplus
        assert beta_floor < beta < contagion_exponent < 0.4926


def test_ceiling_depth_preserves_the_chernoff_power_bound() -> None:
    """Regress the scale conversion without computing enormous starts."""

    N0 = 350_000_000
    log2 = math.log(2.0)
    for C, q in ((19, 0.5), (41, 0.55)):
        p = p_of_C(C)
        theta = math.log(p * (1.0 - q) / (q * (1.0 - p)))
        delta = theta * p - math.log(1.0 - q + q * math.exp(theta))
        rate = C * delta / log2
        assert delta > 0.0
        for k in (32, 100, 1_000, 10_000, 1_000_000):
            scale_ratio = (k + 1) * log2 / math.log(N0)
            L = math.log2(scale_ratio)
            d = math.ceil(C * L)
            assert d >= C * L > 0.0
            assert (d - L) / math.log2(3.0) >= p * d - 1e-12
            assert math.exp(-delta * d) <= scale_ratio ** (-rate) * (1.0 + 1e-14)

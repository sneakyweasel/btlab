"""Scale-average sufficiency and its finite algebraic regression checks.

These finite fixtures do not establish an asymptotic bound on actual
Juggler moments. The conditional implication and sparse-source estimate
are human proofs in the dossier; the complementary population is open.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import accumulate, combinations
import math
from pathlib import Path

from research.juggler_sequence.fate_contagion import RECURSIONS, lambda_root
from research.juggler_sequence.tao_reduction import p_of_C

LAMBDA_V6 = lambda_root(RECURSIONS["block_third_plus_oeoee_v6"])

DOSSIER = (
    Path(__file__).resolve().parents[3]
    / "docs"
    / "problems"
    / "juggler_pressure_external_average.md"
)
NEGATIVE = Path(__file__).resolve().parents[3] / "docs" / "negative_knowledge.md"


def test_dossier_headings_and_arithmetic_estimate_park() -> None:
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
    assert "PARK" in decision
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
        (19, 0.5, 0.5269265491091455, 0.01949809383450257),
        (41, 0.55, 0.5194493967422041, 0.01202094146756036),
    ):
        p = p_of_C(C)
        theta = math.log(p * (1.0 - q) / (q * (1.0 - p)))
        log_base = math.log(1.0 - q + q * math.exp(theta))
        rate = C * (theta * p - log_base) / math.log(2.0)
        kl = p * math.log(p / q) + (1.0 - p) * math.log((1.0 - p) / (1.0 - q))
        assert math.isclose(rate, C * kl / math.log(2.0), abs_tol=1e-13)
        assert math.isclose(rate, expected_rate, abs_tol=1e-13)
        assert math.isclose(rate + LAMBDA_V6 - 1.0, expected_surplus, abs_tol=1e-13)
        eta = expected_surplus / 2.0
        beta_floor = max(1.0 + eta - rate, 0.0)
        beta = (beta_floor + LAMBDA_V6) / 2.0
        contagion_exponent = (beta + LAMBDA_V6) / 2.0
        assert 0.0 <= eta < expected_surplus
        assert beta_floor < beta < contagion_exponent < LAMBDA_V6


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


def test_actual_odd_square_sources_obey_the_integer_count_bound() -> None:
    """Small exact blocks check the source count, not its asymptotic proof."""

    for k in range(3, 14):
        y = 2**k
        sources = [
            n
            for n in range(y + 1, 2 * y + 1, 2)
            if math.isqrt(n) ** 2 == n
            or math.isqrt(math.isqrt(n**3)) ** 2 == math.isqrt(n**3)
        ]
        integer_bound = math.isqrt(2 * y) + math.isqrt(math.isqrt((2 * y) ** 3))
        assert sources
        assert len(sources) <= integer_bound
        assert integer_bound <= 4.0 * y**0.75


def test_actual_sparse_source_live_moments_obey_the_crude_tilt_bound() -> None:
    """Finite stopped orbits check a bound independent of all later parities."""

    theta = math.log(p_of_C(19) / (1.0 - p_of_C(19)))
    base = (1.0 + math.exp(theta)) / 2.0
    positive_moments = 0
    for k in (6, 8, 10):
        y = 2**k
        sources = [
            n
            for n in range(y + 1, 2 * y + 1, 2)
            if math.isqrt(n) ** 2 == n
            or math.isqrt(math.isqrt(n**3)) ** 2 == math.isqrt(n**3)
        ]
        for floor in (2, 260):
            for depth in (1, 3, 6):
                terms = []
                for start in sources:
                    state, odd_count = start, 0
                    live = state > floor
                    for _ in range(depth):
                        if not live:
                            break
                        odd_count += state % 2
                        state = math.isqrt(state**3) if state % 2 else math.isqrt(state)
                        live = state > floor
                    if live:
                        terms.append(math.exp(theta * odd_count))
                normalized = math.fsum(terms) / ((y / 2.0) * base**depth)
                positive_moments += normalized > 0.0
                source_bound = 2.0 * len(sources) / y * (math.exp(theta) / base) ** depth
                sparse_bound = 8.0 * y ** (-0.25) * (math.exp(theta) / base) ** depth
                assert normalized <= source_bound * (1.0 + 1e-14)
                assert source_bound <= sparse_bound
    assert positive_moments > 0


def test_sparse_geometric_tail_beats_the_tilt_power() -> None:
    """The explicit ratio is eventually below one and decreases with k."""

    p = p_of_C(19)
    theta = math.log(p / (1.0 - p))
    base = (1.0 + math.exp(theta)) / 2.0
    kappa = 19.0 * (theta - math.log(base)) / math.log(2.0)
    previous = 1.0
    for k in (64, 128, 256, 1024, 10_000):
        ratio = 2.0 ** (-0.25) * ((k + 2.0) / (k + 1.0)) ** kappa
        assert 0.0 < ratio < previous
        previous = ratio
    assert previous > 2.0 ** (-0.25)


def test_crude_complement_bound_still_exceeds_the_averaging_allowance() -> None:
    """Removing thin sources does not bound the complementary population."""

    dossier = DOSSIER.read_text(encoding="utf-8")
    assert "J-pressure-sparse-starts" in dossier
    p = p_of_C(19)
    theta = math.log(p / (1.0 - p))
    log_base = math.log((1.0 + math.exp(theta)) / 2.0)
    kappa = 19.0 * (theta - log_base) / math.log(2.0)
    rate = 19.0 * (theta * p - log_base) / math.log(2.0)
    surplus = rate + LAMBDA_V6 - 1.0
    assert math.isclose(kappa, 4.89342683035, abs_tol=1e-10)
    assert math.isclose(surplus, 0.0194980938, abs_tol=1e-10)
    assert math.isclose(kappa - (1.0 + surplus), 3.8739287365174, abs_tol=1e-10)


def test_fair_cap_gap_persists_under_depth_and_tilt_retuning() -> None:
    """Finite parameter fixtures check the proof, not actual pressure sizes."""

    log2 = math.log(2.0)
    q_star = log2 / math.log(3.0)
    delta_star = 2.0 * q_star - 1.0
    threshold = 1.0 - LAMBDA_V6
    cap_infimum = threshold / delta_star
    assert math.isclose(cap_infimum - 1.0, 0.9377889342688821, abs_tol=1e-13)
    t0 = 2.0 * log2 * cap_infimum
    fixtures = [
        (C, math.log(p_of_C(C) / (1.0 - p_of_C(C))))
        for C in (19, 41, 100)
    ] + [(C, (t0 + C**-0.5) / C) for C in (10_000, 1_000_000, 100_000_000)]
    for C, theta in fixtures:
        # log(a) = theta/2 + log(cosh(theta/2)); log1p keeps small tilts stable.
        log_base = theta / 2.0 + math.log1p(2.0 * math.sinh(theta / 4.0) ** 2)
        rate = C * (theta * p_of_C(C) - log_base) / log2
        kappa = C * (theta - log_base) / log2
        assert rate > threshold
        assert rate / kappa < 2.0 * p_of_C(C) - 1.0 < delta_star
        assert kappa > cap_infimum
        for eta in (0.0, 0.5 * (rate - threshold), 0.9 * (rate - threshold)):
            assert rate - eta > threshold
            assert kappa - 1.0 - eta > cap_infimum - 1.0


def test_fixed_prefix_factor_and_all_odd_density_cost() -> None:
    """These are suffix-cap identities, not claimed Juggler realizations."""

    C = 19
    theta = math.log(p_of_C(C) / (1.0 - p_of_C(C)))
    log_base = theta / 2.0 + math.log1p(2.0 * math.sinh(theta / 4.0) ** 2)
    for depth in (8, 32, 128):
        for prefix in (1, 3, 5, depth):
            fair_prefix_log_moment = theta + (prefix - 1) * log_base
            capped_log_pressure = (
                theta * (depth - prefix) + fair_prefix_log_moment - depth * log_base
            )
            trivial_log_cap = depth * (theta - log_base)
            correction = -(prefix - 1) * (theta - log_base)
            assert math.isclose(capped_log_pressure, trivial_log_cap + correction, abs_tol=1e-13)
    kappa = C * (theta - log_base) / math.log(2.0)
    rate = C * (theta * p_of_C(C) - log_base) / math.log(2.0)
    surplus = rate + LAMBDA_V6 - 1.0
    for eta in (0.0, surplus / 2.0, 0.999 * surplus):
        density_exponent_needed = kappa - 1.0 - eta
        assert density_exponent_needed > 3.8739287365174
        for density_exponent in (density_exponent_needed - 0.25, density_exponent_needed + 0.25):
            for log_scale in (math.log(10.0), 100.0, 1000.0):
                contribution = (kappa - density_exponent) * log_scale
                budget = (1.0 + eta) * log_scale
                difference = (density_exponent_needed - density_exponent) * log_scale
                assert math.isclose(contribution - budget, difference, abs_tol=1e-10)
                assert (contribution <= budget) == (density_exponent >= density_exponent_needed)


def test_abstract_three_wise_fair_bits_can_have_a_large_all_odd_atom() -> None:
    """A finite information barrier, not a distribution of Juggler starts."""

    columns = range(8, 16)
    words = [tuple(1 ^ ((u & column).bit_count() % 2) for column in columns) for u in range(16)]
    for size in (1, 2, 3):
        for positions in combinations(range(8), size):
            counts: dict[tuple[int, ...], int] = {}
            for word in words:
                marginal = tuple(word[position] for position in positions)
                counts[marginal] = counts.get(marginal, 0) + 1
            assert len(counts) == 2**size
            assert set(counts.values()) == {16 // 2**size}
    all_odd_mass = Fraction(sum(word == (1,) * 8 for word in words), len(words))
    assert all_odd_mass == Fraction(1, 16) > Fraction(1, 2**8)


def test_abstract_low_order_matrix_union_bound_and_entropy_cost() -> None:
    """Finite algebra for a random binary matrix; no actual parity estimate."""

    for dimension in (2, 4, 8, 16, 32, 128, 1024):
        orders = {1, 2, dimension // 4, dimension // 2, dimension - 1, dimension}
        for order in sorted(r for r in orders if 1 <= r <= dimension):
            volume = sum(math.comb(dimension, j) for j in range(1, order + 1))
            rows = volume.bit_length()
            assert Fraction(volume, 2**rows) < 1
            assert 2**rows <= 2 * volume
            assert math.log(volume) <= order * math.log(math.e * dimension / order) + 1e-10


def test_square_dilation_source_bounds_on_small_integer_blocks() -> None:
    """Finite source-count checks, not estimates of growing odd prefixes."""

    for y in (1, 10, 100, 1000):
        for minimum_factor in (2, 3, 5, 10, 47):
            count = sum(
                any(n % (a * a) == 0 for a in range(minimum_factor, math.isqrt(n) + 1))
                for n in range(y + 1, 2 * y + 1)
            )
            assert count * (minimum_factor - 1) <= 2 * y
        odd_squarefree_count = sum(
            n % 2 == 1 and all(n % (a * a) != 0 for a in range(2, math.isqrt(n) + 1))
            for n in range(y + 1, 2 * y + 1)
        )
        assert odd_squarefree_count >= 3 * y / 8 - math.sqrt(2 * y) - 1


def test_square_dilation_does_not_preserve_two_letter_parity() -> None:
    """Exact integer witnesses; no asymptotic equidistribution is asserted."""

    for base, factor, expected_base_step, expected_dilated_step in (
        (3, 3, 5, 140),
        (7, 5, 18, 2315),
    ):
        start = factor**2 * base
        base_step = math.isqrt(base**3)
        dilated_step = math.isqrt(start**3)
        assert (base_step, dilated_step) == (expected_base_step, expected_dilated_step)
        assert base % 2 == start % 2 == 1
        assert base_step % 2 != dilated_step % 2
        assert start**3 == factor**6 * base**3
        assert dilated_step**2 <= factor**6 * base**3 < (dilated_step + 1) ** 2
        assert 0 <= dilated_step - factor**3 * base_step < factor**3


def test_squarefree_odd_odd_family_has_small_positive_floor_loss() -> None:
    """Exact bounded fixtures for the family, not a growing-depth count."""

    def squarefree(value: int) -> bool:
        return all(value % (a * a) != 0 for a in range(2, math.isqrt(value) + 1))

    parameters = [
        c for c in range(19, 401, 18)
        if all(squarefree(value) for value in (c, 2 * c - 1, 2 * c + 1))
    ]
    assert {19, 55, 91} <= set(parameters)
    for c in parameters:
        n, m = 4 * c**2 - 1, 8 * c**3 - 3 * c
        assert squarefree(n) and n % 2 == m % 2 == 1
        assert math.isqrt(m) ** 2 != m
        assert math.isqrt(n**3) == m
        assert n**3 - m**2 == 3 * c**2 - 1 > 0
        assert (5 * c * m + 1) ** 2 > 25 * c**2 * n**3
    for prime in (5, 7, 11):
        bad = [c for c in range(prime**2) if c * (2 * c - 1) * (2 * c + 1) % prime**2 == 0]
        assert len(bad) == 3


def test_squarefree_indicator_truncation_for_finite_all_odd_prefixes() -> None:
    """Exact Mobius identities and tail bounds, not asymptotic parity claims."""

    def mobius(value: int) -> int:
        sign, divisor = 1, 2
        while divisor * divisor <= value:
            if value % divisor == 0:
                value //= divisor
                if value % divisor == 0:
                    return 0
                sign = -sign
            divisor += 1
        return -sign if value > 1 else sign

    def all_odd(start: int, depth: int) -> int:
        for _ in range(depth):
            if start % 2 == 0:
                return 0
            start = math.isqrt(start**3)
        return 1

    for y in (10, 50, 100):
        for depth in (1, 3, 6):
            indicators = {n: all_odd(n, depth) for n in range(y + 1, 2 * y + 1, 2)}
            squarefree_count = sum(value for n, value in indicators.items() if mobius(n) != 0)
            for cutoff in (1, 2, 3, 5, 11, math.isqrt(2 * y) + 1):
                truncated = sum(
                    mobius(a) * sum(indicators.get(a * a * m, 0) for m in range(1, 2 * y // (a * a) + 1, 2))
                    for a in range(1, cutoff + 1, 2)
                )
                assert abs(squarefree_count - truncated) * cutoff <= 2 * y
                if cutoff**2 >= 2 * y:
                    assert squarefree_count == truncated


def test_two_successive_odd_floor_losses_have_exact_small_gap_bounds() -> None:
    """Finite nonsquare fixtures, not squarefree or growing-depth claims."""

    for a in (7, 9, 11, 17, 101, 1009):
        n = a**4 - 8
        m = a**6 - 12 * a**2
        z = a**9 - 18 * a**5 + 54 * a
        assert math.isqrt(n**3) == m
        assert math.isqrt(m**3) == z
        assert n % 2 == m % 2 == z % 2 == 1
        delta_one = n**3 - m**2
        delta_two = m**3 - z**2
        assert delta_one == 48 * a**4 - 512 > 0
        assert delta_two == 216 * a**6 - 2916 * a**2 > 0
        # Rationalizing the fractional errors gives denominators > 2m, 2z.
        assert delta_one * a**2 < 50 * m
        assert delta_two * a**3 < 225 * z
        assert math.isqrt(n) ** 2 != n
        assert math.isqrt(m) ** 2 != m
        if a != 9:
            assert all(a % divisor for divisor in range(2, math.isqrt(a) + 1))
            assert z % a == 0 and z % (a * a) != 0
            assert math.isqrt(z) ** 2 != z


def test_first_step_boundary_strip_exponents_and_pressure_cost() -> None:
    """Algebra for first-step trimming; no arithmetic census or deep estimate."""

    cutoff_exponent = Fraction(1, 6)
    discrepancy_exponent = Fraction(5, 6)
    assert 1 - cutoff_exponent == discrepancy_exponent
    assert Fraction(3, 4) + Fraction(1, 2) * cutoff_exponent == discrepancy_exponent
    p = p_of_C(19)
    theta = math.log(p / (1 - p))
    log_base = math.log((1 + math.exp(theta)) / 2)
    kappa = 19 * (theta - log_base) / math.log(2)
    assert math.isclose(kappa, 4.893426830351911, abs_tol=1e-12)
    assert kappa - 6 < -1
    # Exact certificate: p_19 < 3/5 and 19 log_2(6/5) < 5.
    assert 2**30 < 3**19
    assert 6**19 < 2**5 * 5**19
    assert Fraction(3, 2) * discrepancy_exponent == Fraction(5, 4) > 1



def test_pointwise_all_odd_benchmark_does_not_control_its_scale_sum() -> None:
    """Scalar counterexample to sufficiency; not alleged Juggler counts."""

    p = p_of_C(19)
    kappa = 19 * math.log2(2 * p)
    rate = 19 * (
        p * math.log(2 * p) + (1 - p) * math.log(2 * (1 - p))
    ) / math.log(2)
    eta = 0.01
    assert 0 < eta < rate + LAMBDA_V6 - 1
    assert kappa - 1 - eta < 4 < kappa - eta < 5
    for gamma, increasing in ((4, True), (5, False)):
        normalized_sums = [
            math.fsum(k ** (kappa - gamma) for k in range(1, K + 1))
            / K ** (1 + eta)
            for K in (64, 256, 1024)
        ]
        assert all(
            (right > left) == increasing
            for left, right in zip(normalized_sums, normalized_sums[1:])
        )
    assert math.isclose(1 + kappa - 5, 0.8934268303519122, abs_tol=1e-12)
    assert 2**30 < 3**19
    assert 6**19 < 2**5 * 5**19

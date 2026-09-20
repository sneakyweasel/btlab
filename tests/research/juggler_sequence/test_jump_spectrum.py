"""The jump spectrum: a closed form, and the guards against reading more into it."""

from __future__ import annotations

import json
from math import log

import pytest

from research.juggler_sequence.jump_spectrum import (
    A_ONE,
    OEIS_CHECKPOINTS,
    OEIS_ID,
    A_ZERO,
    BETA,
    KAPPA,
    LADDER_JUMP,
    LADDER_RATIO,
    CLASS_CLOSED_FORM,
    JSON_PATH,
    THETA,
    amplitude_ratio,
    barrier_index_consistency,
    class_coordinate_cost,
    fourier_coefficient,
    g_one_via_ladder,
    increment,
    ladder_fourier,
    ladder_profile,
    ladder_value,
    mean_value,
    orbit_series,
    orbit_series_truncation,
    barrier_index_constant,
    barrier_letter,
    ceil_beta,
    g_one,
    probe_payload,
    sturmian_zero_ratios,
    survivor_counts,
    total_variation,
)

# Enumerated by hand over all 2^d words; the same list guards `certificate_increment`.
SURVIVORS_1_TO_9 = [1, 1, 2, 3, 4, 8, 13, 19, 38]


@pytest.fixture(scope="module")
def counts() -> list[int]:
    return survivor_counts(600)


@pytest.fixture(scope="module")
def deep() -> list[int]:
    """Depth enough for the orbit series to be summed, not just the identity checked.

    `G(e(-k beta))` truncates like `psi * D^(-3/2) / |1 - e(k beta)|`, so a shallow run
    is fine for the exact-integer identities above and not for the Fourier side.
    """
    return survivor_counts(3000)


def test_height_program_reproduces_the_enumeration(counts) -> None:
    """The closed form is only worth anything if its `N_n` are the real survivor counts."""
    assert counts[1:10] == SURVIVORS_1_TO_9


def test_barrier_word_is_two_sided(counts) -> None:
    """`psi(x)` is read from a word running backwards past the origin, so the letters
    have to be defined at negative indices and agree with the forward ones there."""
    assert [barrier_letter(m) for m in range(1, 10)] == [1, 1, 0, 1, 1, 0, 1, 1, 0]
    assert [barrier_letter(m) for m in range(0, -5, -1)] == [0, 1, 0, 1, 1]
    assert all(barrier_letter(m) in (0, 1) for m in range(-200, 200))


def test_theta_is_the_constant_the_lean_side_uses() -> None:
    """`theta` here must be `PaperBChernoff.theta`, not a re-derivation of it."""
    assert THETA == pytest.approx(0.96590655, abs=1e-8)
    assert BETA == pytest.approx(0.63092975, abs=1e-8)


def test_the_sturmian_zero_ratio_is_exact_not_approximate(counts) -> None:
    """The ratio across a zero is `1/theta` to the last bit, not to a tolerance.

    This is the retracted `1/rho` law. An even barrier letter kills nothing, so the count
    doubles exactly, and `2 / (2 * theta)` is `1 / theta`. A tolerance here would hide
    that the statement is an identity rather than a measurement.
    """
    ratios = sturmian_zero_ratios(counts, 600)
    assert len(ratios) > 200
    assert all(r == 1.0 / THETA for r in ratios), "the law is exact; do not add a tolerance"


def test_rho_and_theta_were_the_same_number_all_along() -> None:
    """Guard on the correction this branch made.

    The `1/rho` law looked like a discovery because two names were in play for one
    constant. If `_rho` and `THETA` ever drift apart, the retraction recorded in the
    dossier stops making sense and somebody will re-discover the law.
    """
    from research.juggler_sequence.paper_b_prefix_count import _rho

    assert _rho() == THETA


def test_barrier_index_classes_are_consistent(counts) -> None:
    """`C_j` is well defined: the two `n` sharing a barrier index give the same constant.

    Exactly, again -- this is the empty-window theorem of `PaperBCertificateLengths` seen
    from the amplitude side.
    """
    assert barrier_index_consistency(counts, max_j=300) == 0.0


def test_barrier_index_constant_is_available_far_past_the_old_reach(counts) -> None:
    """The point of the branch: `C_j` at `j` the fits could not reach.

    Local differencing stopped near `j = 25` and no global fit went further, because the
    data cannot constrain a high-`n` jump at all. The closed form has no such limit.
    """
    assert barrier_index_constant(counts, 1) == pytest.approx(A_ONE, rel=1e-9)
    assert barrier_index_constant(counts, 300) > 0.0
    values = [barrier_index_constant(counts, j) for j in range(1, 301)]
    assert all(b < a for a, b in zip(values, values[1:])), "C_j must be strictly decreasing"


def test_amplitudes_decay_like_the_three_halves_power(counts) -> None:
    """`a_n = a_1 * 2 * theta * psi(x_n) * n^(-3/2)` asymptotically, so `a_n * n^(3/2)`
    settles onto the same band `psi` occupies rather than drifting."""
    scaled = [amplitude_ratio(counts, n) * n**1.5 / (2 * THETA) for n in (100, 200, 400, 600)]
    assert all(7.0 < s < 12.0 for s in scaled), scaled
    assert scaled[-1] > scaled[0], "the approach to psi is from below"


def test_summability_is_what_makes_psi_bounded_variation(counts) -> None:
    """`sum a_n` converges; it is `2 * theta * a_1 * (G(1) - 1)` and ties to `G(1)`."""
    tv = total_variation(counts)
    assert tv == pytest.approx(2 * THETA * A_ONE * (g_one(counts) - 1.0), rel=1e-12)
    # depth 600 truncates G(1) well short of 7.07, so the variation is an underestimate
    assert 3.5 < tv < 5.0


def test_g_one_is_the_same_object_as_the_jump_spectrum(counts) -> None:
    """A guard on the claim, not on a number: the partial sums must agree term by term."""
    partial = 1.0 + sum(amplitude_ratio(counts, n) / (2 * THETA) for n in range(1, 601))
    assert partial == pytest.approx(g_one(counts), rel=1e-12)


def test_a_one_is_closed_form_and_the_old_values_stay_withdrawn() -> None:
    """`a_1` is not measured, and the two values that were must not come back.

    Both were biased low, by different mechanisms, and both were recorded on the same
    day as the closed form that replaced them. A test that merely checked the current
    number would not stop either from being re-derived.
    """
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["a_one"]["measured"] is False
    assert data["a_one"]["value"] == pytest.approx(A_ONE, rel=1e-12)
    assert sorted(data["a_one"]["withdrawn"]) == [0.42623, 0.426289]
    for gone in data["a_one"]["withdrawn"]:
        assert abs(gone - A_ONE) > 1e-3, "a withdrawn value must not sit on the answer"
    assert "closed form, not measured" in data["a_one"]["note"]


def test_probe_does_not_claim_to_have_determined_psi() -> None:
    """The jumps are not the function.

    Jumps plus the linear rise periodicity demands leaves a residual well above the noise
    floor, and most of that residual is reproducible in the coordinate. The artifact must
    say so, or `psi` looks solved when only its discontinuities are.
    """
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    text = data["anti_overclaim"]
    assert "determines the jumps of psi, not psi" in text
    assert "1.35e-02" in text and "4.4e-03" in text
    assert "psi itself remains measured" in text


def test_committed_artifact_records_the_closed_form() -> None:
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["decision"]["classification"] == CLASS_CLOSED_FORM
    assert data["identity"] == "a_n = a_1 * N_n / (2*theta)^(n-1)"
    assert data["survivors_1_to_9"] == SURVIVORS_1_TO_9
    assert data["sturmian_zeros"]["worst_relative_deviation"] == 0.0
    assert data["barrier_index"]["worst_class_disagreement"] == 0.0
    assert "two independent ways" in data["decision"]["reason"]


def test_the_retraction_travels_with_the_artifact() -> None:
    """Why the `1/rho` law is trivial has to be recorded where the law was."""
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    why = data["sturmian_zeros"]["why_trivial"]
    assert "rho and theta are the same number" in why
    assert "empty-window theorem" in why


def test_a_cheap_run_reaches_the_same_answer() -> None:
    """The result must not depend on the committed depth."""
    payload = probe_payload(max_depth=300)
    assert payload["decision"]["classification"] == CLASS_CLOSED_FORM
    assert payload["sturmian_zeros"]["worst_relative_deviation"] == 0.0
    assert payload["survivors_1_to_9"] == SURVIVORS_1_TO_9


def test_ceil_beta_is_exact_where_float_rounding_would_differ() -> None:
    """`ceil(n*beta)` decides class membership, so a wrong rounding merges two classes."""
    for n in (485, 84, 19, 65, 306, 1000, 2000):
        assert ceil_beta(n) == -(-int(n * BETA * 10**12) // 10**12) or ceil_beta(n) >= 1
    assert ceil_beta(0) == 0
    assert ceil_beta(1) == 1
    assert ceil_beta(-1) == 0
    assert all(ceil_beta(n) - ceil_beta(n - 1) in (0, 1) for n in range(-50, 500))


def test_fourier_coefficients_are_the_series_on_the_rotation_orbit(deep) -> None:
    """`psihat_k = -(2*theta*a_1/(2*pi*i*k)) * G(e(-k*beta))`.

    The values below were measured independently from `psi` itself, by integrating a
    twenty-thousand-level fit of the depth-1e6 prefactor against `e(-k x)`. Agreement
    is the whole claim: the Fourier data of the meander prefactor is the Wiener-Hopf
    series on the rotation orbit, which is what
    `J-paper-b-meander-constant-derived` records as missing.
    """
    measured = {1: 9.940101e-02, 2: 5.977094e-02, 3: 5.599551e-02,
                5: 2.824229e-02, 12: 7.093994e-03, 20: 4.551511e-03}
    for k, value in measured.items():
        predicted = abs(fourier_coefficient(deep, k))
        assert predicted == pytest.approx(value, rel=0.02), k


def test_the_coefficients_scale_with_the_one_constant(deep) -> None:
    """Every `k != 0` coefficient is proportional to `a_1`, exactly and by construction.

    This is what makes the Fourier route a good measurement of `a_1`: it fits one
    constant against sixty modes instead of separating one jump from its neighbours.
    """
    for k in (1, 7, 30):
        base = fourier_coefficient(deep, k, a_one=1.0)
        assert fourier_coefficient(deep, k, a_one=0.5) == pytest.approx(0.5 * base)
        assert fourier_coefficient(deep, k, a_one=2.0) == pytest.approx(2.0 * base)


def test_the_mean_carries_no_amplitude_which_is_why_the_fixed_point_fails(deep) -> None:
    """`psihat_0 = kappa * G(1)` is the one coefficient in closed form without `a_1`.

    That is not a detail, it is the obstruction. The relation `a_n = A*psi(x_n)*n^(-3/2)`
    with periodicity is affine in `psi` -- `psi = C*1 + A*L[psi]` -- so it has a solution
    `C*(I - A*L)^(-1)[1]` for every `A` and selects none. The only coefficient that could
    have closed the loop is the only one `A` does not appear in.
    """
    assert "a_one" not in mean_value.__code__.co_varnames
    # measured directly from psi at depth 1e6: 10.8864. The probe reaches it only to the
    # accuracy of its own truncated G(1), so the band here is the truncation, not psi.
    assert mean_value(deep) == pytest.approx(10.89, abs=0.06)
    assert KAPPA == pytest.approx(1.541814521, abs=1e-9)


def test_truncation_of_the_orbit_series_is_reported_not_assumed(counts, deep) -> None:
    """A mode near a convergent denominator of `beta` is the slow one, not a large `k`.

    The phases cancel, so the honest bound is by partial summation and depends on how
    close `k*beta` sits to an integer. Stating it as `2*psi/sqrt(depth)` would be true
    and useless.
    """
    for k in (1, 2, 3, 5, 20):
        shallow = orbit_series_truncation(counts, k)
        deeper = orbit_series_truncation(deep, k)
        assert deeper < shallow, k
        assert deeper < 2e-4, k
    # 65 is a convergent denominator of beta, so `65 * beta` is the closest of these to
    # an integer, the phases barely cancel, and its series converges an order of
    # magnitude slower than its neighbour's. That is the whole reason to bound by
    # partial summation instead of absolutely: the slow modes are the arithmetically
    # special ones, not the large ones.
    assert orbit_series_truncation(deep, 65) > 5 * orbit_series_truncation(deep, 64)
    assert orbit_series_truncation(deep, 65) < 5e-3
    assert abs(orbit_series(deep, 1)) == pytest.approx(0.7584, rel=2e-3)


def test_the_ladder_profile_is_an_exponential_whose_mean_is_kappa() -> None:
    """`A_n sqrt(n)` is a function of `frac(n beta)`, not a constant, and it is closed form.

    `kappa` is its mean -- identically, not numerically: `beta/(1-beta) = log2/log(3/2)`,
    so `log(beta/(1-beta)) = theta* log 3` and `sqrt(2 pi beta (1-beta))` is
    `sqrt(2 pi) sigma / log 3`. If these ever disagree, the ladder picture is wrong and
    the closed form for `a_1` goes with it.
    """
    assert KAPPA == pytest.approx(1.541814521, abs=1e-9)
    grid = [i / 2000 for i in range(2000)]
    mean = sum(ladder_profile(x) for x in grid) / len(grid)
    assert mean == pytest.approx(KAPPA, rel=1e-3)
    assert ladder_profile(1.0) - ladder_profile(0.0) == pytest.approx(LADDER_JUMP, rel=1e-12)
    assert LADDER_RATIO == pytest.approx((1 - BETA) / BETA, rel=1e-12)
    # convex, because it is an exponential rather than the sawtooth it first looked like
    mid = ladder_profile(0.5)
    chord = 0.5 * (ladder_profile(0.0) + ladder_profile(1.0))
    assert mid < chord, "Phi is an exponential, not a straight ramp"


def test_the_jump_of_psi_is_the_jump_of_the_ladder() -> None:
    """`psihat_k = Phihat_k G(e(-k beta))` for every `k`, which is where `a_1` comes from.

    Measured mode by mode on `psi` at depth `1e6`, the magnitude ratio is
    `1.0015 +/- 0.0020` over `k <= 256`, and the free-amplitude level fit extrapolates
    in `1/sqrt(N)` to `0.428027` against this `0.427957`.
    """
    assert A_ZERO == pytest.approx(LADDER_JUMP, rel=1e-12)
    assert A_ONE == pytest.approx(A_ZERO / (2 * THETA), rel=1e-12)
    assert A_ONE == pytest.approx(0.427956804, abs=1e-9)
    # the 1/k tail of Phihat is the jump and nothing else
    for k in (8, 40, 200):
        assert k * abs(ladder_fourier(k)) == pytest.approx(LADDER_JUMP / (2 * 3.141592653589793),
                                                           rel=2e-3), k
    assert ladder_fourier(0).real == pytest.approx(KAPPA, rel=1e-12)


def test_the_increment_is_the_shape_with_no_free_parameter(counts) -> None:
    """`r_d = 1 - theta t_d/t_(d-1)` exactly, so within a fixed coordinate
    `r_d = a + b/d` with `b = (3/2)(1 - a)` and nothing fitted."""
    for d in (50, 137, 300):
        assert increment(counts, d) == pytest.approx(
            1.0 - counts[d] / (2.0 * counts[d - 1]), rel=1e-12)
        assert 0.0 < increment(counts, d) < 0.5


def test_a_residue_class_loses_a_square_root_on_a_jump_function() -> None:
    """Why the certificate-increment tension was the method and not the shape.

    A class modulo `q` fixes the rotation coordinate to `|frac(q beta)|`, and the method
    assumes the target then moves by that much. `psi` moves by about `17 sqrt` of it,
    because its jumps are dense. At the period the branch used, `485`, that is `4.8%` of
    `psi` against a `1/d` signal of a few percent -- so `b` was never measurable there.
    """
    coarse = class_coordinate_cost(485)
    fine = class_coordinate_cost(50508)
    assert coarse["coordinate_drift"] == pytest.approx(9.3e-4, rel=0.02)
    assert coarse["as_share_of_psi"] > 0.04, "485 cannot resolve a percent-level signal"
    assert fine["coordinate_drift"] < coarse["coordinate_drift"] / 100
    # the square root is the point: 140x finer coordinate buys only 12x less variation
    ratio_drift = coarse["coordinate_drift"] / fine["coordinate_drift"]
    ratio_var = coarse["psi_variation"] / fine["psi_variation"]
    assert ratio_var == pytest.approx(ratio_drift ** 0.5, rel=1e-6)
    assert ratio_drift > 100 and ratio_var < 15


def test_the_ladder_value_tends_to_the_closed_form_profile() -> None:
    """`A_n sqrt(n)` against `Phi(frac(n beta))`, with the gap a `1/n` offset."""
    from decimal import Decimal, getcontext
    getcontext().prec = 60
    beta = Decimal(2).ln() / Decimal(3).ln()
    errs = {}
    for n in (2000, 8000, 20000):
        x = float((beta * n) % 1)
        errs[n] = ladder_value(n) * n ** 0.5 / ladder_profile(x) - 1
    assert all(e < 0 for e in errs.values()), "the profile is approached from below"
    assert abs(errs[20000]) < abs(errs[2000]) / 5, "the gap must fall like 1/n"
    assert abs(errs[20000]) < 2e-3


def test_g_one_agrees_from_two_routes_that_share_nothing(counts) -> None:
    """`G(1)` from the survivor counts and from Spitzer must agree.

    `g_one` sums `N_d/(2 theta)^d`. `g_one_via_ladder` exponentiates `sum_n A_n/n` with
    `A_n` an exact binomial tail and the closed-form profile for the tail, and never
    touches `N_d`. Agreement is a cross-check of the whole picture -- Spitzer, the
    profile, the counts -- rather than a restatement of any of it.
    """
    cheap = g_one_via_ladder(head=6000, tail=200_000)
    assert cheap == pytest.approx(7.0649, rel=3e-4)
    assert cheap == pytest.approx(7.064862, rel=1e-3)


def test_the_survivors_are_oeis_a076227() -> None:
    """The counts are a known sequence, checked against its b-file rather than its head.

    Agreeing on nine terms would mean little; these checkpoints reach `n = 3508`, where
    the value has 999 digits, and they come from Hikawa and Nakanishi's table rather
    than from anything computed here. A drift anywhere in the height program would show.
    """
    assert OEIS_ID == "A076227"
    deep = survivor_counts(max(OEIS_CHECKPOINTS))
    for n, (lead, digits) in OEIS_CHECKPOINTS.items():
        value = str(deep[n])
        assert len(value) == digits, n
        assert value.startswith(lead), n


def test_the_literature_reading_is_not_independent() -> None:
    """Guard on the correction: the sequence is not a laboratory invention.

    The dossier first recorded this cluster's literature status as `independent`. It is
    not, for the counting sequence: A076227 has been in OEIS since 2002 as a Collatz
    stopping-time quantity. The asymptotic is a separate question and is flagged as
    unchecked rather than claimed.
    """
    doc = (JSON_PATH.parent.parent / "problems" / "juggler_jump_spectrum.md")
    body = doc.read_text(encoding="utf-8").split("## Current literature")[1]
    # prose is line-wrapped, so a phrase can straddle a newline; flatten before matching
    section = " ".join(body.split(chr(10) + "## ")[0].split())
    assert "A076227" in section
    assert "Not independent" in section
    assert "`independent`. A laboratory question" not in section, "the old reading is back"
    # and the priority question must travel with it, not be quietly dropped
    assert "priority" in section
    assert "none of which have been read here" in section
    assert "should be called new" in section


def test_the_survivor_rate_is_lagarias_1985_theorem_d() -> None:
    """This cluster's theta IS Lagarias's eta, and the link is one line.

    Lagarias 1985, Theorem D, states 1 - F(k) <= 2^(-eta k) with
    eta = 1 - H(theta_L), H the binary entropy and theta_L = (log_2 3)^(-1),
    which is our beta. Our survivor rate is theta = beta^(-beta)
    (1-beta)^(beta-1) / 2. These are the same number, not numerically but
    algebraically:

        2^(-eta) = 2^(H(beta) - 1)
                 = beta^(-beta) (1-beta)^(-(1-beta)) / 2
                 = beta^(-beta) (1-beta)^(beta-1) / 2
                 = theta.

    Checked here at 50 digits, where the difference is exactly zero. So the
    laboratory's headline constant 0.9659065532 has been in print since 1985,
    and `neverNegCount_div_pow_le_theta` is Theorem D's upper half.

    The same rescaling explains Hikawa's weight-basis constants: gamma =
    H(beta)/beta and c = eta/beta, so his 1.5056 and 0.0793 are Lagarias's eta
    divided by beta and his Section 6 is an independent proof of the same
    rate. Kontorovich-Lagarias 2009 quote it as O(2^(0.94995 k)), and
    0.94995 is H(beta) = log_2(2 theta).

    WHAT THIS DOES NOT TOUCH: the prefactor. No source read states an
    oscillating or almost-periodic prefactor in frac(d beta), an amplitude, or
    anything equivalent to the jump spectrum. The rate is Lagarias's, the
    d^(-3/2) is Hikawa's Conjecture 7.1, and what is this laboratory's is that
    the prefactor exists, oscillates on the rotation orbit, and is computable.
    """
    from mpmath import mp, mpf, log, power

    with mp.workdps(50):
        beta = log(2) / log(3)
        entropy = -(beta * log(beta, 2) + (1 - beta) * log(1 - beta, 2))
        eta = 1 - entropy

        theta = power(beta, -beta) * power(1 - beta, beta - 1) / 2
        assert abs(theta - power(2, -eta)) < mpf(10) ** -45

        # the published decimals, each to the digits the source prints
        assert abs(eta - mpf("0.050044472811669365186")) < mpf(10) ** -20
        assert abs(theta - mpf("0.9659065532334377236055")) < mpf(10) ** -20
        assert abs(entropy / beta - mpf("1.5056438879463007943")) < mpf(10) ** -18
        assert abs(eta / beta - mpf("0.079318612774855387135")) < mpf(10) ** -20
        assert abs(log(2 * theta, 2) - mpf("0.9499555271883306348")) < mpf(10) ** -18

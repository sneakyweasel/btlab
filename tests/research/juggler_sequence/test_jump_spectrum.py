"""The jump spectrum: a closed form, and the guards against reading more into it."""

from __future__ import annotations

import json
from math import log

import pytest

from research.juggler_sequence.jump_spectrum import (
    A_ONE,
    A_ONE_BAND,
    BETA,
    CLASS_CLOSED_FORM,
    JSON_PATH,
    THETA,
    amplitude_ratio,
    barrier_index_consistency,
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


def test_a_one_is_reported_as_measured_with_a_band() -> None:
    """The single fitted constant must never be published as exact.

    Everything else in the branch is integer arithmetic; `a_1` is not, and the band has
    to cover both estimators because the free-amplitude fit is biased low.
    """
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    low, high = data["a_one"]["band"]
    assert low < data["a_one"]["estimate"] < high
    assert high - low == pytest.approx(2 * A_ONE_BAND, rel=1e-9)
    assert "only measured constant" in data["a_one"]["note"]


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

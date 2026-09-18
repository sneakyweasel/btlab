"""The certificate increment probe: exact counts, and a refutation that holds."""

from __future__ import annotations

import json

import pytest

from research.juggler_sequence.certificate_increment import (
    BETA,
    CLASS_REFUTED,
    JSON_PATH,
    PERIOD,
    PERIOD_SMALL,
    class_fits,
    increment,
    probe_payload,
    survivor_counts,
    theta,
)

# Enumerated by hand in the branch dossier over all 2^d words, d <= 9 and d <= 16.
SURVIVORS_1_TO_9 = [1, 1, 2, 3, 4, 8, 13, 19, 38]
MINIMAL_1_TO_16 = [1, 1, 0, 1, 2, 0, 3, 7, 0, 12, 0, 30, 85, 0, 173, 476]


@pytest.fixture(scope="module")
def counts() -> tuple[dict[int, int], dict[int, int]]:
    return survivor_counts(400)


def test_dynamic_program_reproduces_the_enumeration(counts) -> None:
    """The DP is only trustworthy if it agrees with brute force where both run."""
    survivors, minimal = counts
    assert [survivors[d] for d in range(1, 10)] == SURVIVORS_1_TO_9
    assert [minimal[d] for d in range(1, 17)] == MINIMAL_1_TO_16


def test_the_recursion_holds_at_every_depth(counts) -> None:
    """`N_(d+1) + M_(d+1) = 2 N_d`, the identity proved in PaperBCertificateRecursion."""
    survivors, minimal = counts
    for d in range(0, 400):
        assert survivors[d + 1] + minimal[d + 1] == 2 * survivors[d], d


def test_minimal_count_vanishes_exactly_on_the_empty_window(counts) -> None:
    """`M_L = 0` exactly when no power of three lies in `[2^(L-1), 2^L)`."""
    _, minimal = counts
    for L in range(1, 400):
        window = any(2 ** (L - 1) <= 3 ** o < 2 ** L for o in range(0, L + 1))
        assert (minimal[L] > 0) == window, L


def test_the_empty_lengths_start_three_six_nine_eleven_fourteen(counts) -> None:
    """The plateau lengths of the length branch, from the other side."""
    _, minimal = counts
    empty = [L for L in range(1, 17) if minimal[L] == 0]
    assert empty == [3, 6, 9, 11, 14]


def test_theta_matches_the_lean_constant() -> None:
    """`theta(beta)` as `PaperBChernoff.theta` computes it, to nine places."""
    assert theta(BETA) == pytest.approx(0.96590655, abs=1e-8)


def test_every_residue_class_is_monotone_in_depth(counts) -> None:
    """The refutation: a class fixes the rotation coordinate, yet the values move.

    Were `r_d` a function of `frac(d * beta)` alone the members of a class would
    scatter about one value. Scattered values are monotone by chance a few
    percent of the time; every class being monotone is motion in `d`.
    """
    survivors, minimal = counts
    fits = class_fits(survivors, minimal, max_depth=400, fit_from=100, period=PERIOD_SMALL)
    assert len(fits) >= 20
    for f in fits:
        ys = [increment(survivors, minimal, d) for d in f["depths"]]
        down = all(a > b for a, b in zip(ys, ys[1:]))
        up = all(a < b for a, b in zip(ys, ys[1:]))
        assert down or up, f["residue"]


def test_the_effect_is_present_at_a_cheap_depth() -> None:
    """A coarse period sees the effect but cannot resolve it.

    `PERIOD_SMALL` fixes the rotation coordinate only to `1.9e-3`, so a class can
    straddle a jump in the limiting function and break monotonicity. Most classes
    are still monotone, which is the effect; the sharp statement needs
    `PERIOD` and the committed depth, and is asserted against the artifact below.
    """
    payload = probe_payload(max_depth=700, fit_from=200, period=PERIOD_SMALL)
    assert payload["answer"] == "no"
    assert payload["classes_fitted"] >= 20
    assert payload["monotone_share"] > 0.8
    assert payload["coordinate_control"]["share_beating_drift_bound"] == 1.0


def test_committed_artifact_records_the_refutation() -> None:
    """The committed run, at `PERIOD` and the full depth, is the decisive one."""
    data = json.loads(JSON_PATH.read_text(encoding="utf-8"))
    assert data["answer"] == "no"
    assert data["decision"]["classification"] == CLASS_REFUTED
    assert data["monotone_share"] == 1.0, "every class must be monotone in d"
    assert data["period"] == PERIOD
    assert data["classes_fitted"] >= 200


def test_probe_does_not_claim_the_meander_shape_is_refuted() -> None:
    """The tension must stay a tension: this probe refutes one reading, not a shape."""
    payload = probe_payload(max_depth=700, fit_from=200, period=PERIOD_SMALL)
    reason = payload["decision"]["reason"]
    assert "tension, not a refutation of the shape" in reason
    assert "neither proves nor refutes the meander shape" in payload["anti_overclaim"]

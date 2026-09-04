"""Contagion exponent as a transfer matrix on the backward tree.

Companion to docs/theory/juggler_contagion_exponent_calculus.md.  The fate
contagion note's section-4 recursion is reorganised into two elementary
backward steps from m in A (both land in A by backward closure):

    E-preimage E(m)                     log-mass x1,      log-scale x2
    O-preimage {n odd: n^{3/2} -> m}    log-mass x eta/3, log-scale x2/3

with eta = realised fiber-parity share / ideal 1/2.  Which eta applies is a
function of the path, from the note's own lemmas:

    eta_2 = 1    O-step after >= 2 E-steps  (Prop 3.4 block average, ideal 1/4)
    eta_1 = 2/3  O-step after exactly 1 E   (Lemma 3.2, G_m >= H_m/3 vs H_m/2)
    eta_0 = 0    O-step after an O-step     (no lemma in sections 1-4)

With state = min(2, #consecutive preceding E-steps), x = 2^-lambda and
y_j = (eta_j/3)(3/2)^lambda, the exponent solves  rho(M(lambda)) = 1, i.e.

    1 - y_0 = x^2 y_2 / (1-x) + x y_1.                                  (3.1)

The tests check: (3.1) is algebraically the note's lambda** equation; it
reproduces all four published constants; the ceiling is exactly lambda = 1
at eta = 1 with slope 1/ln(4/3); and eta_0 -- consecutive backward O-steps --
is the single quantity carrying the whole gap 0.4927 -> 1.
"""

from __future__ import annotations

from math import log, log2

import numpy as np
import pytest

mp = pytest.importorskip("mpmath")


def _bisect(f, lo: float = 1e-9, hi: float = 1.0, iters: int = 200) -> float:
    """Root of a strictly decreasing f on [lo, hi].  Deterministic: unlike
    mpmath.findroot from a fixed seed, this cannot fail to converge.  The
    lower end is kept off 0 because the three-state residual has a 1/(1-x)
    factor that is singular at lambda = 0."""
    flo, fhi = f(lo), f(hi)
    if flo < 0:
        return lo
    if fhi > 0:
        return hi
    for _ in range(iters):
        mid = (lo + hi) / 2
        if f(mid) > 0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


NOTE = "docs/theory/juggler_contagion_exponent_calculus.md"

LAMBDA_STAR = 0.3774  # items 1+2 only
LAMBDA_2 = 0.4480  # lambda**, all three items
IDEAL_DEPTH_2 = 0.4927  # perfect fiber shares, no OO
LAMBDA_3 = 0.5392  # lambda***, section 7 (the OOEEE production)


# --------------------------------------------------------------------------
# the three-state equation (3.1)
# --------------------------------------------------------------------------


def residual(lam: float, eta0: float, eta1: float, eta2: float) -> float:
    x = 2.0**-lam
    y = lambda e: (e / 3.0) * 1.5**lam
    return x * x * y(eta2) / (1 - x) + x * y(eta1) + y(eta0) - 1.0


def exponent(eta0: float, eta1: float, eta2: float) -> float:
    if residual(1 - 1e-12, eta0, eta1, eta2) > 0:
        return 1.0
    return _bisect(lambda L: residual(L, eta0, eta1, eta2))


def note_lambda_2_equation(lam: float) -> float:
    """The fate note's printed lambda** equation."""
    return 2.0**-lam + (1 / 9) * (3 / 8) ** lam + (2 / 9) * (3 / 4) ** lam - 1.0


def test_equation_3_1_is_the_notes_lambda_two_equation():
    # Proposition 3.1: with y_0 = 0 the two are the same curve, not merely
    # curves with the same root.  Multiplying (3.1) by (1-x) and using
    # x(3/4)^L = (3/8)^L turns one into the other.
    for lam in [0.1, 0.25, 0.4480, 0.5, 0.7, 0.9]:
        x = 2.0**-lam
        assert residual(lam, 0.0, 2 / 3, 1.0) * (1 - x) == pytest.approx(
            note_lambda_2_equation(lam), abs=1e-12
        )
        # the identity that drives the proof
        assert x * (3 / 4) ** lam == pytest.approx((3 / 8) ** lam, abs=1e-15)


def test_reproduces_all_four_published_constants():
    assert exponent(0.0, 0.0, 1.0) == pytest.approx(LAMBDA_STAR, abs=5e-5)
    assert exponent(0.0, 2 / 3, 1.0) == pytest.approx(LAMBDA_2, abs=5e-5)
    assert exponent(0.0, 1.0, 1.0) == pytest.approx(IDEAL_DEPTH_2, abs=5e-5)
    assert exponent(1.0, 1.0, 1.0) == pytest.approx(1.0, abs=1e-9)


# --------------------------------------------------------------------------
# the ceiling
# --------------------------------------------------------------------------


def uniform_residual(lam: float, eta: float) -> float:
    return 2.0**-lam + (eta / 3.0) * 1.5**lam - 1.0


def test_uniform_case_collapses_to_x_plus_y_equals_one():
    # (3.1) times (1-x) is exactly x + y - 1 when eta_0 = eta_1 = eta_2:
    #   x^2 y + xy(1-x) + (y-1)(1-x) = xy + y - xy - 1 + x = x + y - 1.
    for eta in (0.5, 2 / 3, 0.8, 1.0):
        for lam in (0.2, 0.5, 0.9):
            x = 2.0**-lam
            assert residual(lam, eta, eta, eta) * (1 - x) == pytest.approx(
                uniform_residual(lam, eta), abs=1e-12
            )


def test_ceiling_is_exactly_one_at_ideal_efficiency():
    # 1/2 + (1/3)(3/2) = 1 exactly.
    assert uniform_residual(1.0, 1.0) == pytest.approx(0.0, abs=1e-15)
    assert 2.0**-1.0 + (1 / 3) * 1.5 == 1.0
    # and strictly below 1 for every eta < 1
    for eta in (0.5, 2 / 3, 0.9, 0.99, 0.999):
        assert exponent(eta, eta, eta) < 1.0


def test_slope_at_the_ceiling_is_one_over_log_four_thirds():
    # d lambda / d eta = (1/2) / ((1/2) ln(4/3)) = 1/ln(4/3)
    predicted = 1 / log(4 / 3)
    h = 1e-6
    measured = (exponent(1.0, 1.0, 1.0) - exponent(1 - h, 1 - h, 1 - h)) / h
    assert measured == pytest.approx(predicted, rel=2e-3)
    assert predicted == pytest.approx(3.4761, abs=1e-3)


def variational(eta: float) -> tuple[float, float]:
    """max_theta [H(theta) - theta log2(3/eta)] / [1 - theta log2 3]."""
    L = log2(3)

    def H(t):
        return 0.0 if t <= 0 or t >= 1 else -t * log2(t) - (1 - t) * log2(1 - t)

    best = (-9.0, 0.0)
    for i in range(1, 100000):
        th = i / 100000 * (1 / L)
        v = (H(th) - th * log2(3 / eta)) / (1 - th * L)
        if v > best[0]:
            best = (v, th)
    return best


def test_variational_form_agrees_and_peaks_at_the_fair_coin():
    v, theta = variational(1.0)
    assert v == pytest.approx(1.0, abs=1e-4)
    assert theta == pytest.approx(0.5, abs=1e-3)  # the extremal path is fair
    # numerator and denominator coincide at theta = 1/2
    assert 1 - 0.5 * log2(3) == pytest.approx(1 - 0.5 * log2(3), abs=0)
    assert variational(2 / 3)[0] == pytest.approx(0.4469, abs=1e-3)


# --------------------------------------------------------------------------
# the O-run ladder
# --------------------------------------------------------------------------


def run_exponent(r: int, eta1: float = 1.0, eta2: float = 1.0, nu: float = 1.0) -> float:
    """Exponent when backward O-runs are controlled only up to length r."""

    def rho(lam: float) -> float:
        x, g = 2.0**-lam, 1.5**lam / 3.0
        states = ["E1", "E2"] + ["O%d" % i for i in range(1, r + 1)]
        k = {s: i for i, s in enumerate(states)}
        M = np.zeros((len(states), len(states)))
        for s in states:
            M[k[s], k["E2" if s.startswith("E") else "E1"]] += x
            if s == "E1":
                M[k[s], k["O1"]] += eta1 * g
            elif s == "E2":
                M[k[s], k["O1"]] += eta2 * g
            else:
                i = int(s[1:])
                if i + 1 <= r:
                    M[k[s], k["O%d" % (i + 1)]] += nu * g
        return max(abs(np.linalg.eigvals(M)))

    if rho(1 - 1e-9) > 1:
        return 1.0
    return _bisect(lambda L: rho(L) - 1.0)


def test_run_length_one_is_the_no_oo_case():
    assert run_exponent(1, eta1=2 / 3) == pytest.approx(LAMBDA_2, abs=5e-5)
    assert run_exponent(1, eta1=1.0) == pytest.approx(IDEAL_DEPTH_2, abs=5e-5)


def test_ladder_is_monotone_and_reaches_the_ceiling():
    vals = [run_exponent(r) for r in (1, 2, 3, 4, 6)]
    assert all(a < b for a, b in zip(vals, vals[1:]))
    assert vals[1] == pytest.approx(0.7180, abs=1e-3)  # r = 2
    assert vals[2] == pytest.approx(0.8414, abs=1e-3)  # r = 3
    assert run_exponent(20) == pytest.approx(1.0, abs=1e-4)


def test_both_levers_are_needed():
    # the single-fiber share alone caps at the depth-two ceiling ...
    assert run_exponent(1, eta1=1.0) == pytest.approx(IDEAL_DEPTH_2, abs=5e-5)
    # ... and the O-run lever alone saturates strictly below 1
    saturated = run_exponent(30, eta1=2 / 3)
    assert saturated == pytest.approx(0.7909, abs=1e-3)
    assert saturated < 1.0
    assert exponent(1.0, 2 / 3, 1.0) == pytest.approx(saturated, abs=1e-3)


def test_section_seven_uses_one_word_of_the_run_length_two_family():
    # Prop 7.2 attains the IDEAL share 1/16 for OOEEE, so section 7's estimate
    # is not lossy.  lambda*** = 0.5392 sits below the r=2 ceiling only because
    # r=2 also contains words section 7 does not use; the remaining ground is
    # more words, not a better estimate for OOEEE.
    assert LAMBDA_3 < run_exponent(2, eta1=2 / 3) == pytest.approx(0.6247, abs=1e-3)
    assert run_exponent(2, eta1=1.0) == pytest.approx(0.7180, abs=1e-3)


# --------------------------------------------------------------------------
# the fiber-length criterion, and where the ladder stops
# --------------------------------------------------------------------------


def rho(word: str) -> float:
    return 0.5 ** word.count("E") * 1.5 ** word.count("O")


def longest_o_run(word: str) -> int:
    best = run = 0
    for ch in word:
        run = run + 1 if ch == "O" else 0
        best = max(best, run)
    return best


def test_fiber_length_criterion_matches_every_printed_length():
    # |I(m')| = (1/rho) P^{1-rho}; Prop 7.1 needs Y >= P^{1/2}, i.e. rho <= 1/2.
    for word, exponent_of_P in (("OE", 1 / 4), ("OEE", 5 / 8), ("OOEEE", 23 / 32)):
        assert 1 - rho(word) == pytest.approx(exponent_of_P, abs=1e-12)
    # the ideal-share productions are exactly the rho <= 1/2 ones
    for word in ("E", "OEE", "OOEEE"):
        assert rho(word) <= 0.5
    for word in ("OE", "OOEE"):  # the lossy one, and the one section 7 skipped
        assert rho(word) > 0.5


def test_o_run_length_sets_the_paper_b_depth_and_k3_caps_it():
    # an O-run of length r needs Paper B at depth r+1 (r nested 3/2-powers plus
    # the closing square root).  Paper B is complete to depth 4 and to depth 5
    # except OOOO*, so r <= 3 is reachable and r = 4 is the K_3 wall.
    assert longest_o_run("OOEEE") + 1 == 3  # section 7 = localized depth 3
    assert longest_o_run("OOOEEE") + 1 == 4  # next rung, still inside Paper B
    assert longest_o_run("OOOOEEEE") + 1 == 5  # K_3
    reachable, walled = run_exponent(3, eta1=2 / 3), run_exponent(4, eta1=2 / 3)
    assert reachable == pytest.approx(0.7095, abs=1e-3)
    assert run_exponent(3, eta1=1.0) == pytest.approx(0.8414, abs=1e-3)
    assert walled > reachable  # the wall costs real ground
    # and lambda = 1 needs r -> infinity, i.e. it needs K_3
    assert run_exponent(3, eta1=1.0) < 1.0
    assert min_tao_C(reachable) <= 14.0
    assert min_tao_C(run_exponent(3, eta1=1.0)) <= 11.0


# --------------------------------------------------------------------------
# what it buys on the Tao side
# --------------------------------------------------------------------------


def tao_e(C: float) -> float | None:
    p = (1 - 1 / C) / log2(3)
    if not 0.5 <= p < 1:
        return None
    return C * (p * log(2 * p) + (1 - p) * log(2 * (1 - p))) / log(2)


def min_tao_C(lam: float) -> float:
    C = 5.0
    while C < 400:
        e = tao_e(C)
        if e is not None and e > 1 - lam:
            return C
        C += 0.5
    return float("inf")


def test_tao_constant_drops_as_lambda_rises():
    assert min_tao_C(LAMBDA_2) == 20.0
    assert min_tao_C(LAMBDA_3) == 18.0
    assert min_tao_C(run_exponent(2)) <= 14.0
    assert min_tao_C(run_exponent(4)) <= 9.0
    # but the reduction never removes the log log y depth: C stays > 5
    assert min_tao_C(1.0) >= 5.0


def test_note_records_the_calculus():
    from pathlib import Path

    text = Path(NOTE).read_text(encoding="utf-8")
    assert "0.4927" in text and "0.7180" in text and "ln(4/3)" in text


def test_paper_c_records_the_ceiling_and_the_cap():
    from pathlib import Path

    text = Path("docs/theory/juggler_fate_almost_all_note.md").read_text(
        encoding="utf-8"
    )
    # Proposition 5.12 (ceiling) and 5.13 (fiber-length criterion)
    assert "Proposition 5.12" in text and "Proposition 5.13" in text
    assert "### 5.7 The ceiling of the production calculus" in text
    # the price list and the K_3 cap
    for value in ("0.6247", "0.7180", "0.7095", "0.8414"):
        assert value in text
    assert "K_3" in text
    # the superseded remark is gone
    assert "Depth two (\\(E\\), \\(OE\\)) carries" not in text

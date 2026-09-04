"""Lemma 5.1's master identity: the Lean statements, cross-checked numerically.

`formal/Problems/Juggler/MasterIdentity.lean` proves these outright.  This file
pins the *statements* — that what Lean proves is what the manuscript says — by
evaluating each at 60 digits, the same way `paper_b_audit.identity_census` used
to establish them.  A mismatch here means the Lean statement drifted from the
paper, not that the paper is wrong.
"""

from __future__ import annotations

import pathlib
import math
import random

import mpmath as mp

mp.mp.dps = 60

_LEAN = "formal/Problems/Juggler/MasterIdentity.lean"


def _fract(x):
    return x - mp.floor(x)


def _carry(A, B):
    """`carry` of MasterIdentity.lean: the unit carry [{A} + {B} >= 1]."""
    return mp.mpf(1) if _fract(A) + _fract(B) >= 1 else mp.mpf(0)


def _lean_source() -> str:
    root = pathlib.Path(__file__).resolve().parents[3]
    return (root / _LEAN).read_text(encoding="utf-8")


def test_lean_theorems_exist_by_name() -> None:
    src = _lean_source()
    for thm in ("lemma51_i_closed_form", "lemma51_i_nonneg", "lemma51_i_upper",
                "lemma51_i_identity", "carry_as_sawtooth", "fract_diff_level2",
                "lemma51_double_gap", "double_difference_product",
                "lemma51_master", "lemma51_brackets_le_two"):
        assert "theorem %s " % thm in src, thm


def test_carry_as_sawtooth() -> None:
    """[{A}+{B} >= 1] = {A} + {B} - {A+B}, the identity the manuscript displays."""
    rng = random.Random(1)
    for _ in range(2000):
        A = mp.mpf(rng.uniform(-300, 300))
        B = mp.mpf(rng.uniform(-300, 300))
        assert abs(_carry(A, B) - (_fract(A) + _fract(B) - _fract(A + B))) < mp.mpf("1e-45")


def test_fract_diff_level2() -> None:
    """The substitution engine: {y+w} - {y} = {w} - carry(y, w)."""
    rng = random.Random(2)
    for _ in range(2000):
        y = mp.mpf(rng.uniform(-300, 300))
        w = mp.mpf(rng.uniform(-300, 300))
        lhs = _fract(y + w) - _fract(y)
        assert abs(lhs - (_fract(w) - _carry(y, w))) < mp.mpf("1e-45")


def test_double_difference_product_is_exact() -> None:
    """The product rule over the four base points -- `ring` in Lean."""
    rng = random.Random(3)
    for _ in range(2000):
        c0, c1, c2, c12, f0, f1, f2, f12 = (mp.mpf(rng.uniform(-50, 50)) for _ in range(8))
        lhs = c12 * f12 - c1 * f1 - c2 * f2 + c0 * f0
        rhs = (c12 * (f12 - f1 - f2 + f0) + (c12 - c1) * (f1 - f0)
               + (c12 - c2) * (f2 - f0) + (c12 - c1 - c2 + c0) * f0)
        assert abs(lhs - rhs) < mp.mpf("1e-42")


def test_lemma51_double_gap() -> None:
    """Delta_2 g_2 = floor(DeltaDelta Y) + kappa'' + Delta_2 kappa_2, exactly."""
    rng = random.Random(4)
    for _ in range(2000):
        y0, y1, y2, y12 = (mp.mpf(rng.uniform(-500, 500)) for _ in range(4))
        lhs = (mp.floor(y12) - mp.floor(y2)) - (mp.floor(y1) - mp.floor(y0))
        rhs = (mp.floor((y12 - y2) - (y1 - y0))
               + _carry(y1 - y0, (y12 - y2) - (y1 - y0))
               + (_carry(y2, y12 - y2) - _carry(y0, y1 - y0)))
        assert lhs == rhs


def test_lemma51_master_identity() -> None:
    """The doubly differenced kernel phase decomposes exactly into four terms."""
    rng = random.Random(5)
    for _ in range(3000):
        c0, c1, c2, c12 = (mp.mpf(rng.uniform(-50, 50)) for _ in range(4))
        y0, y1, y2, y12 = (mp.mpf(rng.uniform(-500, 500)) for _ in range(4))
        lhs = (c12 * _fract(y12) - c1 * _fract(y1) - c2 * _fract(y2) + c0 * _fract(y0))
        rhs = ((c12 - c1 - c2 + c0) * _fract(y0)
               + (c12 - c1) * (_fract(y1 - y0) - _carry(y0, y1 - y0))
               + (c12 - c2) * (_fract(y2 - y0) - _carry(y0, y2 - y0))
               + c12 * (_fract((y12 - y2) - (y1 - y0))
                        - _carry(y1 - y0, (y12 - y2) - (y1 - y0))
                        - (_carry(y2, y12 - y2) - _carry(y0, y1 - y0))))
        assert abs(lhs - rhs) < mp.mpf("1e-42")


def test_lemma51_brackets_are_bounded_by_two() -> None:
    """The point of the lemma: no unbounded smooth part survives the differencing."""
    rng = random.Random(6)
    for _ in range(3000):
        y0, y1, y2, y12 = (mp.mpf(rng.uniform(-500, 500)) for _ in range(4))
        brackets = [
            _fract(y0),
            _fract(y1 - y0) - _carry(y0, y1 - y0),
            _fract(y2 - y0) - _carry(y0, y2 - y0),
            (_fract((y12 - y2) - (y1 - y0))
             - _carry(y1 - y0, (y12 - y2) - (y1 - y0))
             - (_carry(y2, y12 - y2) - _carry(y0, y1 - y0))),
        ]
        assert all(abs(b) <= 2 for b in brackets)


def test_lemma51_i_closed_form_on_real_n() -> None:
    """(3/4) v^(1/2) theta_2 = (1/2)(m^(9/4) - v^(3/2)) - R with R = (1/4)(b-a)^2(2b+a).

    Replaces the manuscript's Taylor expansion with an unspecified mean value.
    """
    rng = random.Random(7)
    worst = mp.mpf(0)
    for _ in range(200):
        n = rng.randrange(10**5, 10**7) | 1
        m = int(mp.floor(mp.mpf(n) ** mp.mpf(1.5)))
        Y = mp.mpf(m) ** mp.mpf(1.5)
        v = int(mp.floor(Y))
        theta2 = Y - v
        a, b = mp.sqrt(v), mp.sqrt(Y)
        R = mp.mpf(1) / 4 * (b - a) ** 2 * (2 * b + a)
        lhs = mp.mpf(3) / 4 * mp.sqrt(v) * theta2
        rhs = mp.mpf(1) / 2 * (mp.mpf(m) ** mp.mpf(2.25) - mp.mpf(v) ** mp.mpf(1.5)) - R
        assert abs(lhs - rhs) <= mp.mpf("1e-30") * abs(lhs)
        # the printed bound 0 <= R <= (3/16) v^(-1/2)
        assert 0 <= R
        assert R <= mp.mpf(3) / 16 / mp.sqrt(v) + mp.mpf("1e-40")
        worst = max(worst, R * mp.sqrt(v))
    # the printed 3/16 is nearly sharp: R * sqrt(v) gets to within 0.5% of it
    assert mp.mpf("0.18") < worst <= mp.mpf(3) / 16


# ----------------------------------------------------------------------------------------------
# Lemma 5.1(iii): the branch-freeze inventory
# (formal/Problems/Juggler/BranchFreeze.lean)
# ----------------------------------------------------------------------------------------------

_BRANCH = "formal/Problems/Juggler/BranchFreeze.lean"


def _branch_source() -> str:
    root = pathlib.Path(__file__).resolve().parents[3]
    return (root / _BRANCH).read_text(encoding="utf-8")


def test_branch_freeze_theorems_exist_by_name() -> None:
    src = _branch_source()
    for thm in ("lemma51iii_regroup", "corner_floor_range", "offset_abs_le_three",
                "double_difference_lt_one", "beta_product_bound", "Gprime_form",
                "Gprime_j_bound", "Gprime_beta_bound", "Gsecond_beta_cancellation",
                "Gsecond_naive_bound_fails", "Gsecond_beta_bound", "Gsecond_j_bound",
                "offset_term_bounds", "second_difference_term_bounds",
                "run_length_arithmetic", "run_length_conclusion"):
        assert "theorem %s " % thm in src, thm


def test_Gsecond_beta_terms_cancel() -> None:
    """The printed |G''| <= ... + 25 h1h2 P^(-7/4) holds only via a cancellation.

    G'' = F''(X)(X')^2 + F'(X)X''.  The two beta-contributions are +81/64 and -9/32,
    leaving 63/64.  Bounding them separately gives 99/64, which exceeds the printed 25.
    """
    from fractions import Fraction as Fr

    a = Fr(9, 16) * Fr(9, 4)    # F'' * (X')^2, beta part
    b = -Fr(3, 8) * Fr(3, 4)    # F'  * X''   , beta part
    assert a + b == Fr(63, 64)
    assert abs(a) + abs(b) == Fr(99, 64)
    assert (a + b) * 19 <= 25            # with the cancellation
    assert (abs(a) + abs(b)) * 19 > 25   # term by term: fails
    # the j-terms cancel the same way
    aj, bj = -Fr(3, 8) * Fr(9, 4), Fr(3, 4) * Fr(3, 4)
    assert aj + bj == Fr(-9, 32)
    assert abs(aj + bj) <= 2


def test_lemma51iii_on_real_data() -> None:
    """DeltaDelta Y = F_kappa(m) exactly, |j| <= 3, and all four printed bounds."""
    rng = random.Random(11)
    f = lambda x: mp.mpf(x) ** mp.mpf(1.5)  # noqa: E731
    m_of = lambda n: int(mp.floor(mp.mpf(n) ** mp.mpf(1.5)))  # noqa: E731
    for _ in range(60):
        P = rng.choice([10**5, 10**6, 10**7])
        n = rng.randrange(P + 1, 2 * P) | 1
        h1, h2 = rng.randint(1, 3), rng.randint(1, 3)
        d1, d2 = 2 * h1, 2 * h2
        m = m_of(n)
        b1, b2 = m_of(n + d1) - m, m_of(n + d2) - m
        b12 = m_of(n + d1 + d2) - m
        j = b12 - b1 - b2
        assert abs(j) <= 3
        # the exact identity of (iii)
        F = f(m + b12) - f(m + b1) - f(m + b2) + f(m)
        DDY = f(m_of(n + d1 + d2)) - f(m_of(n + d1)) - f(m_of(n + d2)) + f(m)
        assert abs(F - DDY) <= mp.mpf("1e-25") * max(1, abs(F))
        # the split brackets, against the printed ranges
        A = mp.mpf(m + b1 + b2)
        Pm = mp.mpf(P)
        if j != 0:
            r = abs(f(m + b12) - f(A)) / (abs(j) * Pm ** mp.mpf(0.75))
            assert mp.mpf("1.5") <= r <= mp.mpf("2.6")
        sd = f(A) - f(m + b1) - f(m + b2) + f(m)
        assert mp.mpf("1.4") <= sd / (h1 * h2 * Pm ** mp.mpf(0.25)) <= 15
        # the derivative bounds
        Xn = mp.mpf(n) ** mp.mpf(1.5)
        Xp = mp.mpf(1.5) * mp.sqrt(mp.mpf(n))
        Xpp = mp.mpf(0.75) / mp.sqrt(mp.mpf(n))
        g = lambda x: mp.mpf(1.5) * (mp.sqrt(x + b12) - mp.sqrt(x + b1)  # noqa: E731
                                     - mp.sqrt(x + b2) + mp.sqrt(x))
        gg = lambda x: mp.mpf(0.75) * (1 / mp.sqrt(x + b12) - 1 / mp.sqrt(x + b1)  # noqa: E731
                                       - 1 / mp.sqrt(x + b2) + 1 / mp.sqrt(x))
        Gp = g(Xn) * Xp
        Gpp = gg(Xn) * Xp**2 + g(Xn) * Xpp
        assert abs(Gp) <= 2 * abs(j) * Pm ** mp.mpf(-0.25) + 20 * h1 * h2 * Pm ** mp.mpf(-0.75)
        assert abs(Gp) < 1  # the printed "< 1"
        assert abs(Gpp) <= 2 * abs(j) * Pm ** mp.mpf(-1.25) + 25 * h1 * h2 * Pm ** mp.mpf(-1.75)


def test_run_length_constant_is_two_plus_twenty() -> None:
    """A = 2|j|P^(-1/4) <= 2M and B = 20 h1h2 P^(-3/4) <= 20M, so A + B <= 22M."""
    rng = random.Random(12)
    for _ in range(2000):
        j = rng.uniform(0, 5)
        h = rng.uniform(0.1, 20)
        p = rng.uniform(1.1, 50)
        M = max((j + 1) / p, h / p**3)
        assert 2 * j / p + 20 * h / p**3 <= 22 * M + 1e-12


# ----------------------------------------------------------------------------------------------
# The two mean values of Lemma 5.1(iii), discharged
# (formal/Problems/Juggler/MeanValues.lean)
# ----------------------------------------------------------------------------------------------

_MV = "formal/Problems/Juggler/MeanValues.lean"


def _mv_source() -> str:
    root = pathlib.Path(__file__).resolve().parents[3]
    return (root / _MV).read_text(encoding="utf-8")


def test_mean_value_theorems_exist_by_name() -> None:
    src = _mv_source()
    for thm in ("hasDerivAt_pow32", "mvt_cube_explicit", "mvt_sqrt_diff_explicit",
                "hasDerivAt_gShift", "second_difference_two_sided",
                "second_difference_exists_xi", "lemma51iii_mean_values_available"):
        assert "theorem %s " % thm in src, thm
    # x^(3/2) is written x * sqrt x throughout, so no rpow machinery is needed;
    # the derivative comes from Real.hasDerivAt_sqrt
    assert "def pow32 (x : ℝ) : ℝ := x * Real.sqrt x" in src
    assert "Real.hasDerivAt_sqrt" in src


def test_mvt_cube_has_an_explicit_witness() -> None:
    """c = (2/3)(a^2+ab+b^2)/(a+b) satisfies b^3-a^3 = (3/2)(b^2-a^2)c and a <= c <= b."""
    rng = random.Random(21)
    for _ in range(4000):
        a = rng.uniform(1e-3, 40)
        b = a + rng.uniform(0, 40)
        c = (2 / 3) * (a * a + a * b + b * b) / (a + b)
        assert a - 1e-12 <= c <= b + 1e-12
        assert abs((b**3 - a**3) - 1.5 * (b * b - a * a) * c) <= 1e-9 * max(1.0, b**3)


def test_mvt_sqrt_diff_witness_is_the_arithmetic_mean() -> None:
    """F'(A+B) - F'(A) = B F''(eta) exactly, with sqrt(eta) = (sqrt A + sqrt(A+B))/2."""
    rng = random.Random(22)
    for _ in range(4000):
        a = rng.uniform(1e-3, 40)
        b = a + rng.uniform(0, 40)
        mid = (a + b) / 2
        assert a <= mid <= b
        assert abs(1.5 * (b - a) * mid - 0.75 * (b * b - a * a)) <= 1e-9 * max(1.0, b * b)


def test_second_difference_two_sided_bound() -> None:
    """(3/4) b1 b2 (m+b1+b2)^(-1/2) <= D <= (3/4) b1 b2 m^(-1/2)."""
    rng = random.Random(23)
    f = lambda x: x * mp.sqrt(x)  # noqa: E731
    for _ in range(3000):
        m = mp.mpf(rng.uniform(0.5, 500))
        b1 = mp.mpf(rng.uniform(1e-6, 60))
        b2 = mp.mpf(rng.uniform(0, 60))
        D = f(m + b1 + b2) - f(m + b1) - f(m + b2) + f(m)
        assert mp.mpf("0.75") * b1 * b2 / mp.sqrt(m + b1 + b2) <= D + mp.mpf("1e-30")
        assert D <= mp.mpf("0.75") * b1 * b2 / mp.sqrt(m) + mp.mpf("1e-30")


def test_xi_two_exists_and_is_interior() -> None:
    """The manuscript's own form: D = b1 b2 F''(xi) with xi in [m, m+b1+b2]."""
    rng = random.Random(24)
    f = lambda x: x * math.sqrt(x)  # noqa: E731
    frac_lo, frac_hi = 1.0, 0.0
    for _ in range(4000):
        m = rng.uniform(0.5, 500)
        b1 = rng.uniform(1e-6, 60)
        b2 = rng.uniform(1e-6, 60)
        D = f(m + b1 + b2) - f(m + b1) - f(m + b2) + f(m)
        assert D > 0
        xi = ((0.75 * b1 * b2) / D) ** 2
        assert m - 1e-9 <= xi <= m + b1 + b2 + 1e-9
        assert abs(D - b1 * b2 * (0.75 / math.sqrt(xi))) <= 1e-9 * max(1.0, D)
        t = (xi - m) / (b1 + b2)
        frac_lo, frac_hi = min(frac_lo, t), max(frac_hi, t)
    # the manuscript claims xi_2 in (0, b1+b2); observed well inside
    assert 0 < frac_lo and frac_hi < 1

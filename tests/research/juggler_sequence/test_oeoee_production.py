"""The OEOEE production: an elementary fourth contagion family.

Companion to docs/theory/juggler_oeoee_production.md.  The word OEOEE was
labelled "needs localized Paper B depth 2"; it does not.  Its two O-steps are
separated by an E-step, and the E-step's transparent nesting makes

    J^2(n) = floor(n^{3/4}) =: w        (exact)

so that J^3 = floor(w^{3/2}), J^4 = floor(w^{3/4}), J^5 = floor(w^{3/8}) are
functions of the single integer w.  The parities of J^2, J^3, J^4 are therefore
constant on the level sets I_w = [w^{4/3},(w+1)^{4/3}), and only
psi_1 = psi(n^{3/2}) varies inside a block.  Nothing is nested, so no Paper B
estimate is needed -- unlike OOEEE, which carries floor(floor(n^{3/2})^{3/2}).

These tests check the exact identities, the block decomposition, the fiber, the
1/16 share, the mean-square behaviour that Half B needs, the +1/27 bookkeeping,
and the resulting exponents.
"""

from __future__ import annotations

from fractions import Fraction as F
from math import isqrt, log

import pytest

mp = pytest.importorskip("mpmath")

NOTE = "docs/theory/juggler_oeoee_production.md"

RHO = F(9, 32)  # source scale of OEOEE
NET_GAIN = F(1, 27)  # what the family adds to (4.2)
LAMBDA_2 = 0.4480  # lambda**, current
LAMBDA_3 = 0.5392  # lambda***, Appendix C


def J(n: int) -> int:
    return isqrt(n) if n % 2 == 0 else isqrt(n**3)


def floor_three_quarters(n: int) -> int:
    """floor(n^{3/4}) = floor(sqrt(floor(sqrt(n^3))))."""
    return isqrt(isqrt(n**3))


def word5(n: int) -> str:
    letters, x = [], n
    for _ in range(5):
        letters.append("O" if x % 2 else "E")
        x = J(x)
    return "".join(letters)


# --------------------------------------------------------------------------
# Lemma 1: the exact chain
# --------------------------------------------------------------------------


def oeoee_starts(lo: int, hi: int):
    for n in range(lo | 1, hi, 2):
        if word5(n) == "OEOEE":
            yield n


def test_exact_chain_and_fiber():
    tested = 0
    for n in oeoee_starts(10**7, 10**7 + 400_001):
        tested += 1
        w = floor_three_quarters(n)
        assert J(J(n)) == w  # J^2 = floor(n^{3/4})
        j3 = J(J(J(n)))
        assert j3 == isqrt(w**3)  # J^3 = floor(w^{3/2})
        j4 = J(j3)
        assert j4 == isqrt(isqrt(w**3))  # J^4 = floor(w^{3/4})
        j5 = J(j4)
        assert j5 == isqrt(isqrt(isqrt(w**3)))  # J^5 = floor(w^{3/8})
        # the fiber is EXACT: J^5(n) = m' iff w in [m'^{8/3},(m'+1)^{8/3})
        m = j5
        assert m**8 <= w**3 < (m + 1) ** 8
    assert tested > 5_000


def test_rho_and_fiber_length():
    scale = F(1)
    for ch in "OEOEE":
        scale *= F(3, 2) if ch == "O" else F(1, 2)
    assert scale == RHO
    # |J(m')| = (1/rho) P^{1-rho}; rho <= 1/2 so the fiber clears the threshold
    assert 1 - RHO == F(23, 32)
    assert RHO <= F(1, 2)


# --------------------------------------------------------------------------
# Lemma 2: the block decomposition
# --------------------------------------------------------------------------


def test_parities_are_constant_on_level_sets():
    seen: dict[int, tuple[int, int, int]] = {}
    blocks: dict[int, int] = {}
    for n in range(10**7 | 1, 10**7 + 200_001, 2):
        w = floor_three_quarters(n)
        j3 = isqrt(w**3)
        key = (w % 2, j3 % 2, isqrt(j3) % 2)  # parities of J^2, J^3, J^4
        if w in seen:
            assert seen[w] == key  # constant on the block
        seen[w] = key
        blocks[w] = blocks.get(w, 0) + 1
    assert len(seen) > 100
    # block lengths match (4/3) w^{1/3}
    interior = sorted(blocks)[1:-1]
    for w in interior[:: max(1, len(interior) // 20)]:
        assert abs(2 * blocks[w] - (4 / 3) * w ** (1 / 3)) < 3


def test_sixteen_times_indicator_identity():
    for n in range(10**6 | 1, 10**6 + 40_001, 2):
        w = floor_three_quarters(n)
        j3 = isqrt(w**3)
        psi1 = 1 if isqrt(n**3) % 2 == 0 else -1
        lam1 = 1 if w % 2 == 0 else -1
        lam2 = 1 if j3 % 2 == 0 else -1
        lam3 = 1 if isqrt(j3) % 2 == 0 else -1
        product = (1 + psi1) * (1 - lam1) * (1 + lam2) * (1 + lam3)
        assert product == 16 * (word5(n) == "OEOEE")


# --------------------------------------------------------------------------
# Proposition 3: the share, and the mean square Half B needs
# --------------------------------------------------------------------------


def census(P: int):
    Y = int(P ** (23 / 32))
    total = hits = 0
    blocks: dict[int, int] = {}
    for n in range(P | 1, P + Y, 2):
        total += 1
        j1 = isqrt(n**3)
        w = floor_three_quarters(n)
        blocks[w] = blocks.get(w, 0) + (1 if j1 % 2 == 0 else -1)
        if j1 % 2 == 0 and w % 2 == 1:
            j3 = isqrt(w**3)
            if j3 % 2 == 0 and isqrt(j3) % 2 == 0:
                hits += 1
    t2 = sum(v * v for v in blocks.values())
    t1 = sum(abs(v) for v in blocks.values())
    return Y, total, hits, len(blocks), t1, t2


def test_share_approaches_one_sixteenth():
    shares = []
    for P in (10**6, 10**7):
        _, total, hits, *_ = census(P)
        shares.append(hits / total)
    assert abs(shares[-1] - 1 / 16) < 0.005
    # and it is improving
    assert abs(shares[-1] - 1 / 16) < abs(shares[0] - 1 / 16)


def test_mean_square_is_linear_not_trivial():
    P = 10**7
    Y, _, _, nblocks, t1, t2 = census(P)
    H = Y / nblocks
    assert abs(H - (4 / 3) * P**0.25) / H < 0.02  # block length as predicted
    assert t2 < 2 * Y  # Half B's prediction: sum|T|^2 << Y
    assert t2 < 0.05 * nblocks * H * H  # far below the trivial bound
    saving = log(t1 / Y) / log(P)
    assert saving < -1 / 16  # beats the proved P^{-1/16}


# --------------------------------------------------------------------------
# Proposition 4: the bookkeeping, and the new exponents
# --------------------------------------------------------------------------


def test_net_gain_is_one_twenty_seventh():
    ideal_oe, sweep_oe = F(1, 3), F(2, 9)  # OE at eta=1 and at eta=2/3
    oee_mass = F(1, 3)  # OEE-produced mass at scale 3t/4, per Prop 3.4
    assert ideal_oe * oee_mass - sweep_oe * oee_mass == NET_GAIN


def root(terms) -> float:
    return float(
        mp.findroot(lambda L: sum(float(c) * float(e) ** L for c, e in terms) - 1, 0.5)
    )


BASE = [(F(1), F(1, 2)), (F(1, 9), F(3, 8)), (F(2, 9), F(3, 4))]


def test_new_exponents():
    assert root(BASE) == pytest.approx(LAMBDA_2, abs=5e-5)
    assert root(BASE + [(F(1, 9), RHO)]) == pytest.approx(LAMBDA_3, abs=5e-5)
    # + OEOEE, unconditional
    assert root(BASE + [(NET_GAIN, RHO)]) == pytest.approx(0.4801, abs=5e-4)
    # + OEOEE and OOEEE
    assert root(BASE + [(F(1, 9) + NET_GAIN, RHO)]) == pytest.approx(0.5665, abs=5e-4)
    assert F(1, 9) + NET_GAIN == F(4, 27)


def test_ooeee_really_is_nested_and_oeoee_is_not():
    # OEOEE has no two consecutive O's, so every O is absorbed by the following
    # E into an exact floor(.^{3/4}); OOEEE does not, and carries the genuinely
    # nested floor(floor(n^{3/2})^{3/2}).
    def longest_o_run(word: str) -> int:
        best = run = 0
        for ch in word:
            run = run + 1 if ch == "O" else 0
            best = max(best, run)
        return best

    assert longest_o_run("OEOEE") == 1
    assert longest_o_run("OOEEE") == 2
    # the nested object OOEEE needs is not a function of floor(n^{3/4})
    n = 10**7 + 1
    assert isqrt(isqrt(n**3) ** 3) != isqrt(floor_three_quarters(n) ** 3)


def test_note_records_the_production():
    from pathlib import Path

    text = Path(NOTE).read_text(encoding="utf-8")
    assert "0.4801" in text and "0.5665" in text and "0.4927" in text
    assert "no exceptional set" in text


# --------------------------------------------------------------------------
# Section 8: the layer criterion, and the (OE)^{k-1}OEE family
# --------------------------------------------------------------------------


def binding_layer_relative_length(K: int, j: int) -> F:
    """For (OE)^K E^j the binding layer w_{K-1} has this relative length."""
    return 1 - F(3, 4) * F(1, 2) ** j


def test_layer_criterion_is_independent_of_K():
    # relative length = 1 - (3/4)2^{-j}: needs j >= 1, and does not depend on K
    for K in (2, 3, 4, 7):
        assert binding_layer_relative_length(K, 1) == F(5, 8)
        assert binding_layer_relative_length(K, 0) == F(1, 4)
        assert binding_layer_relative_length(K, 2) == F(13, 16)
    assert binding_layer_relative_length(3, 0) < F(1, 2)  # OEOEOE fails
    assert binding_layer_relative_length(3, 1) >= F(1, 2)  # OEOEOEE is fine
    # and it really is (3/4)^{K-1} - rho over (3/4)^{K-1}
    for K, j in ((2, 1), (3, 0), (3, 1), (4, 1)):
        rho = F(3, 4) ** K * F(1, 2) ** j
        top = F(3, 4) ** (K - 1)
        assert (top - rho) / top == binding_layer_relative_length(K, j)


def test_short_layer_has_no_uniform_cancellation():
    # At relative length 1/4 the phase is essentially linear over the range, so
    # some placements give no cancellation at all; at 5/8 it cancels uniformly.
    # A per-source bound is what the recursion needs, so the worst case over
    # placements is the figure of merit, and it is a tail event at 1/4: sample
    # the cheap short range densely and the long one sparsely.
    import random

    W = 10**8

    def worst_ratio(rel: float, trials: int) -> float:
        L = int(W**rel)
        random.seed(1)
        best = 0.0
        for _ in range(trials):
            w0 = random.randrange(W, 2 * W)
            s = sum(1 if isqrt(w**3) % 2 == 0 else -1 for w in range(w0, w0 + L))
            best = max(best, abs(s) / L)
        return best

    short, long = worst_ratio(0.25, 200), worst_ratio(0.625, 8)
    assert long < 0.05  # relative length 5/8: uniform cancellation
    assert short > 10 * long  # relative length 1/4: no uniform saving
    assert short > 0.3


def family(count: int):
    """Net gains of V_2..V_{count+1}: 3^{-(k+2)} at scale (3/4)^k (3/8)."""
    return [(F(1, 3) ** (k + 2), F(3, 4) ** k * F(3, 8)) for k in range(1, count + 1)]


def test_family_coefficients():
    for k in range(1, 6):
        rho_k = F(3, 4) ** (k - 1) * F(3, 8)
        assert F(1, 2) ** (2 * k + 1) / rho_k == F(1, 3) ** k  # ideal c_k = 3^-k
        assert (F(1, 3) - F(2, 9)) * F(1, 3) ** k == F(1, 3) ** (k + 2)  # net gain


def test_family_telescopes_to_the_ideal_depth_two_recursion():
    # base + full family  <=>  2^-L + (1/3)(3/4)^L = 1, exactly.
    ideal = root([(F(1), F(1, 2)), (F(1, 3), F(3, 4))])
    assert root(BASE + family(60)) == pytest.approx(ideal, abs=1e-6)
    assert ideal == pytest.approx(0.4927, abs=5e-5)
    # the identity, checked symbolically at x = 1 - y/3
    for y in (F(1, 2), F(2, 3), F(7, 10), F(9, 10)):
        x = 1 - y / 3
        lhs = x + F(1, 9) * x * y + F(2, 9) * y + F(1, 27) * x * y**2 / (1 - y / 3)
        assert lhs == 1


# --------------------------------------------------------------------------
# Section 9: V_3 = OEOEOEE worked out
# --------------------------------------------------------------------------

RHO_V3 = F(27, 128)


def f34(x: int) -> int:
    """floor(x^{3/4})."""
    return isqrt(isqrt(x**3))


def word7(n: int) -> str:
    letters, x = [], n
    for _ in range(7):
        letters.append("O" if x % 2 else "E")
        x = J(x)
    return "".join(letters)


def test_v3_scales_and_layers():
    scale = F(1)
    for ch in "OEOEOEE":
        scale *= F(3, 2) if ch == "O" else F(1, 2)
    assert scale == RHO_V3
    Y = 1 - RHO_V3
    assert Y == F(101, 128)
    # layer w_1 at 3/4 with blocks P^{1/4}; layer w_2 at 9/16 with blocks P^{3/16}
    L1 = Y - F(1, 4)
    L2 = L1 - F(9, 16) / 3
    assert L1 == F(69, 128) and L2 == F(45, 128)
    assert L1 / F(3, 4) == F(23, 32)
    assert L2 / F(9, 16) == F(5, 8)  # the binding layer, as the criterion predicts
    assert F(1, 2) ** 7 / RHO_V3 == F(1, 27)  # ideal coefficient c_3


def test_v3_exact_chain_and_fiber():
    tested = 0
    for n in range(10**6 | 1, 10**6 + 300_001, 2):
        if word7(n) != "OEOEOEE":
            continue
        tested += 1
        w1, = (f34(n),)
        w2 = f34(w1)
        assert J(J(n)) == w1
        assert J(J(J(n))) == isqrt(w1**3)
        assert J(J(J(J(n)))) == w2
        j5 = isqrt(w2**3)
        assert J(J(J(J(J(n))))) == j5
        w3 = isqrt(j5)
        m = isqrt(w3)
        # the fiber is exact in the w_2 variable
        assert m**8 <= w2**3 < (m + 1) ** 8
    assert tested > 200


def test_v3_block_constancy_at_both_layers():
    seen: dict[int, tuple] = {}
    for n in range(10**6 | 1, 10**6 + 120_001, 2):
        w1 = f34(n)
        w2 = f34(w1)
        j3, j5 = isqrt(w1**3), isqrt(w2**3)
        key = (w1 % 2, j3 % 2, w2 % 2, j5 % 2, isqrt(j5) % 2)
        if w1 in seen:
            assert seen[w1] == key
        seen[w1] = key
    assert len(seen) > 200


def test_v3_deep_layer_functions_are_unbiased():
    # the fiber-level share deviation is a small-sample effect, not a bias:
    # over long ranges at the w_2 and w_3 scales both functions are fair.
    for lo in (31623, 2371):
        n = 60_000
        even32 = sum(1 for w in range(lo, lo + n) if isqrt(w**3) % 2 == 0)
        even34 = sum(1 for w in range(lo, lo + n) if f34(w) % 2 == 0)
        assert abs(even32 / n - 0.5) < 0.02
        assert abs(even34 / n - 0.5) < 0.02


def test_v3_gain_and_exponents():
    assert (F(1, 3) - F(2, 9)) * F(1, 3) ** 2 == F(1, 81)  # net gain
    assert root(BASE + family(2)) == pytest.approx(0.4891, abs=5e-4)
    assert root(BASE + family(2) + [(F(1, 9), RHO)]) == pytest.approx(0.5740, abs=5e-4)


# --------------------------------------------------------------------------
# Section 10: V_4, and the saving law
# --------------------------------------------------------------------------


def layers(k: int):
    """(rho, Y, [(scale_i, H_i, L_i)]) for V_k = (OE)^{k-1}OEE."""
    rho = F(3, 4) ** (k - 1) * F(3, 8)
    Y = 1 - rho
    out, L = [], Y
    for i in range(1, k):
        scale = F(3, 4) ** i
        H = scale / 3
        L = L - H
        out.append((scale, H, L))
    return rho, Y, out


def test_binding_layer_is_always_five_eighths():
    for k in range(2, 8):
        rho, Y, lay = layers(k)
        scale, H, L = lay[-1]  # the binding layer w_{k-1}
        assert L / scale == F(5, 8)
        assert F(1, 2) ** (2 * k + 1) / rho == F(1, 3) ** k  # ideal c_k


def test_saving_law():
    # With |S_q| summed directly (not via Cauchy-Schwarz) and every Vaaler
    # truncation balanced, each Cauchy-Schwarz case saves H_i/2 and the
    # one-variable case saves scale/6 -- and the two TIE, at (1/6)(3/4)^{k-1}.
    for k in range(2, 8):
        rho, Y, lay = layers(k)
        cauchy = [H / 2 for _, H, _ in lay]
        one_var = F(3, 4) ** (k - 1) / 6
        assert min(cauchy) == one_var  # the tie
        assert min(cauchy + [one_var]) == F(1, 6) * F(3, 4) ** (k - 1)
    assert F(1, 6) * F(3, 4) == F(1, 8)  # V_2
    assert F(1, 6) * F(3, 4) ** 2 == F(3, 32)  # V_3
    assert F(1, 6) * F(3, 4) ** 3 == F(9, 128)  # V_4
    # strictly better than the earlier (1/9)(3/4)^{k-1}, by a factor 3/2
    for k in range(2, 8):
        assert F(1, 6) * F(3, 4) ** (k - 1) == F(3, 2) * F(1, 9) * F(3, 4) ** (k - 1)
    # positive for every k: the family never runs out of saving
    assert all(F(1, 6) * F(3, 4) ** (k - 1) > 0 for k in range(2, 40))


# --------------------------------------------------------------------------
# Section 11: the constants
# --------------------------------------------------------------------------


def test_kusmin_landau_constant():
    from math import cos, pi, sin

    # cot(pi d / 2) <= 2/(pi d) on (0, 1/2]
    for i in range(1, 500):
        d = i / 1000
        assert cos(pi * d / 2) / sin(pi * d / 2) <= 2 / (pi * d)


def test_second_derivative_test_constant():
    # (T3): lambda <= |f''| <= alpha*lambda on length M, 0 < lambda <= pi/4
    #       => |sum e(f)| <= (alpha*lambda*M + 1)(2.26 lambda^{-1/2} + 1)
    import cmath
    import math
    import random

    random.seed(3)
    worst = 0.0
    for _ in range(400):
        W = random.choice([1e4, 1e5, 1e6])
        q = random.randrange(1, 40)
        a = random.uniform(W, 2 * W)
        M = random.choice([50, 200, 1000])
        c = q / 2.0
        fpp = lambda x: c * 0.75 * x**-0.5
        lam_lo, lam_hi = fpp(a + M), fpp(a)
        if lam_lo <= 0 or lam_hi > math.pi / 4:
            continue
        alpha = lam_hi / lam_lo
        S = abs(sum(cmath.exp(2j * math.pi * c * n**1.5) for n in range(int(a), int(a + M))))
        bound = (alpha * lam_lo * M + 1) * (2.26 * lam_lo**-0.5 + 1)
        worst = max(worst, S / bound)
    assert worst < 1.0


def test_explicit_envelope_end_to_end():
    # |16|O(m')| - Y|  <=  100 Y m'^{-4/9} (1+log m')^2, checked exactly.
    from math import log

    def ninth_root_floor(x):
        r = int(round(x ** (1 / 9)))
        while r**9 > x:
            r -= 1
        while (r + 1) ** 9 <= x:
            r += 1
        return r

    for mp in (60, 90, 120):
        a, b = ninth_root_floor(mp**32), ninth_root_floor((mp + 1) ** 32 - 1)
        Y = hits = 0
        n = a | 1
        while n <= b:
            Y += 1
            j1 = isqrt(n**3)
            if j1 % 2 == 0:
                w = isqrt(j1)
                if w % 2 == 1:
                    j3 = isqrt(w**3)
                    if j3 % 2 == 0 and isqrt(j3) % 2 == 0:
                        hits += 1
            n += 2
        err = abs(16 * hits - Y)
        assert err <= 100 * Y * mp ** (-4 / 9) * (1 + log(mp)) ** 2
        # and the measured ratio against the bare envelope stays below 1/2
        assert err / (Y * mp ** (-4 / 9)) < 0.5


def test_v4_scales():
    rho, Y, lay = layers(4)
    assert rho == F(81, 512) and Y == F(431, 512)
    assert [L for _, _, L in lay] == [F(303, 512), F(207, 512), F(135, 512)]
    assert [L / s for s, _, L in lay] == [F(101, 128), F(23, 32), F(5, 8)]


def word9(n: int) -> str:
    letters, x = [], n
    for _ in range(9):
        letters.append("O" if x % 2 else "E")
        x = J(x)
    return "".join(letters)


def test_v4_exact_chain_fiber_and_block_constancy():
    tested = 0
    seen: dict[int, tuple] = {}
    for n in range(10**6 | 1, 10**6 + 400_001, 2):
        w1 = f34(n)
        w2 = f34(w1)
        w3 = f34(w2)
        key = (
            w1 % 2, isqrt(w1**3) % 2, w2 % 2, isqrt(w2**3) % 2,
            w3 % 2, isqrt(w3**3) % 2, f34(w3) % 2,
        )
        if w1 in seen:
            assert seen[w1] == key  # constant on the n-blocks
        seen[w1] = key
        if word9(n) != "OEOEOEOEE":
            continue
        tested += 1
        assert J(J(n)) == w1 and J(J(J(J(n)))) == w2
        assert J(J(J(J(J(J(n)))))) == w3
        w4 = f34(w3)
        assert J(J(J(J(J(J(J(J(n)))))))) == w4
        m = isqrt(w4)
        assert m**8 <= w3**3 < (m + 1) ** 8  # exact fiber, in the w_3 variable
    assert tested > 20


def test_v4_gain_and_exponents():
    assert (F(1, 3) - F(2, 9)) * F(1, 3) ** 3 == F(1, 243)
    assert root(BASE + family(3)) == pytest.approx(0.4916, abs=5e-4)
    assert root(BASE + family(3) + [(F(1, 9), RHO)]) == pytest.approx(0.5761, abs=5e-4)


def test_v4_census_cannot_reach_the_constant():
    # the deepest layer is sampled at only L_4 = P^{81/512} points
    assert float(F(81, 512)) == pytest.approx(0.1582, abs=1e-4)
    assert 10 ** (8 * 81 / 512) < 20  # ~18 distinct w_4 at P = 1e8
    assert 10 ** (12.7 * 81 / 512) > 90  # 100 needs P ~ 1e12.7


def test_family_ladder():
    ladder = [root(BASE + family(K)) for K in (1, 2, 3, 4)]
    assert ladder[0] == pytest.approx(0.4801, abs=5e-4)
    assert ladder[1] == pytest.approx(0.4891, abs=5e-4)
    assert all(a < b for a, b in zip(ladder, ladder[1:]))  # monotone
    assert ladder[-1] < 0.4927
    # with Appendix C's OOEEE as well
    assert root(BASE + family(60) + [(F(1, 9), RHO)]) == pytest.approx(0.5769, abs=5e-4)

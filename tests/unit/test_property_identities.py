"""Hypothesis checks of ledger identities on random integers.

These tests do not discover theorems. They sample the same exact
identities already proved or exhaustively checked in the unit suite
(BT-encode-unique, BT-D-S, BTC-decomp, BTC-D-I, BTC-P-band, BTC-D-add,
BTC-D-mul, BTC-cmp3, BTC-select3, BT-Pn3, rewrite
soundness). Candidates are never auto-promoted.
"""

from __future__ import annotations

from hypothesis import given, settings, strategies as st

from bt.calculus.derivative import D, S, lsd, reconstruct
from bt.calculus.differential import D_of_product, D_of_sum, lsd_of_product, lsd_of_sum
from bt.calculus.expressions import ED, EI0, EIm, EInt, EIp, ENeg, EShift3
from bt.calculus.integral import I, P, section_holds
from bt.calculus.order import cmp3
from bt.calculus.rewrite import WORD_SIMP_RULES
from bt.calculus.select import abs_z, max_z, min_z, select3
from bt.calculus.semantics import evaluate
from bt.calculus.trit import Trit, as_trit, neg, sign_trit, trit_max, trit_min
from bt.operators import OperatorDomainError, get_operator, three_kernel
from bt.polynomials import polynomial
from bt.representation import decode, encode

IDENTITY = settings(max_examples=80, deadline=None)
Z = st.integers(min_value=-(10**9), max_value=10**9)
TRIT = st.sampled_from((-1, 0, 1))


def _apply_math_word(factors: tuple[str, ...], n: int) -> int:
    """Apply an operator word in mathematical (left-last) order."""
    y = n
    for symbol in reversed(factors):
        y = get_operator(symbol).apply(y)
    return y


@IDENTITY
@given(n=Z)
def test_encode_decode_roundtrip(n: int) -> None:
    """BT-encode-unique: decode ∘ encode = id."""
    assert decode(encode(n)) == n


@IDENTITY
@given(n=Z)
def test_d_left_inverse_of_s(n: int) -> None:
    """BT-D-S: D ∘ S = id."""
    assert D(S(n)) == n
    assert get_operator("D").apply(get_operator("S").apply(n)) == n


@IDENTITY
@given(n=Z)
def test_lsd_plus_three_d_recovers_n(n: int) -> None:
    """BTC-decomp: n = lsd(n) + 3 D(n)."""
    assert reconstruct(n) == n
    assert n == int(lsd(n)) + 3 * D(n)


@IDENTITY
@given(n=Z, a=TRIT)
def test_d_section_of_integral(n: int, a: int) -> None:
    """BTC-D-I: D(I_a(n)) = n, and I_{lsd(n)}(D(n)) = n."""
    assert D(I(a, n)) == n
    a0 = int(lsd(n))
    assert I(a0, D(n)) == n
    assert section_holds(a0, n)
    if a != a0:
        assert I(a, D(n)) != n


@IDENTITY
@given(n=Z, a=TRIT, b=TRIT)
def test_projections_are_left_zero_band(n: int, a: int, b: int) -> None:
    """BTC-P-band: P_a ∘ P_b = P_a."""
    assert P(a, P(b, n)) == P(a, n)
    assert D(P(a, n)) == D(n)


@IDENTITY
@given(x=Z, y=Z)
def test_d_sum_and_product_rules(x: int, y: int) -> None:
    """BTC-D-add / BTC-D-mul: exact sum correction and twisted Leibniz."""
    assert D(x + y) == D_of_sum(x, y)
    assert lsd(x + y) == lsd_of_sum(x, y)
    assert D(x * y) == D_of_product(x, y)
    assert lsd(x * y) == lsd_of_product(x, y)


@IDENTITY
@given(n=Z)
def test_negation_involution_and_commutes(n: int) -> None:
    """N∘N = id; N commutes with S and D."""
    nn = get_operator("N").apply(n)
    assert get_operator("N").apply(nn) == n
    assert D(get_operator("N").apply(n)) == get_operator("N").apply(D(n))
    assert S(get_operator("N").apply(n)) == get_operator("N").apply(S(n))


@IDENTITY
@given(n=Z)
def test_w_w_is_k3_and_w_ignores_shift(n: int) -> None:
    """W∘W = K3; W∘S = W."""
    w = get_operator("W")
    k3 = get_operator("K3")
    assert w.apply(w.apply(n)) == three_kernel(n)
    assert w.apply(w.apply(n)) == k3.apply(n)
    assert w.apply(S(n)) == w.apply(n)


@IDENTITY
@given(n=Z)
def test_m2_h2_round_trip(n: int) -> None:
    """H2∘M2 = id on Z."""
    assert get_operator("H2").apply(get_operator("M2").apply(n)) == n


@IDENTITY
@given(x=Z, y=Z)
def test_cmp3_is_sign_of_difference(x: int, y: int) -> None:
    """BTC-cmp3: cmp3(x, y) = sign(x - y), translation and negation laws."""
    assert cmp3(x, y) == sign_trit(x - y)
    assert cmp3(x, y) == neg(cmp3(y, x))
    assert cmp3(-x, -y) == neg(cmp3(x, y))
    z = 11
    assert cmp3(x + z, y + z) == cmp3(x, y)


@IDENTITY
@given(c=TRIT, xm=Z, xz=Z, xp=Z)
def test_select3_branches_and_abs(c: int, xm: int, xz: int, xp: int) -> None:
    """BTC-select3: select3 matches the trit branch; abs_z / min / max."""
    got = select3(c, xm, xz, xp)
    if c < 0:
        assert got == xm
    elif c == 0:
        assert got == xz
    else:
        assert got == xp
    n = xm
    assert abs_z(n) == abs(n)
    assert max_z(n, xz) == max(n, xz)
    assert min_z(n, xz) == min(n, xz)


@IDENTITY
@given(a=TRIT, b=TRIT, c=TRIT)
def test_trit_lattice_associativity(a: int, b: int, c: int) -> None:
    """BTC-trit-kleene fragment: min/max associative; not Boolean."""
    ta, tb, tc = as_trit(a), as_trit(b), as_trit(c)
    assert trit_min(ta, trit_min(tb, tc)) == trit_min(trit_min(ta, tb), tc)
    assert trit_max(ta, trit_max(tb, tc)) == trit_max(trit_max(ta, tb), tc)
    join_neg = trit_max(ta, neg(ta))
    if ta is Trit.ZERO:
        assert join_neg is Trit.ZERO
    else:
        assert join_neg is Trit.PLUS


@IDENTITY
@given(n=Z)
def test_pn_evaluates_to_n_at_three(n: int) -> None:
    """BT-Pn3: P_n(3) = n."""
    assert polynomial(n).evaluate(3) == n


@IDENTITY
@given(n=Z)
def test_tree_rewrite_section_identities(n: int) -> None:
    """D∘I_a = id and N∘N = id as evaluated trees."""
    x = EInt(n)
    assert evaluate(ED(EShift3(x))) == n
    assert evaluate(ED(EIp(x))) == n
    assert evaluate(ED(EIm(x))) == n
    assert evaluate(ED(EI0(x))) == n
    assert evaluate(ENeg(ENeg(x))) == n
    assert evaluate(ENeg(EShift3(x))) == evaluate(EShift3(ENeg(x)))


@IDENTITY
@given(n=Z)
def test_simplifying_word_rules_sound_on_z(n: int) -> None:
    """Every simplifying word rule preserves the integer action."""
    for rule in WORD_SIMP_RULES:
        try:
            left = _apply_math_word(rule.src, n)
            right = _apply_math_word(rule.dst, n)
        except OperatorDomainError:
            continue
        assert left == right, rule.reason

"""Paper A's cycle finance, transposed to Collatz, reproduces Eliahou 1993 and Hercher 2018.

`J-juggler-is-collatz-one-exponential-up` says the two problems share the linear form
`o log 3 - L log 2` and part only at how words attach to integers. On cycles that claim has a
numerical test, and this probe runs it.

**The two finance inequalities are one inequality with the sign of the gap flipped.** For a
shortcut Collatz cycle of length `K` with `p` odd steps, multiplying the step relations around
the cycle gives the exact identity `K log 2 - p log 3 = sum over odd steps of log(1 + 1/(3 x_j))`
(Eliahou's inequality (2), Hercher's Theorem 16), hence

    Lambda_C(K) := K log 2 - p log 3 = log 3 * frac(K x),   x = log 2 / log 3,   p = floor(K x),
    x_min <= p / (3 Lambda_C).

For a Juggler cycle Paper A Theorem 4.4 (`cycleMin_finance`, constant 1) gives

    Lambda_J(L) := o log 3 - L log 2 = log 3 * (1 - frac(L x)),   o = ceil(L x),
    n log n <= L / (1 - exp(-Lambda_J)) = L 3^o / (3^o - 2^L).

So `Lambda_J(L) = log 3 - Lambda_C(L)` for every length: the Collatz-dangerous lengths have
`frac(L x)` just above `0`, the Juggler-dangerous ones just below `1`, and the convergents of
`log 3 / log 2` alternate between the two. The cycle-level dictionary is `x_min <-> n log n`,
not the walk-level `log x <-> log log n`; the two differ by a factor `n` and must not be
substituted for one another.

**The test.** A length survives finance at a floor when its bound does not fall below the floor.
Enumerating the survivors exactly with the three-gap walk (the set `{K : frac(K x) < eps}` is
walked by the two one-sided return times of the rotation), the Collatz side gives

* floor `2^40`: smallest survivor `17087915`, every survivor of the form
  `301994 a + 17087915 b + 85137581 c` with `b >= 1` and `a c = 0` -- Eliahou 1993 exactly;
* floor `2^68`: smallest survivor `114208327604`, with `72057431991` odd steps -- Hercher's
  2018 period bound, quoted as "more than 7.2e10 odd numbers";
* floor `2^71`: the second survivor is `217976794617`, Barina's 2025 bound; the first is still
  `114208327604`, which Barina removes with a sharper averaging this probe does not use.

and the Juggler side, at constant 1, leaves `1054` and its multiples first at floor `10^6` and
`50508` first at `3.5e8`. Paper A's certified comparison (Lemma 4.4b, evens charged at `n^2` and
climb interiors at `n^(3/2)`) is sharper and leaves `25781` and `176251` -- the printed Theorem
4.6 and Corollary 5.11 finance floors -- so the inequality used on the Collatz side here is the
weaker of the two Juggler forms, and it is that weaker form which already matches the published
Collatz bounds.

**What it does not do.** No cycle of any length is excluded or claimed in either problem; the
Collatz numbers are re-derived, not new. The 1-cycle length `9809721694` (a Juggler-side
convergent numerator) survives the Juggler finance at `N_0 = 3.5e8` by ten orders of magnitude,
which is the numerical form of "Juggler has no Steiner theorem": nothing floor-free excludes a
Juggler 1-cycle, where Collatz has excluded them since 1977 through the 2-adic run congruence.
"""

from __future__ import annotations

import json
import math
from typing import Any

import numpy as np
from mpmath import mp, mpf, exp, floor, log

from research.juggler_sequence.lean_paths import DATA_ROOT, DOCS_RESEARCH
from research.juggler_sequence.paper_a_audit import survivors as paper_a_survivors

DATA_DIR = DATA_ROOT / "collatz_finance_mirror"
JSON_PATH = DATA_DIR / "summary.json"
DOC_PATH = DOCS_RESEARCH / "juggler_collatz_finance_mirror.md"

CLASS_MIRROR = "FINANCE_MIRROR_REPRODUCES_ELIAHOU_HERCHER"

#: Eliahou 1993: the admissible Collatz periods at floor 2^40.
ELIAHOU_GENERATORS = (301994, 17087915, 85137581)
#: Hercher 2018 (Die Wurzel, with Puchert), the period bound as quoted by Hercher 2023 at the
#: floor 695 * 2^60: the smallest surviving shortcut length, and its odd count.
HERCHER_LENGTH, HERCHER_ODD = 114208327604, 72057431991
#: Barina 2025 at floor 2^71.
BARINA_LENGTH = 217976794617

_DPS = 80


def _x() -> mpf:
    return log(2) / log(3)


def frac(v: mpf) -> mpf:
    return v - floor(v)


def lambda_collatz(K: int) -> tuple[int, mpf]:
    """``(p, Lambda_C)``: ``p = floor(K x)`` and ``K log 2 - p log 3 = log 3 * frac(K x)``."""
    with mp.workdps(_DPS):
        v = K * _x()
        p = int(floor(v))
        return p, log(3) * frac(v)


def lambda_juggler(L: int) -> tuple[int, mpf]:
    """``(o, Lambda_J)``: ``o = ceil(L x)`` and ``o log 3 - L log 2 = log 3 * (1 - frac(L x))``."""
    with mp.workdps(_DPS):
        v = L * _x()
        o = int(floor(v)) + 1
        return o, log(3) * (1 - frac(v))


def collatz_bound(K: int) -> mpf:
    """The Collatz finance majorant on the cycle minimum, ``p / (3 Lambda_C)``."""
    p, lam = lambda_collatz(K)
    with mp.workdps(_DPS):
        return mpf(p) / (3 * lam)


def juggler_bound(L: int) -> mpf:
    """Paper A Theorem 4.4 at constant 1, as a bound on ``n log n``: ``L / (1 - exp(-Lambda_J))``."""
    _, lam = lambda_juggler(L)
    with mp.workdps(_DPS):
        return mpf(L) / (1 - exp(-lam))


def nlogn(N0: int) -> mpf:
    with mp.workdps(_DPS):
        return mpf(N0) * log(mpf(N0))


# ---------------------------------------------------------------------------------------------
# The walk charge, transposed: odd-step heights are at least frac(a * alpha)
# ---------------------------------------------------------------------------------------------

#: `1/(2 log 2)`: the average of `2^(-t)` over `[0, 1)`, the hug-word constant.
HUG_INTEGRAL = 0.7213475204444817
#: Hercher 2023, Theorem 27: `sum over odd steps of 1/x_j <= (3/4) K / X_0`, `K` the odd count.
HERCHER_THEOREM_27 = 0.75


def word_const(word: list[int]) -> int:
    """`wordConst` of CollatzBridge.lean: `2^d C^d(x) = 3^o x + wordConst w`."""
    c, o = 0, 0
    for b in reversed(word):
        c = 3**o + 2 * c if b else 2 * c
        o += b
    return c


def even_charge(word: list[int]) -> int:
    """`evenCharge` of CollatzBridge.lean: `2^d (C^d(x) + 1) = 3^o (x + 1) + evenCharge w`."""
    e, o = 0, 0
    for b in reversed(word):
        e = 2 * e if b else 3**o + 2 * e
        o += b
    return e


def shortcut_orbit(x: int, d: int) -> tuple[list[int], list[int]]:
    """The parity word and the states `x_0 .. x_d` of the shortcut orbit."""
    word, states = [], [x]
    for _ in range(d):
        word.append(x % 2)
        x = x // 2 if x % 2 == 0 else (3 * x + 1) // 2
        states.append(x)
    return word, states


def hug_sum(p: int) -> float:
    """`H(p) = sum_{a < p} 2^(-frac(a alpha))`, `alpha = log2(3/2)`: the largest possible sum of
    `2^(-h)` over the first `p` odd steps of any orbit that never falls below its start, attained
    by the hug word. float64; the fractional parts carry error below `p * 2.2e-16`."""
    with mp.workdps(30):
        alpha = float(log(3) / log(2) - 1)
    total = 0.0
    for start in range(0, p, 50_000_000):
        a = np.arange(start, min(start + 50_000_000, p), dtype=np.float64)
        total += float(np.sum(2.0 ** (-np.mod(a * alpha, 1.0))))
    return total


def hug_sup(lo: int, P: int = 2 * 10**7) -> tuple[float, int]:
    """``sup_{lo <= p <= P} H(p)/p`` and where it is attained: the effective constant beyond ``lo``."""
    with mp.workdps(30):
        alpha = float(log(3) / log(2) - 1)
    a = np.arange(P, dtype=np.float64)
    ratio = np.cumsum(2.0 ** (-np.mod(a * alpha, 1.0))) / np.arange(1, P + 1)
    seg = ratio[lo - 1:]
    i = int(np.argmax(seg))
    return float(seg[i]), i + lo


def height_bound_holds(x0: int, dmax: int = 200) -> dict[str, Any]:
    """Check the height inequality on the non-dropping prefix of the orbit of ``x0``.

    Along the prefix on which ``x_j >= x0``, the height ``h_j = a_j alpha - e_j`` before the
    ``a_j``-th odd step must satisfy ``h_j >= frac(a_j alpha)`` unless
    ``frac(a_j alpha) >= 1 - delta_j``, ``delta_j = log2((x0 + 1 + S_j)/(x0 + 1))`` with ``S_j``
    the even-step sum ``sum 2^(-h_i)`` so far; and ``sum over odd steps of 2^(-h_j)`` must be at
    most ``H(a) + N_delta``. Exact rationals for the heights' integer parts, floats for the rest.
    """
    from fractions import Fraction
    with mp.workdps(30):
        alpha = float(log(3) / log(2) - 1)
    word, states = shortcut_orbit(x0, dmax)
    a = e = 0
    S = 0.0
    odd_sum = 0.0
    exceptional = 0
    bad = 0
    for j, b in enumerate(word):
        if states[j] < x0:
            break
        h = a * alpha - e
        if b == 1:
            fr = a * alpha - math.floor(a * alpha)
            delta = math.log2((x0 + 1 + S) / (x0 + 1))
            if h < fr - 1e-12:
                if fr >= 1 - delta - 1e-12:
                    exceptional += 1
                else:
                    bad += 1
            odd_sum += 2.0 ** (-h)
            a += 1
        else:
            S += 2.0 ** (-h)
            e += 1
    H = hug_sum(a) if a else 0.0
    return {"prefix_length": j, "odd_steps": a, "violations": bad, "exceptional": exceptional,
            "odd_sum_le_H_plus_N": odd_sum <= H + exceptional + 1e-9}


def hug_word(p: int) -> list[int]:
    """The hug word with ``p`` odd letters: the lowest non-negative walk, odd exactly when the
    height is below ``1``, closed with the evens that bring the height back below ``1``. Its odd
    steps sit at the heights ``frac(a alpha)``, ``a = 0 .. p-1``."""
    with mp.workdps(60):
        alpha = log(3) / log(2) - 1
        w, h, a = [], mpf(0), 0
        while a < p:
            if h < 1:
                w.append(1)
                h += alpha
                a += 1
            else:
                w.append(0)
                h -= 1
        while h >= 1:
            w.append(0)
            h -= 1
        return w


def realize_word(word: list[int]) -> int:
    """A residue ``r < 2^K`` whose shortcut parity word is ``word``: Terras's bijection, built one
    letter at a time (``exists_residue_of_word`` in CollatzBridge.lean, made effective)."""
    r = 0
    for d in range(len(word)):
        for cand in (r, r + (1 << d)):
            x = cand
            for _ in range(d):
                x = x // 2 if x % 2 == 0 else (3 * x + 1) // 2
            if x % 2 == word[d]:
                r = cand
                break
        else:  # pragma: no cover - Terras forbids it
            raise RuntimeError("no lift realises the next letter")
    return r


def sharpness_ratio(p: int, extra_bits: int = 300) -> float:
    """``x_0 * sum_{odd} 1/x_j / H(p)`` along the hug word realised at a start with ``extra_bits``
    more bits than its length: ``1`` to the precision of the ``O(K/x_0)`` correction, which is
    the statement that no bound using only ``x_j + 1 >= 2^(h_j) (x_0 + 1)`` can beat ``H(p)``."""
    from fractions import Fraction
    word = hug_word(p)
    r = realize_word(word)
    x0 = r + (1 << (len(word) + extra_bits))
    x, s = x0, Fraction(0)
    for b in word:
        assert x % 2 == b and x >= x0
        if b:
            s += Fraction(1, x)
        x = x // 2 if x % 2 == 0 else (3 * x + 1) // 2
    return float(s * x0) / hug_sum(p)


# ---------------------------------------------------------------------------------------------
# The cycle equation as a word problem: rational cycles of minimal certificates and of survivors
# ---------------------------------------------------------------------------------------------

def rational_cycle(word: list[int]):
    """The rational fixed point of the word's affine map, `x_0 = wordConst w / (2^K - 3^o)`.

    Positive for contracting words, negative for expanding ones; Lagarias 1990: it is the unique
    rational with odd denominator whose parity vector is `w` repeated. An integer cycle with word
    `w` exists exactly when it is an integer (the `2^K - 3^o | evenCharge w` of
    `cycle_dvd` / `cycle_of_equation` in CollatzBridge.lean).
    """
    from fractions import Fraction
    K, o = len(word), sum(word)
    return Fraction(word_const(word), 2**K - 3**o)


def follows_rational(x0, word: list[int]) -> bool:
    """Whether the shortcut map, extended to rationals with odd denominator (parity = parity of
    the numerator), follows `word` from `x0` and returns to it."""
    x = x0
    for b in word:
        assert x.denominator % 2 == 1
        if x.numerator % 2 != b:
            return False
        x = x / 2 if b == 0 else (3 * x + 1) / 2
    return x == x0


def minimal_certificates(K: int) -> list[tuple[int, ...]]:
    """The minimal certificates of length `K`: proper prefixes non-contracting, the word contracting.
    These are the Collatz positive-cycle words (at the cycle minimum, up to the `delta`
    exceptions of `J-collatz-walk-charge-constant`), and `M_K` counts them."""
    out: list[tuple[int, ...]] = []

    def rec(prefix: list[int], a: int, j: int) -> None:
        if j == K:
            if 3**a < 2**K:
                out.append(tuple(prefix))
            return
        for b in (1, 0):
            a2, j2 = a + b, j + 1
            if j2 < K and 3**a2 < 2**j2:
                continue
            prefix.append(b)
            rec(prefix, a2, j2)
            prefix.pop()

    rec([], 0, 0)
    return out


def expanding_survivors(L: int) -> list[tuple[int, ...]]:
    """The words of length `L` with every prefix non-contracting and `3^o > 2^L`: Paper A's
    cycle-word shape for Juggler, and the Collatz negative-cycle words."""
    out: list[tuple[int, ...]] = []

    def rec(prefix: list[int], a: int, j: int) -> None:
        if j == L:
            if 3**a > 2**L:
                out.append(tuple(prefix))
            return
        for b in (1, 0):
            a2, j2 = a + b, j + 1
            if 3**a2 < 2**j2:
                continue
            prefix.append(b)
            rec(prefix, a2, j2)
            prefix.pop()

    rec([], 0, 0)
    return out


def cycle_census(kmax: int = 20, lmax: int = 18) -> dict[str, Any]:
    """Rational cycles of every minimal certificate up to length `kmax` and every expanding
    survivor up to length `lmax`: each must follow its word and return (Lagarias's rational-cycle
    theorem, checked), and the integral ones are the integer cycles."""
    pos_total = neg_total = 0
    pos_fail = neg_fail = 0
    pos_integral: list[tuple[int, str, int]] = []
    neg_integral: list[tuple[int, str, int]] = []
    counts: dict[int, int] = {}
    for K in range(1, kmax + 1):
        certs = minimal_certificates(K)
        counts[K] = len(certs)
        for w in certs:
            x0 = rational_cycle(list(w))
            pos_total += 1
            if not follows_rational(x0, list(w)):
                pos_fail += 1
            if x0.denominator == 1 and x0 > 0:
                pos_integral.append((K, "".join("O" if b else "E" for b in w), int(x0)))
    for L in range(1, lmax + 1):
        for w in expanding_survivors(L):
            x0 = rational_cycle(list(w))
            neg_total += 1
            if not follows_rational(x0, list(w)):
                neg_fail += 1
            if x0.denominator == 1:
                neg_integral.append((L, "".join("O" if b else "E" for b in w), int(x0)))
    primitive_neg = sorted({(x, wd) for (_, wd, x) in neg_integral
                            if all(wd != wd[:k] * (len(wd) // k) for k in range(1, len(wd)) if len(wd) % k == 0)})
    return {
        "kmax": kmax, "lmax": lmax,
        "minimal_certificate_counts": counts,
        "positive_words": pos_total, "positive_failures": pos_fail, "positive_integral": pos_integral,
        "negative_words": neg_total, "negative_failures": neg_fail,
        "negative_integral_primitive": primitive_neg,
    }


# ---------------------------------------------------------------------------------------------
# The negative cycles: Juggler's finance, read on Collatz's negative integers
# ---------------------------------------------------------------------------------------------

#: `1/(6 alpha log 2)`: the average of `2^(-h)` over even steps of the hug word, whose heights
#: before an even step are uniform on `[1, 1 + alpha)`.
EVEN_HUG_INTEGRAL = 0.4110505770627386


def even_hug_sum(m: int) -> float:
    """`H_E(m) = sum_{e < m} 2^(-h_e)` with `h_e = ceil((e+1)/alpha) alpha - e`, the least height
    an admissible word can have before its `e`-th even step (the height after it must stay
    non-negative); the hug word attains every term."""
    with mp.workdps(30):
        alpha = float(log(3) / log(2) - 1)
    e = np.arange(m, dtype=np.float64)
    return float(np.sum(2.0 ** (-(np.ceil((e + 1) / alpha) * alpha - e))))


def negative_cycle_survivors(Y0: mpf, kmax: int, *, charge: float = 0.5) -> list[dict[str, Any]]:
    """Lengths `K <= kmax` that a negative Collatz cycle with least `|x| >= Y0` could have.

    On a negative cycle read at its least `|x|` (`neg_prefix_noncontracting`), the cycle equation
    gives `(|x| - 1)(3^o - 2^K) = evenCharge w = 3^o sum over even steps of 2^(-h_i)` with every
    `h_i >= 1`, so `|x| - 1 <= charge * (K - o) / theta_J(K)`, `theta_J = 1 - 2^K/3^o`, with
    `charge = 1/2` uniformly and `EVEN_HUG_INTEGRAL` on the hug word. The survivors are the
    Juggler-side dangerous lengths: this is Paper A's finance table on the other side.
    """
    with mp.workdps(_DPS):
        eps = min(mpf(kmax) * charge / (log(3) * (Y0 - 1)) * mpf("1.01"), mpf("0.5"))
        out = []
        for K in three_gap_walk(eps, -1, kmax):
            o, lam = lambda_juggler(K)
            theta = 1 - exp(-lam)
            bound = 1 + mpf(charge) * (K - o) / theta
            if bound >= Y0:
                out.append({"K": K, "o": o, "abs_x_le": float(bound)})
        return out


def walk_charge_bound(K: int, *, exact_below: int = 3 * 10**8) -> mpf:
    """The transposed walk charge on the cycle minimum: `x_min <= H(p) / (3 Lambda_C) (1 + o(1))`.

    Above `exact_below` odd steps `H(p)` is replaced by `p / (2 log 2)`; by Koksma the relative
    error is below `1e-9` at `p ~ 7e10` (variation `1/2` times the discrepancy of `{a alpha}`).
    """
    p, lam = lambda_collatz(K)
    H = hug_sum(p) if p <= exact_below else p * HUG_INTEGRAL
    with mp.workdps(_DPS):
        return mpf(H) / (3 * lam)


# ---------------------------------------------------------------------------------------------
# Sides of the convergents
# ---------------------------------------------------------------------------------------------

def continued_fraction(terms: int = 30) -> list[int]:
    """Partial quotients of ``log 2 / log 3``."""
    with mp.workdps(_DPS):
        a, y = [], _x()
        for _ in range(terms):
            ai = int(floor(y))
            a.append(ai)
            y = 1 / (y - ai)
        return a


def convergent_sides(terms: int = 22, exact_below: int = 2 * 10**7) -> list[dict[str, Any]]:
    """Each convergent ``p/q`` of ``x`` with the sign of ``q log 2 - p log 3``.

    ``3^p > 2^q`` (gap negative, Juggler-admissible) or ``2^q > 3^p`` (gap positive,
    Collatz-admissible). Below ``exact_below`` the side is decided by comparing the integers
    ``3^p`` and ``2^q`` themselves; above it by ``frac(q x)`` at 80 digits, which is certified by
    the margin recorded in the row.
    """
    a = continued_fraction(terms)
    p0, q0, p1, q1 = 0, 1, 1, 0
    rows: list[dict[str, Any]] = []
    for ai in a:
        p0, p1 = p1, ai * p1 + p0
        q0, q1 = q1, ai * q1 + q0
        p, q = p1, q1
        if q == 0:
            continue
        with mp.workdps(_DPS):
            f = frac(q * _x())
            margin = float(min(f, 1 - f))
        if q <= exact_below:
            juggler_side = (3**p).bit_length() > q   # 3^p > 2^q  <=>  bit_length(3^p) > q
            method = "integers"
        else:
            juggler_side = bool(f > mpf("0.5"))
            method = "frac at 80 digits"
        rows.append({
            "p": p, "q": q, "frac_q_x": float(f), "margin": margin, "method": method,
            "side": "juggler" if juggler_side else "collatz",
        })
    return rows


#: OEIS A355512, offset 1: the sum of numerator and denominator over the convergents of
#: ``log 2 / log 3``. Its first term is the sum at the convergent ``1/1``; the degenerate
#: ``0/1`` that ``convergent_cycle_lengths`` emits first has no OEIS counterpart, which is
#: the whole of the index shift between the two.
A355512_HEAD = (2, 3, 5, 13, 31, 106, 137, 791, 1719, 40328, 82375, 205078, 287453, 492531)


def convergent_cycle_lengths(terms: int = 30) -> list[dict[str, Any]]:
    """Both cycle-length conventions on each convergent ``p/q`` of ``log 2 / log 3``.

    **This laboratory works in the shortcut map**, where every step halves: a cycle with ``o``
    odd steps and length ``K`` satisfies ``3^o ~ 2^K``, so ``o/K ~ log 2 / log 3`` and the period
    is the **denominator** ``q``. Eliahou 1993's ``17087915`` is such a ``q``, as are the
    leftovers ``3, 19, 84, 1054, 301994`` and the ``103768467013`` of the floor table.

    **The unaccelerated map does not halve on an odd step**, so a cycle there has length
    ``o + h = p + q``. That sum over the convergents is OEIS **A355512**, and it is a different
    quantity from the period above: the two differ by exactly ``p``, the odd-step count. A period
    quoted from the literature has to be read in the convention it was written in before it is
    compared with anything here -- ``17026679261``, which circulates as a cycle-length bound, is a
    ``p + q`` and so is **not** commensurable with this laboratory's ``q`` periods.
    """
    a = continued_fraction(terms)
    p0, q0, p1, q1 = 0, 1, 1, 0
    rows: list[dict[str, Any]] = []
    for ai in a:
        p0, p1 = p1, ai * p1 + p0
        q0, q1 = q1, ai * q1 + q0
        if q1 == 0:
            continue
        rows.append({
            "p": p1,
            "q": q1,
            "odd_steps": p1,
            "shortcut_period": q1,
            "unaccelerated_length": p1 + q1,
        })
    return rows


def a355512(terms: int = 30) -> list[int]:
    """OEIS A355512 as this laboratory computes it, with the degenerate convergent dropped."""
    return [r["unaccelerated_length"] for r in convergent_cycle_lengths(terms)][1:]


# ---------------------------------------------------------------------------------------------
# The three-gap walk
# ---------------------------------------------------------------------------------------------

def _one_sided_returns(eps: mpf, terms: int = 40) -> tuple[int, int, mpf, mpf]:
    """``(q1, q2, d1, d2)``: least ``q`` with ``frac(q x) < eps`` and least ``q`` with
    ``1 - frac(q x) < eps``, found among convergents and semiconvergents."""
    a = continued_fraction(terms)
    p0, q0, p1, q1 = 0, 1, 1, 0
    conv = []
    for ai in a:
        p0, p1 = p1, ai * p1 + p0
        q0, q1 = q1, ai * q1 + q0
        conv.append((p1, q1))
    x = _x()
    best = {+1: None, -1: None}
    for i in range(1, len(conv)):
        (_, qp), (_, q) = conv[i - 1], conv[i]
        ai1 = a[i + 1] if i + 1 < len(a) else 1
        for j in range(0, ai1 + 1):
            Q = qp + j * q
            if Q <= 0:
                continue
            f = frac(Q * x)
            for side, val in ((+1, f), (-1, 1 - f)):
                if val < eps and (best[side] is None or Q < best[side]):
                    best[side] = Q
        if best[+1] is not None and best[-1] is not None and q > max(best[+1], best[-1]):
            break
    q1, q2 = best[+1], best[-1]
    return q1, q2, frac(q1 * x), 1 - frac(q2 * x)


def three_gap_walk(eps: mpf, side: int, kmax: int) -> list[int]:
    """All ``K <= kmax`` with ``g(K) < eps``, ``g = frac(K x)`` (side +1) or ``1 - frac(K x)``
    (side -1), enumerated exactly: from a member with value ``g``, the next member is ``K + up``
    if ``g + du < eps``, else ``K + dn`` if ``g >= dd``, else ``K + up + dn``."""
    with mp.workdps(_DPS):
        q1, q2, d1, d2 = _one_sided_returns(eps)
        up, dn, du, dd = (q1, q2, d1, d2) if side > 0 else (q2, q1, d2, d1)
        K, g, out = up, du, []
        while K <= kmax:
            out.append(K)
            if g + du < eps:
                K += up
                g += du
            elif g >= dd:
                K += dn
                g -= dd
            else:
                K += up + dn
                g += du - dd
        return out


def collatz_survivors(X0: mpf, kmax: int, *, charge: float = 1.0) -> list[dict[str, Any]]:
    """Collatz lengths ``K <= kmax`` whose finance majorant does not fall below the floor.

    ``charge`` scales the majorant: ``1`` is the trivial per-odd-step bound ``p/(3 Lambda)``,
    ``HERCHER_THEOREM_27`` is Hercher's ``3/4`` and ``HUG_INTEGRAL`` the transposed walk charge.
    """
    with mp.workdps(_DPS):
        eps = mpf(kmax) * _x() / (3 * log(3) * X0) * mpf("1.001")
        out = []
        for K in three_gap_walk(eps, +1, kmax):
            p, lam = lambda_collatz(K)
            bound = mpf(charge) * mpf(p) / (3 * lam)
            if bound >= X0:
                out.append({"K": K, "p": p, "frac": float(lam / log(3)), "x_min_le": float(bound)})
        return out


def juggler_survivors(N0: int, lmax: int) -> list[dict[str, Any]]:
    """Juggler lengths ``L <= lmax`` surviving Theorem 4.4 at constant 1 at floor ``N0``."""
    with mp.workdps(_DPS):
        F = nlogn(N0)
        eps = min(mpf(lmax) / (log(3) * F) * mpf("1.001"), mpf("0.5"))
        out = []
        for L in three_gap_walk(eps, -1, lmax):
            o, lam = lambda_juggler(L)
            bound = mpf(L) / (1 - exp(-lam))
            if bound >= F:
                out.append({"L": L, "o": o, "one_minus_frac": float(lam / log(3)),
                            "nlogn_le": float(bound)})
        return out


def brute_force_collatz_survivors(X0: float, kmax: int) -> list[int]:
    """Independent check of the walk: every ``K <= kmax`` by a float candidate filter and an
    exact refinement. ``kmax`` up to a few ``10^7`` runs in about a second."""
    xf = float(_x())
    log3 = math.log(3)
    K = np.arange(1, kmax + 1, dtype=np.float64)
    f = np.mod(K * xf, 1.0)
    sel = f <= K * xf / (3.0 * log3 * X0) * 1.01 + 1e-7
    out = []
    for k in K[sel].astype(np.int64).tolist():
        if collatz_bound(int(k)) >= X0:
            out.append(int(k))
    return out


def eliahou_decomposition(K: int) -> tuple[int, int, int] | None:
    """``(a, b, c)`` with ``K = 301994 a + 17087915 b + 85137581 c``, ``b >= 1``, ``a c = 0``."""
    g1, g2, g3 = ELIAHOU_GENERATORS
    for c in range(0, K // g3 + 1):
        for b in range(1, (K - g3 * c) // g2 + 1):
            rest = K - g3 * c - g2 * b
            if rest % g1 == 0:
                a = rest // g1
                if a * c == 0:
                    return (a, b, c)
    return None


# ---------------------------------------------------------------------------------------------
# The record
# ---------------------------------------------------------------------------------------------

def probe_payload(*, kmax_40: int = 4 * 10**8, brute_kmax: int = 3 * 10**7) -> dict[str, Any]:
    with mp.workdps(_DPS):
        two40, two68, two71 = mpf(2) ** 40, mpf(2) ** 68, mpf(2) ** 71
        hercher_floor = 695 * mpf(2) ** 60
        s40 = collatz_survivors(two40, kmax_40)
        brute = brute_force_collatz_survivors(float(two40), brute_kmax)
        walk_below = [r["K"] for r in s40 if r["K"] <= brute_kmax]
        s_h = collatz_survivors(hercher_floor, 4 * 10**11)
        s68 = collatz_survivors(two68, 4 * 10**11)
        s71 = collatz_survivors(two71, 10**12)
        j6 = juggler_survivors(10**6, 2 * 10**6)
        j35 = juggler_survivors(350_000_000, 2 * 10**6)
        one_cycle = 9809721694
        o1, lam1 = lambda_juggler(one_cycle)
        mirror = max(abs(lambda_collatz(K)[1] + lambda_juggler(K)[1] - log(3))
                     for K in (1, 19, 84, 1054, 301994, 17087915, 85137581))
        hug = {p: hug_sum(p) / p for p in (12, 53, 665, 31867, 111202, 190537, 10781274)}
        wc68 = collatz_survivors(two68, 4 * 10**11, charge=HUG_INTEGRAL)
        wc71 = collatz_survivors(two71, 10**12, charge=HUG_INTEGRAL)
        identities_hold = all(
            2**d * (states[d] + 1) == 3**sum(word) * (x0 + 1) + even_charge(word)
            and word_const(word) + 2**d == 3**sum(word) + even_charge(word)
            for x0 in (1, 7, 27, 97, 871, 6171, 77031, 2**20 + 1)
            for d in (1, 2, 5, 17, 40)
            for word, states in [shortcut_orbit(x0, d)]
        )
    census = cycle_census(26, 24)
    with mp.workdps(_DPS):
        neg_table = {}
        for name, Y0, kmax in (("2^40", mpf(2) ** 40, 3 * 10**8), ("2^60", mpf(2) ** 60, 2 * 10**10),
                               ("2^68", mpf(2) ** 68, 4 * 10**11), ("2^71", mpf(2) ** 71, 10**12)):
            su = negative_cycle_survivors(Y0, kmax, charge=0.5)
            sh = negative_cycle_survivors(Y0, kmax, charge=EVEN_HUG_INTEGRAL)
            neg_table[name] = {"uniform_smallest": su[0]["K"], "uniform_count": len(su),
                               "hug_smallest": sh[0]["K"], "hug_count": len(sh), "kmax": kmax}
        known = {}
        for K, o, y in ((1, 1, 1), (3, 2, 5), (11, 7, 17)):
            lam = o * log(3) - K * log(2)
            theta = 1 - exp(-lam)
            known[str(y)] = {"K": K, "o": o, "uniform_bound": float(1 + mpf(K - o) / (2 * theta)),
                             "hug_bound": float(1 + mpf(even_hug_sum(K - o)) / theta)}
    return {
        "cycle_census": census,
        "negative_cycles": {
            "statement": (
                "a negative Collatz cycle read at its least |x| has an expanding word with no"
                " contracting prefix (neg_cycle_word_is_juggler_shape), and (|x|-1)(3^o - 2^K) ="
                " evenCharge w = 3^o sum over even steps of 2^(-h_i) with h_i >= 1, so"
                " |x| - 1 <= charge (K - o)/theta_J(K): Paper A's finance on the other side"
            ),
            "even_hug_average_at": {str(m): even_hug_sum(m) / m for m in (10**3, 10**5, 10**7)},
            "even_hug_constant": EVEN_HUG_INTEGRAL,
            "survivors": neg_table,
            "known_cycles_against_the_bound": known,
            "verification_floor": "no published verification floor for the 3x-1 map was found; the table is conditional on the floor",
        },
        "walk_charge": {
            "statement": (
                "on a cycle at its minimum x_0 the height before the a-th odd step is at least"
                " frac(a alpha), alpha = log2(3/2), up to a correction of order K/x_0, so"
                " Lambda_C <= H(p)/(3 x_0) (1 + o(1)) with H(p) = sum_{a<p} 2^(-frac(a alpha))"
            ),
            "hug_average": {str(p): v for p, v in hug.items()},
            "constant": HUG_INTEGRAL,
            "hercher_theorem_27": HERCHER_THEOREM_27,
            "trivial": 1.0,
            "remark_28_threshold_units_2_60": {
                "eliahou_methods": 3781, "theorem_27": 2836,
                "walk_charge": round(2836 * HUG_INTEGRAL / HERCHER_THEOREM_27),
                "corollary_29_computational": 1536,
            },
            "smallest_survivor_with_walk_charge": {"2^68": wc68[0]["K"], "2^71": wc71[0]["K"]},
            "margin_at_2_71": float(walk_charge_bound(HERCHER_LENGTH) / two71),
            "integer_identities_hold": identities_hold,
            "effective": {
                "sup_hug_average_p_ge_100": hug_sup(100)[0],
                "sup_hug_average_p_ge_1e5": hug_sup(100_000)[0],
                "partial_quotient_sum_to_5e12": 150,
                "exceptional_bound": "N_delta(p) <= p delta + 151 for p <= 5e12",
                "delta_at_hercher_floor": float(log(1 + mpf(HERCHER_LENGTH) / (695 * mpf(2) ** 60 + 1 - HERCHER_LENGTH)) / log(2)),
                "orbit_prefix_checks": {str(x): height_bound_holds(x) for x in (27, 97, 871, 6171, 77031, 2**31 + 1)},
            },
        },
        "answer": "Paper A's finance transposed by x_min <-> n log n reproduces Eliahou and Hercher",
        "identities": {
            "lambda_collatz": "K log 2 - floor(K x) log 3 = log 3 * frac(K x)",
            "lambda_juggler": "ceil(L x) log 3 - L log 2 = log 3 * (1 - frac(L x))",
            "mirror": "Lambda_J(L) = log 3 - Lambda_C(L)",
            "mirror_residual": float(mirror),
            "cycle_dictionary": "x_min <-> n log n (not the walk-level log x <-> log log n)",
        },
        "convergent_sides": convergent_sides(),
        "collatz": {
            "floor_2_40": {
                "smallest": s40[0]["K"], "count_below": kmax_40, "n_survivors": len(s40),
                "first": s40[:8],
                "all_in_eliahou_lattice": all(eliahou_decomposition(r["K"]) is not None for r in s40),
                "pure_301994_multiples_excluded": all(
                    collatz_bound(301994 * a) < two40 for a in range(1, 57)),
                "brute_force_agrees_below": brute_kmax,
                "brute_force_agrees": brute == walk_below,
            },
            "floor_695_2_60": {"smallest": s_h[0]["K"], "odd": s_h[0]["p"], "first": s_h[:4]},
            "floor_2_68": {"smallest": s68[0]["K"], "odd": s68[0]["p"], "first": s68[:4]},
            "floor_2_71": {"first_two": [r["K"] for r in s71[:2]], "first": s71[:4]},
            "eliahou_generators": list(ELIAHOU_GENERATORS),
            "hercher": [HERCHER_LENGTH, HERCHER_ODD], "barina": BARINA_LENGTH,
        },
        "juggler": {
            "floor_1e6": {"smallest": j6[0]["L"], "first": [r["L"] for r in j6[:12]],
                          "paper_a_certified_smallest": paper_a_survivors(10**6, 30_000)[0]},
            "floor_3_5e8": {"smallest": j35[0]["L"], "first": [r["L"] for r in j35[:12]],
                            "paper_a_certified_smallest": paper_a_survivors(350_000_000, 200_000)[0]},
            "one_cycle_length": one_cycle, "one_cycle_odd": o1,
            "one_cycle_nlogn_bound": float(mpf(one_cycle) / (1 - exp(-lam1))),
            "floor_nlogn_3_5e8": float(nlogn(350_000_000)),
        },
        "decision": {
            "classification": CLASS_MIRROR,
            "reason": (
                "the Collatz transposition of Theorem 4.4 reproduces Eliahou's period bound and"
                " lattice at 2^40 and Hercher's bound at 2^68 from the same inequality, walk and"
                " brute force agreeing; the Juggler side reproduces the laboratory's own survivors"
            ),
        },
        "anti_overclaim": (
            "No cycle of any length is excluded or claimed in either problem. The Collatz numbers"
            " are re-derived from a classical inequality, not new; Barina's 2025 bound needs a"
            " sharper averaging than this inequality. The Juggler 1-cycle length 9809721694"
            " survives finance at N_0 = 3.5e8, which records that no Juggler analogue of Steiner's"
            " theorem exists, not that a cycle does."
        ),
    }


def render_markdown(data: dict[str, Any]) -> str:
    c, j = data["collatz"], data["juggler"]
    lines = [
        "# Paper A's finance, transposed to Collatz, reproduces Eliahou 1993 and Hercher 2018",
        "",
        "Generated by `python -m research.juggler_sequence.collatz_finance_mirror`.",
        "",
        "## The mirror",
        "",
        f"- `{data['identities']['lambda_collatz']}`",
        f"- `{data['identities']['lambda_juggler']}`",
        f"- `{data['identities']['mirror']}` (residual `{data['identities']['mirror_residual']:.1e}`)",
        f"- cycle-level dictionary: `{data['identities']['cycle_dictionary']}`",
        "",
        "## Collatz side, `x_min <= p / (3 Lambda_C)`",
        "",
        f"- floor `2^40`: smallest survivor `{c['floor_2_40']['smallest']}`;"
        f" all `{c['floor_2_40']['n_survivors']}` survivors below `{c['floor_2_40']['count_below']}`"
        f" in Eliahou's lattice = `{c['floor_2_40']['all_in_eliahou_lattice']}`;"
        f" brute force agrees below `{c['floor_2_40']['brute_force_agrees_below']}` ="
        f" `{c['floor_2_40']['brute_force_agrees']}`",
        f"- floor `695 * 2^60`: smallest `{c['floor_695_2_60']['smallest']}` with"
        f" `{c['floor_695_2_60']['odd']}` odd steps (Hercher 2018)",
        f"- floor `2^68`: smallest `{c['floor_2_68']['smallest']}` with `{c['floor_2_68']['odd']}` odd steps",
        f"- floor `2^71`: first two `{c['floor_2_71']['first_two']}` (Barina 2025 is the second)",
        "",
        "## Juggler side, `n log n <= L / (1 - exp(-Lambda_J))` (Theorem 4.4, constant 1)",
        "",
        f"- floor `10^6`: smallest `{j['floor_1e6']['smallest']}`, first `{j['floor_1e6']['first']}`",
        f"- floor `3.5e8`: smallest `{j['floor_3_5e8']['smallest']}`, first `{j['floor_3_5e8']['first']}`",
        f"- the 1-cycle length `{j['one_cycle_length']}` has bound `{j['one_cycle_nlogn_bound']:.3e}`"
        f" against the floor `{j['floor_nlogn_3_5e8']:.3e}`: not excluded by finance",
        "",
        "## The walk charge, transposed",
        "",
        f"- `H(p)/p` at `p = 10781274`: `{data['walk_charge']['hug_average']['10781274']:.8f}`;"
        f" limit `1/(2 log 2) = {data['walk_charge']['constant']:.8f}`; Hercher's Theorem 27 constant"
        f" `{data['walk_charge']['hercher_theorem_27']}`; trivial `1`",
        f"- Remark 28 threshold in units of `2^60`: `{data['walk_charge']['remark_28_threshold_units_2_60']}`",
        f"- smallest survivor with the walk charge: `{data['walk_charge']['smallest_survivor_with_walk_charge']}`"
        f" (margin at `2^71`: `{data['walk_charge']['margin_at_2_71']:.3f}`)",
        f"- integer identities of `CollatzBridge.lean` re-checked on orbits: `{data['walk_charge']['integer_identities_hold']}`",
        "",
        "## What this does not say",
        "",
        data["anti_overclaim"],
        "",
    ]
    return "\n".join(lines)


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    DOC_PATH.write_text(render_markdown(data), encoding="utf-8")
    return data


def main() -> None:
    data = write_artifacts()
    print(data["decision"]["classification"])
    c = data["collatz"]
    print("2^40 smallest", c["floor_2_40"]["smallest"], "| lattice", c["floor_2_40"]["all_in_eliahou_lattice"],
          "| brute agrees", c["floor_2_40"]["brute_force_agrees"])
    print("2^68 smallest", c["floor_2_68"]["smallest"], "odd", c["floor_2_68"]["odd"])
    print("2^71 first two", c["floor_2_71"]["first_two"])
    print("juggler smallest", data["juggler"]["floor_1e6"]["smallest"], data["juggler"]["floor_3_5e8"]["smallest"])


if __name__ == "__main__":
    main()

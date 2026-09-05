"""The run-suffix law: Section 3's twelve exclusions are one inequality.

Section 3 of Paper A excludes cycle itineraries with at most three even letters by proving
eleven separate statements -- Lemma 3.4(v), Theorems 3.12, 3.14-3.20 and the two families of
Theorem 3.21 -- each of the form "the word ``O^a`` followed by this short suffix is not a cycle
itinerary once ``a`` is at least such-and-such".  The thresholds (3, 4, 3, 6, 5, 4, 3, 5, 4, 3)
look like a list.  They are not: every one of them is the least ``a`` satisfying

    (3/2)^a  >  2^s / 3^l,

where ``s`` is the length of the suffix and ``l`` its odd count.  This module states the
underlying inequality, tests whether it is exact on all eleven, and prices the threshold on
``n``.

Two ingredients, both already in the paper, and one new closed form:

* forward -- Lemma 3.10 says ``n^(3^a) <= 2^(e_a) J^a(n)^(2^a)`` with ``e_a = 2(3^a - 2^a)``.
  Dividing exponents by ``2^a`` turns that into ``J^a(n) >= 4 (n/4)^((3/2)^a)``: one constant,
  one exponent.  ``forward_bound`` is that closed form.
* backward -- Lemma 3.9 says the state before a trailing run of ``r`` even letters is below
  ``(n+1)^(2^r)``.  Its induction does not need the run to be even: an odd letter contributes
  ``x^3 < (next + 1)^2``.  So the bound propagates backward through *any* suffix, squaring the
  exponent on an even letter and multiplying it by 2/3 on an odd one -- ``suffix_exponent``.
  With integer bounds no slop accumulates (``exact_backward_envelope`` checks this).

Putting an odd run of length ``a`` between them, at a state ``m >= n`` because the itinerary is
minimum-based, gives the criterion of ``excluded``.  At leading order it says that no proper
suffix beginning with an odd letter may be formally expanding, which is the mirror image of
Theorem 3.2(i) for the whole word.
"""

from __future__ import annotations

import math
from fractions import Fraction
from typing import Any

LN2 = math.log(2.0)
LN4 = 2.0 * LN2

# suffix, threshold on a printed in the paper, and where it is printed
RECOVERIES: tuple[tuple[str, int, str], ...] = (
    ("E", 3, "Lemma 3.4(v)"),
    ("EE", 4, "Theorem 3.12 first family / Theorem 3.21 first family"),
    ("EOE", 3, "Theorem 3.12 second family / Theorem 3.21 second family"),
    ("EEE", 6, "Theorem 3.14"),
    ("EOEE", 5, "Theorem 3.15"),
    ("EOOEE", 4, "Theorem 3.16"),
    ("EOOOEE", 3, "Theorem 3.17"),
    ("EEOE", 5, "Theorem 3.18"),
    ("EOEOE", 4, "Theorem 3.19"),
    ("EOOEOE", 3, "Theorem 3.20"),
)

LAB_FLOOR = 26_254_995   # the certified descent floor Paper A quotes


def forward_exponent(a: int) -> Fraction:
    """``J^a(n) >= 4 (n/4)^P`` with ``P = (3/2)^a`` -- Lemma 3.10 in closed form."""
    return Fraction(3, 2) ** a


def forward_bound(n: int, a: int) -> float:
    """The closed form itself, in logarithms."""
    P = float(forward_exponent(a))
    return LN4 + P * (math.log(n) - LN4)


def suffix_exponent(suffix: str) -> Fraction:
    """``x < (n+1)^T`` for the state entering ``suffix``: ``T = 2^s / 3^l``."""
    s = len(suffix)
    l = suffix.count("O")
    return Fraction(2) ** s / Fraction(3) ** l


def icbrt(m: int) -> int:
    """Floor cube root of a non-negative integer, exactly."""
    if m < 2:
        if m < 0:
            raise ValueError(m)
        return m
    r = 1 << ((m.bit_length() + 2) // 3)      # an over-estimate; Newton descends
    while True:
        nxt = (2 * r + m // (r * r)) // 3
        if nxt >= r:
            break
        r = nxt
    while r ** 3 > m:
        r -= 1
    while (r + 1) ** 3 <= m:
        r += 1
    return r


def exact_backward_envelope(suffix: str, n: int) -> int:
    """Integer version of the backward envelope: the state entering ``suffix`` is ``< B``.

    Slop does not accumulate.  ``x < B`` for an integer bound means ``x + 1 <= B``, so an even
    predecessor obeys ``y < (x+1)^2 <= B^2`` exactly, and an odd predecessor obeys
    ``y^3 < (x+1)^2 <= B^2``, whose integer solutions are ``y < icbrt(B^2 - 1) + 1``.
    """
    B = n + 1
    for letter in reversed(suffix):
        B = B * B if letter == "E" else icbrt(B * B - 1) + 1
    return B


def excluded(a: int, suffix: str, n: int) -> bool:
    """Is ``O^a`` + ``suffix`` refuted at a cycle minimum ``n``?

    The odd run starts at a state ``m >= n``; the forward bound is increasing in ``m``, so the
    worst case is ``m = n``.  A contradiction is ``4 (n/4)^P >= (n+1)^T``.
    """
    T = float(suffix_exponent(suffix))
    return forward_bound(n, a) >= T * math.log(n + 1)


def threshold(a: int, suffix: str, hi: int = 10 ** 60) -> int | None:
    """Least cycle minimum ``n`` at which ``O^a`` + ``suffix`` is refuted, or ``None``."""
    if forward_exponent(a) <= suffix_exponent(suffix):
        return None                      # no margin: the envelopes never cross
    lo = 2
    if not excluded(a, suffix, hi):
        return None
    while lo < hi:
        mid = (lo + hi) // 2
        if excluded(a, suffix, mid):
            hi = mid
        else:
            lo = mid + 1
    return lo


def excluded_exact(a: int, suffix: str, n: int, dps: int = 60) -> bool:
    """The same criterion against the exact integer backward envelope, not its exponent.

    ``excluded`` compares the forward bound with ``(n+1)^(2^s/3^l)``, which is the limit of the
    envelope but not the envelope: each backward odd letter rounds a cube root up.  This version
    compares against ``exact_backward_envelope`` itself, so the thresholds it returns are the
    ones a proof can quote.  The two agree to within a few percent on ``n`` (the slop is
    additive in the state, hence negligible once ``n`` is large), and the exact one is never
    the weaker of the two.
    """
    from mpmath import mp, mpf, log as mlog

    with mp.workdps(dps):
        B = exact_backward_envelope(suffix, n)
        P = mpf(forward_exponent(a).numerator) / forward_exponent(a).denominator
        lhs = mlog(mpf(4)) + P * (mlog(mpf(n)) - mlog(mpf(4)))
        return bool(lhs >= mlog(mpf(B)))


def threshold_exact(a: int, suffix: str, hi: int = 10 ** 30) -> int | None:
    """Least cycle minimum at which ``excluded_exact`` fires."""
    if forward_exponent(a) <= suffix_exponent(suffix):
        return None
    if not excluded_exact(a, suffix, hi):
        return None
    lo = 2
    while lo < hi:
        mid = (lo + hi) // 2
        if excluded_exact(a, suffix, mid):
            hi = mid
        else:
            lo = mid + 1
    return lo


def least_run(suffix: str, a_max: int = 40) -> int | None:
    """Least ``a`` with ``(3/2)^a > 2^s / 3^l`` -- the law's threshold, ``n`` aside."""
    T = suffix_exponent(suffix)
    for a in range(1, a_max + 1):
        if forward_exponent(a) > T:
            return a
    return None


def margin(a: int, suffix: str) -> float:
    """``theta = 1 - T/P``: how much room the leading exponents leave."""
    P = float(forward_exponent(a))
    return 1.0 - float(suffix_exponent(suffix)) / P


def floor_constant(n: int = LAB_FLOOR) -> float:
    """Least margin the crude constant can pay for at a cycle minimum ``n``.

    ``4 (n/4)^P >= (n+1)^T`` with ``T = (1-theta)P`` reads ``P theta ln n >= (P-1) ln 4 +
    T ln(1+1/n)``.  Taking ``P -> infinity`` (the worst case, since the right side's leading
    term is ``P ln 4``) gives ``theta >= ln 4 / ln n``.
    """
    return LN4 / math.log(n)


# --- applying the law to whole minimum-based words ---


def word_suffix(runs: tuple[int, ...], i: int) -> str:
    """The suffix following run ``i`` of the canonical word ``O^a1 E O^a2 E ... O^ae E``."""
    out = "E"
    for a in runs[i + 1:]:
        out += "O" * a + "E"
    return out


def excluded_word(runs: tuple[int, ...], n: int) -> bool:
    """Is the canonical word refuted at a cycle minimum ``n`` by *any* of its runs?

    Minimum-basedness puts every run start at a state ``>= n``, so the law applies at each of
    them independently.  A word is closed as soon as one run fires.
    """
    return any(a and excluded(a, word_suffix(runs, i), n) for i, a in enumerate(runs))


def word_threshold(runs: tuple[int, ...], hi: int = 10 ** 60) -> int | None:
    """Least floor at which the law closes this word."""
    if not excluded_word(runs, hi):
        return None
    lo = 2
    while lo < hi:
        mid = (lo + hi) // 2
        if excluded_word(runs, mid):
            hi = mid
        else:
            lo = mid + 1
    return lo


def canonical_words(e: int, cap: int, o_max: int):
    """Minimum-based canonical run vectors with ``e`` even letters and ``3^o > 2^L``."""
    def rec(prefix: tuple[int, ...]):
        if len(prefix) == e:
            o = sum(prefix)
            if o <= o_max and 3 ** o > 2 ** (o + e):
                yield prefix
            return
        lo = 2 if not prefix else 0
        for a in range(lo, cap):
            if sum(prefix) + a <= o_max:
                yield from rec(prefix + (a,))
    yield from rec(())


def even_count_floor(e: int = 4, cap: int = 30, o_max: int = 40) -> dict[str, Any]:
    """The floor at which the law closes every word with ``e`` even letters.

    Reaching that floor upgrades the even-count theorem from ``e >= 4`` to ``e >= e+1``.  The
    binding word is reported: it is the one whose ``(o, L)`` is the best rational approximation
    to ``log_2 3`` available at that even count, which is why the floor is as high as it is.
    """
    worst: tuple[int, tuple[int, ...]] | None = None
    unclosable = []
    for runs in canonical_words(e, cap, o_max):
        t = word_threshold(runs)
        if t is None:
            unclosable.append(runs)
        elif worst is None or t > worst[0]:
            worst = (t, runs)
    assert worst is not None
    o = sum(worst[1])
    return {
        "e": e,
        "floor": worst[0],
        "binding_word": worst[1],
        "binding_o": o,
        "binding_L": o + e,
        "unclosable": unclosable,
    }


# --- the sharp envelope: minimum-basedness used at every step of the run ---


def sharp_exponents(a: int) -> tuple[int, int]:
    """``(X_a, Y_a)`` with ``n^X_a < (n+1)^Y_a (J^a(n)+1)^(2^a)`` on a minimum-based run.

    Lemma 3.24 applies minimum-basedness once, at the start of the run, and pays Lemma 3.3's
    factor 4 at every step.  It need not: at step ``k`` the state ``x_k`` is itself at least the
    cycle minimum, so ``(x_k+1)^e n^e <= (n+1)^e x_k^e`` converts the successor's ``+1`` into a
    factor ``((n+1)/n)^e`` instead of a factor 4.  Cubing the invariant and absorbing one odd
    one-step preimage gives ``X_(k+1) = 3 X_k + 3*2^k`` and the same recurrence for ``Y``, from
    ``X_1 = 3``, ``Y_1 = 0`` -- that is, ``X_a = 3(3^a - 2^a)`` and ``Y_a = 2*3^a - 3*2^a``.

    ``formal/Problems/Juggler/O7EEEEGap.lean`` is this chain at ``a = 7``, where it produces the
    constants 6177 and 3990; ``absorb_odd_step`` there is the inductive step.
    """
    return 3 * (3 ** a - 2 ** a), 2 * 3 ** a - 3 * 2 ** a


def excluded_sharp(a: int, suffix: str, n: int, dps: int = 80) -> bool:
    """The run-suffix law with the sharp envelope: no constant, only ``(1+1/n)`` corrections.

    The contradiction is ``B(u)^(2^a) (n+1)^(Y_a) <= n^(X_a)``, whose leading order is simply
    ``2^s/3^l < (3/2)^a`` -- the same crossing as ``excluded``, but reached without paying
    Lemma 3.3's factor 4 at each step.
    """
    from mpmath import mp, mpf, log as mlog

    with mp.workdps(dps):
        X, Y = sharp_exponents(a)
        B = exact_backward_envelope(suffix, n)
        lhs = 2 ** a * mlog(mpf(B)) + Y * mlog(mpf(n + 1))
        return bool(lhs <= X * mlog(mpf(n)))


def threshold_sharp(a: int, suffix: str, hi: int = 10 ** 30) -> int | None:
    """Least cycle minimum at which the sharp criterion fires."""
    if forward_exponent(a) <= suffix_exponent(suffix):
        return None
    if not excluded_sharp(a, suffix, hi):
        return None
    lo = 2
    while lo < hi:
        mid = (lo + hi) // 2
        if excluded_sharp(a, suffix, mid):
            hi = mid
        else:
            lo = mid + 1
    return lo


def excluded_word_sharp(runs: tuple[int, ...], n: int) -> bool:
    return any(a and excluded_sharp(a, word_suffix(runs, i), n) for i, a in enumerate(runs))


def word_threshold_sharp(runs: tuple[int, ...], hi: int = 10 ** 30) -> int | None:
    if not excluded_word_sharp(runs, hi):
        return None
    lo = 2
    while lo < hi:
        mid = (lo + hi) // 2
        if excluded_word_sharp(runs, mid):
            hi = mid
        else:
            lo = mid + 1
    return lo


def even_count_floor_sharp(e: int = 4, cap: int = 12, o_max: int = 22) -> dict[str, Any]:
    """The floor at which the sharp law closes every word with ``e`` even letters."""
    worst = None
    unclosable = []
    for runs in canonical_words(e, cap, o_max):
        t = word_threshold_sharp(runs)
        if t is None:
            unclosable.append(runs)
        elif worst is None or t > worst[0]:
            worst = (t, runs)
    assert worst is not None
    o = sum(worst[1])
    return {"e": e, "floor": worst[0], "binding_word": worst[1],
            "binding_o": o, "binding_L": o + e, "unclosable": unclosable}


def run_bound(e: int, i: int) -> int:
    """Largest odd-run length the law leaves open at run ``i`` of an ``e``-even word.

    The suffix after run ``i`` carries ``e - i`` even letters and however many odd letters the
    later runs contribute.  Odd letters only shrink ``2^s/3^l``, and the criterion is monotone
    in the envelope, so the worst case is the later runs empty: ``T <= 2^(e-i)``.
    """
    return least_run("E" * (e - i)) - 1


def bounded_canonical_words(e: int):
    """Every minimum-based canonical form with ``e`` even letters, using ``run_bound``.

    This enumeration is complete, not truncated: any run longer than its bound is closed by
    the law at that run, at the threshold of the corresponding pure trailing block.
    """
    bounds = [run_bound(e, i) for i in range(e)]

    def rec(pre: tuple[int, ...]):
        i = len(pre)
        if i == e:
            o = sum(pre)
            if pre and pre[0] >= 2 and 3 ** o > 2 ** (o + e):
                yield pre
            return
        for a in range(bounds[i] + 1):
            yield from rec(pre + (a,))

    return bounds, rec(())


LADDER = (16, 32, 64, 128, 256)


def closure(e: int, ladder: tuple[int, ...] = LADDER) -> dict[str, Any]:
    """Least rung of ``ladder`` at which the sharp law closes every ``e``-even word."""
    bounds, gen = bounded_canonical_words(e)
    words = list(gen)
    worst: tuple[int, tuple[int, ...]] | None = None
    still_open = []
    for w in words:
        got = next((n for n in ladder if excluded_word_sharp(w, n)), None)
        if got is None:
            still_open.append(w)
        elif worst is None or got > worst[0]:
            worst = (got, w)
    return {"e": e, "run_bounds": bounds, "words": len(words),
            "closed_at": worst[0] if worst else None,
            "binding_word": worst[1] if worst else None,
            "still_open": still_open}


def recovery_table(n: int = LAB_FLOOR) -> list[dict[str, Any]]:
    rows = []
    for suffix, printed, source in RECOVERIES:
        law = least_run(suffix)
        rows.append({
            "suffix": suffix,
            "T": suffix_exponent(suffix),
            "printed": printed,
            "law": law,
            "agrees": law == printed,
            "threshold_at_law": threshold(law, suffix),
            "threshold_exact": threshold_exact(law, suffix),
            "excluded_at_floor": excluded(law, suffix, n),
            "source": source,
        })
    return rows


def main() -> None:
    print("the run-suffix law against the eleven statements of Section 3")
    print()
    print("  %-8s %-10s %-8s %-6s %-11s %-11s %s"
          % ("suffix", "T=2^s/3^l", "paper a", "law a", "n (exact)", "n (limit)", "source"))
    rows = recovery_table()
    for r in rows:
        print("  %-8s %-10s %-8d %-6s %-11s %-11s %s"
              % (r["suffix"], r["T"], r["printed"], r["law"], r["threshold_exact"],
                 r["threshold_at_law"], r["source"].split(" /")[0]))
    agree = sum(1 for r in rows if r["agrees"])
    print()
    print("  law reproduces %d of %d printed thresholds exactly" % (agree, len(rows)))
    off = [(r["suffix"], r["printed"], r["law"]) for r in rows if not r["agrees"]]
    if off:
        print("  disagreements (suffix, paper, law): %s" % off)

    print()
    print("at the certified floor n >= %d the crude constant pays for any margin above %.4f"
          % (LAB_FLOOR, floor_constant()))
    print("  i.e. every suffix beginning with an odd letter obeys 3^o < %.4f * 2^L"
          % (1.0 / (1.0 - floor_constant())))
    worst = min(rows, key=lambda r: margin(r["law"], r["suffix"]))
    print("  thinnest margin among the eleven: %s at a=%d, theta=%.4f"
          % (worst["suffix"], worst["law"], margin(worst["law"], worst["suffix"])))

    print()
    for e in (3, 4):
        r = even_count_floor(e)
        print("floor at which the law closes every word with e = %d: %s"
              % (e, "{:,}".format(r["floor"])))
        print("   binding word: O^%s, (o, L) = (%d, %d), 3^o / 2^L = %.6f"
              % ("EO^".join(str(a) for a in r["binding_word"]) + "E",
                 r["binding_o"], r["binding_L"],
                 3.0 ** r["binding_o"] / 2.0 ** r["binding_L"]))
        if r["unclosable"]:
            print("   words the law never closes: %s" % r["unclosable"][:5])

    print()
    print("no slop: exact integer backward envelope vs the (n+1)^T exponent, n = 12345")
    for suffix, _p, _s in RECOVERIES[:6]:
        B = exact_backward_envelope(suffix, 12345)
        T = float(suffix_exponent(suffix))
        print("   %-8s exact log_(n+1) B = %.9f   T = %.9f"
              % (suffix, math.log(B) / math.log(12346), T))


if __name__ == "__main__":
    main()

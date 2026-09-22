"""Juggler is Collatz one exponential level up, and that is why the counts coincide.

`J-paper-b-survivors-are-oeis-a076227` records that Paper B's survivor count is a
known Collatz sequence. This probe asks why, and answers it structurally rather than
by coincidence of small numbers.

**The shared walk.** Accelerated Collatz sends `x` to `x/2` or `(3x+1)/2`, so `log x`
moves by `-log 2` or `+log(3/2)`. Juggler sends `n` to `floor(sqrt n)` or
`floor(n^(3/2))`, so `log n` is *multiplied* by `1/2` or `3/2`, and therefore

    log log n  moves by  -log 2  or  +log(3/2)

the same two steps on a different variable. Measured from a twenty-one digit seed the
Juggler increments match to `2e-16`. Both maps realise the same additive walk with
steps `log(3/2)` and `-log 2`; Collatz on `log x`, Juggler on `log log n`. Nothing is
conjugate here -- the maps are not conjugate -- but the multiplier semigroup is one.

**Hence one count.** After `m` steps with `o` odd ones the walk sits at
`o log 3 - m log 2`, and "has not yet dropped below the start" is `3 ^ o >= 2 ^ m` in
both problems. So the non-contracting words are the same words and `N_d` is the same
integer. On the Collatz side that integer is the number of residue classes modulo
`2 ^ d` whose stopping time is not constant, and this probe checks that directly by
running Collatz rather than by quoting the OEIS entry.

**Where the two part, and it is the whole of Paper B.** For Collatz the parity word of
the first `d` steps is a function of `x mod 2 ^ d`, and the map to `{0,1}^d` is a
bijection, so every word has density exactly `2 ^ (-d)`. That is Terras: arithmetic,
exact, free. For Juggler the word is a function of `frac(n^(3/2))`, `frac(n^(3/4))` and
so on -- fractional parts, not congruences -- and that the densities are `2 ^ (-d)` is
Hypothesis FD, which is open and is the analytic burden of Paper B.

Same combinatorics, incompatible arithmetic. The two are not equivalent, and this is
exactly where the inequivalence lives.

**Three consequences, recorded because they cut both ways.** The asymptotic of
`J-paper-b-jump-spectrum-is-the-survivor-sequence` is unconditional for Collatz and
conditional for Juggler. Collatz is a free validator for any FD-conditional derivation
that depends only on word densities, since there such a statement is a theorem. And any
result that depends only on word densities is not Juggler-specific at all -- see
`collatz_reachable`, which is the audit this identification forces.
"""

from __future__ import annotations

import json
import math
from fractions import Fraction
from itertools import product
from typing import Any

from research.juggler_sequence.lean_paths import DOCS_RESEARCH

JSON_PATH = DOCS_RESEARCH / "juggler_collatz_bridge.json"
DOC_PATH = DOCS_RESEARCH / "juggler_collatz_bridge.md"

CLASS_BRIDGE = "JUGGLER_IS_COLLATZ_ONE_EXPONENTIAL_UP"

#: The two steps of the shared additive walk.
STEP_ODD = math.log(1.5)
STEP_EVEN = -math.log(2.0)


def big_log(n: int) -> float:
    """`log n` for integers far past the float range.

    Juggler values are doubly exponential, so the third iterate of a twenty-digit seed
    already overflows a float. Taking the top fifty-three bits and correcting by the
    shift keeps full double precision without any big-float dependency.
    """
    bits = n.bit_length()
    if bits <= 53:
        return math.log(n)
    return (bits - 53) * math.log(2.0) + math.log(n >> (bits - 53))


def juggler(n: int) -> int:
    """`floor(sqrt n)` for even `n`, `floor(n^(3/2))` for odd -- exact in integers."""
    return math.isqrt(n) if n % 2 == 0 else math.isqrt(n**3)


def loglog_increments(seed: int, steps: int = 8,
                      floor: int = 1_000_000) -> list[tuple[bool, float, float]]:
    """Measured increments of `log log n` along a Juggler orbit, against the targets.

    Returned as `(was_odd, measured, target)`. The floor costs `O(1)` in `n`, hence
    `O(1/n)` in `log n`, so the agreement is only as good as the seed is large: at
    `n = 7` the error is a percent, and past twenty digits it is at the last bit.
    `floor` stops the walk before `log log` loses meaning; drop it to see the small-`n`
    error, which is the point of the comparison rather than noise to hide.
    """
    out: list[tuple[bool, float, float]] = []
    current = seed
    for _ in range(steps):
        odd = current % 2 == 1
        nxt = juggler(current)
        if nxt < floor:
            break
        measured = math.log(big_log(nxt)) - math.log(big_log(current))
        out.append((odd, measured, STEP_ODD if odd else STEP_EVEN))
        current = nxt
    return out


def collatz(x: int) -> int:
    """The shortcut map, `x/2` on evens and `(3x+1)/2` on odds."""
    return x // 2 if x % 2 == 0 else (3 * x + 1) // 2


def parity_word(x: int, depth: int) -> tuple[int, ...]:
    """The first `depth` parities of the Collatz orbit of `x`."""
    word, current = [], x
    for _ in range(depth):
        word.append(current % 2)
        current = collatz(current)
    return tuple(word)


def parity_map_is_bijective(depth: int) -> bool:
    """Terras: `x mod 2^depth` determines the word, and does so bijectively.

    This is the statement Juggler has no analogue of, and checking it here keeps the
    asymmetry visible rather than asserted.
    """
    return len({parity_word(x, depth) for x in range(2**depth)}) == 2**depth


def undecided_classes(depth: int, representatives: int = 8) -> int:
    """Residue classes modulo `2^depth` on which the Collatz stopping time varies.

    A class whose word has already dropped has one stopping time for every member; a
    class whose word never drops does not. Counted by running Collatz, so that the
    identification with `N_d` is checked and not quoted.
    """
    count = 0
    for residue in range(2**depth):
        times: set[int | None] = set()
        for k in range(1, representatives + 1):
            start = residue + k * 2**depth
            steps, value = 0, start
            while True:
                steps += 1
                value = collatz(value)
                if value < start:
                    times.add(steps)
                    break
                if steps > 4 * depth:
                    times.add(None)
                    break
        if len(times) > 1 or None in times:
            count += 1
    return count


#: The audit's four outcomes. `collatz_reachable` is `audit_class(...) == CLASS_SHARED`.
CLASS_SHARED = "SHARED"                    # word densities: a Collatz result too
CLASS_ANALYTIC = "JUGGLER_ANALYTIC"        # how orbits realise words: FD, Weyl, the kernel
CLASS_METRIC = "JUGGLER_METRIC"            # how the map deforms scale: fibres, log-mass
CLASS_UNCLASSIFIED = "UNCLASSIFIED"        # the audit does not recognise it -- say so

_SHARED_WORDS = ("word", "certificate", "barrier", "survivor", "jump", "amplitude",
                 "recursion", "count", "spectrum", "ladder")
_ANALYTIC_WORDS = ("equidistribution", "hypothesis fd", "weyl", "kernel",
                   "frac(n^", "floor power", "orbit of n", "discrepancy",
                   "conjecture k")
_METRIC_WORDS = ("preimage", "fibre", "fiber", "even block", "harmonic mass",
                 "log-mass", "backward-closed", "contagion", "jacobian",
                 "deforms scale", "fat")


def audit_class(statement: str) -> str:
    """Which of the three classes a claim sits in, or that it sits in none.

    `J-word-density-results-are-not-juggler-specific` was recorded as a binary:
    word combinatorics is shared with Collatz, how orbits realise words is
    Juggler-only. That is one class short, and the missing one is the
    load-bearing one for Paper C.

    **The third class is metric.** Paper C's engine -- Lemma 2.1's even block,
    Lemma 2.2's OE fibre, Lemma 4.1's seed, contagion itself -- is about how
    the map deforms SCALE, the reciprocal Jacobian of its action on the log
    line. It is exact, elementary, Lean-checked and needs no equidistribution,
    and it is still Juggler-only, because the shortcut Collatz map has no
    fat preimages. It is neither word combinatorics nor orbit realisation, so
    the binary audit had nowhere to put it.

    The binary also overloaded `False`, which meant both "Juggler-specific" and
    "not recognised". A metric claim returned `False` for the second reason
    while looking like the first. `CLASS_UNCLASSIFIED` now says so out loud,
    which is the point of an audit that exists to make a question unavoidable.

    Precedence is analytic, then metric, then shared: a claim naming both a
    fibre and Hypothesis FD rests on FD, and one naming both a fibre and a word
    count rests on the fibre. Still a vocabulary check and not a theorem
    prover.
    """
    lowered = statement.lower()
    if any(term in lowered for term in _ANALYTIC_WORDS):
        return CLASS_ANALYTIC
    if any(term in lowered for term in _METRIC_WORDS):
        return CLASS_METRIC
    if any(term in lowered for term in _SHARED_WORDS):
        return CLASS_SHARED
    return CLASS_UNCLASSIFIED


def collatz_reachable(statement: str) -> bool:
    """Does a claim depend only on word densities, and so belong to Collatz too?

    The audit this identification forces. Paper B's laboratory side splits in two. What
    uses only the words -- the survivor recursion, the empty-window theorem, the
    transposition cost, the jump spectrum, `a_1`, the ladder profile -- is a statement
    about the shared multiplier semigroup, true of Collatz as well, and is not
    Juggler-specific however Juggler-shaped its wording. What uses how orbits realise
    words is Juggler-specific, and is Hypothesis FD and everything built on it.

    Deliberately a vocabulary check rather than a theorem prover: it exists to make the
    question unavoidable when a row is written, not to answer it.

    Now a thin wrapper over `audit_class`, which has a third class the binary was
    missing -- metric facts about how the map deforms scale, which is where Paper C's
    engine lives -- and which reports `UNCLASSIFIED` rather than returning `False` for
    a claim it does not recognise.
    """
    return audit_class(statement) == CLASS_SHARED


#: `-log2(theta)`. Collatz's unconditional density exponent, and the unit the
#: conditional Juggler one is measured in.
COLLATZ_EXPONENT = -math.log(
    (math.log(2) / math.log(3)) ** (-math.log(2) / math.log(3))
    * (1 - math.log(2) / math.log(3)) ** (math.log(2) / math.log(3) - 1) / 2
) / math.log(2)


def density_exponent(delta: float, combination: str = "union") -> float:
    """What a power saving `delta` buys, as a density exponent.

    The power-saving hypothesis is **Conjecture K**, not Hypothesis FD. FD is stated
    with no common error rate in `d` assumed at all, so it carries no `delta`; an
    earlier version of this docstring said "Hypothesis FD with power saving `delta`"
    and conflated the two.

    Proposition J bounds the starts with no contracting prefix of length `<= d` by
    `(N_d / 2^d) N + N_d E_d(N)`. The main term is about `theta^d N` and wants `d`
    large; the error caps it. Minimising over `d` turns `delta` into an exponent, and
    the answer depends on how the word classes are combined:

    - `union`: the error is `N_d E_d(N) = (2 theta)^d N^(1-delta)`, the bound as
      Proposition J states it. Gives `-log2(theta) * delta`.
    - `sqrt`: if the per-word errors cancelled at square root, `sqrt(N_d) E_d(N)`.
    - `direct`: one estimate of the whole good set, with no factor of `N_d` at all.
      The error is then free of `d`, so the depth is capped only by the main term and
      the exponent is `delta` itself.

    **The `direct` reading is unreachable and the `sqrt` reading is conditional.** The
    combination factor is `N_d / ||ghat||_1`, and `||ghat||_1` saturates the Parseval
    ceiling: `gamma = sqrt(2*theta)` exactly, measured to `d = 386`, so `sqrt` is the
    best there is and `direct` is not on the table. Worse, even `sqrt` needs the
    analytic input given as a character bound on `W_S`; under Proposition J's per-word
    hypothesis the conversion costs `2^d` and the route LOSES -- see
    `walsh_conversion_penalty` and `J-good-set-walsh-route-is-refuted`. This function is
    kept as the arithmetic of the comparison, not as a menu of available options.
    """
    from math import log

    beta = log(2) / log(3)
    theta = beta ** (-beta) * (1 - beta) ** (beta - 1) / 2
    if combination == "union":
        return -log(theta) / log(2.0) * delta
    if combination == "sqrt":
        return 2.0 * (-log(theta)) / log(2.0 / theta) * delta
    if combination == "direct":
        return delta
    raise ValueError(f"unknown combination {combination!r}")


def good_set_wiener_norm(depth: int) -> float:
    """`||ghat||_1` for the good set, from the library function that already had it.

    `collision_large_sieve.bad_set_spectrum(d, L)` has computed this since the Paper C
    collision branch; `L = 0` is the good set and nobody had called it there. Its
    `wiener_norm` field reproduces a hand-rolled transform to the last digit at every
    depth checked. Two of its other fields do NOT carry over: `p_bad` at `L = 0` is
    `N_d / 2^(d-1)`, twice the good-set density, because the first letter is forced, and
    `wiener_over_density` inherits that factor.
    """
    from research.juggler_sequence.collision_large_sieve import bad_set_spectrum

    return float(bad_set_spectrum(depth, 0.0)["wiener_norm"])


def walsh_conversion_penalty(counts: list[int], depth: int) -> float:
    """What the Walsh route costs under Proposition J's hypothesis as it is stated.

    The two bases are related by an exact identity in each direction:

        W_S(N) = sum_w (-1)^(w.S) (#w(N) - 2^-d N)        =>  max_S |W_S| <= 2^d E_d
        #w(N) - 2^-d N = 2^-d sum_(S != 0) (-1)^(w.S) W_S  =>  E_d <= max_(S != 0) |W_S|

    so `E_d <= max|W_S| <= 2^d E_d` and the gap is attained at both ends. A Walsh
    estimate needs the SECOND bound and Proposition J supplies only the first, so
    converting costs `2^d`: the route is worse by this factor, not better by
    `N_d / ||ghat||_1`.
    """
    return (2.0**depth) * good_set_wiener_norm(depth) / counts[depth]


def collatz_is_proposition_j_at_delta_one() -> dict[str, float]:
    """Proposition J applied to Collatz is Terras 1976, and this is the arithmetic.

    Terras makes the parity map a bijection on `Z/2^d`, so a word class holds
    `floor(N/2^d)` or `ceil(N/2^d)` integers and `E_d(N) = O(1)` -- the `delta = 1`
    case. The usable depth is then `log2 N` and the non-descending starts are
    `N^(1 - 0.0500)`, which is the quantitative form of the density-one stopping-time
    theorem. So the laboratory's central conditional, if `FD` were proved outright,
    would deliver for Juggler exactly what has been known for Collatz since 1976.
    """
    return {
        "delta": 1.0,
        "density_exponent": density_exponent(1.0),
        "non_descenders": 1.0 - density_exponent(1.0),
    }


def winkler_sandwich(orders: int = 2213) -> dict[str, Any]:
    """Winkler's rational-Catalan sandwich on A100982, checked on the laboratory's `M_d`.

    A Collatz-side import. Winkler (OEIS A100982 comment, 15 September 2026) states, with
    `alpha = log2 3` and `m_n = floor(n alpha)`, that
    `(1/n) C(m_n - 1, n - 1) <= a(n) <= (1/n) C(m_n, n - 1)`, with equality below exactly at the
    strict record minima of `{n alpha}` over `1 <= j <= n` and above exactly at the strict record
    maxima -- the one-sided convergents and semiconvergents of `log2 3`. The laboratory's
    minimal-certificate count `M_d = 2 N_{d-1} - N_d` equals `a(n)` at `d = A020914(n)`, the
    binary length of `3^n`, and vanishes at every other length (the empty-window theorem). Both
    are checked here on the counts the laboratory computes itself.
    """
    from math import comb

    from mpmath import mp
    from mpmath import floor as mfloor
    from mpmath import log as mlog

    from research.juggler_sequence.jump_spectrum import survivor_counts

    max_len = (3**orders).bit_length()
    counts = survivor_counts(max_len)

    def minimal(d: int) -> int:
        return 2 * counts[d - 1] - counts[d]

    with mp.workdps(60):
        alpha = mlog(3) / mlog(2)
        holds = True
        lower_eq: list[int] = []
        upper_eq: list[int] = []
        rec_min: list[int] = []
        rec_max: list[int] = []
        best_min = best_max = None
        for n in range(1, orders + 1):
            d = (3**n).bit_length()
            a = minimal(d)
            m = int(mfloor(n * alpha))
            lo, hi = comb(m - 1, n - 1), comb(m, n - 1)
            if not (lo <= n * a <= hi):
                holds = False
            if n * a == lo:
                lower_eq.append(n)
            if n * a == hi:
                upper_eq.append(n)
            f = n * alpha - mfloor(n * alpha)
            if best_min is None or f < best_min:
                best_min = f
                if n >= 2:
                    rec_min.append(n)
            if best_max is None or f > best_max:
                best_max = f
                if n >= 2:
                    rec_max.append(n)
    nonzero = [d for d in range(1, max_len + 1) if minimal(d) != 0]
    a020914 = [(3**k).bit_length() for k in range(0, orders + 1)]
    return {
        "orders_checked": orders,
        "holds": holds,
        "a100982_head": [minimal((3**k).bit_length()) for k in range(1, 13)],
        "lower_equality": lower_eq,
        "upper_equality": upper_eq,
        "record_minima": rec_min,
        "record_maxima": rec_max,
        "lower_matches_record_minima": [n for n in lower_eq if n >= 2] == rec_min,
        "upper_matches_record_maxima": [n for n in upper_eq if n >= 2] == rec_max,
        "lengths_are_a020914": nonzero == a020914,
        "nonzero_lengths": len(nonzero),
    }


# ---------------------------------------------------------------------------
# Paper C under the bridge.
#
# Paper C's engine is not the shared walk. It is the way the Juggler map
# deforms scale: the even preimage of `m` is the whole interval
# `[m^2, (m+1)^2)`, whose harmonic mass is asymptotic to `1/m`. The question this
# section settles is what the bridge does to that, and the answer has three
# exact parts and one measured one.
# ---------------------------------------------------------------------------

BARREN_RESIDUE = 3


def even_block_log_mass(m: int) -> Fraction:
    """`m * sum 1/n` over the even preimages of `m`, exactly.

    Lemma 2.1 of Paper C: `J(n) = floor(sqrt n) = m` for every `n` in
    `[m^2, (m+1)^2)`, so the even members of that interval all map to `m`.
    The returned value tends to `1` and is the fibre's log-mass in
    units of `1/m` -- the quantity the contagion recursion actually consumes.
    Odd and even targets must both be retained: the value at `m=3` is
    `107/140 < 1`, so convergence is not uniformly from above.
    """
    if m < 1:
        raise ValueError("m must be positive")
    return m * sum(Fraction(1, n)
                   for n in range(m * m, (m + 1) * (m + 1)) if n % 2 == 0)


def collatz_preimages(m: int) -> list[int]:
    """The integer preimages of `m` under the shortcut Collatz map.

    Always `2m`; additionally `(2m-1)/3` when that is an odd integer, which
    needs `m = 2 mod 3`. So the fibre has one or two elements and never more.

    Note this is a statement about integers, not about `Z_2`: on the 2-adics
    `3` is a unit, `(2m-1)/3` always exists and is always odd, so the map is
    exactly 2-to-1 there. The shortcut map is *not* a bijection on `Z_2`;
    the bijection of Terras is the parity-vector map `Z/2^d -> {0,1}^d`, which
    `parity_map_is_bijective` checks.
    """
    out = [2 * m]
    if (2 * m - 1) % 3 == 0:
        x = (2 * m - 1) // 3
        if x > 0 and x % 2 == 1:
            out.append(x)
    return sorted(out)


def collatz_backward_log_mass(m: int) -> Fraction:
    """`m * sum 1/y` over the shortcut-Collatz preimages of `m`, exactly.

    The counterpart of `even_block_log_mass`. `2m` alone contributes exactly
    `1/2`; the odd preimage, when it exists, contributes `3m/(2m-1)`.
    Thus the value is `1/2` on two residues out of three and approaches
    `2` on the third. Its arithmetic mean tends to `1`; it is not an
    exact finite mean.
    """
    if m < 1:
        raise ValueError("m must be positive")
    return m * sum(Fraction(1, y) for y in collatz_preimages(m))


def log_mass_census(limit: int = 200_000) -> dict[str, Any]:
    """Mean and worst case of the backward log-mass, for both maps.

    The dichotomy Paper C actually runs on. Juggler is asymptotically critical
    *uniformly*; shortcut Collatz is critical *on average* and subcritical in the worst
    case, and the worst case is not a rare event -- it is every multiple of
    three, forever. Theorem 1 quantifies over every nonempty backward-closed
    set, so the worst case is what governs and the mean is irrelevant.
    """
    masses = [float(collatz_backward_log_mass(m)) for m in range(2, limit + 1)]
    worst = min(range(len(masses)), key=masses.__getitem__)
    return {
        "collatz_mean": sum(masses) / len(masses),
        "collatz_min": masses[worst],
        "collatz_argmin": worst + 2,
        "collatz_min_is_on_multiples_of_three": (worst + 2) % BARREN_RESIDUE == 0,
        "juggler_block_mass": {str(m): float(even_block_log_mass(m))
                               for m in (3, 10, 11, 100, 101, 1000, 1001)},
        "verdict": (
            "Juggler even-block mass is asymptotic to 1/m, with the proved lower"
            " bound m/(m+1)^2; OE supplies additional production; shortcut Collatz"
            " critical in the mean and exactly 1/2 in the worst case, attained on"
            " every multiple of three"
        ),
    }


def barren_chain(terms: int = 40) -> list[int]:
    """`{3 * 2^k}`: the counterexample to the Collatz analogue of Theorem 1."""
    return [3 * 2 ** k for k in range(terms)]


def barren_chain_is_backward_closed(terms: int = 40) -> bool:
    """Every preimage of a member is a member.

    `3 * 2^k` has no odd preimage, because `2(3 * 2^k) - 1` is `2 mod 3`. So the
    fibre is the single even point `3 * 2^(k+1)`, which is the next member. The
    set is therefore closed under taking preimages, infinite, and has counting
    function `log_2 x` with `sum 1/n = 2/3`.
    """
    members = set(barren_chain(terms))
    ceiling = max(members)
    return all(y in members for m in members if 2 * m <= ceiling
               for y in collatz_preimages(m))


def collatz_theorem_one_counterexample(terms: int = 40) -> dict[str, Any]:
    """Paper C's Theorem 1 is false for Collatz, by exhibit rather than by tree size.

    This replaces the reason the laboratory's working notes gave. Those notes
    said the Collatz analogue fails "because Collatz backward trees are thin
    (x^0.84, Krasikov--Lagarias)". That exponent is a *lower* bound on preimage
    counts and so cannot establish thinness of anything; conjecturally the tree
    is everything. The published manuscript never makes that error -- it says
    only that an `x^0.84` lower bound is compatible with a bounded reciprocal
    sum, which is correct and is a statement about what is proved rather than
    about the trees.

    The exhibit is stronger than either wording: the analogue is not merely
    unavailable, it is false.
    """
    members = barren_chain(terms)
    return {
        "set": "{3 * 2^k}",
        "backward_closed": barren_chain_is_backward_closed(terms),
        "infinite": True,
        "reciprocal_sum": float(sum(Fraction(1, n) for n in members)),
        "reciprocal_sum_exact": "2/3",
        "counting_function": "0 for x < 3; floor(log_2(x/3)) + 1 for x >= 3",
        "reason": (
            "multiples of three have no odd preimage, so the backward orbit is a"
            " bare doubling chain and loses exactly half its log-mass at every step"
        ),
        "kills": (
            "the Collatz analogue of Paper C Theorem 1, which asserts a divergent"
            " logarithmic count for EVERY nonempty backward-closed set"
        ),
    }


def _word_multiplier(word: str) -> Fraction:
    """`rho_w = 2^(-a) (3/2)^b` for a word in the letters `E` and `O`."""
    a = word.count("E")
    b = word.count("O")
    if a + b != len(word):
        raise ValueError(f"word must use only E and O: {word!r}")
    return Fraction(3, 2) ** b * Fraction(1, 2) ** a


def ideal_coefficient(word: str) -> Fraction:
    """Paper C's ideal production coefficient, `2^(-|w|) / rho_w`, simplified.

    The simplification is exact and immediate:

        2^(-(a+b)) * 2^a * (2/3)^b = 3^(-b)

    so the coefficient does not depend on the word at all beyond its number of
    odd letters.

    Against the published table the identity is exact on **every** term:
    `c_E = 1`, `c_OE = c_OEE = 1/3`, the conditional `c_OOEEE = 1/9` of
    Appendix C, and the whole ladder `c_k = 3^(-k)` for `V_k = (OE)^(k-1) OEE`,
    whose odd count is exactly `k`. Paper C's entire production inventory
    therefore sits at the Collatz-side ideal, with no parity shortfall in any
    coefficient.

    The `3^(-(k+1))` that appears in the `lambda**` equation is not the
    coefficient but the *increment* `c_k - (2/9) c_(k-1) = 3^(-(k+1))`, an
    inclusion-exclusion subtraction removing the `V_k`-starts already counted
    in family 3. So the ladder's factor of three below ideal is double
    counting, not a parity loss, and the shortfall from the ceiling is overlap
    and truncation rather than weak coefficients. An earlier version of this
    docstring read that factor as a parity share; the peer session caught it.

    `3^(-b)` is the probability that the Collatz backward step along `w` exists,
    the `b`-fold divisibility by three. Juggler is handed as a fibre-measure
    fact the quantity Collatz has to pay for arithmetically.
    """
    return Fraction(1, 2) ** len(word) / _word_multiplier(word)


def _all_words(depth: int) -> list[str]:
    return ["".join(w) for w in product("EO", repeat=depth)]


def contagion_mgf_shift(depth: int = 5,
                        lambdas: tuple[float, ...] = (0.5, 1.0, 2.0, 0.4926)
                        ) -> dict[str, Any]:
    """`F_J(lambda) = F_C(lambda - 1)`, where `F_C` is the Collatz walk's mgf.

    With `c_w = 3^(-b) = 2^(-|w|) / rho_w`, Paper C's ideal contagion sum is

        F_J(lambda) = sum_w c_w rho_w^lambda
                    = sum_w 2^(-|w|) rho_w^(lambda - 1) = F_C(lambda - 1),

    an identity, not an approximation. `F_C(0) = 1` is Kraft equality and
    `F_C(1) = 1` is the martingale identity `E[rho] = 1`, the two classical
    Collatz facts; they sit at `lambda = 1` and `lambda = 2`. So the ceiling of
    Paper C's method, `lambda = 1` (Proposition 5.12), is a Collatz identity
    read one exponential level up, and the entire shortfall from `1` to
    `lambda** = 0.4926` is the Juggler-side realized parity share, `eta_0 = 0`.
    """
    words = _all_words(depth)
    rows = {}
    for lam in lambdas:
        f_j = sum(float(ideal_coefficient(w)) * float(_word_multiplier(w)) ** lam
                  for w in words)
        f_c = sum(float(Fraction(1, 2) ** len(w))
                  * float(_word_multiplier(w)) ** (lam - 1.0) for w in words)
        rows[f"{lam:g}"] = {"F_J": f_j, "F_C_shifted": f_c, "gap": abs(f_j - f_c)}
    return {
        "depth": depth,
        "rows": rows,
        "worst_gap": max(r["gap"] for r in rows.values()),
        "coefficient_sum": sum(float(ideal_coefficient(w)) for w in words),
        "four_thirds_power": (4.0 / 3.0) ** depth,
        "kraft": sum(float(Fraction(1, 2) ** len(w) * _word_multiplier(w))
                     for w in words),
    }


def paper_c_payload() -> dict[str, Any]:
    """What the bridge does to Paper C, and what it does not do."""
    return {
        "engine_is_not_shared": (
            "Lemmas 2.1 and 2.2, Lemma 4.1 and Theorem 4.2 rest on how the map"
            " deforms scale, not on word statistics. The standing audit"
            " J-word-density-results-are-not-juggler-specific sorts results into"
            " word combinatorics (shared) and how orbits realise words (Juggler"
            " only); Paper C's engine is in neither class, being exact,"
            " elementary and free of equidistribution, and still Juggler only."
        ),
        "ceiling_is_shared": contagion_mgf_shift(),
        "log_mass": log_mass_census(20_000),
        "counterexample": collatz_theorem_one_counterexample(),
        "no_import": (
            "A counting bound x^kappa with kappa < 1 contributes total log-mass"
            " sum_j 2^(-(1-kappa) j) = O(1), so Krasikov--Lagarias cannot enter"
            " the contagion recursion as a term at any exponent below one. It is"
            " in the wrong metric, not merely too weak."
        ),
        "errata": (
            "Three working artifacts said Collatz backward trees are thin,"
            " citing the Krasikov--Lagarias exponent 0.84. That exponent is a"
            " LOWER bound on preimage counts and cannot establish thinness. The"
            " published manuscript juggler_fate_almost_all_note.md is correct in"
            " both places it makes the comparison and needs no revision."
        ),
    }


def probe_payload(max_depth: int = 10) -> dict[str, Any]:
    from research.juggler_sequence.jump_spectrum import survivor_counts

    counts = survivor_counts(max_depth)
    increments = loglog_increments(10**20 + 1)
    worst = max(abs(m - t) for _, m, t in increments) if increments else 1.0
    classes = {d: undecided_classes(d) for d in range(4, max_depth + 1)}
    return {
        "answer": "Juggler is Collatz one exponential level up",
        "shared_walk": {
            "steps": [STEP_ODD, STEP_EVEN],
            "collatz_variable": "log x",
            "juggler_variable": "log log n",
            "worst_increment_error": worst,
            "note": (
                "the same additive walk on different variables; the maps are not"
                " conjugate, the multiplier semigroup is one"
            ),
        },
        "shared_count": {
            "depths": sorted(classes),
            "undecided_collatz_classes": {str(d): v for d, v in classes.items()},
            "survivor_counts": {str(d): counts[d] for d in sorted(classes)},
            "agree": all(classes[d] == counts[d] for d in classes),
            "parity_map_bijective": {str(d): parity_map_is_bijective(d)
                                     for d in (4, 6, 8)},
        },
        "paper_c": paper_c_payload(),
        "where_they_part": (
            "For Collatz the parity word is a function of x mod 2^d and the map to"
            " {0,1}^d is a bijection, so every word has density exactly 2^(-d): Terras,"
            " arithmetic and free. For Juggler the word is a function of frac(n^(3/2))"
            " and its relatives, and equal densities are Hypothesis FD, which is open."
            " Same combinatorics, incompatible arithmetic."
        ),
        "calibration": {
            "collatz_exponent": density_exponent(1.0),
            "juggler_is_delta_times_collatz": True,
            "proved_delta": {"depth_four": 1.0 / 24, "depth_five": 1.0 / 128},
            "withdrawn_delta": 1.0 / 96,
            "at_proved_delta": {
                f"{name}:{c}": 1.0 - density_exponent(v, c)
                for name, v in (("depth_four", 1.0 / 24), ("depth_five", 1.0 / 128))
                for c in ("union", "sqrt")
            },
            "combination_is_worth": density_exponent(1.0, "direct")
            / density_exponent(1.0, "union"),
            "exponent_step_is_worth": 96.0 / 72.0,
            "note": (
                "Proposition J on Collatz is Terras 1976. For Juggler the same"
                " proposition gives a density exponent of delta times Collatz's, so FD"
                " with any power saving short of a bijection cannot reach it. The loss"
                " is the union bound over N_d words, not the exponent: combining the"
                " words better is worth about twenty times. BOTH HALVES OF THAT ARE"
                " WITHDRAWN: the twenty times is refuted outright"
                " (J-good-set-walsh-route-is-refuted), and the delta it was measured"
                " against, 1/96, is the 4 September target that Paper B withdrew --"
                " what the current paper proves is 1/24 at four steps and 1/128 at"
                " five, and the power-saving hypothesis is Conjecture K, not FD"
            ),
        },
        "decision": {
            "classification": CLASS_BRIDGE,
            "reason": (
                "the walk identification is exact to 2e-16 from a twenty-one digit seed,"
                " and the count identification is checked by running Collatz rather than"
                " by quoting OEIS"
            ),
        },
        "anti_overclaim": (
            "This is not an equivalence and not a conjugacy. It moves no bound in either"
            " problem, proves nothing new about Collatz beyond restating Terras, and"
            " proves nothing about Juggler at all. Its content is a partition: results"
            " that use only word densities belong to both problems, results that use how"
            " orbits realise words belong to Juggler and rest on Hypothesis FD. Juggler"
            " is not an easier Collatz -- it is Collatz's word problem plus a Weyl-sum"
            " problem, and both stall at the same wall."
        ),
    }


def render_markdown(data: dict[str, Any]) -> str:
    walk = data["shared_walk"]
    shared = data["shared_count"]
    paper_c = data["paper_c"]
    lines = [
        "# Juggler is Collatz one exponential level up",
        "",
        "Generated by `python -m research.juggler_sequence.collatz_bridge`.",
        "",
        "## The shared walk",
        "",
        f"- steps `log(3/2) = {walk['steps'][0]:.12f}` and"
        f" `-log 2 = {walk['steps'][1]:.12f}`",
        f"- Collatz carries them on `{walk['collatz_variable']}`, Juggler on"
        f" `{walk['juggler_variable']}`",
        f"- worst measured Juggler increment error from a 21-digit seed:"
        f" `{walk['worst_increment_error']:.2e}`",
        "",
        "## The shared count",
        "",
        f"- undecided Collatz residue classes against `N_d`, depths"
        f" {shared['depths'][0]} to {shared['depths'][-1]}: agree ="
        f" `{shared['agree']}`",
        f"- parity map bijective on `Z/2^d`: `{shared['parity_map_bijective']}`",
        "",
        "## Paper C under the bridge",
        "",
        f"- Paper C's ideal coefficient is `c_w = 2^(-|w|)/rho_w ="
        f" 3^(-b(w))`, the Collatz backward-step probability, so"
        f" `F_J(lambda) = F_C(lambda - 1)` exactly (worst gap"
        f" `{paper_c['ceiling_is_shared']['worst_gap']:.1e}`) and the"
        f" method ceiling `lambda = 1` is Kraft equality",
        f"- backward log-mass: Juggler asymptotic to `1/m`, bounded below by `m/(m+1)^2`;"
        f" shortcut Collatz `{paper_c['log_mass']['collatz_mean']:.4f}/m` in"
        f" the mean but `{paper_c['log_mass']['collatz_min']:.1f}/m` on every"
        f" multiple of three",
        f"- so the Collatz analogue of Theorem 1 is false:"
        f" `{paper_c['counterexample']['set']}` is backward-closed with"
        f" reciprocal sum `{paper_c['counterexample']['reciprocal_sum_exact']}`",
        "- " + paper_c["errata"],
        "",
        "## Where they part",
        "",
        data["where_they_part"],
        "",
        "## What this does not say",
        "",
        data["anti_overclaim"],
        "",
    ]
    return "\n".join(lines)


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    DOC_PATH.write_text(render_markdown(data), encoding="utf-8")
    return data


def main() -> None:
    payload = write_artifacts()
    print(payload["decision"]["classification"])
    print("walk error", f"{payload['shared_walk']['worst_increment_error']:.2e}",
          "| counts agree", payload["shared_count"]["agree"])


if __name__ == "__main__":
    main()

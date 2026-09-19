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
    """The accelerated map, `x/2` on evens and `(3x+1)/2` on odds."""
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
    """
    words_only = ("word", "certificate", "barrier", "survivor", "jump", "amplitude",
                  "recursion", "count", "spectrum", "ladder")
    juggler_only = ("equidistribution", "hypothesis fd", "weyl", "kernel",
                    "frac(n^", "floor power", "orbit of n")
    lowered = statement.lower()
    return (any(w in lowered for w in words_only)
            and not any(j in lowered for j in juggler_only))


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

"""Hercher's Lemma 8 survives the exponential, on the exponent, and dies of density.

`J-juggler-is-collatz-one-exponential-up` says the exponential conjugacy keeps the
combinatorics and *removes the 2-adic rigidity*: for Collatz the length-`d` parity word is a
function of `x mod 2^d` and the map onto `{0,1}^d` is a bijection (Terras), while for Juggler
the word is a function of `frac(n^(3/2))` and equal densities are Hypothesis FD. This probe
locates the part of the rigidity that is **not** removed, and prices it.

**THE FIXED POINT OF THE DICTIONARY.** Collatz's odd step is `x -> (3x+1)/2`; in the
coordinate `u = x + 1` it is exactly `u -> 3u/2`. Juggler's exact odd step on `n = a^e` is
`a^e -> a^(3e/2)`; on the exponent it is exactly `e -> 3e/2`. Same map, same prime, same
reason: `3` is a 2-adic unit, so one step costs exactly one unit of `v_2` and nothing else.
Collatz carries the 2-adic integer in the *value*, Juggler in the *exponent*. The exact even
step is `e -> e/2` and costs the same unit, so during an exact run the valuation drops by one
per step whatever the letter.

Hence the run laws are the same statement at the two ends of `x = 2^y`:

    Collatz   run(x)      = v_2(x + 1)                    (Hercher 2023, Lemma 8)
    Juggler   exactRun(n) = v_2(e(n)),  e(n) = max{e : n = a^e}

where `run` counts consecutive odd states and `exactRun` counts consecutive square states --
the states at which the floor is not charged. The laboratory already owns the Juggler half in
Lean as `HasPowTwoDepth` (`hasPowTwoDepth_even_exact`, `hasPowTwoDepth_odd_exact`,
`power_bound_eq_implies_pow_two_depth`, `j-saturation-budget`); what was missing is that it is
Lemma 8, and what that costs.

**THE PRICE IS THE EXPONENTIAL, AND IT IS EXACTLY ONE LOG.** Both laws convert to a pointwise
lower bound by the same product-formula step -- a nonzero integer with `v_2 >= k` has absolute
value at least `2^k` -- and both bounds are attained:

    Collatz   run(x) >= k   =>  x >= 2^k - 1,      attained at x = 2^k - 1
    Juggler   exactRun(n) >= k  =>  n >= 2^(2^k),  attained at n = 2^(2^k)
                                    n odd: n >= 3^(2^k), attained at n = 3^(2^k)

so the Juggler floor is the exponential of the Collatz floor, `log(3^(2^k)) = 2^k log 3`, and
the dictionary that was verified on the walk holds pointwise as well. The same exponential
turns the counting function inside out:

    #{x <= N : run(x) >= k}        = floor((N + 1) / 2^k) ~ 2^(-k) N
    #{2 <= n <= N : exactRun >= k} = floor(N^(2^-k)) - 1     ~ N^(2^-k)

Collatz pays `2^(-k)` in the density; Juggler pays `2^(-k)` in the *exponent* of the density.
The locus where the 2-adics still act is therefore density zero for every `k >= 1`, and empty
of information besides: on it the word is monochrome (`O^k` from an odd base, `E^k` from an
even one), so the fibre carries `1` bit where Terras's bijection carries `k`. That is the
sharp form of "the exponential removes the 2-adic rigidity" -- it does not remove it, it
turns a bijection onto `2^k` words into a constant map onto `2`.

**THE FIBRE, WITHOUT ANY EXPONENTIAL TALK.** On a prime power the exponent *is* a valuation:
`n = p^e` has `v_p(n) = e`, and the Juggler sends `v_p` to `3 v_p / 2` on an odd prime and to
`v_p / 2` on `p = 2`. Collatz's even step sends `v_2(x)` to `v_2(x) - 1` and its odd step sends
the value `u = x + 1` to `3u/2`. So the Juggler does to valuations what Collatz does to values,
which is the whole dictionary in one line and needs no limit to state.

**WHERE THE HAND-OVER HAPPENS, EXPLICITLY.** The valuation runs out at the first odd exponent,
and the first inexact image is `floor(m^N sqrt m)`. On the fibre of the powers of two,
`n = 2^e` with `e` odd, that is `floor(2^((e-1)/2) sqrt 2)`, whose parity is the
`((e-1)/2)`-th binary digit of `sqrt 2`. The 2-adic fibre hands the itinerary to an
Archimedean digit of a quadratic irrational, at a named place, with no room for a congruence.

**WHAT THIS DOES NOT SAY.** The mirror is inert for cycles and for termination, and that is
the mechanism behind the 19 September negative-knowledge entry rather than a repair of it.
Hercher's hypothesis is `k consecutive odd letters` -- a condition on the *word*, which every
cycle with a long run supplies for free. The mirror's hypothesis is `k consecutive exact
steps` -- a condition on the *integer*, which no word implies. The exponential moves the
hypothesis from the word to the arithmetic, so the Juggler twin cannot be fed by a cycle word,
and the door named there (the pointwise odd-run bound `run(n) <= C log n` for *inexact* odd
runs) is untouched: it is Archimedean, and the reason is structural, not a gap in the
laboratory's machinery. There is no 2-adic avatar of `x = 2^y` to carry it:
`|2^y - 2^z|_2 = 2^(-min(y,z))` depends on the Archimedean size of the exponents and not on
`y - z` in the 2-adic metric, so the conjugacy is not uniformly continuous and does not extend
to `Z_2`. Off the perfect powers there is no exponent whose valuation could be taken.

No floor is raised, no cycle is excluded, no Collatz bound is improved, and Lemma 8 is quoted,
not reproved.
"""

from __future__ import annotations

import json
from math import isqrt
from typing import Any

from research.juggler_sequence.lean_paths import DATA_ROOT, DOCS_RESEARCH

DATA_DIR = DATA_ROOT / "exponent_valuation_mirror"
JSON_PATH = DATA_DIR / "summary.json"
DOC_PATH = DOCS_RESEARCH / "juggler_exponent_valuation_mirror.md"

CLASS_MIRROR = "LEMMA_EIGHT_MIRROR_IS_THE_EXPONENT_VALUATION"

#: exhaustive range for the run law and the counting law
SCAN_N = 10**6
#: depths tested in the counting and minimal-realizer tables
DEPTHS = (0, 1, 2, 3, 4, 5)
#: word lengths at which the Terras fibre is compared with the perfect-power fibre
WORD_LENGTHS = (1, 2, 3, 4, 5, 6, 7, 8)
#: odd exponents tested against the binary digits of sqrt 2
EXIT_EXPONENTS = tuple(range(1, 402, 2))

PRIMES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61)


def floor_power(n: int) -> int:
    """The Juggler step: `isqrt(n)` on even `n`, `isqrt(n^3)` on odd `n`."""
    if n < 1:
        raise ValueError("floor_power is defined on positive integers")
    if n % 2 == 0:
        return isqrt(n)
    return isqrt(n * n * n)


def inthroot(n: int, k: int) -> tuple[int, bool]:
    """Integer `k`-th root of `n >= 0` by Newton, with an exactness flag."""
    if k == 1 or n in (0, 1):
        return n, True
    r = 1 << (-(-n.bit_length() // k))
    while True:
        nxt = ((k - 1) * r + n // r ** (k - 1)) // k
        if nxt >= r:
            break
        r = nxt
    return r, r**k == n


def power_exponent(n: int) -> int:
    """`max{e : n = a^e}` for `n >= 2`; the gcd of the exponents of `n`."""
    if n < 2:
        raise ValueError("power_exponent is defined on n >= 2")
    exponent = 1
    for p in PRIMES:
        if p > n.bit_length():
            break
        while True:
            root, exact = inthroot(n, p)
            if not exact or root < 2:
                break
            n = root
            exponent *= p
    return exponent


def v2(m: int) -> int:
    """2-adic valuation of a positive integer."""
    return (m & -m).bit_length() - 1


def is_square(n: int) -> bool:
    root = isqrt(n)
    return root * root == n


def exact_run(n: int, cap: int = 4096) -> int:
    """Consecutive states at which the Juggler floor is not charged (square states)."""
    steps = 0
    while steps < cap and n > 1 and is_square(n):
        n = floor_power(n)
        steps += 1
    return steps


def exact_word(n: int) -> str:
    """The letters read along the exact run at `n`."""
    letters = []
    for _ in range(exact_run(n)):
        letters.append("E" if n % 2 == 0 else "O")
        n = floor_power(n)
    return "".join(letters)


def collatz_run(x: int) -> int:
    """Consecutive odd states of the accelerated map `x -> (3x+1)/2`."""
    steps = 0
    while x % 2 == 1:
        steps += 1
        x = (3 * x + 1) // 2
    return steps


def run_law(limit: int = SCAN_N) -> dict[str, Any]:
    """`exactRun(n) = v_2(e(n))` on `[2, limit]`, and `run(x) = v_2(x+1)` on the odds."""
    juggler_fails: list[list[int]] = []
    squares = 0
    for n in range(2, limit + 1):
        if not is_square(n):
            continue  # exactRun = 0 and 2 does not divide e(n); both sides vanish
        squares += 1
        measured = exact_run(n)
        predicted = v2(power_exponent(n))
        if measured != predicted:
            juggler_fails.append([n, measured, predicted])
    nonsquare_checked = 0
    for n in range(2, min(limit, 20000) + 1):
        if is_square(n):
            continue
        nonsquare_checked += 1
        if exact_run(n) != 0 or v2(power_exponent(n)) != 0:
            juggler_fails.append([n, exact_run(n), v2(power_exponent(n))])
    collatz_fails = [
        [x, collatz_run(x), v2(x + 1)]
        for x in range(1, min(limit, 200001), 2)
        if collatz_run(x) != v2(x + 1)
    ]
    return {
        "limit": limit,
        "square_states_checked": squares,
        "nonsquare_states_checked": nonsquare_checked,
        "juggler_law": "exactRun(n) = v_2(e(n))",
        "juggler_failures": juggler_fails[:8],
        "juggler_holds": not juggler_fails,
        "collatz_law": "run(x) = v_2(x+1)  [Hercher 2023, Lemma 8]",
        "collatz_odds_checked": len(range(1, min(limit, 200001), 2)),
        "collatz_failures": collatz_fails[:8],
        "collatz_holds": not collatz_fails,
    }


def monochrome(limit: int = SCAN_N) -> dict[str, Any]:
    """An exact run is monochrome; the letter is the parity of the base."""
    words: dict[int, set[str]] = {}
    mixed: list[int] = []
    for n in range(2, limit + 1):
        if not is_square(n):
            continue
        word = exact_word(n)
        if len(set(word)) > 1:
            mixed.append(n)
        words.setdefault(len(word), set()).add(word)
    return {
        "limit": limit,
        "mixed_exact_words": mixed[:8],
        "all_monochrome": not mixed,
        "words_by_length": {str(k): sorted(v) for k, v in sorted(words.items()) if k},
    }


def fibre_entropy(lengths: tuple[int, ...] = WORD_LENGTHS) -> dict[str, Any]:
    """Terras's bijection against the perfect-power fibre, word counts side by side."""
    rows = []
    for d in lengths:
        seen = set()
        for r in range(2**d):
            x, letters = r, []
            for _ in range(d):
                if x % 2 == 0:
                    letters.append("E")
                    x //= 2
                else:
                    letters.append("O")
                    x = (3 * x + 1) // 2
            seen.add("".join(letters))
        rows.append(
            {
                "length": d,
                "collatz_words_on_one_residue_system": len(seen),
                "collatz_is_bijective": len(seen) == 2**d,
                "juggler_words_on_the_depth_d_locus": 2,
                "juggler_words": [f"O^{d}", f"E^{d}"],
            }
        )
    return {
        "note": "Collatz: x mod 2^d -> word is a bijection onto {O,E}^d (Terras 1976). "
        "Juggler: depth-d perfect powers carry the two monochrome words only.",
        "rows": rows,
    }


def counting(limit: int = SCAN_N, depths: tuple[int, ...] = DEPTHS) -> dict[str, Any]:
    """Density `2^(-k)` for Collatz against log-density `2^(-k)` for Juggler."""
    juggler = {k: 0 for k in depths}
    collatz = {k: 0 for k in depths}
    for n in range(2, limit + 1):
        run = exact_run(n) if is_square(n) else 0
        for k in depths:
            if run >= k:
                juggler[k] += 1
    for x in range(1, limit + 1):
        run = v2(x + 1) if x % 2 == 1 else 0
        for k in depths:
            if run >= k:
                collatz[k] += 1
    rows = []
    for k in depths:
        predicted = inthroot(limit, 2**k)[0] - 1
        collatz_predicted = limit if k == 0 else (limit + 1) // 2**k
        rows.append(
            {
                "k": k,
                "juggler_measured": juggler[k],
                "juggler_predicted_floor_Nth_root": predicted,
                "juggler_agrees": juggler[k] == predicted,
                "collatz_measured": collatz[k],
                "collatz_predicted": collatz_predicted,
                "collatz_agrees": collatz[k] == collatz_predicted,
            }
        )
    return {
        "limit": limit,
        "juggler_law": "#{2<=n<=N : exactRun(n)>=k} = floor(N^(2^-k)) - 1",
        "collatz_law": "#{x<=N : run(x)>=k} = floor((N+1)/2^k) for k >= 1",
        "rows": rows,
        "all_agree": all(r["juggler_agrees"] and r["collatz_agrees"] for r in rows),
    }


def minimal_realizers(depths: tuple[int, ...] = DEPTHS) -> dict[str, Any]:
    """Lemma 8's floor and its exponential, both attained."""
    rows = []
    for k in depths:
        collatz_min = 2**k - 1
        juggler_min = 2 ** (2**k)
        juggler_odd_min = 3 ** (2**k)
        rows.append(
            {
                "k": k,
                "collatz_min": collatz_min,
                "collatz_min_attains": collatz_run(collatz_min) >= k if collatz_min >= 1 else True,
                "juggler_min_log2": 2**k,
                "juggler_min_attains": exact_run(juggler_min) == k,
                "juggler_odd_min_log3": 2**k,
                "juggler_odd_min_attains": exact_run(juggler_odd_min) == k,
                "juggler_odd_word": exact_word(juggler_odd_min),
            }
        )
    return {
        "collatz": "run(x) >= k  =>  x >= 2^k - 1  (attained)",
        "juggler": "exactRun(n) >= k  =>  n >= 2^(2^k); odd n >= 3^(2^k)  (both attained)",
        "identity": "log(3^(2^k)) = (2^k) log 3, so the Juggler floor is the exponential "
        "of the Collatz floor -- the walk dictionary, pointwise",
        "rows": rows,
        "all_attained": all(
            r["juggler_min_attains"] and r["juggler_odd_min_attains"] and r["collatz_min_attains"]
            for r in rows
        ),
    }


def valuation_fibre(primes: tuple[int, ...] = (2, 3, 5, 7, 11), max_exp: int = 40) -> dict[str, Any]:
    """On a prime power the exponent is a valuation, and the Juggler acts on it directly."""
    fails = []
    for p in primes:
        for e in range(2, max_exp + 1, 2):
            image = floor_power(p**e)
            expected = p ** (e // 2) if p == 2 else p ** (3 * e // 2)
            if image != expected:
                fails.append([p, e])
    collatz_fails = [x for x in range(2, 20000, 2) if v2(x // 2) != v2(x) - 1]
    return {
        "juggler": "n = p^e has v_p(n) = e; the Juggler sends v_p to 3 v_p / 2 on an odd prime "
        "and to v_p / 2 at p = 2",
        "collatz": "the even step sends v_2(x) to v_2(x) - 1; the odd step sends u = x + 1 to 3u/2",
        "reading": "the Juggler does to valuations what Collatz does to values",
        "primes": list(primes),
        "max_exponent": max_exp,
        "juggler_failures": fails,
        "collatz_failures": collatz_fails[:8],
        "holds": not fails and not collatz_fails,
    }


def sqrt_two_bit(k: int) -> int:
    """`k`-th binary digit of `sqrt 2`, i.e. `floor(2^k sqrt 2) mod 2`."""
    return isqrt(2 ** (2 * k + 1)) % 2


def exit_digit(exponents: tuple[int, ...] = EXIT_EXPONENTS) -> dict[str, Any]:
    """The first inexact image on the fibre of the powers of two is a digit of `sqrt 2`."""
    fails = []
    for e in exponents:
        image = floor_power(2**e)
        if image % 2 != sqrt_two_bit((e - 1) // 2):
            fails.append(e)
    bits = "".join(str(sqrt_two_bit(k)) for k in range(32))
    return {
        "identity": "e odd: floorPower(2^e) = floor(2^((e-1)/2) sqrt 2), parity = bit_{(e-1)/2}(sqrt 2)",
        "odd_exponents_checked": len(exponents),
        "max_exponent": exponents[-1],
        "failures": fails,
        "holds": not fails,
        "first_32_bits_of_sqrt_two": bits,
        "general_base": "n = m^e with e odd: the first inexact image is floor(m^((3e-1)/2) sqrt m) "
        "on an odd base and floor(m^((e-1)/2) sqrt m) on an even one",
    }


def probe_payload() -> dict[str, Any]:
    law = run_law()
    mono = monochrome()
    fibre = fibre_entropy()
    count = counting()
    minima = minimal_realizers()
    exits = exit_digit()
    valuations = valuation_fibre()
    green = (
        law["juggler_holds"]
        and law["collatz_holds"]
        and mono["all_monochrome"]
        and count["all_agree"]
        and minima["all_attained"]
        and exits["holds"]
        and valuations["holds"]
    )
    return {
        "dictionary": {
            "collatz_state": "u = x + 1 in Z_2",
            "juggler_state": "e = e(n), the exponent of the perfect power, in Z",
            "shared_map": "u -> 3u/2 (Collatz odd step); e -> 3e/2 (Juggler exact odd step)",
            "shared_reason": "3 is a 2-adic unit, so one step costs exactly one unit of v_2",
            "juggler_even_step": "e -> e/2, the same unit",
            "collatz_lemma": "Hercher 2023 Lemma 8: k consecutive odd steps force x = -1 mod 2^k",
            "juggler_lemma": "HasPowTwoDepth: k consecutive exact steps force n = a^(2^k)",
            "lean": [
                "hasPowTwoDepth_even_exact",
                "hasPowTwoDepth_odd_exact",
                "power_bound_eq_implies_pow_two_depth",
            ],
        },
        "run_law": law,
        "monochrome": mono,
        "fibre_entropy": fibre,
        "counting": count,
        "minimal_realizers": minima,
        "exit_digit": exits,
        "valuation_fibre": valuations,
        "decision": {
            "classification": CLASS_MIRROR if green else "LEMMA_EIGHT_MIRROR_FAILED",
            "branch": "CLOSE",
            "green": green,
        },
        "anti_overclaim": (
            "No floor is raised, no cycle of any length is excluded in either problem, and no "
            "Collatz bound is improved; Lemma 8 is quoted from hercher-2023-collatz-m-cycles, "
            "not reproved. The mirror's hypothesis is k consecutive EXACT steps, a condition on "
            "the integer, where Hercher's is k consecutive odd LETTERS, a condition on the word; "
            "no word implies the former, so the mirror is inert for cycles and does not weaken "
            "the 19 September negative-knowledge entry. The pointwise odd-run bound for inexact "
            "runs -- the odd-tower fragment -- stays open and stays Archimedean."
        ),
    }


def render_markdown(data: dict[str, Any]) -> str:
    law = data["run_law"]
    lines = [
        "# Hercher's Lemma 8 on the exponent",
        "",
        f"Status: **{data['decision']['classification']}**",
        "",
        "Generated by `python -m research.juggler_sequence.exponent_valuation_mirror`.",
        "",
        "## The dictionary",
        "",
        "| | Collatz | Juggler |",
        "| --- | --- | --- |",
        "| carrier of the 2-adic integer | the value `u = x + 1` | the exponent `e(n)` |",
        "| the map | `u -> 3u/2` | `e -> 3e/2` (odd), `e -> e/2` (even) |",
        "| why one unit per step | `3` is a 2-adic unit | the same |",
        "| run law | `run(x) = v_2(x+1)` | `exactRun(n) = v_2(e(n))` |",
        "| pointwise floor | `x >= 2^k - 1` | `n >= 2^(2^k)`, odd `n >= 3^(2^k)` |",
        "| count at depth `k` | `~ 2^(-k) N` | `~ N^(2^-k)` |",
        "| word on the fibre | bijection onto `2^k` words (Terras) | the `2` monochrome words |",
        "",
        "## Run law",
        "",
        f"- `exactRun(n) = v_2(e(n))` on `2 <= n <= {law['limit']}`: "
        f"`{law['juggler_holds']}` ({law['square_states_checked']} square states, "
        f"{law['nonsquare_states_checked']} non-square states)",
        f"- `run(x) = v_2(x+1)` on {law['collatz_odds_checked']} odd starts: "
        f"`{law['collatz_holds']}`",
        f"- exact runs monochrome: `{data['monochrome']['all_monochrome']}`",
        "",
        "## Counting",
        "",
        "| k | Juggler measured | `floor(N^(2^-k)) - 1` | Collatz measured | `floor((N+1)/2^k)` |",
        "| --- | --- | --- | --- | --- |",
    ]
    for row in data["counting"]["rows"]:
        lines.append(
            f"| {row['k']} | {row['juggler_measured']} | {row['juggler_predicted_floor_Nth_root']} "
            f"| {row['collatz_measured']} | {row['collatz_predicted']} |"
        )
    lines += [
        "",
        f"`N = {data['counting']['limit']}`, every row exact: `{data['counting']['all_agree']}`.",
        "",
        "## Minimal realizers",
        "",
        "| k | Collatz `2^k - 1` | Juggler `log2` of the minimum | odd Juggler `log3` | word |",
        "| --- | --- | --- | --- | --- |",
    ]
    for row in data["minimal_realizers"]["rows"]:
        lines.append(
            f"| {row['k']} | {row['collatz_min']} | {row['juggler_min_log2']} "
            f"| {row['juggler_odd_min_log3']} | `{row['juggler_odd_word'] or '(empty)'}` |"
        )
    lines += [
        "",
        f"All attained: `{data['minimal_realizers']['all_attained']}`. "
        + data["minimal_realizers"]["identity"],
        "",
        "## The fibre",
        "",
        f"- {data['valuation_fibre']['juggler']}",
        f"- {data['valuation_fibre']['collatz']}",
        f"- {data['valuation_fibre']['reading']}; checked on primes "
        f"`{data['valuation_fibre']['primes']}` to exponent "
        f"`{data['valuation_fibre']['max_exponent']}`: `{data['valuation_fibre']['holds']}`",
        "",
        "## The hand-over",
        "",
        f"- {data['exit_digit']['identity']}",
        f"- checked on {data['exit_digit']['odd_exponents_checked']} odd exponents up to "
        f"`{data['exit_digit']['max_exponent']}`: `{data['exit_digit']['holds']}`",
        f"- first 32 bits of `sqrt 2`: `{data['exit_digit']['first_32_bits_of_sqrt_two']}`",
        f"- {data['exit_digit']['general_base']}",
        "",
        "## Fibre entropy",
        "",
        "| length | Collatz words per residue system | bijective | Juggler words on the locus |",
        "| --- | --- | --- | --- |",
    ]
    for row in data["fibre_entropy"]["rows"]:
        lines.append(
            f"| {row['length']} | {row['collatz_words_on_one_residue_system']} "
            f"| {row['collatz_is_bijective']} | {row['juggler_words_on_the_depth_d_locus']} |"
        )
    lines += [
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
    print("run law", data["run_law"]["juggler_holds"], data["run_law"]["collatz_holds"])
    print("monochrome", data["monochrome"]["all_monochrome"])
    print("counting", data["counting"]["all_agree"])
    print("minima", data["minimal_realizers"]["all_attained"])
    print("exit digit", data["exit_digit"]["holds"])


if __name__ == "__main__":
    main()

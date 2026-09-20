"""Lemma 8 has a dual on the even runs, and the CycleMin shape is exactly what kills it.

`J-lemma-eight-floor-is-tight-at-every-known-cycle` settled what the 2-adic **valuation**
of the odd-run structure is worth on the mirror side. This probe asks the complementary
question that the valuation reading leaves open: `2` acts on the odd part of `Z` in two
ways, by its valuation and by its multiplicative **order**, and Hercher's Lemma 8 uses only
the first. What does the second give?

**THE DUAL FLOOR.** Let `C` be a cycle of the shortcut map `T(x) = x/2` / `(3x+1)/2` on `Z`
carrying at least one even step, with odd elements `x_1, ..., x_o` in cyclic order and `r_i`
halvings between the odd step at `x_i` and `x_{i+1}`, so `2^(r_i + 1) x_{i+1} = 3 x_i + 1`.
Let `R = gcd` of the nonzero `r_i`, and let `m` be any divisor of `2^R - 1` with
`gcd(m, 2^o - 3^o) = 1`. Then

    x = -1  (mod m)   for every odd element x of C,   hence |x| >= m - 1.

The proof is Hercher's own conjugation read the other way. In `u = x + 1` the passage is
`2^(r_i + 1) u_{i+1} = 3 u_i - 2 + 2^(r_i + 1)`; if `ord_m(2) | R | r_i` then
`2^(r_i + 1) = 2 (mod m)` and the correction `2^(r_i + 1) - 2` vanishes, leaving

    2 u_{i+1} = 3 u_i  (mod m).

Composing once around gives `u (2^o - 3^o) = 0 (mod m)`, and the coprimality forces `m | u`.
Lemma 8 reads `v_2` off the odd runs and yields `|x| >= 2^a - 1`; this reads `ord(2)` off the
even runs and yields `|x| >= 2^R - 1`. Same congruence `x = -1`, two different moduli.

**WHAT THE MECHANISM IS.** Modulo `2^R - 1` the even steps become invisible and the orbit is
the *free* recursion `u -> 3u/2`. That recursion is not a new object in this laboratory: it is
the Juggler's exponent transport (`J-lemma-eight-is-the-exponent-valuation`), where on the
perfect-power locus `n = a^e` the exact step acts as `e -> 3e/2` on an odd base and `e -> e/2`
on an even one, with no floor loss at all. So the Mersenne modulus is precisely the reduction
under which Collatz *becomes* the Juggler's exponent dynamics -- and the Juggler's no-cycle
argument there is a pure exponent count, `3^o != 2^o`, needing neither Catalan nor Baker.
The price of the transport is exactly this: pulled back through the congruence, the equation
`3^o != 2^o` degrades from a contradiction into `m | u`. An impossibility becomes a floor.

**AND THE CycleMin SHAPE IS WHAT KILLS IT.** On a word all of whose proper prefixes are
non-contracting -- Paper A's CycleMin shape, which by `neg_cycle_word_is_juggler_shape` is
the shape of a negative Collatz cycle word at its minimum and of a Juggler cycle word, and
by `prefix_bound_of_min` of a positive one too -- the leading run of `a` odd letters is
followed by an E-run of length `r_1 >= 1`, and non-contraction at the end of that run is
`3^a >= 2^(a + r_1)`. Since `R | r_1`,

    R <= r_1 <= floor((log2 3 - 1) a) = floor(0.58496 a),

so the dual floor `2^R` sits below Lemma 8's `2^a` by the factor
`2^((2 - log2 3) a) = 2^(0.41504 a)` and can never be the binding one. The single exception
to the cap is the word whose first E-run is also its last, `O^a E^r` -- the circuit, whose
nontrivial case Steiner 1977 already excludes, and where the dual floor still does not win.

The two floors are anti-correlated by the very condition that defines the family: prefix
non-contraction forces the word to bunch its odd letters, which lengthens odd runs and
shortens even runs. The dual is not an opportunity this laboratory missed. It is structurally
excluded from the side the Juggler lives on.

**MEASURED.** Zero new kills. Against the `neg_cycle_finance` ceiling the dual floor kills
some shape words and Lemma 8 had killed every one of them already, at every length tested.
The cap is attained, so it is sharp rather than an artifact of the census.

**NOVELTY IS NOT CLAIMED.** Hercher's Lemma 8 is stated in terms of both run types and the
even-run structure is the whole subject of Eliahou 1993 and of Simons-de Weger's `m`-cycle
financing; the primary sources were unreachable from the container that ran this probe
(arxiv.org, cs.uwaterloo.ca and oeis.org are refused by the network egress policy), so
whether the dual congruence is in print is recorded here as unknown rather than guessed.
What is claimed is the subordination: the dual exists, it is correct, and the CycleMin shape
caps it below Lemma 8 by a proved exponential factor.
"""

from __future__ import annotations

import json
import math
import re
from fractions import Fraction
from math import gcd
from typing import Any

from research.juggler_sequence.lean_paths import DATA_ROOT, DOCS_RESEARCH
from research.juggler_sequence.negative_lemma_eight_window import (
    cycle_from,
    even_charge,
    leading_odd_run,
    shortcut,
    window,
    word_of,
)

DATA_DIR = DATA_ROOT / "even_run_mersenne_floor"
JSON_PATH = DATA_DIR / "summary.json"
DOC_PATH = DOCS_RESEARCH / "juggler_even_run_mersenne_floor.md"

CLASS_DUAL = "THE_EVEN_RUN_DUAL_IS_CAPPED_BELOW_LEMMA_EIGHT_BY_THE_SHAPE"

#: word lengths enumerated for the census
MAX_LEN = 22
#: log2 3 - 1, the cap's constant; 2 - log2 3 is the separation exponent
CAP_SLOPE = math.log2(3) - 1
SEPARATION_EXPONENT = 2 - math.log2(3)


def even_charge_blocks(word: str) -> list[int]:
    """`r_j`, `j = 0..o`: `r_0` the trailing E-run, `r_o` the leading one."""
    odds = word.count("O")
    parts = word.split("O")
    return [len(parts[odds - j]) for j in range(odds + 1)]


def charge_block_expansion(word: str) -> int:
    """`evenCharge w = sum_j 3^j 2^(A_j) (2^(r_j) - 1)`, `A_j = (o - j) + sum_(l>j) r_l`.

    Every term carries a Mersenne factor; that is the whole source of the dual floor.
    """
    odds = word.count("O")
    blocks = even_charge_blocks(word)
    total = 0
    for j in range(odds + 1):
        exponent = (odds - j) + sum(blocks[l] for l in range(j + 1, odds + 1))
        total += 3**j * 2**exponent * (2 ** blocks[j] - 1)
    return total


def cyclic_blocks(word: str) -> list[int] | None:
    """Halvings between consecutive odd steps, read cyclically. `None` with no odd letter."""
    odds = word.count("O")
    if odds == 0:
        return None
    length = len(word)
    idx = [i for i, letter in enumerate(word) if letter == "O"]
    return [
        (idx[(j + 1) % odds] + (length if j == odds - 1 else 0)) - i - 1
        for j, i in enumerate(idx)
    ]


def even_run_gcd(word: str) -> int:
    """`R`, the gcd of the nonzero cyclic even-run lengths; `0` when every run is empty."""
    blocks = cyclic_blocks(word)
    if not blocks:
        return 0
    nonzero = [b for b in blocks if b > 0]
    if not nonzero:
        return 0
    value = 0
    for b in nonzero:
        value = gcd(value, b)
    return value


def largest_coprime_divisor(value: int, other: int) -> int:
    """The largest divisor of `value` coprime to `other`."""
    if value < 1:
        raise ValueError(f"value must be >= 1, got {value}")
    remaining = value
    while True:
        common = gcd(remaining, other)
        if common == 1:
            return remaining
        remaining //= common


def dual_modulus(word: str, odds: int) -> int:
    """`M(R, o)`: the largest divisor of `2^R - 1` coprime to `2^o - 3^o`. `0` if vacuous."""
    run_gcd = even_run_gcd(word)
    if run_gcd < 2:
        return 0
    return largest_coprime_divisor(2**run_gcd - 1, abs(2**odds - 3**odds))


def mersenne_divides_charge(max_len: int = 16) -> dict[str, Any]:
    """`(2^R - 1) | evenCharge w` whenever `R` divides every nonzero E-run: the identity (+)."""
    tested = 0
    violations: list[str] = []
    expansion_checked = 0
    expansion_violations: list[str] = []
    for length in range(1, max_len + 1):
        for code in range(2**length):
            word = "".join("O" if (code >> i) & 1 else "E" for i in range(length))
            expansion_checked += 1
            if even_charge(word) != charge_block_expansion(word):
                expansion_violations.append(word)
            blocks = [b for b in even_charge_blocks(word) if b > 0]
            if not blocks:
                continue
            run_gcd = 0
            for b in blocks:
                run_gcd = gcd(run_gcd, b)
            if run_gcd < 2:
                continue
            tested += 1
            if even_charge(word) % (2**run_gcd - 1) != 0:
                violations.append(word)
    return {
        "max_len": max_len,
        "block_expansion_words_checked": expansion_checked,
        "block_expansion_violations": expansion_violations,
        "mersenne_words_tested": tested,
        "mersenne_violations": violations,
        "identity": "evenCharge w = sum_j 3^j 2^(A_j) (2^(r_j) - 1)",
    }


def rational_cycle_check(max_len: int = 16) -> dict[str, Any]:
    """`(++)` at every odd element of the rational cycle of every word (Lagarias 1990).

    The statement is about ODD elements; read at a word beginning with `E` the value
    `evenCharge/(2^d - 3^o)` is `x + 1` at an EVEN element and the congruence does not apply.
    """
    tested = 0
    violations: list[Any] = []
    for length in range(1, max_len + 1):
        for code in range(2**length):
            word = "".join("O" if (code >> i) & 1 else "E" for i in range(length))
            if not word.startswith("O"):
                continue
            odds = word.count("O")
            gap = 2**length - 3**odds
            if odds == 0 or gap == 0:
                continue
            modulus = dual_modulus(word, odds)
            if modulus < 2:
                continue
            tested += 1
            for i in [j for j, c in enumerate(word) if c == "O"]:
                rotated = word[i:] + word[:i]
                value = Fraction(even_charge(rotated), gap)
                num, den = value.numerator, value.denominator
                if gcd(den, modulus) != 1:
                    violations.append((word, rotated, "denominator not coprime"))
                    continue
                if (num * pow(den, -1, modulus)) % modulus != 0:
                    violations.append((word, rotated, str(value)))
    return {
        "max_len": max_len,
        "words_tested": tested,
        "violations": violations,
        "note": "read at odd elements only; at an even element u = x + 1 is not pinned",
    }


def known_cycles() -> dict[str, Any]:
    """The dual floor is vacuous at every known cycle of the `Z` map, and must be."""
    rows = []
    for start in (1, -1, -5, -17):
        cycle = cycle_from(start)
        assert cycle is not None
        word = word_of(cycle)
        odds = word.count("O")
        run_gcd = even_run_gcd(word)
        modulus = dual_modulus(word, odds)
        least = max(cycle) if start < 0 else min(cycle)
        rows.append(
            {
                "x": start,
                "word": word,
                "odds": odds,
                "cyclic_blocks": cyclic_blocks(word),
                "even_run_gcd": run_gcd,
                "dual_modulus": modulus,
                "dual_floor_is_vacuous": modulus < 2,
                "least_abs": abs(least),
            }
        )
    return {
        "rows": rows,
        "all_vacuous": all(r["dual_floor_is_vacuous"] for r in rows),
        "reading": "every known cycle has an E-run of length 1, so R = 1 and the dual says "
        "nothing -- unlike Lemma 8, which every one of them attains with equality",
    }


def cycle_min_words(max_len: int = MAX_LEN) -> tuple[list[tuple[str, int, int]], list[tuple[str, int, int]]]:
    """Cycle-minimum-shaped words on both signs: every PROPER prefix non-contracting.

    Expanding overall is the negative family (`neg_prefix_noncontracting`); contracting at
    the last letter only is the positive one (`prefix_bound_of_min`).
    """
    expanding: list[tuple[str, int, int]] = []
    contracting: list[tuple[str, int, int]] = []

    def walk(word: str, odds: int, length: int) -> None:
        if length and 2**length < 3**odds:
            expanding.append((word, odds, length))
        if length == max_len:
            return
        for letter in "OE":
            odds2 = odds + (letter == "O")
            length2 = length + 1
            if 2**length2 <= 3**odds2:
                walk(word + letter, odds2, length2)
            elif letter == "E":
                contracting.append((word + letter, odds2, length2))

    walk("", 0, 0)
    return expanding, contracting


def cap(max_len: int = MAX_LEN) -> dict[str, Any]:
    """`R <= floor((log2 3 - 1) a)` on every cycle-minimum word but the circuits."""
    expanding, contracting = cycle_min_words(max_len)
    out: dict[str, Any] = {"max_len": max_len, "families": {}}
    for name, family in (("expanding", expanding), ("contracting", contracting)):
        with_gcd = 0
        attained = 0
        max_gcd = 0
        exceptions: list[str] = []
        beats: list[str] = []
        by_run: dict[int, int] = {}
        for word, odds, _length in family:
            run_gcd = even_run_gcd(word)
            if run_gcd < 2:
                continue
            with_gcd += 1
            max_gcd = max(max_gcd, run_gcd)
            run = leading_odd_run(word)
            bound = math.floor(CAP_SLOPE * run)
            if run_gcd > bound:
                exceptions.append(word)
            elif run_gcd == bound:
                attained += 1
            by_run[run] = max(by_run.get(run, 0), run_gcd)
            if dual_modulus(word, odds) > 2**run:
                beats.append(word)
        out["families"][name] = {
            "words": len(family),
            "with_even_run_gcd": with_gcd,
            "max_even_run_gcd": max_gcd,
            "cap_attained": attained,
            "cap_exceptions": exceptions,
            "cap_exceptions_are_all_circuits": all(
                re.fullmatch(r"O+E+", w) is not None for w in exceptions
            ),
            "dual_beats_lemma_eight": beats,
            "max_even_run_gcd_by_leading_run": dict(sorted(by_run.items())),
        }
    out["cap"] = "R <= floor((log2 3 - 1) a)"
    out["cap_slope"] = CAP_SLOPE
    out["separation_exponent"] = SEPARATION_EXPONENT
    out["exception_class"] = "O^a E^r, the circuit; Steiner 1977 excludes the nontrivial case"
    return out


def sieve(max_len: int = MAX_LEN) -> dict[str, Any]:
    """Against the `neg_cycle_finance` ceiling: does the dual kill anything Lemma 8 misses?"""
    expanding, _ = cycle_min_words(max_len)
    counts = {"lemma_eight": 0, "dual": 0, "both": 0, "dual_only": 0, "neither": 0}
    dual_only: list[str] = []
    for word, odds, length in expanding:
        floor_l8, ceiling = window(word, odds, length)
        modulus = dual_modulus(word, odds)
        kill_l8 = floor_l8 > ceiling
        kill_dual = modulus >= 2 and modulus + 1 > ceiling
        counts["lemma_eight"] += kill_l8
        counts["dual"] += kill_dual
        if kill_l8 and kill_dual:
            counts["both"] += 1
        elif kill_dual:
            counts["dual_only"] += 1
            dual_only.append(word)
        elif not kill_l8:
            counts["neither"] += 1
    return {
        "max_len": max_len,
        "shape_words": len(expanding),
        "counts": counts,
        "dual_only_examples": dual_only[:8],
        "reading": "every word the dual kills, Lemma 8 had already killed",
    }


def bridge() -> dict[str, Any]:
    """What the reduction is, in the laboratory's own terms."""
    return {
        "reduction": "mod 2^R - 1 with R dividing every even run, 2^(r_i + 1) = 2 and the "
        "correction 2^(r_i + 1) - 2 vanishes, leaving 2 u_(i+1) = 3 u_i",
        "target": "the Juggler exponent transport e -> 3e/2 (odd base), e -> e/2 (even base) "
        "on the perfect-power locus, where there is no floor loss at all",
        "juggler_no_cycle_argument": "3^o != 2^o, a pure exponent count needing neither "
        "Catalan nor Baker; the exponent map has no nontrivial cycle for that reason alone",
        "price": "pulled back through the congruence the equation 3^o != 2^o degrades from a "
        "contradiction into m | u -- an impossibility becomes a floor",
        "why_it_stops": "the floor it becomes is capped by the CycleMin shape at "
        "2^(floor((log2 3 - 1) a)), below Lemma 8's own 2^a",
    }


def probe_payload(max_len: int = MAX_LEN) -> dict[str, Any]:
    identities = mersenne_divides_charge()
    rationals = rational_cycle_check()
    capped = cap(max_len)
    census = sieve(max_len)
    return {
        "decision": {
            "classification": CLASS_DUAL,
            "call": "CLOSE",
            "reason": "the dual floor is correct and is capped below Lemma 8 by the shape "
            "condition that defines the family, with zero new kills at every length tested",
        },
        "identities": identities,
        "rational_cycles": rationals,
        "known_cycles": known_cycles(),
        "cap": capped,
        "sieve": census,
        "bridge": bridge(),
        "novelty": "not established; arxiv.org, cs.uwaterloo.ca and oeis.org are refused by "
        "this container's network egress policy, so Hercher 2023, Eliahou 1993 and "
        "Simons-de Weger 2005 could not be read at source for the dual congruence",
        "anti_overclaim": "No Juggler cycle is excluded, no floor is raised, N_0 is untouched, "
        "and no negative Collatz cycle is newly excluded. The dual floor is a theorem about "
        "cycles of the Z shortcut map; its laboratory content is that the CycleMin shape caps "
        "it below the floor this laboratory already has, so it closes a direction rather than "
        "opening one. Neither map is claimed to halt.",
    }


def render_markdown(data: dict[str, Any]) -> str:
    cap_rows = data["cap"]["families"]["expanding"]["max_even_run_gcd_by_leading_run"]
    lines = [
        "# The even-run dual of Lemma 8",
        "",
        f"Status: **{data['decision']['classification']}**",
        "",
        "Generated by `python -m research.juggler_sequence.even_run_mersenne_floor`.",
        "",
        "## The dual floor",
        "",
        "On a cycle of the `Z` shortcut map with at least one even step, odd elements "
        "`x_1, ..., x_o` and `r_i` halvings between consecutive odd steps, let `R` be the gcd "
        "of the nonzero `r_i` and `m` any divisor of `2^R - 1` with `gcd(m, 2^o - 3^o) = 1`. "
        "Then `x = -1 (mod m)` for every odd element, hence `|x| >= m - 1`.",
        "",
        "In `u = x + 1` the passage is `2^(r_i + 1) u_(i+1) = 3 u_i - 2 + 2^(r_i + 1)`; "
        "`ord_m(2) | R | r_i` makes `2^(r_i + 1) = 2 (mod m)`, the correction vanishes, and "
        "`2 u_(i+1) = 3 u_i`. Once around: `u (2^o - 3^o) = 0 (mod m)`.",
        "",
        "Lemma 8 reads the **valuation** of `2` off the odd runs and gives `|x| >= 2^a - 1`; "
        "this reads the **order** of `2` off the even runs and gives `|x| >= 2^R - 1`.",
        "",
        "## Verification",
        "",
        f"- block expansion `evenCharge w = sum_j 3^j 2^(A_j) (2^(r_j) - 1)`: "
        f"`{data['identities']['block_expansion_words_checked']}` words, "
        f"`{len(data['identities']['block_expansion_violations'])}` violations",
        f"- `(2^R - 1) | evenCharge w`: `{data['identities']['mersenne_words_tested']}` words "
        f"with `R >= 2`, `{len(data['identities']['mersenne_violations'])}` violations",
        f"- the congruence at every odd element of the rational cycle: "
        f"`{data['rational_cycles']['words_tested']}` words, "
        f"`{len(data['rational_cycles']['violations'])}` violations",
        f"- vacuous at every known cycle: `{data['known_cycles']['all_vacuous']}` "
        "(each has an E-run of length 1, so `R = 1`)",
        "",
        "## The cap, and why it is the shape that imposes it",
        "",
        "On a word whose proper prefixes are all non-contracting the leading run of `a` odd "
        "letters is followed by an E-run of length `r_1 >= 1`, and non-contraction at its end "
        "is `3^a >= 2^(a + r_1)`. Since `R | r_1`,",
        "",
        "    R <= floor((log2 3 - 1) a) = floor(0.58496 a),",
        "",
        f"so the dual floor sits below Lemma 8's by `2^({data['cap']['separation_exponent']:.5f} a)`.",
        "",
        "| family | words | with `R >= 2` | max `R` | cap attained | exceptions | all circuits | dual beats Lemma 8 |",
        "| --- | --- | --- | --- | --- | --- | --- | --- |",
    ]
    for name, fam in data["cap"]["families"].items():
        lines.append(
            f"| {name} | {fam['words']} | {fam['with_even_run_gcd']} | "
            f"{fam['max_even_run_gcd']} | {fam['cap_attained']} | "
            f"{len(fam['cap_exceptions'])} | {fam['cap_exceptions_are_all_circuits']} | "
            f"{len(fam['dual_beats_lemma_eight'])} |"
        )
    lines += [
        "",
        f"The exception class is exactly `{data['cap']['exception_class']}`.",
        "",
        "| leading odd run `a` | greatest `R` seen | Lemma 8 floor `2^a` |",
        "| --- | --- | --- |",
    ]
    for run, run_gcd in cap_rows.items():
        lines.append(f"| {run} | {run_gcd} | {2 ** int(run)} |")
    lines += [
        "",
        "## Against the finance ceiling: zero new kills",
        "",
        f"On the `{data['sieve']['shape_words']}` CycleMin shape words of length at most "
        f"`{data['sieve']['max_len']}`, sieved against `neg_cycle_finance`:",
        "",
        f"- Lemma 8 kills `{data['sieve']['counts']['lemma_eight']}`",
        f"- the dual kills `{data['sieve']['counts']['dual']}`, of which "
        f"`{data['sieve']['counts']['both']}` were already dead",
        f"- the dual kills alone: `{data['sieve']['counts']['dual_only']}`",
        "",
        "## What the reduction is",
        "",
        f"- {data['bridge']['reduction']}",
        f"- which is {data['bridge']['target']}",
        f"- where the no-cycle argument is {data['bridge']['juggler_no_cycle_argument']}",
        f"- and the price is that {data['bridge']['price']}",
        f"- and it stops because {data['bridge']['why_it_stops']}",
        "",
        "## Novelty",
        "",
        data["novelty"] + ".",
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
    print("mersenne violations:", len(data["identities"]["mersenne_violations"]))
    print("rational-cycle violations:", len(data["rational_cycles"]["violations"]))
    for name, fam in data["cap"]["families"].items():
        print(
            f"{name}: R>=2 in {fam['with_even_run_gcd']}, max R {fam['max_even_run_gcd']}, "
            f"cap exceptions {len(fam['cap_exceptions'])} (all circuits "
            f"{fam['cap_exceptions_are_all_circuits']}), beats Lemma 8 "
            f"{len(fam['dual_beats_lemma_eight'])}"
        )
    print("dual-only kills:", data["sieve"]["counts"]["dual_only"])


if __name__ == "__main__":
    main()

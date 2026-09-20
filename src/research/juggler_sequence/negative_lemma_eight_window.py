"""The Lemma 8 floor is sign-symmetric, attained by every known cycle, and useless at the leftovers.

`J-lemma-eight-is-the-exponent-valuation` located the Juggler's copy of Hercher's Lemma 8 on the
exponent and showed it is confined to a density-zero locus. This probe asks the complementary
question on the side where the laboratory's bridge says the Juggler's cycle words actually live:
the negative integers, where `neg_cycle_word_is_juggler_shape` makes a negative Collatz cycle
word a Paper A CycleMin word, letter for letter. What is the pointwise 2-adic floor worth THERE,
where it exists in full?

**THE FLOOR IS SIGN-SYMMETRIC, AND THE SIGN COSTS EXACTLY 2.** The congruence of Lemma 8 holds
over `Z` (`two_pow_mul_iter_add_one_int`): `a` consecutive odd states force `x = -1 mod 2^a`.
On the positive side `x + 1 >= 2^a` gives Hercher's `x >= 2^a - 1`. On the negative side
`x <= -2` gives `x + 1 <= -1`, so `x + 1 <= -2^a` and

    x <= -(2^a + 1),    i.e.   |x| >= 2^a + 1,

the same fact two units the other way. The negative floor is the LARGER of the two, and the
negative side is the one that has cycles -- so the valuation is not what discriminates between
the signs. The linear form is: `2^K - 3^o > 0` small forces `K` enormous, while `3^o - 2^K > 0`
is `1` at `K = 3` and `139` at `K = 11`.

**EVERY KNOWN CYCLE OF THE Z MAP ATTAINS ITS FLOOR WITH EQUALITY.** `{1, 2}` has `a = 1` and
`x = 1 = 2^1 - 1`; `-5` has `a = 2` and `|x| = 5 = 2^2 + 1`; `-17` has `a = 4` and
`|x| = 17 = 2^4 + 1`. Equivalently `x + 1 = -2^a` exactly on both negative cycles, which by the
cycle equation says the odd part of the word's even-charge equals the gap: `1 = 3^2 - 2^3` for
`OOE` and `139 = 3^7 - 2^11` for the `-17` word. A bound tight at every object it is supposed to
exclude cannot be the exclusion.

**THE FLOOR MEETS THE LABORATORY'S CEILING, AND THE PAIR IS A SIEVE.** `neg_cycle_finance` is
kernel-checked: on a cycle at `x <= -2` read at its least `|x|`,
`2 (|x| - 1)(3^o - 2^K) <= (K - o) 3^o`. With the floor that is a window

    2^a + 1  <=  |x|  <=  1 + e 3^o / (2 (3^o - 2^K)),    e = K - o,

and an empty window excludes the word at every length, not merely inside a census. Emptiness is

    2^(a+1) theta_J > e,      theta_J = 1 - 2^K / 3^o,

so a negative cycle word obeys `a <= log2(e / theta_J) - 1`: a pointwise logarithmic bound on the
leading odd run, which is exactly the shape of the door the 19 September entry names for the
Juggler. Here it is available, and this probe measures what it buys.

**WHAT IT BUYS, MEASURED HONESTLY.** On the 198891 expanding prefix-noncontracting words of
length at most 22 the window excludes 84.7 per cent and empties the lengths 1, 2, 4, 5, 7, 8, 10,
13 and 16 outright -- but that figure flatters it, because Paper A's Theorem 3.31 census bound
`e >= 8` already excludes every shape word shorter than 22. (`e >= 8` with `3^o > 2^K` forces
`o >= 14`, hence `K >= 22`.) The two criteria can only be compared from `K = 22`, and there the
number is this: of the 93222 shape words of length 22, 17637 are admissible to `e >= 8`, and the
window kills 4787 of them, 27.1 per cent. Every word it kills has leading run at least 6; every
survivor has leading run at most 5. So what the missing Juggler floor would buy, at the first
length Paper A allows a cycle word at all, is a cap of 5 on the leading odd run and a quarter of
the candidates.

**AND WHERE IT STOPS.** The bound reads `a <= log2(e / theta_J) - 1`, and `theta_J` is the record
near-convergent defect. At the laboratory's leftover lengths it is

    L = 19    theta = 1.35e-2    a <= 8.02
    L = 84    theta = 2.09e-3    a <= 12.86
    L = 569   theta = 1.07e-3    a <= 16.59
    L = 1054  theta = 4.37e-5    a <= 22.09

against `a <= 2.17` at `L = 3` and `a <= 5` at `L = 22`. The leftovers are precisely the lengths
where the gap is a record near-convergent of `log 2 / log 3`, so they are precisely the lengths
where this sieve goes slack: the cap it imposes on the leading run grows with `log2(1 / theta_J)`
while the words needing to be excluded need only a short leading run to pass.

So the door, priced on the mirror side where it is open, is worth most of the short word list and
nothing at all at the lengths the cycle problem turns on. That is a sharper statement than "it
would deliver at most Collatz's cycle starting line": it would deliver the starting line and stop
before the first leftover.

No Juggler cycle is excluded here, no floor is raised, and no negative Collatz cycle is newly
excluded either -- the laboratory's own census already settled every length to 24 by exhibiting
the rational cycles. What is new is that the exclusion is a criterion rather than a census, and
the number attached to it.
"""

from __future__ import annotations

import json
import math
from fractions import Fraction
from typing import Any

from research.juggler_sequence.lean_paths import DATA_ROOT, DOCS_RESEARCH

DATA_DIR = DATA_ROOT / "negative_lemma_eight_window"
JSON_PATH = DATA_DIR / "summary.json"
DOC_PATH = DOCS_RESEARCH / "juggler_negative_lemma_eight_window.md"

CLASS_WINDOW = "NEGATIVE_FLOOR_IS_SLACK_AT_THE_LEFTOVERS"

#: word lengths enumerated for the sieve
MAX_LEN = 22
#: Paper A Theorem 3.31's census bound on even letters, for comparison
PAPER_A_EVEN_FLOOR = 8
#: the laboratory's record near-convergent lengths
LEFTOVERS = (3, 11, 19, 84, 569, 1054)


def shortcut(x: int) -> int:
    """The shortcut Collatz map on `Z`: `x/2` on even, `(3x+1)/2` on odd."""
    return x // 2 if x % 2 == 0 else (3 * x + 1) // 2


def cycle_from(x: int, cap: int = 4096) -> list[int] | None:
    seen: dict[int, int] = {}
    seq: list[int] = []
    y = x
    for i in range(cap):
        if y in seen:
            return seq[seen[y] :]
        seen[y] = i
        seq.append(y)
        y = shortcut(y)
    return None


def word_of(cycle: list[int]) -> str:
    return "".join("O" if y % 2 else "E" for y in cycle)


def leading_odd_run(word: str) -> int:
    run = 0
    for letter in word:
        if letter != "O":
            break
        run += 1
    return run


def even_charge(word: str) -> int:
    """`evenCharge [] = 0`, `(E::w) = 3^oddCount(w) + 2 evenCharge w`, `(O::w) = 2 evenCharge w`."""
    total = 0
    for i, letter in enumerate(word):
        if letter == "E":
            total += 2**i * 3 ** sum(1 for c in word[i + 1 :] if c == "O")
    return total


def v2(m: int) -> int | None:
    m = abs(m)
    if m == 0:
        return None
    k = 0
    while m % 2 == 0:
        m //= 2
        k += 1
    return k


def shape_words(max_len: int = MAX_LEN) -> list[tuple[str, int, int]]:
    """Expanding, prefix-noncontracting words: Paper A's CycleMin shape, the shared object."""
    out: list[tuple[str, int, int]] = []

    def walk(word: str, odds: int, length: int) -> None:
        if length and 2**length < 3**odds:
            out.append((word, odds, length))
        if length == max_len:
            return
        for letter in "OE":
            odds2 = odds + (letter == "O")
            length2 = length + 1
            if 2**length2 <= 3**odds2:
                walk(word + letter, odds2, length2)

    walk("", 0, 0)
    return out


def window(word: str, odds: int, length: int) -> tuple[int, Fraction]:
    """`2^a + 1 <= |x| <= 1 + e 3^o / (2 (3^o - 2^K))`, floor new, ceiling `neg_cycle_finance`."""
    evens = length - odds
    gap = 3**odds - 2**length
    floor = 2 ** leading_odd_run(word) + 1
    ceiling = 1 + Fraction(evens * 3**odds, 2 * gap)
    return floor, ceiling


def known_cycles() -> dict[str, Any]:
    """Every known cycle of the `Z` map attains its own Lemma 8 floor."""
    rows = []
    for start in (1, -1, -5, -17):
        cycle = cycle_from(start)
        assert cycle is not None
        least = max(cycle) if start < 0 else min(cycle)
        rotation = cycle[cycle.index(least) :] + cycle[: cycle.index(least)]
        word = word_of(rotation)
        odds = word.count("O")
        run = leading_odd_run(word)
        charge = even_charge(word)
        gap = 3**odds - 2 ** len(word)
        floor = 2**run + 1 if least < 0 else 2**run - 1
        rows.append(
            {
                "x": least,
                "u": least + 1,
                "word": word,
                "length": len(word),
                "odds": odds,
                "leading_odd_run": run,
                "v2_of_u": v2(least + 1),
                "floor": floor,
                "attains_floor": abs(least) == floor,
                "u_is_minus_a_power_of_two": least + 1 == -(2**run) if least < 0 else None,
                "even_charge": charge,
                "odd_part_of_charge": charge // 2 ** (v2(charge) or 0) if charge else 0,
                "gap": gap,
                "odd_part_equals_abs_gap": (
                    (charge // 2 ** (v2(charge) or 0) if charge else 0) == abs(gap)
                ),
            }
        )
    return {
        "law": "a consecutive odd states force x = -1 mod 2^a; x >= 2^a - 1 on the positive side "
        "and x <= -(2^a + 1) on the negative, the same fact two units apart",
        "rows": rows,
        "all_attain": all(r["attains_floor"] for r in rows if r["x"] != -1),
        "all_odd_parts_are_the_gap": all(
            r["odd_part_equals_abs_gap"] for r in rows if r["x"] != -1
        ),
        "minus_one_is_the_degenerate_case": "u = 0, excluded by the hypothesis x <= -2",
    }


def sieve(max_len: int = MAX_LEN) -> dict[str, Any]:
    words = shape_words(max_len)
    excluded: set[int] = set()
    by_even_floor: set[int] = set()
    by_length: dict[int, list[int]] = {}
    longest_run: dict[int, int] = {}
    for i, (word, odds, length) in enumerate(words):
        floor, ceiling = window(word, odds, length)
        row = by_length.setdefault(length, [0, 0])
        if floor > ceiling:
            excluded.add(i)
            row[0] += 1
        else:
            row[1] += 1
            run = leading_odd_run(word)
            longest_run[length] = max(longest_run.get(length, 0), run)
        if length - odds < PAPER_A_EVEN_FLOOR:
            by_even_floor.add(i)
    total = len(words)
    return {
        "max_len": max_len,
        "shape_words": total,
        "excluded": len(excluded),
        "excluded_share": len(excluded) / total,
        "empty_lengths": sorted(k for k, v in by_length.items() if v[1] == 0),
        "by_length": {str(k): {"excluded": v[0], "kept": v[1]} for k, v in sorted(by_length.items())},
        "longest_surviving_leading_run": {str(k): v for k, v in sorted(longest_run.items())},
        "paper_a_even_floor": PAPER_A_EVEN_FLOOR,
        "paper_a_excludes": len(by_even_floor),
        "window_only": len(excluded - by_even_floor),
        "paper_a_only": len(by_even_floor - excluded),
        "both": len(excluded & by_even_floor),
        "survive_both": total - len(excluded | by_even_floor),
        "not_subsumed": bool(excluded - by_even_floor),
    }


def first_admissible_length(length: int = MAX_LEN) -> dict[str, Any]:
    """What the floor would buy at the first length Paper A Theorem 3.31 admits.

    `e >= 8` with `3^o > 2^K` forces `o >= 14`, hence `K >= 22`: the census bound excludes every
    shape word shorter than 22 outright, so the two criteria can only be compared from there.
    """
    words = [t for t in shape_words(length) if t[2] == length]
    admissible = [t for t in words if t[2] - t[1] >= PAPER_A_EVEN_FLOOR]
    killed = [t for t in admissible if window(*t)[0] > window(*t)[1]]
    kept = [t for t in admissible if window(*t)[0] <= window(*t)[1]]
    return {
        "length": length,
        "paper_a_forces_length_at_least": PAPER_A_EVEN_FLOOR
        + math.ceil(PAPER_A_EVEN_FLOOR * math.log(2) / math.log(1.5)),
        "shape_words_at_length": len(words),
        "paper_a_admissible": len(admissible),
        "window_kills": len(killed),
        "window_kills_share_of_admissible": len(killed) / len(admissible) if admissible else 0.0,
        "least_run_killed": min((leading_odd_run(t[0]) for t in killed), default=None),
        "greatest_run_surviving": max((leading_odd_run(t[0]) for t in kept), default=None),
        "reading": "at the first length the census bound admits, the pointwise floor caps the "
        "leading odd run and removes just over a quarter of what is left",
    }


def leftover_slack(lengths: tuple[int, ...] = LEFTOVERS) -> dict[str, Any]:
    """The run bound `a <= log2(e / theta_J) - 1` at the record near-convergent lengths."""
    rows = []
    for length in lengths:
        odds = math.ceil(length * math.log(2) / math.log(3))
        while 3**odds <= 2**length:
            odds += 1
        evens = length - odds
        theta = 1 - Fraction(2**length, 3**odds)
        rows.append(
            {
                "length": length,
                "odds": odds,
                "evens": evens,
                "theta_J": float(theta),
                "run_bound": math.log2(evens / float(theta)) - 1,
            }
        )
    return {
        "law": "an empty window is 2^(a+1) theta_J > e, so a negative cycle word has "
        "a <= log2(e / theta_J) - 1",
        "rows": rows,
        "reading": "theta_J is the record near-convergent defect at a leftover length, so the "
        "bound goes slack exactly at the lengths the cycle frontier lives on",
    }


def probe_payload() -> dict[str, Any]:
    cycles = known_cycles()
    counts = sieve()
    slack = leftover_slack()
    first = first_admissible_length()
    green = cycles["all_attain"] and cycles["all_odd_parts_are_the_gap"] and counts["not_subsumed"] and counts["excluded_share"] > 0.5
    return {
        "known_cycles": cycles,
        "sieve": counts,
        "leftover_slack": slack,
        "first_admissible_length": first,
        "decision": {
            "classification": CLASS_WINDOW if green else "NEGATIVE_FLOOR_WINDOW_FAILED",
            "branch": "CLOSE",
            "green": green,
        },
        "anti_overclaim": (
            "No Juggler cycle is excluded, no floor is raised, and no negative Collatz cycle is "
            "newly excluded: the laboratory's own rational-cycle census already settled every "
            "length to 24 by exhibiting the cycles. The sieve is a criterion rather than a "
            "census, which is why it is worth stating, and its value is the measurement -- what "
            "the missing Juggler floor would buy, and where it would stop. The ceiling is "
            "neg_cycle_finance, kernel-checked; the floor is two lines of integer arithmetic; "
            "neither is a Baker argument and neither touches the leftovers."
        ),
    }


def render_markdown(data: dict[str, Any]) -> str:
    lines = [
        "# The negative Lemma 8 window",
        "",
        f"Status: **{data['decision']['classification']}**",
        "",
        "Generated by `python -m research.juggler_sequence.negative_lemma_eight_window`.",
        "",
        "## Every known cycle of the Z map sits on its floor",
        "",
        "| x | u = x+1 | word | a | floor | attained | odd part of charge = \|gap\| |",
        "| --- | --- | --- | --- | --- | --- | --- |",
    ]
    for row in data["known_cycles"]["rows"]:
        lines.append(
            f"| {row['x']} | {row['u']} | `{row['word']}` | {row['leading_odd_run']} "
            f"| {row['floor']} | {row['attains_floor']} | {row['odd_part_equals_abs_gap']} |"
        )
    counts = data["sieve"]
    lines += [
        "",
        f"`-1` is the degenerate case: {data['known_cycles']['minus_one_is_the_degenerate_case']}.",
        "",
        "## The sieve",
        "",
        f"- shape words of length at most `{counts['max_len']}`: `{counts['shape_words']}`",
        f"- excluded by the window: `{counts['excluded']}` "
        f"(`{100 * counts['excluded_share']:.1f}%`)",
        f"- lengths emptied outright: `{counts['empty_lengths']}`",
        f"- Paper A Theorem 3.31 `e >= {counts['paper_a_even_floor']}` excludes "
        f"`{counts['paper_a_excludes']}`; window only `{counts['window_only']}`, "
        f"Paper A only `{counts['paper_a_only']}`, both `{counts['both']}`, "
        f"survive both `{counts['survive_both']}`",
        f"- not subsumed by the census bound: `{counts['not_subsumed']}`",
        "",
        "## What it adds where Paper A stops",
        "",
        f"- `e >= {data['sieve']['paper_a_even_floor']}` with an expanding word forces length at "
        f"least `{data['first_admissible_length']['paper_a_forces_length_at_least']}`, so the "
        "census bound alone excludes every shorter shape word and the comparison begins there",
        f"- at `L = {data['first_admissible_length']['length']}`: "
        f"`{data['first_admissible_length']['shape_words_at_length']}` shape words, "
        f"`{data['first_admissible_length']['paper_a_admissible']}` admissible to Paper A, of "
        f"which the window kills `{data['first_admissible_length']['window_kills']}` "
        f"(`{100 * data['first_admissible_length']['window_kills_share_of_admissible']:.1f}%`)",
        f"- every word it kills has leading run at least "
        f"`{data['first_admissible_length']['least_run_killed']}`; every survivor has run at most "
        f"`{data['first_admissible_length']['greatest_run_surviving']}`",
        "",
        "## Where it goes slack",
        "",
        "| L | o | e | theta_J | a <= |",
        "| --- | --- | --- | --- | --- |",
    ]
    for row in data["leftover_slack"]["rows"]:
        lines.append(
            f"| {row['length']} | {row['odds']} | {row['evens']} | {row['theta_J']:.3e} "
            f"| {row['run_bound']:.2f} |"
        )
    lines += [
        "",
        data["leftover_slack"]["reading"] + ".",
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
    print("all known cycles attain the floor:", data["known_cycles"]["all_attain"])
    print("excluded share:", round(data["sieve"]["excluded_share"], 4))
    print("empty lengths:", data["sieve"]["empty_lengths"])
    print("window only:", data["sieve"]["window_only"], "| survive both:", data["sieve"]["survive_both"])


if __name__ == "__main__":
    main()

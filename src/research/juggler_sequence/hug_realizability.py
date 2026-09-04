"""Is the hug word realizable, and is it harder to realize than a typical word?

Section 6 now poses the obstruction in this form: which Sturmian words in the two blocks
``OE`` and ``OOE``, mixed at density ``log 2 / log 3``, occur as Juggler itineraries?  The
extremal walk of Theorem 5.3 is exactly such a word, so the question is not decorative --- if
the hug word were systematically hard to realize, the walk charge would be bounding an
adversary that cannot occur, and the whole comparison would be loose.

The tractable form of the question is a density.  A word of length ``l`` occupies a fraction
``~2^-l`` of starts if realizability is generic, so the count of odd ``m < N`` realizing a given
prefix should be ``~N/2^(l+1)``.  This module measures that count for prefixes of the hug word
and, as a control, for the other words that actually occur at the same length.  A hug-specific
obstruction would show as a systematic deficit against the control.
"""

from __future__ import annotations

import math
from collections import Counter
from typing import Any

from .cycle_walk_charge import STEP
from .walk_realizability import word_of
from .walk_runs import extremal_walk


def hug_word(length: int, odd_count: int, n: int) -> tuple[int, ...]:
    """The charge-extremal walk as a 0/1 tuple: the adversary of Theorem 5.3."""
    return tuple(extremal_walk(length, odd_count, n))


def sturmian_blocks(word: tuple[int, ...]) -> dict[str, Any]:
    """Confirm the word is a mixture of OE and OOE only, and report the mix."""
    # the final block may be truncated by the prefix cut; drop it before classifying
    blocks, i = [], 0
    while i < len(word):
        if word[i] == 0:
            blocks.append("E")
            i += 1
            continue
        j = i
        while j < len(word) and word[j] == 1:
            j += 1
        run = j - i
        tail = "E" if j < len(word) and word[j] == 0 else ""
        blocks.append("O" * run + tail)
        i = j + (1 if tail else 0)
    if blocks and not blocks[-1].endswith("E"):
        blocks.pop()                       # truncated tail, not a block of the word
    c = Counter(blocks)
    total = sum(c.values())
    return {"blocks": dict(c), "distinct": sorted(c),
            "only_OE_OOE": set(c) <= {"OE", "OOE"},
            "OOE_share": c.get("OOE", 0) / total if total else 0.0}


def prefix_counts(target: tuple[int, ...], depth: int, hi: int) -> list[int]:
    """``counts[l]`` = number of odd ``m < hi`` whose itinerary starts with ``target[:l]``."""
    counts = [0] * (depth + 1)
    for m in range(3, hi, 2):
        w = word_of(m, depth)
        for l in range(depth + 1):
            if (w & ((1 << l) - 1)) == _mask(target, l):
                counts[l] += 1
            else:
                break
    return counts


def _mask(word: tuple[int, ...], l: int) -> int:
    return sum(1 << k for k in range(l) if word[k])


def realizability_profile(length: int = 40, depth: int = 22,
                          hi: int = 4_000_000) -> dict[str, Any]:
    """Hug-prefix realization counts against the generic ``2^-l`` expectation."""
    from .paper_a_audit import o_min

    hug = hug_word(length, o_min(length), 1000)
    counts = prefix_counts(hug, depth, hi)
    odd_starts = (hi - 3) // 2 + 1
    rows = []
    for l in range(1, depth + 1):
        # every odd start begins with O, so the first letter is free: 2^(l-1) classes, not 2^l
        expected = odd_starts / (1 << (l - 1))
        rows.append({"l": l, "count": counts[l], "expected": expected,
                     "ratio": counts[l] / expected if expected > 0 else None})
    return {"length": length, "depth": depth, "hi": hi, "odd_starts": odd_starts,
            "hug_prefix": "".join("O" if c else "E" for c in hug[:depth]),
            "blocks": sturmian_blocks(hug), "rows": rows}


def control_profile(depth: int = 18, hi: int = 4_000_000, top: int = 40) -> dict[str, Any]:
    """The same statistic for the most common itineraries at ``depth``.

    If the hug word were specifically hard to realize, its count would sit below this
    control band; if the drift above 1 is a property of the Juggler measure rather than of
    the hug word, the control drifts too.
    """
    counts: Counter = Counter()
    for m in range(3, hi, 2):
        counts[word_of(m, depth)] += 1
    odd_starts = (hi - 3) // 2 + 1
    expected = odd_starts / (1 << (depth - 1))
    vals = sorted(counts.values(), reverse=True)
    return {"depth": depth, "hi": hi, "distinct_words": len(counts),
            "expected": expected,
            "max_ratio": vals[0] / expected,
            "median_ratio": vals[len(vals) // 2] / expected,
            "min_ratio": vals[-1] / expected,
            "top_ratios": [v / expected for v in vals[:top]]}


def main() -> None:
    r = realizability_profile()
    b = r["blocks"]
    print("hug word: %s" % r["hug_prefix"])
    print("blocks: %s   only OE/OOE: %s   OOE share %.4f  (log2/log3 - 1/2 = %.4f)"
          % (b["blocks"], b["only_OE_OOE"], b["OOE_share"], math.log(2) / math.log(3) - 0.5))
    print()
    print("realization count of each hug prefix among %d odd starts" % r["odd_starts"])
    print("  %-4s %-10s %-12s %s" % ("l", "count", "expected", "count/expected"))
    for row in r["rows"]:
        if row["count"] == 0:
            print("  %-4d %-10d %-12.1f  -- none" % (row["l"], row["count"], row["expected"]))
            break
        print("  %-4d %-10d %-12.1f %.3f"
              % (row["l"], row["count"], row["expected"], row["ratio"]))
    c = control_profile()
    print()
    print("control at depth %d: %d distinct itineraries, count/expected"
          % (c["depth"], c["distinct_words"]))
    print("   max %.3f   median %.3f   min %.3f"
          % (c["max_ratio"], c["median_ratio"], c["min_ratio"]))


if __name__ == "__main__":
    main()

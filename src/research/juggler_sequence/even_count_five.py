"""What an even-count bound of five would require.

Theorem 3.22 is the only unconditional exclusion in Paper A: no cycle itinerary has fewer than
four even letters, hence (Corollary 3.23) no cycle has period below eleven.  Everything else in
the paper needs a certified descent floor.  Raising the even count is therefore the only route to
a stronger *floor-free* statement, and Section 3 already advertises the shape of the argument.

The e <= 3 proof runs on three ingredients: the internal-even bootstrap (Lemma 3.4) bounding the
last odd run, the gapped-leftover theorem (3.21) killing large middle runs, and seven bunched
families (3.14-3.20) for the small ones.  None of them transfers to e = 4: each is a statement
about a complete itinerary, not a sub-word.  So `e >= 5` needs its own family program, and the
useful thing to produce first is the explicit list of what that program must prove.

This module enumerates the e = 4 canonical forms that survive the ingredients which *do*
generalise -- the canonical run form of Lemma 3.21b, the bootstrap, and formal expansion -- and
reports the residual families, each of which needs a theorem.
"""

from __future__ import annotations

import math
from typing import Any, Iterator


def expansion_ok(o: int, L: int) -> bool:
    """Formal expansion: a cycle itinerary needs ``3^o > 2^L`` (Theorem 3.2)."""
    return 3**o > 2**L


def canonical_forms(e: int, o_max: int) -> Iterator[tuple[int, ...]]:
    """Minimum-based canonical run forms ``O^a1 E O^a2 E ... O^ae E``.

    Lemma 3.21b: the orientation starts ``OO`` and ends ``E``, so ``a1 >= 2`` and there are
    exactly ``e`` even letters.  Lemma 3.4's internal-even bootstrap excludes a final odd run of
    length two or more, so ``a_e <= 1``.
    """
    def rec(prefix: tuple[int, ...], remaining: int) -> Iterator[tuple[int, ...]]:
        idx = len(prefix)
        if idx == e:
            if remaining == 0:            # the run lengths must exhaust the odd count
                yield prefix
            return
        lo = 2 if idx == 0 else 0
        hi = 1 if idx == e - 1 else remaining
        for a in range(lo, hi + 1):
            if a <= remaining:
                yield from rec(prefix + (a,), remaining - a)

    for o in range(2, o_max + 1):
        yield from rec((), o)


def word_of_form(form: tuple[int, ...]) -> str:
    return "".join("O" * a + "E" for a in form)


def residual_families(e: int = 4, o_max: int = 14) -> dict[str, Any]:
    """The e = 4 forms that survive canonical form + bootstrap + expansion."""
    kept, dropped_expansion = [], 0
    for form in canonical_forms(e, o_max):
        o = sum(form)
        L = o + e
        if not expansion_ok(o, L):
            dropped_expansion += 1
            continue
        kept.append(form)
    by_tail: dict[tuple[int, ...], list[tuple[int, ...]]] = {}
    for f in kept:
        by_tail.setdefault(f[1:], []).append(f)
    return {
        "e": e, "o_max": o_max,
        "surviving": len(kept),
        "dropped_by_expansion": dropped_expansion,
        "min_odd_count": min((sum(f) for f in kept), default=None),
        "tails": {t: sorted(x[0] for x in v) for t, v in sorted(by_tail.items())},
        "families": len(by_tail),
    }


def cycle_search(max_n: int, max_len: int = 40) -> dict[str, Any]:
    """Direct search: any cycle at all with minimum below ``max_n``, and its even count."""
    def J(x: int) -> int:
        return math.isqrt(x) if x % 2 == 0 else math.isqrt(x**3)

    found = []
    for n in range(3, max_n, 2):
        x, evens = n, 0
        for k in range(1, max_len + 1):
            if x % 2 == 0:
                evens += 1
            x = J(x)
            if x < n:
                break
            if x == n:
                found.append({"n": n, "L": k, "evens": evens})
                break
    return {"max_n": max_n, "max_len": max_len, "cycles": found}


def program_size(gap_thresholds: tuple[int, int] = (4, 3)) -> dict[str, Any]:
    """How large the ``e >= 5`` program is, if gapped-leftover analogues transfer.

    For ``e = 3`` Theorem 3.21 kills the middle run at ``b >= 4`` (tail ``EE``) and ``b >= 3``
    (tail ``OE``), which is what leaves the seven bunched families of Theorems 3.14-3.20.  If
    analogues at the same thresholds hold for ``e = 4``, both middle runs are bounded and the
    residual list is finite; this counts it.
    """
    a_ee, a_oe = gap_thresholds
    tails = []
    for a4 in (0, 1):
        cap2 = a_ee if a4 == 0 else a_oe
        cap3 = a_ee if a4 == 0 else a_oe
        for a2 in range(cap2):
            for a3 in range(cap3):
                tails.append((a2, a3, a4))
    return {
        "thresholds": gap_thresholds,
        "e3_actual": {"gapped_leftover_theorems": 1, "bunched_families": 7},
        "e4_projected": {"gapped_leftover_theorems": 2, "bunched_families": len(tails)},
        "tails": tails,
        "payoff": {"from": "L >= 11", "to": "L >= 14"},
    }


def main() -> None:
    r = residual_families()
    print("e = 4 canonical forms surviving canonical-form + bootstrap + expansion")
    print("  odd counts up to %d: %d forms survive, %d dropped by expansion alone"
          % (r["o_max"], r["surviving"], r["dropped_by_expansion"]))
    print("  least odd count with a surviving form: %s (so L >= %s)"
          % (r["min_odd_count"], r["min_odd_count"] + 4))
    print("  %d distinct tails (a2, a3, a4); each needs its own theorem:" % r["families"])
    for tail, firsts in list(r["tails"].items())[:14]:
        shape = "O^a E " + " ".join("O^%d E" % a for a in tail)
        print("     %-26s a in %s%s"
              % (shape.replace("O^0 ", ""), firsts[:6], " ..." if len(firsts) > 6 else ""))
    g = program_size()
    print()
    print("size of the e >= 5 program, if the gapped-leftover thresholds transfer:")
    print("   e = 3 (done):      %d gapped-leftover theorem, %d bunched families"
          % (g["e3_actual"]["gapped_leftover_theorems"], g["e3_actual"]["bunched_families"]))
    print("   e = 4 (needed):    %d gapped-leftover theorems, %d bunched families"
          % (g["e4_projected"]["gapped_leftover_theorems"], g["e4_projected"]["bunched_families"]))
    print("   payoff:            %s  ->  %s" % (g["payoff"]["from"], g["payoff"]["to"]))
    s = cycle_search(200_000)
    print()
    print("direct search to n < %d, length <= %d: %s"
          % (s["max_n"], s["max_len"], s["cycles"] or "no cycle of any even count"))


if __name__ == "__main__":
    main()

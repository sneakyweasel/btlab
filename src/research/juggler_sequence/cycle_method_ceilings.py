"""Two measured ceilings on the methods Paper A actually uses.

Not a halt theorem, not a floor raise, not a refutation. It asks what the
paper's two exclusion mechanisms can reach *in the limit*, and answers
with numbers rather than intuition.

**The floor route diverges.** Finance excludes a length `L` when
`n_max(L) <= N_0`. Along the convergents `p_k/q_k` of `log2/log3` the
surplus is `theta ~ log3 / q_{k+1}`, so

    n_max(q_k) * log n_max  ~  c * q_k * q_{k+1},    c ~ 0.45,

which `paper_a_audit.convergent_invariant` verifies over five orders of
magnitude. Since `q_{k+1} -> infinity`, so does `n_max`. Every length
needs its own descent floor and the floors are unbounded, so no finite
computation excludes all lengths. This is intrinsic to using a floor,
not a defect of any particular table.

**The shape route is exponential.** Section 3's exclusions are the only
family here that is both floor-free and length-free -- they kill *words*
rather than lengths, so in principle they could close the problem
uniformly. But the admissible shapes multiply by about six per even
letter. Theorem 3.31 reached `e = 7`; the lengths that survive finance
need `e` in the tens of thousands.

Counting shapes is a dynamic program, not a search: the above-anchor
condition after block `i` depends only on the cumulative odd count, since
the walk rises inside a run and dips only at the even letters. So the
state is `(block, odds used)` and the count is exact.
"""

from __future__ import annotations

import json
import math
from typing import Any

from research.juggler_sequence.cycle_finance import DATA_DIR
from research.juggler_sequence.paper_a_audit import (
    convergent_invariant,
    n_max,
    o_min,
)

#: `log 2 / log(3/2)`: the odd letters an even letter must be paid for.
RUN_CONST = math.log(2) / math.log(1.5)


def admissible_shape_count(even: int) -> tuple[int, int]:
    """`(o_min, #run vectors)` for `even` even letters at the least odd count.

    A run vector `(a_0, ..., a_{e-1})` spells `O^{a_0} E ... O^{a_{e-1}} E`.
    Constraints, all of them ones the paper proves for a cycle minimum:
    `a_0 >= 2` (the word starts `OO`), every run within Theorem 3.31's cap
    `floor((e - i) * RUN_CONST)`, and every prefix above the anchor, which
    after block `i` reads `cumulative odds >= (i + 1) * RUN_CONST`.
    """
    odd = int(even * RUN_CONST) + 1
    dp: dict[int, int] = {0: 1}
    for i in range(even):
        cap = int((even - i) * RUN_CONST)
        low = 2 if i == 0 else 0
        need = (i + 1) * RUN_CONST
        nxt: dict[int, int] = {}
        for used, ways in dp.items():
            for a in range(low, cap + 1):
                total = used + a
                if total > odd:
                    break
                if total < need:
                    continue
                nxt[total] = nxt.get(total, 0) + ways
        dp = nxt
    return odd, dp.get(odd, 0)


def surplus(even: int) -> float:
    """`Lambda = o log3 - L log2` at the least odd count.

    Equal to `log(3/2) * (1 - frac(e * RUN_CONST))`, so it is small exactly
    when `e * RUN_CONST` sits just under an integer -- which is what makes a
    length survive finance.
    """
    odd = int(even * RUN_CONST) + 1
    return odd * math.log(3) - (odd + even) * math.log(2)


def shape_count_under(even: int, *, run_suffix_law: bool) -> int:
    """Shapes at the least odd count, under one of the two prefix conditions.

    `run_suffix_law=False` imposes only the anchor, `3^{o_p} >= 2^{|p|}` at
    every block boundary. `True` imposes Theorem 3.26's law, which says the
    whole word expands but no proper tail beginning with an odd letter does.
    Complementing a tail to its prefix, that reads
    `3^{o_p}/2^{|p|} >= 3^o/2^L`, i.e. the anchor raised from `1` to
    `1 + theta`. So the law is the anchor tightened by the surplus, and it
    degenerates to the anchor as the surplus goes to zero.
    """
    odd = int(even * RUN_CONST) + 1
    threshold = surplus(even) if run_suffix_law else 0.0
    log2, log3 = math.log(2), math.log(3)
    dp: dict[int, int] = {0: 1}
    for i in range(even):
        cap = int((even - i) * RUN_CONST)
        low = 2 if i == 0 else 0
        nxt: dict[int, int] = {}
        for used, ways in dp.items():
            for a in range(low, cap + 1):
                total = used + a
                if total > odd:
                    break
                if total * log3 - (total + i + 1) * log2 < threshold - 1e-12:
                    continue
                nxt[total] = nxt.get(total, 0) + ways
        dp = nxt
    return dp.get(odd, 0)


def law_kill_fraction(even: int) -> dict[str, Any]:
    """What Theorem 3.26's law removes beyond the anchor, at this even count."""
    anchor = shape_count_under(even, run_suffix_law=False)
    law = shape_count_under(even, run_suffix_law=True)
    return {
        "e": even,
        "surplus": surplus(even),
        "anchor_shapes": anchor,
        "law_shapes": law,
        "killed_fraction": (1.0 - law / anchor) if anchor else 0.0,
    }


def small_surplus_evens(count: int = 6, limit: int = 400) -> list[int]:
    """Even counts with the smallest surplus -- the regime a survivor lives in.

    `limit` is a cost control, not mathematics: the shape counts are exact
    integers whose length grows with `e`, so the DP at `e = 389` carries
    300-digit values and takes minutes. `e = 31` already has surplus
    `2.1e-3` and already shows the law killing nothing.
    """
    return [e for _, e in sorted((surplus(e), e) for e in range(5, limit))[:count]]


#: Cheap witnesses for the report: two where the law bites and two where it
#: does not. The expensive confirmation at `e = 389` lives in a slow test.
LAW_REPORT_EVENS: tuple[int, ...] = (10, 16, 31, 62)


def shape_growth(evens: tuple[int, ...] = tuple(range(4, 21))) -> list[dict[str, Any]]:
    rows = []
    previous = None
    for even in evens:
        odd, count = admissible_shape_count(even)
        rows.append(
            {
                "e": even,
                "o_min": odd,
                "shapes": count,
                "growth": (count / previous) if previous else None,
            }
        )
        previous = count or None
    return rows


def distinctness_gain(length: int, n: int | None = None) -> dict[str, Any]:
    """What orbit distinctness is worth to the three-class charge.

    A primitive cycle's states are pairwise distinct (Lean
    `cyclePrimitive_orbit_injOn`), so the `e` valleys are distinct odd
    integers at least `n` -- hence at least `n, n+2, ..., n+2(e-1)`, not all
    at `n` as the charge assumes. The refinement is therefore real, and it is
    worth `O(e/n)`.

    Evaluated at `n = n_max(length)`, the floor where the length actually
    matters, since `n_max ~ q q_next` grows faster than `e ~ 0.37 L`, that is
    already negligible and shrinks as the floor rises. This is the counting
    route, measured rather than waved at.
    """
    odd = o_min(length)
    even = length - odd
    base = n if n is not None else n_max(length)
    crude = even / (base * math.log(base))
    # The exact sum of e terms, to O((e/n)^2), is this integral.
    fine = 0.5 * (
        math.log(math.log(base + 2 * even)) - math.log(math.log(base))
    )
    return {
        "L": length,
        "e": even,
        "n": base,
        "e_over_n": even / base,
        "crude": crude,
        "distinct_aware": fine,
        "gain": 1.0 - fine / crude,
    }


def length_only_optimum() -> list[dict[str, Any]]:
    """How close finance is to the best possible *length-only* charge.

    A charge that sees only `(n, L, o)` and not the orbit must upper-bound
    every configuration those numbers allow -- including `e` valleys sitting
    at `n, n+2, ...`, which no proved constraint forbids. So any such charge
    is at least `~e/(n log n)`, and exclusion needs
    `theta * n log n > e`. With `theta ~ log3 / q_next` that puts the
    optimal threshold at

        n_max log n  ~  (e/q) * q * q_next / log 3,

    against which `convergent_invariant` measures what finance achieves.
    The ratio is the room left in the family. It comes out at the `6/5`
    unroll, so the family is exhausted: what remains is orbit-dependent
    information, which is what the walk charge uses.
    """
    rows = []
    for row in convergent_invariant():
        q, q_next = row["q"], row["q_next"]
        even = q - o_min(q)
        optimum = (even / q) / math.log(3)
        achieved = row["nlogn_over_q_qnext"]
        rows.append(
            {
                "q": q,
                "q_next": q_next,
                "even_share": even / q,
                "optimum": optimum,
                "achieved": achieved,
                "ratio": achieved / optimum,
            }
        )
    return rows


def even_count_of(length: int) -> int:
    """Even letters of a leftover length at its least admissible odd count."""
    return length - o_min(length)


def ceilings_report() -> dict[str, Any]:
    rows = shape_growth()
    invariant = convergent_invariant()
    ratios = [r["nlogn_over_q_qnext"] for r in invariant]
    growths = [r["growth"] for r in rows if r["growth"]]
    return {
        "bound": "method_ceilings",
        # The floor route.
        "convergent_rows": invariant,
        "invariant_min": min(ratios),
        "invariant_max": max(ratios),
        # n_max ~ c q q_next, and q_next is unbounded, so the reach diverges.
        "floor_route_reach_diverges": True,
        "largest_n_max_tabulated": max(r["n_max"] for r in invariant),
        # The shape route.
        "shape_rows": rows,
        "shape_growth_median": sorted(growths)[len(growths) // 2],
        "shapes_at_theorem_3_31_frontier": admissible_shape_count(7)[1],
        "even_count_at_first_survivor": even_count_of(25781),
        # The sharper statement: the law is the anchor tightened by the
        # surplus, so where the surplus vanishes the law does too -- and the
        # surviving lengths are exactly the small-surplus ones.
        "law_rows": [law_kill_fraction(e) for e in LAW_REPORT_EVENS],
        "surplus_at_first_survivor": surplus(even_count_of(25781)),
        # The counting route, measured: distinctness of the orbit states is
        # real but worth O(e/n), and n >> e at every relevant floor.
        "distinctness_rows": [
            distinctness_gain(L) for L in (25781, 50508, 176251)
        ],
        # The charge family, priced against its own optimum. The ratio lands
        # on the 6/5 unroll, so length-only charges are exhausted.
        "length_only_rows": length_only_optimum(),
        "halt_theorem": False,
        "no_cycle_all_lengths": False,
    }


def write_ceilings_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else ceilings_report()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    (DATA_DIR / "method_ceilings.json").write_text(
        json.dumps(data, indent=2) + "\n", encoding="utf-8"
    )
    return data


def main() -> None:
    data = write_ceilings_artifacts()
    print(
        "floor route: n_max log n / (q q_next) in "
        f"[{data['invariant_min']:.4f}, {data['invariant_max']:.4f}], "
        f"largest n_max tabulated {data['largest_n_max_tabulated']:,}"
    )
    print(
        "shape route: about "
        f"{data['shape_growth_median']:.1f}x per even letter; "
        f"{data['shapes_at_theorem_3_31_frontier']:,} shapes at e=7, "
        f"but the first survivor needs e={data['even_count_at_first_survivor']:,}"
    )


if __name__ == "__main__":
    main()

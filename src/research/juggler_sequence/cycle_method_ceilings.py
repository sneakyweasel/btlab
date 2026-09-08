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
from research.juggler_sequence.paper_a_audit import convergent_invariant, o_min

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

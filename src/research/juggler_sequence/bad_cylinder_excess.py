"""Phase-0 probe for ``bad_cylinder_excess``: is the one-sided hypothesis satisfiable?

Paper C's Section 9 criteria are implications from hypotheses nobody has proved, and the
laboratory has already refuted one member of the family: the all-word cylinder bound is false
because absorbed starts overpopulate a cylinder (``J-absorbed-cylinder``), which is why
``H(C, A)`` and ``H_q(C, A)`` are stated on the ``L(y)``-bad words only.  This probe asks
whether the bad-word versions are satisfiable, by measuring the quantity they bound.

``H_q(C, A)`` at the scale ``y`` says: for every ``L(y)``-bad word ``w`` of length
``1 <= t < d(y)``, ``#[wO] <= q #[w] + y (log y)^{-A}``.  So it holds exactly when

    excess(t, q) = max over bad w of (#[wO] - q #[w])

is at most ``y (log y)^{-A}`` at every such depth.  The probe computes ``excess`` exactly, by
enumerating every odd start of ``(y, 2y]``, keeping the starts whose word is still bad, and
grouping them by word at each depth.  ``#[wO]`` is the number of members whose ``t``-th
iterate is odd, since the next letter of a member is the parity of its ``t``-th iterate.

Comparing ``excess`` to ``y (log y)^{-A}`` for the ``A`` the criteria need (``A > C``, so
``A >= 32`` at ``C = 30``) is meaningless at computable scales: ``(log y)^{-32}`` is below
``10^{-38}`` already at ``y = 10^7``, so the additive error is dead and the hypothesis
degenerates to an exact share bound that no finite sample obeys.  The scale-honest comparison
is against a fair coin.  Under fair splitting the standardised bias
``z_w = (#[wO] - #[w]/2) / sqrt(#[w]/4)`` of each cylinder is ``N(0, 1)``, so the largest over
``W`` cylinders is about ``sqrt(2 log W)``.  The probe reports ``max |z_w|`` against that
baseline: a ratio near one means the map is as fair as a coin at that depth and the hypothesis
is as satisfiable as it would be for a coin; a ratio growing with ``y`` means the map is
getting worse, and the hypothesis is in trouble.

It also reports the collapse alphabet: the number ``W`` of nonempty bad cylinders, the number
``V`` of distinct ``t``-th iterates among bad starts, and the number ``P`` of distinct
(word, iterate) pairs.  ``P/W`` near one says each bad cylinder sits over a single value, so
its members share a next letter whatever the map does; that is the mechanism recorded in
``cylinder_energy_measure``.  Whether the per-cylinder hypotheses survive asymptotically turns
on whether ``V`` outgrows the mass, which is what the scaling of ``max_cyl`` reports.

No sampling.  Not a halt theorem, and nothing here proves or refutes a hypothesis: four scales
cannot decide an asymptotic statement, and the depths reachable here are the first few.
"""

from __future__ import annotations

import json
import math
import time
from math import isqrt
from typing import Any

from research.juggler_sequence.lean_paths import DATA_ROOT

DATA_DIR = DATA_ROOT / "bad_cylinder_excess"
SUMMARY = DATA_DIR / "summary.json"

LOG2_3 = math.log(3.0) / math.log(2.0)
SCALES = (10**4, 10**5, 10**6, 10**7)
DEPTH = 32
SHARES = (0.5, 0.55)
N0_LEAN = 260
CONSTANTS = (19.0, 30.0)


def floor_power(n: int) -> int:
    """The map ``T(n) = floor(sqrt n)`` for even ``n``, ``floor(n sqrt n)`` for odd ``n``."""
    if n < 1:
        raise ValueError("floor_power is defined on positive integers")
    return isqrt(n) if n % 2 == 0 else isqrt(n * n * n)


def scale_L(y: float, n0: float) -> float:
    """Paper C's ``L(y) = log_2 (log 2y / log N_0)``."""
    return math.log2(math.log(2.0 * y) / math.log(n0))


def depth_of(y: float, C: float, n0: float) -> int:
    """Paper C's ``d(y) = ceil(C L(y))``."""
    return math.ceil(C * scale_L(y, n0))


def odd_starts(y: int) -> range:
    """The odd integers of ``(y, 2y]``."""
    first = y + 1 if (y + 1) % 2 == 1 else y + 2
    return range(first, 2 * y + 1, 2)


def fair_max_z(w_count: int) -> float:
    """The largest standardised binomial deviation expected over ``W`` fair cylinders."""
    return math.sqrt(2.0 * math.log(w_count)) if w_count > 1 else 0.0


def _depth_row(words: dict[int, list[int]], y: int, t: int, n_starts: int,
               values: set[int], pairs: set[tuple[int, int]],
               shares: tuple[float, ...]) -> dict[str, Any]:
    """Statistics of one depth from the per-word (members, odd members) counts."""
    w_count = len(words)
    alive = sum(g[0] for g in words.values())
    max_cyl = max((g[0] for g in words.values()), default=0)
    z_max = 0.0
    for total, odd in words.values():
        if total > 0:
            z = abs(odd - total / 2.0) / math.sqrt(total / 4.0)
            if z > z_max:
                z_max = z
    fair_z = fair_max_z(w_count)
    row: dict[str, Any] = {
        "t": t,
        "bad_mass_fraction": alive / n_starts,
        "words": w_count,
        "values": len(values),
        "word_value_pairs": len(pairs),
        "values_per_word": (len(pairs) / w_count) if w_count else 0.0,
        "max_cylinder": max_cyl,
        "z_max": z_max,
        "z_fair": fair_z,
        "z_ratio": (z_max / fair_z) if fair_z > 0 else 0.0,
        "excess": {},
    }
    loglog = math.log(math.log(y))
    for q in shares:
        excess = max((odd - q * total for total, odd in words.values()), default=0.0)
        row["excess"][str(q)] = {
            "max_excess": excess,
            # the largest A with excess <= y (log y)^{-A}; the criteria need A > C
            "A_required": (math.log(y / excess) / loglog) if excess > 0 else None,
        }
    # what a fair coin would produce with these same cylinder sizes: the largest cylinder
    # carries the largest expected deviation, sqrt(2 log W * n) / 2
    fair_excess = math.sqrt(2.0 * math.log(w_count) * max_cyl) / 2.0 if w_count > 1 else 0.0
    row["fair_excess"] = fair_excess
    row["A_fair"] = (math.log(y / fair_excess) / loglog) if fair_excess > 0 else None
    # the cylinder bound of H(C, A) compares against the fair share 2^{-(t-1)} y/2
    fair_share = (2.0 ** (-(t - 1))) * y / 2.0 if t >= 1 else float(y)
    cyl_excess = max((g[0] - fair_share for g in words.values()), default=0.0)
    row["cylinder_excess"] = cyl_excess
    row["cylinder_A_required"] = (math.log(y / cyl_excess) / loglog) if cyl_excess > 0 else None
    return row


def measure(y: int, depth: int = DEPTH, n0: int = N0_LEAN,
            shares: tuple[float, ...] = SHARES) -> dict[str, Any]:
    """Exact per-depth statistics of the `L(y)`-bad cylinders of `(y, 2y]`.

    The walk after ``t`` letters is ``popcount(word) log_2 3 - t``, so the word carries its own
    badness test and no separate state is needed.  Starts whose word has crossed are dropped:
    badness depends only on the word, so they cannot belong to any later bad cylinder.
    """
    t0 = time.time()
    L = scale_L(y, n0)
    starts = odd_starts(y)
    n_starts = len(starts)
    vals = [n for n in starts]
    words = [0] * n_starts
    rows: list[dict[str, Any]] = []
    for t in range(depth + 1):
        groups: dict[int, list[int]] = {}
        value_set: set[int] = set()
        pair_set: set[tuple[int, int]] = set()
        for v, w in zip(vals, words):
            g = groups.get(w)
            if g is None:
                groups[w] = g = [0, 0]
            g[0] += 1
            if v & 1:
                g[1] += 1
            value_set.add(v)
            pair_set.add((w, v))
        rows.append(_depth_row(groups, y, t, n_starts, value_set, pair_set, shares))
        if t == depth:
            break
        new_vals: list[int] = []
        new_words: list[int] = []
        for v, w in zip(vals, words):
            bit = v & 1
            w2 = (w << 1) | bit
            if bin(w2).count("1") * LOG2_3 - (t + 1) > -L:
                new_vals.append(floor_power(v))
                new_words.append(w2)
        vals, words = new_vals, new_words
        if not vals:
            break
    return {
        "y": y,
        "starts": n_starts,
        "depth": depth,
        "floor": n0,
        "L": round(L, 4),
        "depths": {str(int(C)): depth_of(y, C, n0) for C in CONSTANTS},
        "seconds": round(time.time() - t0, 2),
        "rows": rows,
    }


def verdict(result: dict[str, Any], C: float = 19.0) -> dict[str, Any]:
    """The worst depth below `d(y)` for the constant `C`: the least `A` the hypothesis could
    carry, and the largest excess over the fair-coin baseline."""
    d = result["depths"][str(int(C))]
    window = [r for r in result["rows"] if 1 <= r["t"] < d]
    if not window:
        return {"C": C, "d": d, "depths_measured": 0}
    a_values = [r["excess"]["0.5"]["A_required"] for r in window
                if r["excess"]["0.5"]["A_required"] is not None]
    f_values = [r["A_fair"] for r in window if r.get("A_fair") is not None]
    a_min = min(a_values) if a_values else None
    f_min = min(f_values) if f_values else None
    return {
        "C": C,
        "d": d,
        "depths_measured": len(window),
        "A_required_min": a_min,
        "A_fair_min": f_min,
        "A_gap": (a_min - f_min) if (a_min is not None and f_min is not None) else None,
        "z_ratio_max": max(r["z_ratio"] for r in window),
        "z_ratio_at_d_minus_one": window[-1]["z_ratio"],
        "max_cylinder_at_d_minus_one": window[-1]["max_cylinder"],
        "values_per_word_at_d_minus_one": window[-1]["values_per_word"],
    }


def run(scales: tuple[int, ...] = SCALES, depth: int = DEPTH) -> dict[str, Any]:
    from research.juggler_sequence.cycle_finance import git_commit

    results = [measure(y, depth) for y in scales]
    summary = {
        "branch": "bad_cylinder_excess",
        "git_commit": git_commit(),
        "depth": depth,
        "floor": N0_LEAN,
        "shares": list(SHARES),
        "scales": results,
        "verdicts": {str(int(C)): [verdict(r, C) for r in results] for C in CONSTANTS},
    }
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    SUMMARY.write_text(json.dumps(summary, indent=1) + "\n", encoding="utf-8")
    return summary


def format_summary(summary: dict[str, Any]) -> str:
    lines = []
    for res in summary["scales"]:
        lines.append(f"y = {res['y']:>10}  starts = {res['starts']:>8}  L = {res['L']}  "
                     f"d(19) = {res['depths']['19']}  d(30) = {res['depths']['30']}  "
                     f"{res['seconds']:.1f} s")
        lines.append("    t   badmass   words    values   val/word   maxcyl     z_max   "
                     "z_fair  ratio   A_req  A_fair")
        for row in res["rows"]:
            a = row["excess"]["0.5"]["A_required"]
            a_s = f"{a:6.2f}" if a is not None else "   inf"
            f = row.get("A_fair")
            f_s = f"{f:6.2f}" if f is not None else "     -"
            lines.append(f"   {row['t']:>2}  {row['bad_mass_fraction']:8.4f}  "
                         f"{row['words']:>7}  {row['values']:>8}  {row['values_per_word']:8.2f}  "
                         f"{row['max_cylinder']:>7}  {row['z_max']:8.2f}  {row['z_fair']:6.2f}  "
                         f"{row['z_ratio']:5.2f}  {a_s}  {f_s}")
    for C, rows in summary["verdicts"].items():
        lines.append(f"verdict at C = {C}:")
        for v in rows:
            if v.get("depths_measured"):
                lines.append(f"  d = {v['d']:>3}  A_req_min = {v['A_required_min']:.2f}  "
                             f"A_fair_min = {v['A_fair_min']:.2f}  "
                             f"gap = {v['A_gap']:+.2f}  z_ratio_max = {v['z_ratio_max']:.2f}  "
                             f"maxcyl(d-1) = {v['max_cylinder_at_d_minus_one']}  "
                             f"val/word(d-1) = {v['values_per_word_at_d_minus_one']:.2f}")
    return "\n".join(lines)


if __name__ == "__main__":
    print(format_summary(run()))

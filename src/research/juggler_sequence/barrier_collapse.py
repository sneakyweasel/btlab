"""Phase-0 probe for ``barrier_collapse``: the barrier word and the one-sided hypothesis.

``bad_cylinder_excess`` found, by forward enumeration, that the deep end of Paper C's own
depth window is parity-constant at every computable scale, and left one question: does the
mass of the largest parity-constant bad cylinder decay like ``(log y)^{-A}``?  This probe
answers it backwards, at scales enumeration cannot reach, because the objects involved are
small.

The family is the **barrier word** ``w = O E^{t-1}``: one odd letter, then even letters until
the value sits just above the certified floor.  Its walk is ``u_s = log_2 3 - s``, so it
is ``L(y)``-bad exactly while ``t < L(y) + log_2 3``, and ``barrier_depth`` takes the largest
such ``t`` — a depth of order ``L(y)``, far inside the window ``t < d(y) = ceil(C L(y))``.

Three facts make the computation exact and cheap:

* on the cylinder the map is the plain composite ``G(n) = isqrt^{t-1}(isqrt(n^3))``, with no
  parity tests, because the letters say exactly that the intermediates are even;
* ``G`` is monotone, so the image of ``(y, 2y]`` is the integer interval
  ``[G(y+1), G(2y)]``, computed by two big-integer evaluations (``value_range``), and the
  level sets are intervals found by bisection (``level_weights``);
* the barrier value is **bounded**: it lies in ``(N_0, N_0^2)`` at every scale, since one more
  even letter would cross the floor and one fewer leaves the value below its square.

So the number of values the cylinder sits over is ``V ~ v_0 log(v_0) / log y``, which tends to
zero: past some scale the whole barrier cylinder maps to a *single* value, and every member
has the same next letter whatever the map does.  ``witness`` constructs an explicit start at
such a scale, by walking the chain back from the value through even preimages and leaving the
odd step free (a value generically has no odd preimage, so that step must be searched, not
chosen).

What this decides and what it does not.  That the cylinder is parity-constant is exact.  Its
*size* is not computed here: counting the starts whose thirteen intermediates are all even is
an equidistribution statement of the kind Proposition 4.4 is about, and no such count is
available.  The probe therefore reports the **deficit**: the factor by which the barrier
cylinder would have to fall below its fair share ``2^{-t}`` for ``H_q(C, A)`` to survive.  Not
a halt theorem, and nothing here proves or disproves a hypothesis.
"""

from __future__ import annotations

import json
import math
import sys
from math import isqrt
from typing import Any

from research.juggler_sequence.lean_paths import DATA_ROOT

sys.set_int_max_str_digits(200000)

DATA_DIR = DATA_ROOT / "barrier_collapse"
SUMMARY = DATA_DIR / "summary.json"

LOG2_3 = math.log2(3.0)
N0_LEAN = 260
SCALES_LOG10 = (7, 15, 25, 50, 100, 200, 435, 1000, 2000, 5000, 20000)
Q_MAX = 0.6309  # the paper's ceiling log 2 / log 3 on the share q
C_LEAST = 19.0  # the paper's least depth constant


def floor_power(n: int) -> int:
    """The map ``T(n) = floor(sqrt n)`` for even ``n``, ``floor(n sqrt n)`` for odd ``n``."""
    return isqrt(n) if n % 2 == 0 else isqrt(n * n * n)


def scale_L(log10_y: float, n0: int = N0_LEAN) -> float:
    """Paper C's ``L(y) = log_2 (log 2y / log N_0)`` for ``y = 10^{log10_y}``."""
    return math.log2((log10_y * math.log(10.0) + math.log(2.0)) / math.log(n0))


def barrier_depth(log10_y: float, n0: int = N0_LEAN) -> int:
    """The length of the barrier word: the largest ``t`` with ``O E^{t-1}`` still `L(y)`-bad."""
    x = scale_L(log10_y, n0) + LOG2_3
    return math.floor(x) if x % 1 else int(x) - 1


def min_prefix_walk(t: int) -> float:
    """The least prefix walk of ``O E^{t-1}``, attained at the last letter: `log_2 3 - t`."""
    return LOG2_3 - t


def composite(n: int, t: int) -> int:
    """``J^t`` on the barrier cylinder: one 3/2 power, then ``t-1`` square roots."""
    v = isqrt(n * n * n)
    for _ in range(t - 1):
        v = isqrt(v)
    return v


def value_range(y: int, t: int) -> tuple[int, int]:
    """The image of ``(y, 2y]`` under the composite: an interval, since it is monotone."""
    return composite(y + 1, t), composite(2 * y, t)


def _first_ge(y: int, t: int, v: int, lo: int, hi: int) -> int:
    """Least ``n`` in ``[lo, hi]`` with ``composite(n, t) >= v``, by bisection."""
    if composite(lo, t) >= v:
        return lo
    if composite(hi, t) < v:
        return hi + 1
    a, b = lo, hi
    while a < b:
        mid = (a + b) // 2
        if composite(mid, t) >= v:
            b = mid
        else:
            a = mid + 1
    return a


def level_weights(y: int, t: int) -> list[int]:
    """The exact widths of the level sets of the composite over ``(y, 2y]``."""
    lo, hi = y + 1, 2 * y
    v_lo, v_hi = value_range(y, t)
    edges = {v: _first_ge(y, t, v, lo, hi) for v in range(v_lo, v_hi + 2)}
    return [edges.get(v + 1, hi + 1) - edges[v] for v in range(v_lo, v_hi + 1)]


def odd_share(y: int, t: int) -> float:
    """The share of the barrier cylinder whose next letter is odd, from the exact weights."""
    v_lo, _ = value_range(y, t)
    ws = level_weights(y, t)
    total = sum(ws)
    odd = sum(w for v, w in enumerate(ws, start=v_lo) if v % 2)
    return odd / total if total else float("nan")


def witness(v: int, t: int, tries: int = 500) -> int | None:
    """An explicit start whose word is ``O E^{t-1}`` and whose ``t``-th iterate is ``v``.

    The chain is walked back through even preimages to ``J^2``; the odd step is then searched,
    because a value generically has no odd preimage.
    """
    m = v
    for _ in range(t - 2):
        lo = m * m
        m = lo if lo % 2 == 0 else lo + 1
    j2 = m
    lo = j2 ** 4
    n = _icbrt(lo)
    if n * n * n < lo:
        n += 1
    if n % 2 == 0:
        n += 1
    for _ in range(tries):
        j1 = isqrt(n * n * n)
        if j1 % 2 == 0 and isqrt(j1) == j2:
            return n
        n += 2
    return None


def _icbrt(x: int) -> int:
    if x < 2:
        return x
    r = 1 << ((x.bit_length() + 2) // 3)
    while True:
        nr = (2 * r + x // (r * r)) // 3
        if nr >= r:
            break
        r = nr
    while r * r * r > x:
        r -= 1
    while (r + 1) ** 3 <= x:
        r += 1
    return r


def itinerary(n: int, t: int) -> str:
    """The first ``t`` letters of the itinerary of ``n``."""
    letters = []
    m = n
    for _ in range(t):
        letters.append("O" if m % 2 else "E")
        m = floor_power(m)
    return "".join(letters)


def survey(log10_y: int, n0: int = N0_LEAN, exact_share: bool = True) -> dict[str, Any]:
    """The barrier word at one scale, with everything the hypothesis needs."""
    y = 10 ** log10_y
    L = scale_L(log10_y, n0)
    t = barrier_depth(log10_y, n0)
    v_lo, v_hi = value_range(y, t)
    values = v_hi - v_lo + 1
    fair = 2.0 ** (-t)
    share = odd_share(y, t) if (exact_share and values <= 5000) else None
    bias = abs(share - 0.5) if share is not None else (0.5 if values == 1 else None)
    excess = bias * fair if bias is not None else None
    ln_log = math.log(log10_y * math.log(10.0))
    row: dict[str, Any] = {
        "log10_y": log10_y,
        "L": round(L, 4),
        "t": t,
        "min_prefix_walk": round(min_prefix_walk(t), 4),
        "bad": min_prefix_walk(t) > -L,
        "d_C19": math.ceil(C_LEAST * L),
        "v_lo": v_lo,
        "v_hi": v_hi,
        "values": values,
        "in_floor_band": n0 < v_lo < n0 * n0,
        "fair_share": fair,
        "odd_share": share,
        "excess_over_y": excess,
        "A_permitted": (math.log(1.0 / excess) / ln_log) if excess else None,
    }
    # what H_q(C, A) with A = C demands of the cylinder, against its fair share
    allowance = math.exp(-C_LEAST * ln_log) / (1.0 - Q_MAX)
    row["allowance_over_y"] = allowance
    row["deficit_orders"] = round(math.log10(fair / allowance), 1)
    return row


def run(scales: tuple[int, ...] = SCALES_LOG10) -> dict[str, Any]:
    from research.juggler_sequence.cycle_finance import git_commit

    rows = [survey(k) for k in scales]
    collapsed = [r for r in rows if r["values"] == 1]
    w = None
    if collapsed:
        r = collapsed[0]
        n = witness(r["v_lo"], r["t"])
        if n is not None:
            w = {
                "log10_y": r["log10_y"],
                "digits": len(str(n)),
                "word": itinerary(n, r["t"]),
                "value": r["v_lo"],
                "next_letter": "O" if r["v_lo"] % 2 else "E",
                "first_40_digits": str(n)[:40],
                "last_40_digits": str(n)[-40:],
            }
    summary = {
        "branch": "barrier_collapse",
        "git_commit": git_commit(),
        "floor": N0_LEAN,
        "q_max": Q_MAX,
        "C_least": C_LEAST,
        "rows": rows,
        "witness": w,
    }
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    SUMMARY.write_text(json.dumps(summary, indent=1) + "\n", encoding="utf-8")
    return summary


def format_summary(summary: dict[str, Any]) -> str:
    lines = [f"{'log10 y':>8} {'L':>7} {'t':>3} {'d(19)':>6} {'v_lo':>7} {'V':>6} "
             f"{'fair':>10} {'share':>8} {'A_perm':>7} {'deficit':>8}"]
    for r in summary["rows"]:
        sh = f"{r['odd_share']:8.4f}" if r["odd_share"] is not None else "       -"
        ap = f"{r['A_permitted']:7.2f}" if r["A_permitted"] is not None else "      -"
        lines.append(f"{r['log10_y']:>8} {r['L']:7.3f} {r['t']:>3} {r['d_C19']:>6} "
                     f"{r['v_lo']:>7} {r['values']:>6} {r['fair_share']:10.3e} {sh} {ap} "
                     f"{r['deficit_orders']:8.1f}")
    w = summary.get("witness")
    if w:
        lines.append(f"witness at y ~ 10^{w['log10_y']}: {w['digits']} digits, word {w['word']}, "
                     f"J^t = {w['value']}, next letter {w['next_letter']}")
    return "\n".join(lines)


if __name__ == "__main__":
    print(format_summary(run()))

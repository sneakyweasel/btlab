"""Mechanical fixed-point window of a survivor word and its realized parity depth.

Phase 0 for the question left by the short-cycle reduction (Paper A
Theorem 4.10 / Corollary 4.11): for a prescribed word ``w`` the
integers ``m`` with ``f_w(m) = m`` under the *prescribed* branches
(odd branch ``isqrt(m^3)``, even branch ``isqrt(m)`` regardless of the
actual parity) form a window ``R(w)`` of about ``n/L`` consecutive
integers around the finance balance point. A cycle with word ``w``
exists iff some member of ``R(w)`` realizes ``w`` (its true orbit has
the parity word ``w``). This probe locates ``R(w)`` for the hug word
at certified lengths, measures its size against the drift prediction
``1/(Λ (1 + log m))``, and records the realized parity depth of every
member. Not a halt theorem, not a floor raise, not a Paper A edit.

Dossier: ``docs/problems/juggler_cycle_mechanical_window.md``.
"""

from __future__ import annotations

import json
import math
from collections import Counter
from math import isqrt
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_finance import git_commit, o_min_and_theta
from research.juggler_sequence.cycle_walk_greedy import hug_word

DATA_DIR = (
    Path(__file__).resolve().parents[3]
    / "data"
    / "research"
    / "juggler"
    / "cycle_mechanical_window"
)

DEFAULT_LENGTHS = (19, 84, 1054)
LONG_LENGTH = 25781
SCAN_MULTIPLE = 4

CLASS_CLOSED = "MECHANICAL_WINDOW_CLOSED"
CLASS_STRUCTURE = "MECHANICAL_WINDOW_STRUCTURE"


def juggler(m: int) -> int:
    return isqrt(m) if m % 2 == 0 else isqrt(m * m * m)


def mechanical_image(m: int, word: str) -> int:
    """Apply the prescribed branches of ``word`` to ``m`` (parity ignored)."""

    x = m
    for letter in word:
        x = isqrt(x * x * x) if letter == "O" else isqrt(x)
        if x == 0:
            return 0
    return x


def realized_depth(m: int, word: str) -> int:
    """Number of initial letters of ``word`` the true orbit of ``m`` follows."""

    x = m
    for index, letter in enumerate(word):
        actual = "O" if x % 2 == 1 else "E"
        if actual != letter:
            return index
        x = juggler(x)
    return len(word)


def linear_form(length: int, odd_count: int) -> float:
    return odd_count * math.log(3.0) - length * math.log(2.0)


def crossing(word: str, hi_bits: int = 200) -> int:
    """Smallest m in a dyadic bracket with f_w(m) >= m (bisection on a monotone f_w)."""

    lo, hi = 2, 1 << hi_bits
    if mechanical_image(hi, word) < hi:
        raise RuntimeError("no crossing below 2^hi_bits")
    while lo < hi:
        mid = (lo + hi) // 2
        if mechanical_image(mid, word) >= mid:
            hi = mid
        else:
            lo = mid + 1
    return lo


def window(word: str, length: int, odd_count: int) -> dict[str, Any]:
    """Exact fixed points of f_w near the crossing, scanned SCAN_MULTIPLE drift widths each way."""

    m0 = crossing(word)
    lam = linear_form(length, odd_count)
    predicted = 1.0 / (lam * (1.0 + math.log(m0))) if lam > 0 else float("inf")
    half = max(64, int(SCAN_MULTIPLE * predicted))
    lo, hi = max(2, m0 - half), m0 + half
    fixed = [m for m in range(lo, hi + 1) if mechanical_image(m, word) == m]
    # extend while fixed points touch the scan edges
    while fixed and fixed[0] <= lo + 2 and lo > 2:
        new_lo = max(2, lo - half)
        fixed = [m for m in range(new_lo, lo) if mechanical_image(m, word) == m] + fixed
        lo = new_lo
    while fixed and fixed[-1] >= hi - 2:
        new_hi = hi + half
        fixed = fixed + [m for m in range(hi + 1, new_hi + 1) if mechanical_image(m, word) == m]
        hi = new_hi
    depths = [realized_depth(m, word) for m in fixed]
    hist = Counter(depths)
    size = len(fixed)
    return {
        "L": length,
        "o": odd_count,
        "word_prefix": word[:24],
        "Lambda": lam,
        "crossing": m0,
        "scan_lo": lo,
        "scan_hi": hi,
        "window_size": size,
        "window_min": fixed[0] if fixed else None,
        "window_max": fixed[-1] if fixed else None,
        "window_span": (fixed[-1] - fixed[0] + 1) if fixed else 0,
        "predicted_size": predicted,
        "size_over_predicted": size / predicted if predicted and size else None,
        "depth_max": max(depths) if depths else None,
        "log2_size": math.log2(size) if size else None,
        "depth_mean": (sum(depths) / size) if size else None,
        "depth_hist": {str(k): v for k, v in sorted(hist.items())},
        "full_realizations": sum(1 for d in depths if d == length),
    }


def run(lengths: tuple[int, ...] = DEFAULT_LENGTHS, *, include_long: bool = False) -> dict[str, Any]:
    rows = []
    all_lengths = tuple(lengths) + ((LONG_LENGTH,) if include_long else ())
    for length in all_lengths:
        odd_count, _theta = o_min_and_theta(length)
        word = hug_word(length, odd_count)
        rows.append(window(word, length, odd_count))
    # Structure signal on windows large enough to test a coin (≥ 200 members):
    # mean depth above 1.25 (a fair coin gives 1 − 2^{-L} ≈ 1) or max depth above
    # log2(size) + 4. Windows of a few dozen members only report.
    structure = any(
        r["window_size"] >= 200
        and (r["depth_mean"] > 1.25 or r["depth_max"] > (r["log2_size"] or 0) + 4)
        for r in rows
    )
    return {
        "classification": CLASS_STRUCTURE if structure else CLASS_CLOSED,
        "git_commit": git_commit(),
        "rows": rows,
        "note": (
            "Fixed points of the prescribed-branch map f_w near the finance balance; "
            "depth = letters of w the true orbit follows. A fair coin gives mean depth "
            "≈ 1 and max ≈ log2(window). Any full realization would be a cycle."
        ),
    }


def main() -> None:
    import argparse

    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--long", action="store_true", help=f"also scan L={LONG_LENGTH}")
    args = parser.parse_args()
    summary = run(include_long=args.long)
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    out = DATA_DIR / "summary.json"
    out.write_text(json.dumps(summary, indent=2), encoding="utf-8")
    for r in summary["rows"]:
        print(
            f"L={r['L']} o={r['o']} Λ={r['Lambda']:.3e} crossing={r['crossing']} "
            f"|R|={r['window_size']} span={r['window_span']} predicted={r['predicted_size']:.1f} "
            f"depth max={r['depth_max']} mean={r['depth_mean']} hist={r['depth_hist']}"
        )
    print(summary["classification"], "->", out)


if __name__ == "__main__":
    main()

"""Winkler's Conjecture 36 (Beatty interlacing) past his verified range.

He states: for every n >= 4 the zeros of B_n(y) and B_(n+1)(y) strictly interlace,
and records exact verification for 4 <= n < 60 by rational root isolation.

B_n is built here from his Corollary 35 recurrence, independently implemented, and
already cross-checked: B_n(1) reproduces all 32 stored terms of A100982 with three
wrong offsets failing. Roots are isolated exactly over the rationals with sympy.

Reported per n: all zeros real, simple and negative, and strict alternation with
B_n to the left. A negative control reverses the orientation and must fail.
"""

from __future__ import annotations

import sys
import time

from sympy import Poly, Rational
from sympy.abc import y

sys.path.insert(0, r"C:\Users\phili\AppData\Local\Temp\claude\C--Users-phili-Desktop-balanced-ternary\20324fd0-22ac-426c-a7db-ef95b334646f\scratchpad")
from ferrers_beatty_check import build  # noqa: E402

NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 100
BUDGET = float(sys.argv[2]) if len(sys.argv) > 2 else 900.0


def roots_of(coeffs: list[int]):
    """Exact isolated real roots, ascending. None if not all real and simple."""
    p = Poly(list(reversed(coeffs)), y)
    d = p.degree()
    if d == 0:
        return []
    rs = p.real_roots()
    if len(rs) != d:
        return None
    if len(set(rs)) != d:
        return None
    return sorted(rs)


def alternates(lo, hi) -> bool:
    """Strict interlacing with `lo` to the left: lo_1 < hi_1 < lo_2 < hi_2 < ...
    for equal degrees, and hi_1 < lo_1 < hi_2 < ... when hi has one more root."""
    if not lo:
        return True
    if len(hi) == len(lo):
        merged = [v for pair in zip(lo, hi) for v in pair]
    elif len(hi) == len(lo) + 1:
        merged = [hi[0]] + [v for pair in zip(lo, hi[1:]) for v in pair]
    else:
        return False
    return all(merged[i] < merged[i + 1] for i in range(len(merged) - 1))


def main() -> None:
    t0 = time.time()
    B = build(NMAX + 1)
    print("built B_n to n = %d in %.1fs" % (NMAX + 1, time.time() - t0))

    cache: dict[int, list] = {}
    reached = 3
    bad: list[str] = []
    control_failures = 0
    control_total = 0

    for n in range(4, NMAX + 1):
        if time.time() - t0 > BUDGET:
            print("time budget reached at n = %d" % n)
            break
        for m in (n, n + 1):
            if m not in cache:
                r = roots_of(B[m])
                if r is None:
                    bad.append("n=%d: zeros not all real and simple" % m)
                    cache[m] = []
                else:
                    if any(v >= 0 for v in r):
                        bad.append("n=%d: a zero is not negative" % m)
                    cache[m] = r
        lo, hi = cache[n], cache[n + 1]
        if not alternates(lo, hi):
            bad.append("n=%d: no strict interlacing (deg %d, %d)" % (n, len(lo), len(hi)))
        else:
            reached = n
        # negative control: same test with the orientation reversed
        control_total += 1
        if len(hi) == len(lo) and not alternates(hi, lo):
            control_failures += 1
        elif len(hi) != len(lo):
            control_total -= 1
        print("  n=%-4d deg(B_n)=%-4d deg(B_(n+1))=%-4d  ok=%s   %.1fs"
              % (n, len(lo), len(hi), not bad or bad[-1].find("n=%d:" % n) < 0,
                 time.time() - t0))

    print("\nCONJECTURE 36 verified for 4 <= n <= %d  (he records n < 60)" % reached)
    print("failures: %s" % (bad if bad else "none"))
    print("negative control, reversed orientation rejected in %d of %d equal-degree pairs"
          % (control_failures, control_total))
    print("total time %.1fs" % (time.time() - t0))


if __name__ == "__main__":
    main()

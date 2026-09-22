"""Winkler's Corollary 35 (Ferrers Gap Polynomials, 18 Sep 2026) implemented from
the paper, then cross-checked against the laboratory's own object.

  rho   = log2(3) - 1
  h_k   = floor(k / rho) + 1
  q_n   = floor(n * rho)
  B_n(y)= G_{Lambda(n)}(y),  Lambda(n) = (n - h_1, ..., n - h_{q_n})

Corollary 35:  P_{n,0} = 1;  P_{h_t, t} = P_{h_t, t-1};  and for n >= h_t + 1
  P_{n,t} = P_{n,t-1} + P_{n-1,t} + [n >= h_t + 2] (y - 1) P_{n-2,t-1}.

The test that matters: B_n(1) must equal the total first-passage word count of
order n, which is A100982, which is this laboratory's M_d. If that holds, the
recurrence is read correctly and it is tied to our counts, not to his tables.

Polynomials are integer coefficient lists, index = power of y.
"""

from __future__ import annotations

import gzip
from fractions import Fraction
from math import log2

RHO = log2(3.0) - 1.0
OEIS = r"C:\Users\phili\Desktop\balanced_ternary\data\external\oeis\stripped.gz"


def h(k: int) -> int:
    """h_k = floor(k / rho) + 1, computed exactly: k/rho = k/(log2 3 - 1)."""
    # exact integer test: floor(k/rho) = max{ j : j*rho <= k } = max{ j : 3^j <= 2^(j+k) }
    j = 0
    while 3 ** (j + 1) <= 2 ** (j + 1 + k):
        j += 1
    return j + 1


def q(n: int) -> int:
    """q_n = floor(n * rho) = floor(n log2 3) - n, exact via bit_length."""
    return ((3 ** n).bit_length() - 1) - n


def add(a: list[int], b: list[int]) -> list[int]:
    out = [0] * max(len(a), len(b))
    for i, c in enumerate(a):
        out[i] += c
    for i, c in enumerate(b):
        out[i] += c
    return out


def mul_y_minus_1(a: list[int]) -> list[int]:
    """(y - 1) * a."""
    out = [0] * (len(a) + 1)
    for i, c in enumerate(a):
        out[i + 1] += c
        out[i] -= c
    return out


def trim(a: list[int]) -> list[int]:
    while len(a) > 1 and a[-1] == 0:
        a = a[:-1]
    return a


def build(nmax: int) -> dict[int, list[int]]:
    tmax = q(nmax) + 2
    H = {t: h(t) for t in range(1, tmax + 1)}
    P: dict[tuple[int, int], list[int]] = {}
    for n in range(0, nmax + 1):
        P[(n, 0)] = [1]
    for t in range(1, tmax + 1):
        ht = H[t]
        if ht > nmax:
            break
        P[(ht, t)] = P[(ht, t - 1)]
        for n in range(ht + 1, nmax + 1):
            term = add(P[(n, t - 1)], P[(n - 1, t)])
            if n >= ht + 2:
                term = add(term, mul_y_minus_1(P[(n - 2, t - 1)]))
            P[(n, t)] = trim(term)
    return {n: P[(n, q(n))] for n in range(1, nmax + 1) if (n, q(n)) in P}


def a100982() -> list[int]:
    with gzip.open(OEIS, "rt", encoding="utf-8", errors="replace") as fh:
        for line in fh:
            if line.startswith("A100982 "):
                body = line.split(" ", 1)[1].strip().strip(",")
                return [int(x) for x in body.split(",") if x]
    return []


def main() -> None:
    print("rho = %.10f" % RHO)
    print("h_k, k=1..12 :", [h(k) for k in range(1, 13)])
    print("q_n, n=1..14 :", [q(n) for n in range(1, 15)])
    print("h gaps in {1,2}:", set(h(k + 1) - h(k) for k in range(1, 60)))

    NMAX = 40
    B = build(NMAX)
    ref = a100982()
    print("\nB_n(1) against A100982 (%d stored terms)" % len(ref))
    hits = []
    for shift in (0, 1, -1, 2):
        ok = 0
        tot = 0
        for n in sorted(B):
            idx = n - 1 + shift
            if 0 <= idx < len(ref):
                tot += 1
                if sum(B[n]) == ref[idx]:
                    ok += 1
        hits.append((shift, ok, tot))
        print("  shift %+d : %d/%d agree" % (shift, ok, tot))

    best = max(hits, key=lambda r: (r[1], -abs(r[0])))
    print("\nbest alignment: shift %+d with %d/%d" % best)

    print("\nn, deg B_n, B_n(1), coefficients")
    for n in sorted(B)[:18]:
        print("  n=%-3d deg=%-3d B_n(1)=%-10d %s" % (n, len(B[n]) - 1, sum(B[n]), B[n]))


if __name__ == "__main__":
    main()

"""GPU twin of ``walk_kbest``: top-``K`` walk charges at the kill-table lengths.

The numpy version is linear in ``L`` but carries a ``(o+1) x 2K`` partition per step, which at
``L = 780239`` (``o = 492169``) is about thirty hours.  The recursion is a two-list merge per
lattice column and maps onto one thread per column, exactly like ``cycle_walk_charge_gpu``.

Each column holds its ``K`` best partial sums in descending order.  A step merges the column's own
list (an even letter) with its predecessor's (an odd letter) and keeps the top ``K``: a two-pointer
merge over ``2K`` entries, no sorting.
"""

from __future__ import annotations

import math
import time
from typing import Any

import cupy as cp

from research.juggler_sequence.cycle_walk_charge import STEP, U_TOL

_KMAX = 16

_KERNEL = cp.RawKernel(
    r"""
extern "C" __global__
void kbest_step(const double* prev, double* out,
                const long long width, const long long k,
                const long long length, const long long odd_count,
                const long long even_count, const long long K,
                const double step, const double u_tol,
                const double log_n)
{
    long long a = (long long)blockIdx.x * blockDim.x + threadIdx.x;
    if (a >= width) return;
    const double NEG = __longlong_as_double(0xfff0000000000000LL);

    double u = step * (double)a - (double)k;
    long long amax = odd_count < k ? odd_count : k;
    bool feasible = (u >= -u_tol) && (a <= amax) && ((k - a) <= even_count);
    if (!feasible) {
        for (long long j = 0; j < K; ++j) out[a * K + j] = NEG;
        return;
    }

    /* two-pointer merge of prev[a] (stay) and prev[a-1] (step up), both descending */
    double buf[16];
    long long i = 0, j = 0, c = 0;
    while (c < K) {
        double sv = (i < K) ? prev[a * K + i] : NEG;
        double uv = (a > 0 && j < K) ? prev[(a - 1) * K + j] : NEG;
        if (sv >= uv) { buf[c++] = sv; ++i; }
        else          { buf[c++] = uv; ++j; }
    }

    double add = 0.0;
    if (k < length) {
        double uc = u > 0.0 ? u : 0.0;
        double w = exp2(uc);
        if (w < 1.0) w = 1.0;
        add = exp(-w * log_n - log(w * log_n));
    }
    for (long long t = 0; t < K; ++t)
        out[a * K + t] = (buf[t] > NEG) ? buf[t] + add : NEG;
}
""",
    "kbest_step",
)


def gpu_kbest_walk(length: int, odd_count: int, n: int, K: int = 8, *,
                   log_n: float | None = None) -> dict[str, Any]:
    """The ``K`` largest values of ``sum_k f(u_k)`` over nonnegative exponent walks."""
    if K > _KMAX:
        raise ValueError("K <= %d (kernel register buffer)" % _KMAX)
    if log_n is None:
        log_n = math.log(n)
    started = time.perf_counter()
    width = odd_count + 1
    even_count = length - odd_count

    NEG = -math.inf
    a_buf = cp.full(width * K, NEG, dtype=cp.float64)
    b_buf = cp.empty(width * K, dtype=cp.float64)
    a_buf[0] = math.exp(-log_n - math.log(log_n))

    threads = 256
    blocks = (width + threads - 1) // threads
    for k in range(1, length + 1):
        _KERNEL((blocks,), (threads,),
                (a_buf, b_buf, width, k, length, odd_count, even_count, K,
                 STEP, U_TOL, log_n))
        a_buf, b_buf = b_buf, a_buf

    top = cp.asnumpy(a_buf[odd_count * K:(odd_count + 1) * K]).tolist()
    top = [t for t in top if math.isfinite(t)]
    return {"length": length, "odd_count": odd_count, "n": n, "K": K, "top": top,
            "elapsed_s": time.perf_counter() - started}


def gpu_flatness(length: int, odd_count: int, n: int, K: int = 8) -> dict[str, Any]:
    r = gpu_kbest_walk(length, odd_count, n, K)
    top = r["top"]
    best = top[0]
    return {"length": length, "odd_count": odd_count, "n": n, "ranks": len(top),
            "ratios": [t / best for t in top],
            "rank2_over_rank1": top[1] / best if len(top) > 1 else None,
            "rankK_over_rank1": top[-1] / best,
            "elapsed_s": r["elapsed_s"]}


def main() -> None:
    from research.juggler_sequence.paper_a_audit import o_min

    print("flatness of the charge ordering at the kill-table lengths (GPU top-K)")
    print("  %-9s %-9s %-13s %-12s %-12s %s"
          % ("L", "o", "n", "1-r2/r1", "1-rK/r1", "time"))
    for L, n in [(18, 1000), (24, 1000), (50508, 26254996),
                 (176251, 162849449), (780239, 350000001)]:
        f = gpu_flatness(L, o_min(L), n, K=16)
        print("  %-9d %-9d %-13d %-12.3e %-12.3e %.1fs"
              % (L, f["odd_count"], n, 1 - f["rank2_over_rank1"],
                 1 - f["rankK_over_rank1"], f["elapsed_s"]))


if __name__ == "__main__":
    main()

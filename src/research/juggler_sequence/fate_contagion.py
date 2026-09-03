"""Fate contagion: the two exact productions of a backward-closed set and their censuses.

A set ``A`` of Juggler starts is *backward-closed* when ``J(n) in A`` forces
``n in A``.  Every fate class is backward-closed: the starts that reach ``1``,
the starts that do not, the basin of any cycle, the divergent starts.  Two
productions generate new members from one member ``m``:

* ``E(m)``  : every even ``n`` with ``m^2 <= n < (m+1)^2``  (``J(n) = m``);
* ``OE(m)`` : every odd ``n`` with ``m^4 <= n^3 < (m+1)^4`` (the fiber
  ``floor(n^{3/4}) = m``) whose image ``floor(n^{3/2})`` is even
  (``J(J(n)) = m``).

The note ``docs/theory/juggler_fate_contagion_note.md`` proves that on every
fiber outside a thin exceptional set a positive proportion of the odd ``n``
have even ``floor(n^{3/2})`` (the sweep lemma), that over an even block of
``m`` the proportion averages to ``1/2`` (van der Corput), and that these two
facts close a recursion for the logarithmic counting function of ``A``:
``sum_{n in A, n <= x} 1/n >> (log x)^lambda`` for every ``lambda`` below an
explicit ``lambda*``.  This probe is the Phase-0 census behind those lemmas
and the certified closure of a Lean-verified seed.  Not a halt theorem.

Dossier: ``docs/problems/juggler_fate_contagion.md``.
"""

from __future__ import annotations

import json
import math
import time
from collections import Counter
from math import isqrt
from pathlib import Path
from typing import Any

import numpy as np

from research.juggler_sequence.cycle_finance import git_commit

DATA_DIR = Path(__file__).resolve().parents[3] / "data" / "research" / "juggler" / "fate_contagion"

#: Lean-verified seed: every start below 261 reaches 1
#: (``reachesOne_of_lt_two_hundred_sixty_one``).
LEAN_SEED = 260

CLASS_CONSISTENT = "FATE_CONTAGION_RECURSION_CONSISTENT"
CLASS_FALSIFIED = "FATE_CONTAGION_FALSIFIED"

# proved constants (see the note): sweep proportion 1/7, block average 1/4
SWEEP_PROPORTION = 1.0 / 7.0
GOOD_ALPHA_ZERO = 22.0  # |alpha| >= 22 m^{-1/3}
GOOD_ALPHA_HALF = 2.0  # |alpha - 1/2| >= 2 m^{-1/3}
SWEEP_M0 = 10**6


def juggler(m: int) -> int:
    return isqrt(m) if m % 2 == 0 else isqrt(m * m * m)


def icbrt(x: int) -> int:
    """floor cube root of a nonnegative integer."""

    if x <= 0:
        return 0
    r = int(round(x ** (1.0 / 3.0)))
    while r * r * r > x:
        r -= 1
    while (r + 1) ** 3 <= x:
        r += 1
    return r


def fiber_bounds(m: int) -> tuple[int, int]:
    """Odd ``n`` with ``m^4 <= n^3 < (m+1)^4`` are exactly ``lo <= n < hi``, ``n`` odd."""

    lo = icbrt(m**4)
    if lo**3 < m**4:
        lo += 1
    hi = icbrt((m + 1) ** 4)
    if hi**3 < (m + 1) ** 4:
        hi += 1
    if lo % 2 == 0:
        lo += 1
    return lo, hi


def fiber(m: int) -> list[int]:
    lo, hi = fiber_bounds(m)
    return list(range(lo, hi, 2))


def even_block(m: int) -> list[int]:
    return [n for n in range(m * m, (m + 1) * (m + 1)) if n % 2 == 0]


def circle_distance(x: float, c: float) -> float:
    return abs(((x - c) + 0.5) % 1.0 - 0.5)


def fiber_stats(m: int) -> dict[str, Any]:
    """Size ``H``, good count ``G`` (even ``isqrt(n^3)``), and the step ``alpha`` mod 1."""

    lo, hi = fiber_bounds(m)
    size = 0
    good = 0
    for n in range(lo, hi, 2):
        size += 1
        if isqrt(n**3) % 2 == 0:
            good += 1
    if size >= 2:
        d = ((lo + 2) ** 1.5 - lo**1.5) / 2.0
        alpha = d - math.floor(d)
    else:
        alpha = float("nan")
    return {"m": m, "size": size, "good": good, "alpha": alpha}


def is_good_fiber(m: int, alpha: float) -> bool:
    """The sweep-lemma hypothesis of the note (``m >= 10^6`` for the stated constants)."""

    scale = m ** (-1.0 / 3.0)
    return (
        circle_distance(alpha, 0.0) >= GOOD_ALPHA_ZERO * scale
        and circle_distance(alpha, 0.5) >= GOOD_ALPHA_HALF * scale
    )


def fiber_census(m_lo: int, m_hi: int) -> dict[str, Any]:
    """Census of ``G_m / H_m`` on ``m_lo <= m < m_hi``."""

    hist: Counter[float] = Counter()
    total_size = 0
    total_good = 0
    n_good_fibers = 0
    min_good_prop = 1.0
    min_good_witness: dict[str, Any] | None = None
    below_sweep_unflagged = 0
    n_bad = 0
    for m in range(m_lo, m_hi):
        st = fiber_stats(m)
        if st["size"] == 0:
            continue
        p = st["good"] / st["size"]
        hist[round(p, 1)] += 1
        total_size += st["size"]
        total_good += st["good"]
        good_fiber = is_good_fiber(m, st["alpha"])
        if good_fiber:
            n_good_fibers += 1
            if p < min_good_prop:
                min_good_prop = p
                min_good_witness = st
            if p < SWEEP_PROPORTION:
                below_sweep_unflagged += 1
        else:
            n_bad += 1
    return {
        "m_lo": m_lo,
        "m_hi": m_hi,
        "mean_proportion": total_good / total_size if total_size else None,
        "histogram": {str(k): v for k, v in sorted(hist.items())},
        "good_fibers": n_good_fibers,
        "bad_fibers": n_bad,
        "bad_fraction": n_bad / max(1, n_good_fibers + n_bad),
        "min_proportion_on_good_fibers": min_good_prop,
        "min_proportion_witness": min_good_witness,
        "good_fibers_below_sweep_bound": below_sweep_unflagged,
    }


def block_stats(mp: int) -> dict[str, Any]:
    """Joint parity count on the union of the fibers of the even block of ``mp``.

    ``U(mp) = {n odd in [mp^{8/3}, (mp+1)^{8/3}) : floor(n^{3/4}) even, floor(n^{3/2}) even}``;
    the note proves ``|U| = (1/4) #odd + O(mp^{11/9} log mp)``.
    """

    lo, _ = fiber_bounds(mp * mp)
    _, hi = fiber_bounds((mp + 1) * (mp + 1) - 1)
    total = 0
    both = 0
    for n in range(lo, hi, 2):
        total += 1
        k = isqrt(n**3)
        if k % 2 == 0 and isqrt(k) % 2 == 0:
            both += 1
    dev = both - total / 4.0
    return {
        "m_prime": mp,
        "odd_count": total,
        "both_even": both,
        "deviation": dev,
        "deviation_over_proved_scale": dev / (mp ** (11.0 / 9.0) * max(1.0, math.log(mp))),
        "deviation_over_sqrt": dev / math.sqrt(total) if total else 0.0,
    }


def _isqrt_vec(n: np.ndarray) -> np.ndarray:
    s = np.floor(np.sqrt(n.astype(np.float64))).astype(np.int64)
    s[s * s > n] -= 1
    s[(s + 1) * (s + 1) <= n] += 1
    return s


def _m_of_odd(n: np.ndarray) -> np.ndarray:
    f = n.astype(np.float64) ** 0.75
    m = np.floor(f).astype(np.int64)
    frac = f - m
    for i in np.nonzero((frac < 1e-6) | (frac > 1 - 1e-6))[0]:
        m[i] = isqrt(isqrt(int(n[i]) ** 3))
    return m


def _kpar_even_of_odd(n: np.ndarray) -> tuple[np.ndarray, int]:
    nf = n.astype(np.float64)
    f = nf * np.sqrt(nf)
    k = np.floor(f)
    frac = f - k
    tol = 0.02 * max(1.0, float(n.max()) / 1e9)
    amb = np.nonzero((frac < tol) | (frac > 1 - tol))[0]
    par = k.astype(np.int64) % 2 == 0
    for i in amb:
        par[i] = isqrt(int(n[i]) ** 3) % 2 == 0
    return par, int(len(amb))


def certified_closure(seed: int, limit: int, chunk: int = 50_000_000) -> tuple[np.ndarray, np.ndarray]:
    """Closure of ``[1, seed]`` under ``E`` and ``OE`` (and under ``E`` alone) up to ``limit``.

    Every element of the closure reaches ``1`` whenever every start ``<= seed`` does.
    """

    closed = np.zeros(limit + 1, dtype=bool)
    closed_e = np.zeros(limit + 1, dtype=bool)
    closed[1 : seed + 1] = True
    closed_e[1 : seed + 1] = True
    a = seed + 1
    while a <= limit:
        b = min(limit + 1, max(a + 1, int(a ** (4.0 / 3.0))))
        for a2 in range(a, b, chunk):
            b2 = min(b, a2 + chunk)
            n = np.arange(a2, b2, dtype=np.int64)
            even = n % 2 == 0
            ne = n[even]
            se = _isqrt_vec(ne)
            closed[ne] = closed[se]
            closed_e[ne] = closed_e[se]
            no = n[~even]
            if len(no):
                m = _m_of_odd(no)
                par, _ = _kpar_even_of_odd(no)
                closed[no] = par & closed[m]
        a = b
    return closed, closed_e


def closure_report(closed: np.ndarray, closed_e: np.ndarray, limit: int) -> dict[str, Any]:
    idx = np.arange(limit + 1, dtype=np.int64)
    inv = np.zeros(limit + 1)
    inv[1:] = 1.0 / idx[1:]
    blocks = []
    k = 1
    while 2**k < limit:
        lo, hi = 2**k, min(2 ** (k + 1), limit)
        blk = slice(lo + 1, hi + 1)
        cnt = int(closed[blk].sum())
        blocks.append(
            {
                "k": k,
                "density": cnt / (hi - lo),
                "density_e_only": int(closed_e[blk].sum()) / (hi - lo),
                "logmass": float(inv[blk][closed[blk]].sum()),
                "logmass_e_only": float(inv[blk][closed_e[blk]].sum()),
            }
        )
        k += 1
    x = limit
    r = math.sqrt(x)
    sel = (idx > r) & (idx <= x)
    ell = float(inv[sel][closed[sel]].sum())
    ell_even = float(inv[sel][closed[sel] & (idx[sel] % 2 == 0)].sum())
    ell_odd = ell - ell_even
    src_e = (idx > x**0.25) & (idx <= r)
    src_o = (idx > x**0.375) & (idx <= x**0.75)
    ell_src_e = float(inv[src_e][closed[src_e]].sum())
    ell_src_o = float(inv[src_o][closed[src_o]].sum())
    return {
        "limit": limit,
        "dyadic_blocks": blocks,
        "ell_sqrt_x_to_x": ell,
        "ell_even_part": ell_even,
        "ell_odd_part": ell_odd,
        "e_coefficient_realised": ell_even / ell_src_e if ell_src_e else None,
        "oe_coefficient_realised": ell_odd / ell_src_o if ell_src_o else None,
        "total_logmass": float(inv[1:][closed[1:]].sum()),
        "total_logmass_e_only": float(inv[1:][closed_e[1:]].sum()),
        "log_limit": math.log(limit),
    }


def type_decomposition(closed: np.ndarray, x: int) -> dict[str, Any]:
    """Exact decomposition of the closure's log-mass on ``(sqrt x, x]`` by first letters.

    Even members are the E-blocks of members at scale ``sqrt x``; odd members
    split into OE-type (``floor(n^{3/2})`` even, landing ``floor(n^{3/4})``) and
    OO-type (``floor(n^{3/2})`` odd, image at scale ``x^{3/2}``).  The OO-type
    share is compared with the *fair share*: the log-density of the closure's
    odd members on the image range ``(x^{3/4}, x^{3/2}]``.  Requires the
    closure array to extend to ``x^{3/2}``.
    """

    limit = len(closed) - 1
    assert x ** 1.5 <= limit + 1, "closure must extend to x^{3/2}"
    r = int(math.isqrt(x))
    n = np.arange(r + 1, x + 1, dtype=np.int64)
    inv = 1.0 / n
    inC = closed[n]
    odd = n % 2 == 1
    par, _ = _kpar_even_of_odd(n[odd])
    # OE-type / OO-type among odd n (all odd n, not only members)
    oe_mask = np.zeros(len(n), dtype=bool)
    oo_mask = np.zeros(len(n), dtype=bool)
    oe_mask[np.nonzero(odd)[0][par]] = True
    oo_mask[np.nonzero(odd)[0][~par]] = True
    ell_all = float(inv.sum())
    ell_even_C = float(inv[inC & ~odd].sum())
    ell_oe_C = float(inv[inC & oe_mask].sum())
    ell_oo_C = float(inv[inC & oo_mask].sum())
    ell_oe = float(inv[oe_mask].sum())
    ell_oo = float(inv[oo_mask].sum())
    # fair share of the OO-type members: odd log-density of the closure on the image range
    lo_img, hi_img = int(x ** 0.75), int(x ** 1.5)
    m = np.arange(lo_img + 1, hi_img + 1, dtype=np.int64)
    m_odd = m[m % 2 == 1]
    dens_odd_img = float((1.0 / m_odd[closed[m_odd]]).sum() / (1.0 / m_odd).sum())
    # fair share of the OE-type members: log-density of the closure on the landing range
    lo_l, hi_l = int(x ** 0.375), int(x ** 0.75)
    a = np.arange(lo_l + 1, hi_l + 1, dtype=np.int64)
    dens_land = float((1.0 / a[closed[a]]).sum() / (1.0 / a).sum())
    return {
        "x": x,
        "ell_range": ell_all,
        "ell_even_members": ell_even_C,
        "ell_oe_members": ell_oe_C,
        "ell_oo_members": ell_oo_C,
        "oe_share_of_members": ell_oe_C / ell_oe if ell_oe else None,
        "oe_fair_share": dens_land,
        "oo_share_of_members": ell_oo_C / ell_oo if ell_oo else None,
        "oo_fair_share": dens_odd_img,
        "oo_bias": (ell_oo_C / ell_oo - dens_odd_img) if ell_oo else None,
    }


def lambda_root(coefficients: list[tuple[float, float]]) -> float:
    """Root ``lambda`` of ``sum c_i e_i^lambda = 1`` for the recursion ``g(t) >= sum c_i g(e_i t)``."""

    def f(lam: float) -> float:
        return sum(c * e**lam for c, e in coefficients) - 1.0

    lo, hi = 0.0, 1.0
    if f(lo) <= 0:
        return 0.0
    for _ in range(200):
        mid = (lo + hi) / 2
        if f(mid) > 0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


RECURSIONS = {
    "elementary_sweep_only": [(1.0, 0.5), (2.0 / 21.0, 0.75)],
    "block_average_only": [(1.0, 0.5), (1.0 / 3.0, 3.0 / 8.0)],
    "block_average_plus_sweep": [(1.0, 0.5), (5.0 / 21.0, 3.0 / 8.0), (2.0 / 21.0, 0.75)],
    # + OOEEE production on even blocks (localized Paper B Theorem 4.7, note §7): coefficient
    # P_w / e_w = (1/16) / (9/16) = 1/9 at the root scale (9/32) t
    "block_sweep_plus_ooeee": [(1.0, 0.5), (5.0 / 21.0, 3.0 / 8.0), (2.0 / 21.0, 0.75), (1.0 / 9.0, 9.0 / 32.0)],
    # hypothetical: + OOOEE and OOEOE productions on even blocks (would need the kernel theorem,
    # Paper B Theorem 5.3 / 6.1, localized to |I| >= P^{23/32}; NOT proved, PARK): coefficient
    # (1/32) / (27/32) = 1/27 each at the root scale (27/64) t
    "hypothetical_kernel_localized": [
        (1.0, 0.5),
        (5.0 / 21.0, 3.0 / 8.0),
        (2.0 / 21.0, 0.75),
        (1.0 / 9.0, 9.0 / 32.0),
        (2.0 / 27.0, 27.0 / 64.0),
    ],
    "depth_two_ideal": [(1.0, 0.5), (1.0 / 3.0, 0.75)],
}


def summary(closure_limit: int = 10**8, dense_hi: int = 100_000) -> dict[str, Any]:
    t0 = time.time()
    fibers = {
        "dense": fiber_census(3375, dense_hi),
        "spot_1e6": fiber_census(10**6, 10**6 + 4000),
        "spot_1e7": fiber_census(10**7, 10**7 + 400),
    }
    blocks = [block_stats(mp) for mp in list(range(20, 40)) + list(range(200, 210)) + [1000, 3000]]
    closed, closed_e = certified_closure(LEAN_SEED, closure_limit)
    closure = closure_report(closed, closed_e, closure_limit)
    decomposition = [
        type_decomposition(closed, x) for x in (10**4, 10**5, 10**6) if x**1.5 <= closure_limit
    ]
    roots = {name: lambda_root(coeffs) for name, coeffs in RECURSIONS.items()}
    falsified = (
        any(f["good_fibers_below_sweep_bound"] > 0 for f in fibers.values() if f["m_lo"] >= SWEEP_M0)
        or max(abs(b["deviation_over_proved_scale"]) for b in blocks) > 1.0
    )
    return {
        "git_commit": git_commit(),
        "seed": LEAN_SEED,
        "classification": CLASS_FALSIFIED if falsified else CLASS_CONSISTENT,
        "fiber_census": fibers,
        "block_census": blocks,
        "block_max_deviation_over_proved_scale": max(abs(b["deviation_over_proved_scale"]) for b in blocks),
        "block_max_deviation_over_sqrt": max(abs(b["deviation_over_sqrt"]) for b in blocks),
        "closure": closure,
        "first_letter_decomposition": decomposition,
        "lambda_roots": roots,
        "elapsed_seconds": time.time() - t0,
    }


def main() -> None:
    import argparse

    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--closure-limit", type=float, default=1e8)
    parser.add_argument("--dense-hi", type=int, default=100_000)
    args = parser.parse_args()
    result = summary(int(args.closure_limit), args.dense_hi)
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    out = DATA_DIR / "summary.json"
    out.write_text(json.dumps(result, indent=2), encoding="utf-8")
    print(json.dumps({k: v for k, v in result.items() if k not in ("fiber_census", "block_census", "closure")}, indent=2))
    print("closure:", json.dumps({k: v for k, v in result["closure"].items() if k != "dyadic_blocks"}, indent=2))
    print("fiber dense mean:", result["fiber_census"]["dense"]["mean_proportion"])
    print("spot 1e6 min good proportion:", result["fiber_census"]["spot_1e6"]["min_proportion_on_good_fibers"])
    print(out)


if __name__ == "__main__":
    main()

"""Phase-0: can A^rest average even-share 1/2, lifting 0.448 to 0.4927?

Pairing is a uniform per-fiber 1/3. The depth-two ceiling 0.4927 is the
ideal-fiber equation (even-share 1/2 on the rest). This module tests
whether a backward-closed A can keep a definite log-mass of rest on
poor fibers, or whether the E+OE closure of those fibers drowns them.

No new production, no Lean, no Paper A, no N_0 raise.

Dossier: docs/problems/juggler_oe_rest_average.md.
"""

from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any

import numpy as np

from research.juggler_sequence.cycle_finance import git_commit
from research.juggler_sequence.fate_contagion import (
    _isqrt_vec,
    _kpar_even_of_odd,
    _m_of_odd,
    certified_closure,
    fiber_bounds,
    fiber_stats,
    lambda_root,
)

DATA_DIR = Path(__file__).resolve().parents[3] / "data" / "research" / "juggler" / "oe_rest_average"

CLASS_SHARP = "OE_REST_AVERAGE_SHARP"  # 2/9 is forced
CLASS_DROWNED = "OE_REST_AVERAGE_DROWNED"  # worst seeds still mix
CLASS_MIXED = "OE_REST_AVERAGE_MIXED"

POOR_SHARE = 0.40  # scarcer even-share at or below this is "poor"
IDEAL = [(1.0, 0.5), (1.0 / 3.0, 0.75)]
PAIRING = [(1.0, 0.5), (1.0 / 9.0, 3.0 / 8.0), (2.0 / 9.0, 0.75)]


def alpha_of(m: int) -> float:
    lo, hi = fiber_bounds(m)
    if hi - lo < 4:
        return float("nan")
    d = ((lo + 2) ** 1.5 - lo ** 1.5) / 2.0
    return d - math.floor(d)


def exact_even_share(m: int) -> float:
    """Exact G_m/H_m (even floor(n^{3/2}) along the OE fiber)."""

    st = fiber_stats(m)
    if st["size"] < 4:
        return float("nan")
    return st["good"] / st["size"]


def is_low_even(share: float, cutoff: float = POOR_SHARE) -> bool:
    """One-sided adversary: the even half is the scarcer one."""

    return share == share and share <= cutoff


def poor_mask(limit: int, cutoff: float = POOR_SHARE) -> np.ndarray:
    """Seed set: m with exact even-share ≤ cutoff."""

    out = np.zeros(limit + 1, dtype=bool)
    for m in range(3, limit + 1):
        out[m] = is_low_even(exact_even_share(m), cutoff)
    return out


def dyadic_logmass(mask: np.ndarray, lo: int, hi: int) -> dict[str, float]:
    hi = min(hi, len(mask) - 1)
    lo = max(lo, 1)
    if hi <= lo:
        return {"ell_all": 0.0, "ell_set": 0.0, "fraction": 0.0, "n_set": 0}
    idx = np.arange(lo, hi + 1, dtype=np.int64)
    inv = 1.0 / idx
    sel = mask[idx]
    ell_all = float(inv.sum())
    ell_set = float(inv[sel].sum())
    return {
        "ell_all": ell_all,
        "ell_set": ell_set,
        "fraction": ell_set / ell_all if ell_all else 0.0,
        "n_set": int(sel.sum()),
    }


def close_from_mask(seeds: np.ndarray, limit: int, chunk: int = 200_000) -> np.ndarray:
    """E+OE closure of a seed mask, same upward sweep as ``certified_closure``."""

    closed = np.zeros(limit + 1, dtype=bool)
    cap = min(len(seeds) - 1, limit)
    closed[1 : cap + 1] = seeds[1 : cap + 1]
    a = 2
    while a <= limit:
        b = min(limit + 1, max(a + 1, int(a ** (4.0 / 3.0))))
        for a2 in range(a, b, chunk):
            b2 = min(b, a2 + chunk)
            n = np.arange(a2, b2, dtype=np.int64)
            even = n % 2 == 0
            ne = n[even]
            if len(ne):
                se = _isqrt_vec(ne)
                closed[ne] = closed[ne] | closed[se]
            no = n[~even]
            if len(no):
                m = _m_of_odd(no)
                par, _ = _kpar_even_of_odd(no)
                closed[no] = closed[no] | (par & closed[m])
        a = b
    return closed


def rest_stats(closed: np.ndarray, x: int, sample: int = 120) -> dict[str, Any]:
    """A^rest = odd members of A in (x^{3/8}, x^{3/4}]."""

    lo = max(3, int(x**0.375))
    hi = min(len(closed) - 1, int(x**0.75))
    if hi <= lo:
        return {"x": x, "ell_rest": 0.0, "ell_range": 0.0}
    idx = np.arange(lo, hi + 1, dtype=np.int64)
    inv = 1.0 / idx
    in_a = closed[idx]
    odd = idx % 2 == 1
    rest = in_a & odd
    evens = in_a & ~odd
    ell_rest = float(inv[rest].sum())
    ell_range = float(inv[in_a].sum())
    ell_even = float(inv[evens].sum())
    members = idx[rest]
    if len(members) == 0:
        return {
            "x": x,
            "ell_rest": 0.0,
            "ell_range": ell_range,
            "ell_even": ell_even,
            "rest_over_range": 0.0,
            "n_rest": 0,
        }
    step = max(1, len(members) // sample)
    sample_m = members[::step][:sample]
    shares = []
    poor = 0
    weight_share = 0.0
    weight = 0.0
    for m in sample_m:
        sh = exact_even_share(int(m))
        if sh != sh:
            continue
        w = 1.0 / float(m)
        shares.append(sh)
        weight_share += sh * w
        weight += w
        if is_low_even(sh):
            poor += 1
    mean = weight_share / weight if weight else None
    return {
        "x": x,
        "ell_rest": ell_rest,
        "ell_range": ell_range,
        "ell_even": ell_even,
        "rest_over_range": ell_rest / ell_range if ell_range else 0.0,
        "n_rest": int(len(members)),
        "sample": int(len(shares)),
        "weighted_even_share": mean,
        "sample_mean_even_share": float(np.mean(shares)) if shares else None,
        "sample_mean_scarcer": float(np.mean([min(s, 1.0 - s) for s in shares])) if shares else None,
        "sample_poor_fraction": poor / len(shares) if shares else None,
    }


def odd_dyadic_share(closed: np.ndarray, lo: int, hi: int, sample: int = 150) -> dict[str, Any]:
    """Weighted even-share of odd members of A in [lo, hi]."""

    hi = min(hi, len(closed) - 1)
    lo = max(lo, 3)
    idx = np.arange(lo, hi + 1, dtype=np.int64)
    odd_a = idx[(idx % 2 == 1) & closed[idx]]
    if len(odd_a) == 0:
        return {"lo": lo, "hi": hi, "n_odd": 0, "ell": 0.0}
    inv = 1.0 / odd_a.astype(np.float64)
    ell = float(inv.sum())
    step = max(1, len(odd_a) // sample)
    sample_m = [int(m) for m in odd_a[::step][:sample]]
    pairs = [(m, exact_even_share(m)) for m in sample_m]
    pairs = [(m, s) for m, s in pairs if s == s]
    if not pairs:
        return {"lo": lo, "hi": hi, "n_odd": int(len(odd_a)), "ell": ell}
    shares = [s for _, s in pairs]
    w = [1.0 / float(m) for m, _ in pairs]
    wmean = sum(s * ww for s, ww in zip(shares, w)) / sum(w)
    return {
        "lo": lo,
        "hi": hi,
        "n_odd": int(len(odd_a)),
        "ell": ell,
        "weighted_even_share": wmean,
        "mean_even_share": float(np.mean(shares)),
        "low_even_fraction": sum(1 for s in shares if is_low_even(s)) / len(shares),
        "sample": len(shares),
    }


def child_phase_mixing(m_lo: int, m_hi: int, cutoff: float = POOR_SHARE) -> dict[str, Any]:
    """β(m) = {(3/2) m^{8/9}} on poor parents: should be equidistributed."""

    bins = np.zeros(10, dtype=int)
    n_poor = 0
    for m in range(m_lo, m_hi):
        if not is_low_even(exact_even_share(m), cutoff):
            continue
        n_poor += 1
        beta = (1.5 * (m ** (8.0 / 9.0))) % 1.0
        bins[min(9, int(beta * 10))] += 1
    expected = n_poor / 10.0 if n_poor else 0.0
    tv = 0.5 * float(np.abs(bins - expected).sum() / n_poor) if n_poor else None
    return {
        "m_lo": m_lo,
        "m_hi": m_hi,
        "n_poor": n_poor,
        "beta_bins": [int(v) for v in bins],
        "total_variation_from_uniform": tv,
    }


def model_matches_fiber(m: int) -> dict[str, Any]:
    st = fiber_stats(m)
    exact = st["good"] / st["size"] if st["size"] else float("nan")
    return {
        "m": m,
        "exact": exact,
        "alpha": alpha_of(m),
        "low_even": is_low_even(exact),
    }


def classify(
    poor_fractions: list[float],
    rest_poor: dict[str, Any],
    rest_thick: dict[str, Any],
    dyadic_last: dict[str, Any] | None = None,
    descendants: dict[str, Any] | None = None,
) -> str:
    """Sharp / drowned / mixed from the planted A and the capped-seed descendants."""

    min_poor_frac = min(poor_fractions) if poor_fractions else 0.0
    if min_poor_frac < 0.02:
        return CLASS_MIXED
    share = (dyadic_last or rest_poor).get("weighted_even_share")
    desc = (descendants or {}).get("weighted_even_share")
    thick_share = rest_thick.get("weighted_even_share")
    if desc is not None and 0.45 <= desc <= 0.55 and share is not None and share <= 0.38:
        return CLASS_MIXED
    if share is not None and share <= 0.36:
        return CLASS_SHARP
    if share is not None and 0.45 <= share <= 0.55 and thick_share is not None and 0.45 <= thick_share <= 0.55:
        return CLASS_DROWNED
    return CLASS_MIXED


def summary(limit: int = 80_000) -> dict[str, Any]:
    poor = poor_mask(limit)
    dyads = []
    for k in range(8, int(math.log2(limit))):
        lo, hi = 2**k, min(2 ** (k + 1) - 1, limit)
        rec = dyadic_logmass(poor, lo, hi)
        rec["k"] = k
        dyads.append(rec)
    closed_poor = close_from_mask(poor, limit)
    closed_thick, _ = certified_closure(260, limit)
    xs = [x for x in (8_000, 20_000, 50_000, 80_000) if int(x**0.75) <= limit]
    rest_poor = [rest_stats(closed_poor, x) for x in xs]
    rest_thick = [rest_stats(closed_thick, x) for x in xs]
    mixing = child_phase_mixing(3_000, 8_000)
    dyadic_poor_odds = []
    u = 256
    while u * 2 <= limit:
        dyadic_poor_odds.append(odd_dyadic_share(closed_poor, u, min(2 * u - 1, limit)))
        u *= 2
    seed_cap = min(3_000, limit // 8)
    seeds_capped = np.zeros(limit + 1, dtype=bool)
    seeds_capped[1 : seed_cap + 1] = poor[1 : seed_cap + 1]
    closed_capped = close_from_mask(seeds_capped, limit)
    descendant_lo = seed_cap * 2
    descendants = odd_dyadic_share(closed_capped, descendant_lo, limit)
    witnesses = [model_matches_fiber(m) for m in (1003635, 3375, 10_000) if m <= 10**7]
    roots = {
        "pairing": lambda_root(PAIRING),
        "ideal": lambda_root(IDEAL),
    }
    decision = classify(
        [d["fraction"] for d in dyads if d["ell_all"] > 0.2],
        rest_poor[-1] if rest_poor else {},
        rest_thick[-1] if rest_thick else {},
        dyadic_last=dyadic_poor_odds[-1] if dyadic_poor_odds else None,
        descendants=descendants,
    )
    return {
        "git_commit": git_commit(),
        "limit": limit,
        "poor_cutoff": POOR_SHARE,
        "classification": decision,
        "poor_dyadic": dyads,
        "poor_logmass_fraction_min": min((d["fraction"] for d in dyads if d["ell_all"] > 0.2), default=None),
        "rest_closure_of_poor": rest_poor,
        "rest_thick_control": rest_thick,
        "child_phase_mixing": mixing,
        "odd_dyadic_closure_of_poor": dyadic_poor_odds,
        "seed_cap": seed_cap,
        "descendants_above_capped_seeds": descendants,
        "model_vs_fiber": witnesses,
        "lambda_roots": roots,
        "n_poor": int(poor.sum()),
        "n_closed_poor": int(closed_poor.sum()),
        "n_closed_thick": int(closed_thick.sum()),
    }


def main() -> None:
    result = summary()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    out = DATA_DIR / "summary.json"
    out.write_text(json.dumps(result, indent=2), encoding="utf-8")
    print(json.dumps({k: v for k, v in result.items() if k != "poor_dyadic"}, indent=2))
    print(out)


if __name__ == "__main__":
    main()

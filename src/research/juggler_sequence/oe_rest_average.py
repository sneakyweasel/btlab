"""Phase-0: can A^rest average even-share 1/2, lifting 0.448 to 0.4927?

Pairing is a uniform per-fiber 1/3. The depth-two ceiling 0.4927 is the
ideal-fiber equation (even-share 1/2 on the rest). This module tests
whether a backward-closed A can keep a definite log-mass of rest on
poor fibers, or whether the E+OE closure of those fibers drowns them.

No new production, no Lean, no Paper A, no N_0 raise.

Dossier: docs/problems/juggler_oe_rest_average.md.
"""

from __future__ import annotations

from research.juggler_sequence.lean_paths import (
    DATA_ROOT,
)

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
    fiber_alpha,
    fiber_bounds,
    fiber_stats,
    lambda_root,
)

DATA_DIR = DATA_ROOT / "oe_rest_average"

CLASS_SHARP = "OE_REST_AVERAGE_SHARP"  # 2/9 is forced
CLASS_DROWNED = "OE_REST_AVERAGE_DROWNED"  # worst seeds still mix
CLASS_MIXED = "OE_REST_AVERAGE_MIXED"

POOR_SHARE = 0.40  # scarcer even-share at or below this is "poor"
IDEAL = [(1.0, 0.5), (1.0 / 3.0, 0.75)]
PAIRING = [(1.0, 0.5), (1.0 / 9.0, 3.0 / 8.0), (2.0 / 9.0, 0.75)]


def alpha_of(m: int) -> float:
    """The fiber step, delegated to the exact implementation.

    This used to carry its own copy of the float expression
    `((lo+2)**1.5 - lo**1.5) / 2.0`, which subtracts two numbers of size
    `lo^(3/2)` and then takes the fractional part of the difference. That is
    noise above `m ~ 1e7` and returns exactly `0.0` at `1e8`; see `fiber_alpha`.
    """
    lo, hi = fiber_bounds(m)
    if hi - lo < 4:
        return float("nan")
    return fiber_alpha(lo)


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

def averaging_payoff() -> dict[str, Any]:
    """What reopening this branch would be worth, priced on the two-production route.

    The park decision was weighed against "a better exponent", and on that
    measure it was right. But the two-production inequality
    `2^-L + c (3/4)^L = 1` is the whole unconditional chain, and its root moves
    steeply in `c`:

        c = 2/9    = 0.222222   share 1/3      root 0.326121   pointwise-sharp
        c = 0.300               share 0.450    root 0.442499
        c = 0.320               share 0.480    root 0.472576
        c = 1/3    = 0.333333   share 1/2      root 0.492658   the mean share

    The coefficient that matches `lambda** = 0.492572` on two productions alone
    is `0.3332760`, a parity share of `0.4999140` -- essentially the mean. So if
    an averaged argument delivered the effective share as the MEAN rather than
    the pointwise worst case, two productions would reach the headline exponent
    and the block-average family and the six-word ladder would both be
    unnecessary for it. That would take Proposition 4.4's two exponential-sum
    bounds off the critical path: the analytic core of Paper C, absent from
    `formal/`, and its largest unformalized gap.

    So the prize is not a better number. It is the same number with the
    analytic core removed, which is a different kind of prize from the one the
    park decision was weighed against.

    The target is narrow, and this is the half that vindicates the park. An
    intermediate coefficient is not automatically progress: the break-even
    against the three-production base `0.448017`, which the block average
    already gives, is `c = 0.3036722`, a share of `0.4555`. Anything an
    averaged argument delivers below that share is a REGRESSION, and it must
    reach `0.4999` to match `lambda**`. Recovering "not the worst case" is
    worthless here; only "essentially the mean" pays.

    Quantification contributed by a peer session and reproduced here.
    """
    two = lambda c: lambda_root([(1.0, 0.5), (c, 0.75)])
    base = lambda_root(PAIRING)
    ladder = PAIRING + [(3.0 ** -(k + 1), 0.5 * 0.75**k) for k in range(2, 7)]
    lam_star = lambda_root(ladder)

    def invert(target: float) -> float:
        lo_c, hi_c = 0.01, 1.0
        for _ in range(200):
            mid = (lo_c + hi_c) / 2.0
            if two(mid) < target:
                lo_c = mid
            else:
                hi_c = mid
        return (lo_c + hi_c) / 2.0

    break_even = invert(base)
    matches = invert(lam_star)
    return {
        "two_production_curve": [
            {"coefficient": c, "share": 1.5 * c, "root": two(c)}
            for c in (2.0 / 9.0, 0.30, 0.32, 1.0 / 3.0)
        ],
        "three_production_base": base,
        "lambda_star_star": lam_star,
        "break_even_coefficient": break_even,
        "break_even_share": 1.5 * break_even,
        "matching_coefficient": matches,
        "matching_share": 1.5 * matches,
        "prize": (
            "not a better exponent -- the same exponent with Proposition 4.4's"
            " two exponential-sum bounds off the critical path, which is Paper"
            " C's largest unformalized gap"
        ),
        "why_the_park_still_stands": (
            "the target is narrow: an averaged argument must clear share"
            " 0.4555 merely to beat what the block average already gives, and"
            " reach 0.4999 to match lambda**. Only 'essentially the mean' pays"
        ),
    }

# ---------------------------------------------------------------------------
# Where the missing lemma sits relative to Hypothesis FD.
#
# The capacity-decay observation needs an equidistribution statement about the
# fibre step alpha_m across m. The question that decides whether the route is
# worth anything is whether that statement is Hypothesis FD in disguise -- in
# which case the bootstrap trades two exponential-sum bounds for an open
# hypothesis and buys nothing -- or strictly weaker.
#
# It is strictly weaker, and the reason is that m ranges over the integers
# rather than along an orbit.
# ---------------------------------------------------------------------------

WEYL_EXPONENT = 2.0 / 3.0
WEYL_COEFFICIENT = 1.5


def weyl_step(m: int) -> float:
    """`frac((3/2) m^(2/3))`, the classical sequence `alpha_m` tracks."""
    return (WEYL_COEFFICIENT * m ** WEYL_EXPONENT) % 1.0


def step_is_weyl(scales: tuple[int, ...] = (10**5, 10**6, 10**7, 10**8, 10**9)
                 ) -> dict[str, Any]:
    """`alpha_m = frac((3/2) m^(2/3)) + O(m^(-2/3))`, measured.

    The fibre step is defined as a difference of `3/2` powers at the fibre's
    endpoints, but asymptotically it is just the derivative, and the derivative
    of `n^(3/2)/2` at `n = m^(4/3)` is `(3/2) m^(2/3)`. The residual is the
    curvature across one fibre step and falls like `m^(-2/3)`.
    """
    rows = []
    for m in scales:
        lo, _ = fiber_bounds(m)
        got, want = fiber_alpha(lo), weyl_step(m)
        gap = abs(got - want)
        rows.append({"m": m, "alpha": got, "weyl": want,
                     "circle_gap": min(gap, 1.0 - gap)})
    return {
        "rows": rows,
        "gap_falls": all(a["circle_gap"] > b["circle_gap"]
                         for a, b in zip(rows, rows[1:])),
    }


def weyl_discrepancy(limit: int, bins: int = 200) -> float:
    """Star discrepancy of `frac((3/2) m^(2/3))` on `1 <= m <= limit`."""
    counts = [0] * bins
    for m in range(1, limit + 1):
        counts[int(weyl_step(m) * bins) % bins] += 1
    running = 0
    worst = 0.0
    for i, c in enumerate(counts):
        running += c
        worst = max(worst, abs(running / limit - (i + 1) / bins))
    return worst


def fd_placement(exponents: tuple[int, ...] = (4, 5, 6, 7)) -> dict[str, Any]:
    """The placement, which is the answer to whether the averaging route is real.

    **It is not Hypothesis FD.** FD asks for joint equidistribution of the
    parity words along a Juggler ORBIT -- the fractional parts of `n^(3/2)`,
    `n^(3/4)` and their relatives evaluated at orbit points -- and it is open
    precisely because an orbit is not an arithmetic sequence. The capacity-decay
    lemma asks about `alpha_m` as `m` runs over ALL integers in a dyadic block.
    That is a Weyl problem about an explicit algebraic function of `m`:

    - `f(m) = (3/2) m^(2/3)` has `f -> infinity`, `f'(m) = m^(-1/3) -> 0`
      monotonically, and `m f'(m) = m^(2/3) -> infinity`. Those are exactly
      Fejer's conditions, so `frac(f(m))` is equidistributed UNCONDITIONALLY.
    - the rate is polynomial by van der Corput; measured here the star
      discrepancy falls about like `N^(-1/2)`.

    So the first ingredient of the missing lemma is a theorem, not a hypothesis,
    and the bootstrap is not trading one open problem for another.

    WHAT IS STILL OPEN, and it is not small. The share is not a function of
    `alpha_m` alone: `J-oe-fiber-share-law` gives
    `G_m/H_m = S(beta_m, theta_m) + O(H^(-1/2) + (1+|beta|)/H)` with
    `beta_m = alpha_m (H_m - 1)` and `theta_m` a second phase. So what the
    lemma actually needs is the JOINT distribution of `(beta_m, theta_m)`.
    Both coordinates are Weyl-type sequences in `m` rather than orbit
    quantities, which is the point: the open part is a Weyl-sums question about
    explicit functions, of the kind the laboratory's own Lemma 4.1' and
    Corollary 4.6 already handle in pieces, and not the orbit-equidistribution
    question that FD is.
    """
    rows = [{"limit": 10**e, "discrepancy": weyl_discrepancy(10**e)}
            for e in exponents]
    slopes = [math.log10(b["discrepancy"] / a["discrepancy"])
              for a, b in zip(rows, rows[1:])]
    return {
        "step_is_weyl": step_is_weyl(),
        "discrepancy": rows,
        "slopes_per_decade": slopes,
        "decays_polynomially": all(s < -0.25 for s in slopes),
        "verdict": (
            "below Hypothesis FD: equidistribution of alpha_m is Fejer,"
            " unconditional, with polynomial discrepancy by van der Corput."
            " The open part is the JOINT law of (beta_m, theta_m), still a"
            " Weyl-sums question about explicit functions of m and not an"
            " orbit-equidistribution question"
        ),
    }

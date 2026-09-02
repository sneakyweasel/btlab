"""Rate-free reduction of the K3 wall: exact profiles and tower census.

Not a K3 bound, not a density-one claim, not a Paper B edit, and not
a reopen of the parked toolkit line (BB/GG/JJ stay final).

The branch records two human lemmas and one re-aimed target:

1. **Rate-free reduction** (corollary of Proposition J,
   `J-equidistribution-implies-density-one`): the non-certified count
   obeys  #(no contracting prefix of length <= d) <= e^{-cd} N
   + 2^d E_d(N)  with c = 2(log2/log3 - 1/2)^2.  Fixing d and letting
   N -> infinity FIRST, per-fixed-depth *qualitative* equidistribution
   (E_d(N) = o(N) for each d separately, no rate) already gives upper
   density <= e^{-cd} for every d, hence density-one finite descent.
   Power savings — the only thing BB/GG/JJ obstruct — is not needed.

2. **Biased-split reduction**: full equidistribution is also not
   needed.  If for each fixed depth every surviving class sends at
   most a (1-beta) fraction to the O-child (rate-free), with
   beta > beta* = 1 - log2/log3 = 0.36907...,  then the never-
   contracting measure at depth d is <= exp(-D(gamma || 1-beta) d)
   (Chernoff on the dominated generating function,
   gamma = log2/log3), and density-one descent follows the same way.

The certificate side is Lean (`power_bound_word`: a prefix with
3^{a_k} < 2^k forces x_k <= n^{3^a/2^k} < n — descent below start,
unconditionally).  The measure side is classical.

Exact contents of this probe:

- `never_negative_profile`: exact DP count C_d of length-d parity
  words with no exponent-negative prefix (3^{a_k} >= 2^k for all
  k <= d).  Under per-depth equidistribution the non-certified density
  at depth d is exactly C_d / 2^d; the profile is the true decay that
  Proposition J's Hoeffding bound e^{-cd} majorizes.
- `biased_adversary_profile`: the exact worst-case never-negative
  measure when an adversary pushes every O-share to the cap (1-beta),
  compared against the Chernoff bound; confirms the threshold
  beta* = 1 - log2/log3.
- `tower_census`: exact joint bin counts of the level tower
  ({n^{3/2}}, {v^{3/2}}, {z^{3/2}}) on the 3-torus (integer-only
  binning via isqrt: floor(8 frac(x^{3/2})) = isqrt(64 x^3)
  - 8 isqrt(x^3)), plus the OOOO-conditioned fifth-letter split —
  the rate-free target's empirical face.

Float logarithms are diagnostic; word counts, bins, and parities are
exact integer arithmetic.  The re-aimed target is recorded as
`conjectures/active/juggler_tower_rate_free_equidistribution.json`.
"""

from __future__ import annotations

import json
import math
from math import isqrt
from pathlib import Path
from typing import Any

from research.juggler_sequence.lean_paths import (
    LAYERS,
    has_named,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM

REPO_ROOT = Path(__file__).resolve().parents[3]
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "k3_rate_free"
JSON_PATH = DATA_DIR / "summary.json"

LOG2_3 = math.log2(3.0)
GAMMA = math.log(2.0) / math.log(3.0)  # 0.63092... odd fraction floor
BETA_STAR = 1.0 - GAMMA  # 0.36907... contraction threshold for E-share
HOEFFDING_C = 2.0 * (GAMMA - 0.5) ** 2  # Proposition J's constant

PROFILE_DEPTH = 200
TEST_PROFILE_DEPTH = 40
TOWER_WINDOW = 2_000_000
TEST_TOWER_WINDOW = 40_000
BETAS = (0.37, 0.40, 0.45, 0.50)

CLASS_GREEN = "K3_RATE_FREE_GREEN"
CLASS_VIOLATED = "K3_RATE_FREE_VIOLATED"

ANTI = {
    **ANTI_OVERCLAIM,
    "k3_bound_claimed": False,
    "density_one_claimed": False,
    "toolkit_reopened": False,
    "paper_b_modified": False,
    "ergodic_theorem_claimed": False,
}

REQUIRED_LEAN = (
    ("Envelope", "power_bound_word"),
    ("Envelope", "cycle_strict_envelope"),
)


def o_min_table(d_max: int) -> list[int]:
    """o_min(k) = min{a : 3^a >= 2^k}, exact big-int comparisons."""

    table = [0]
    a = 0
    pow3 = 1
    pow2 = 1
    for _k in range(1, d_max + 1):
        pow2 *= 2
        while pow3 < pow2:
            a += 1
            pow3 *= 3
        table.append(a)
    return table


def never_negative_profile(d_max: int = PROFILE_DEPTH) -> dict[str, Any]:
    """Exact count C_d of length-d words with 3^{a_k} >= 2^k at every k.

    Under per-depth equidistribution the never-contracting density at
    depth d equals C_d / 2^d.  Proposition J majorizes it by e^{-cd}.
    """

    omin = o_min_table(d_max)
    # states: odd count a at step k, a in [omin(k), k]
    counts: dict[int, int] = {0: 1}
    rows = []
    for k in range(1, d_max + 1):
        nxt: dict[int, int] = {}
        for a, c in counts.items():
            for a2 in (a + 1, a):  # O then E
                if a2 >= omin[k]:
                    nxt[a2] = nxt.get(a2, 0) + c
        counts = nxt
        total = sum(counts.values())
        if k % 10 == 0 or k == d_max:
            ratio = total / 2**k
            rows.append(
                {
                    "d": k,
                    "count": total,
                    "ratio": ratio,
                    "hoeffding": math.exp(-HOEFFDING_C * k),
                    "rate": -math.log(ratio) / k if ratio > 0 else None,
                }
            )
    ratios = [r["ratio"] for r in rows]
    return {
        "d_max": d_max,
        "rows": rows,
        "monotone_decreasing": all(
            ratios[i + 1] <= ratios[i] for i in range(len(ratios) - 1)
        ),
        "hoeffding_majorizes": all(r["ratio"] <= r["hoeffding"] for r in rows),
        "hoeffding_c": HOEFFDING_C,
    }


def biased_adversary_profile(
    d_max: int = PROFILE_DEPTH, betas: tuple[float, ...] = BETAS
) -> dict[str, Any]:
    """Worst-case never-negative measure under an O-share cap of 1-beta.

    The adversary maximizes the never-contracting measure by putting
    the full allowed (1-beta) on every O-branch; the exact DP value is
    compared to the Chernoff/relative-entropy bound
    exp(-D(gamma || 1-beta) d), positive iff beta > beta*.
    """

    omin = o_min_table(d_max)
    out = []
    for beta in betas:
        p_odd = 1.0 - beta
        meas: dict[int, float] = {0: 1.0}
        for k in range(1, d_max + 1):
            nxt: dict[int, float] = {}
            for a, m in meas.items():
                if a + 1 >= omin[k]:
                    nxt[a + 1] = nxt.get(a + 1, 0.0) + m * p_odd
                if a >= omin[k]:
                    nxt[a] = nxt.get(a, 0.0) + m * beta
            meas = nxt
        total = sum(meas.values())
        if 0.0 < p_odd < 1.0 and 0.0 < GAMMA < 1.0:
            dkl = GAMMA * math.log(GAMMA / p_odd) + (1.0 - GAMMA) * math.log(
                (1.0 - GAMMA) / beta
            )
        else:
            dkl = None
        out.append(
            {
                "beta": beta,
                "survivor_measure": total,
                "chernoff": math.exp(-dkl * d_max) if dkl is not None else None,
                "kl_rate": dkl,
                "empirical_rate": -math.log(total) / d_max if total > 0 else None,
                "decays": total < 1.0,
            }
        )
    return {
        "d_max": d_max,
        "beta_star": BETA_STAR,
        "rows": out,
        "all_supercritical_decay": all(
            r["decays"] for r in out if r["beta"] > BETA_STAR
        ),
    }


def _frac_bin(x: int, bins: int) -> int:
    """floor(bins * frac(x^{3/2})) exactly: isqrt(bins^2 x^3) - bins*isqrt(x^3)."""

    cube = x * x * x
    return isqrt(bins * bins * cube) - bins * isqrt(cube)


def tower_census(n_max: int = TOWER_WINDOW, bins: int = 8) -> dict[str, Any]:
    """Exact joint bin census of the floor-power tower, plus OOOO split.

    Dyadic window n in (n_max/2, n_max] (matching K3's n ~ P
    convention; small n carry genuine tower correlations that only
    die asymptotically).  For odd n: v = floor(n^{3/2}),
    z = floor(v^{3/2}); the triple ({n^{3/2}}, {v^{3/2}}, {z^{3/2}})
    is binned exactly.  The fifth letter of the OOOO cell is the
    parity of floor(x3^{3/2}) along the all-odd branch
    (x1 = v odd, x2 = z odd, x3 odd).
    """

    hist: dict[tuple[int, int, int], int] = {}
    total = 0
    oooo = 0
    oooo_even_fifth = 0
    n_min = n_max // 2
    start = n_min + 1 if (n_min + 1) % 2 == 1 else n_min + 2
    for n in range(start, n_max + 1, 2):
        b1 = _frac_bin(n, bins)
        v = isqrt(n * n * n)
        b2 = _frac_bin(v, bins)
        z = isqrt(v * v * v)
        b3 = _frac_bin(z, bins)
        key = (b1, b2, b3)
        hist[key] = hist.get(key, 0) + 1
        total += 1
        if v % 2 == 1 and z % 2 == 1:
            x3 = isqrt(z * z * z)
            if x3 % 2 == 1:
                oooo += 1
                x4 = isqrt(x3 * x3 * x3)
                if x4 % 2 == 0:
                    oooo_even_fifth += 1
    cells = bins**3
    expected = total / cells
    max_dev = max(abs(hist.get(k, 0) - expected) for k in _all_keys(bins))
    split = oooo_even_fifth / oooo if oooo else None
    # extreme-value allowance for the max of `cells` near-Gaussian
    # deviations: sqrt(2 ln cells) + 1.5 standard deviations
    dev_cap = (
        (math.sqrt(2.0 * math.log(cells)) + 1.5) * math.sqrt(cells / total)
        if total
        else None
    )
    return {
        "n_max": n_max,
        "bins": bins,
        "samples": total,
        "occupied_cells": len(hist),
        "max_abs_dev": max_dev,
        "max_rel_dev": max_dev / expected if expected else None,
        "rel_dev_cap": dev_cap,
        "oooo_count": oooo,
        "oooo_even_fifth_share": split,
        "split_three_sigma": (
            3.0 / (2.0 * math.sqrt(oooo)) if oooo else None
        ),
    }


def _all_keys(bins: int):
    for i in range(bins):
        for j in range(bins):
            for k in range(bins):
                yield (i, j, k)


def lean_wired() -> dict[str, bool]:
    texts = {
        module: LAYERS[module].read_text(encoding="utf-8")
        for module in {m for m, _ in REQUIRED_LEAN}
    }
    return {
        f"{module}.{name}": has_named(texts[module], name)
        for module, name in REQUIRED_LEAN
    }


def classify(summary: dict[str, Any]) -> str:
    prof = summary["never_negative"]
    biased = summary["biased_adversary"]
    tower = summary["tower"]
    split_ok = (
        tower["oooo_even_fifth_share"] is not None
        and abs(tower["oooo_even_fifth_share"] - 0.5) <= tower["split_three_sigma"]
    )
    ok = (
        prof["monotone_decreasing"]
        and prof["hoeffding_majorizes"]
        and biased["all_supercritical_decay"]
        and tower["occupied_cells"] == tower["bins"] ** 3
        and tower["max_rel_dev"] is not None
        and tower["max_rel_dev"] <= tower["rel_dev_cap"]
        and split_ok
        and all(summary["lean"].values())
    )
    return CLASS_GREEN if ok else CLASS_VIOLATED


def build_summary(
    *,
    d_max: int = PROFILE_DEPTH,
    n_max: int = TOWER_WINDOW,
) -> dict[str, Any]:
    summary: dict[str, Any] = {
        "experiment": "juggler_k3_rate_free",
        "anti_overclaim": ANTI,
        "constants": {
            "gamma_log2_log3": GAMMA,
            "beta_star": BETA_STAR,
            "hoeffding_c": HOEFFDING_C,
        },
        "never_negative": never_negative_profile(d_max),
        "biased_adversary": biased_adversary_profile(d_max),
        "tower": tower_census(n_max),
        "lean": lean_wired(),
        "notes": {
            "reduction": (
                "per-fixed-depth qualitative equidistribution (or any "
                "rate-free node-wise E-share >= beta > beta*) implies "
                "density-one finite descent via Proposition J's "
                "inequality with N -> infinity taken before d"
            ),
            "target": "conjectures/active/juggler_tower_rate_free_equidistribution.json",
            "wall": "BB/GG/JJ obstruct rated methods only; they are not reopened",
        },
    }
    summary["decision"] = {"classification": classify(summary)}
    return summary


def write_artifacts(summary: dict[str, Any] | None = None) -> dict[str, Any]:
    if summary is None:
        summary = build_summary()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(
        json.dumps(summary, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )
    return summary


if __name__ == "__main__":
    result = write_artifacts()
    print(json.dumps(result["decision"], indent=2))
    print(json.dumps(result["never_negative"]["rows"][-3:], indent=2))
    print(json.dumps(result["biased_adversary"]["rows"], indent=2))
    print(
        json.dumps(
            {
                k: result["tower"][k]
                for k in (
                    "samples",
                    "max_rel_dev",
                    "rel_dev_cap",
                    "oooo_count",
                    "oooo_even_fifth_share",
                    "split_three_sigma",
                )
            },
            indent=2,
        )
    )

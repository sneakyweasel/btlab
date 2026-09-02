"""Heisenberg lift of the depth-3 tower phase: exact identity and censuses.

Not an equidistribution theorem, not a K3 bound, not a Paper B edit,
and not a reopen of the parked toolkit line (BB/GG/JJ stay final).

The branch records one exact identity and its empirical face.

**Identity (EXACT — HUMAN PROOF, `J-tower-heisenberg-coordinate`).**
With v = floor(n^{3/2}), B = v^{3/2}, theta = {B}, z = floor(B),
A = (3/2) v^{3/4}:

    z^{3/2} = v^{9/4} - A theta + r,        0 <= r <= (3/8) theta^2 z^{-1/2},

by the exact second-order Taylor bound on (B - theta)^{3/2} with the
midpoint xi in (z, B) (the same mechanism as Paper B's Lemma 7.2;
z^{-1/2} = v^{-3/4} (1 + O(1/z))), and since
A theta = A B - A floor(B) with A B = (3/2) v^{9/4},

    {z^{3/2}} = { -(1/2) v^{9/4} + (3/2) v^{3/4} floor(v^{3/2}) + r }.

The term (3/2) v^{3/4} floor(v^{3/2}) mod 1 is *exactly* the vertical
Mal'cev coordinate of the Heisenberg orbit
g(n) Gamma, g(n) = [[1, A(n), 0], [0, 1, B(n)], [0, 0, 1]]
(reduce y by floor(B): z-entry picks up -A floor(B); then reduce x and
z mod 1).  The lift is pure algebra — Bergelson–Leibman's polynomial
hypothesis enters only in the equidistribution theorem applied AFTER
the lift.  Consequence: the depth-3 tower phase is, up to
O(n^{-9/8}), a coordinate of an explicit orbit on T x Heisenberg with
horizontal torus ((3/2) v^{3/4}, v^{3/2}, (1/2) v^{9/4}) mod 1 — the
amplitude-product class dissolves into a FIXED-harmonic pair problem
(no amplitude ever multiplies a harmonic) plus the ergodic transfer
along a floor-Hardy orbit, which is the single remaining open step of
the rate-free route (`juggler_tower_rate_free_equidistribution`).

Probe contents (dyadic window, exact scaled-integer roots):

- `expansion_check`: max |r| sqrt(z) / theta^2 against the Taylor
  constant 3/8 — exact witnesses of the identity's error bound.
- `horizontal_census`: joint 8^3 census of the horizontal triple —
  falsifier (b): a resonance here kills the nil-route at its base.
- `weyl_grid`: fixed-harmonic Weyl sums |sum e(k . phases)| / sqrt(N)
  over the triple — square-root cancellation is the nil-route's
  quantitative face; the harmonics are FIXED so GG's amplitude drift
  does not apply by construction.
- `heisenberg_census`: joint 16^2 census of the vertical coordinate
  {A floor(B)} against the abelian coordinate {(1/2) v^{9/4}} —
  falsifier (c): fiber correlation kills the lift's prediction.

Scaled-integer roots make every fractional part exact to 10^{-digits}
before any float enters; the Weyl grid uses harmonics |k| <= 2 where
that precision is conservative by seven orders of magnitude.
"""

from __future__ import annotations

import json
import math
from math import isqrt
from pathlib import Path
from typing import Any

import numpy as np

from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM

REPO_ROOT = Path(__file__).resolve().parents[3]
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "bracket_nil_lift"
JSON_PATH = DATA_DIR / "summary.json"

WINDOW = 2_000_000
TEST_WINDOW = 40_000
DIGITS = 22
# the expansion witness needs A * 10^{-digits} << (3/8) theta^2 z^{-1/2}
# down to theta = 10^{-6}: 30 digits gives three orders of margin
EXPANSION_DIGITS = 30
BINS3 = 8
BINS2 = 16
WEYL_RANGE = 2  # harmonics k in [-2, 2]^3 \ {0}
TAYLOR_CONSTANT = 3.0 / 8.0

CLASS_GREEN = "BRACKET_NIL_LIFT_GREEN"
CLASS_VIOLATED = "BRACKET_NIL_LIFT_VIOLATED"

ANTI = {
    **ANTI_OVERCLAIM,
    "equidistribution_claimed": False,
    "k3_bound_claimed": False,
    "toolkit_reopened": False,
    "paper_b_modified": False,
}


def scaled_sqrt(m: int, digits: int) -> int:
    """floor(sqrt(m) * 10^digits) up to one unit (exact scaled root)."""

    return isqrt(m * 10 ** (2 * digits))


def scaled_root4(m: int, digits: int) -> int:
    """floor-ish of m^{1/4} * 10^digits up to one unit."""

    return isqrt(isqrt(m * 10 ** (4 * digits)))


def _frac_of_scaled(r: int, digits: int) -> float:
    return (r % 10**digits) / 10**digits


def tower_data(n: int, digits: int = DIGITS) -> dict[str, Any]:
    """Exact scaled data for one start: v, z, theta, A, and coordinates."""

    scale = 10**digits
    v = isqrt(n * n * n)
    v3 = v * v * v
    r_b = scaled_sqrt(v3, digits)  # B = v^{3/2}
    z = r_b // scale
    theta_scaled = r_b % scale
    r_a34 = scaled_root4(v3, digits)  # v^{3/4}
    v9 = v3 * v3 * v3
    r_v94 = scaled_root4(v9, digits)  # v^{9/4}
    r_z32 = scaled_sqrt(z * z * z, digits)  # z^{3/2}
    # vertical Mal'cev coordinate {A floor(B)} = {3 r_a34 z / (2 scale)}
    num = 3 * r_a34 * z
    den = 2 * scale
    vertical = (num % den) / den
    # abelian coordinate {(1/2) v^{9/4}}
    abelian = ((r_v94 % (2 * scale)) / (2 * scale)) % 1.0
    return {
        "v": v,
        "z": z,
        "theta": theta_scaled / scale,
        "frac_A": ((3 * r_a34) % den) / den,  # {(3/2) v^{3/4}}
        "frac_B": theta_scaled / scale,  # {v^{3/2}}
        "frac_C": _frac_of_scaled(r_v94, digits),  # {v^{9/4}}
        "vertical": vertical,
        "abelian": abelian,
        "r_a34": r_a34,
        "r_v94": r_v94,
        "r_b": r_b,
        "r_z32": r_z32,
    }


def expansion_check(
    n_max: int = WINDOW, digits: int = EXPANSION_DIGITS
) -> dict[str, Any]:
    """Exact witnesses of 0 <= r <= (3/8) theta^2 z^{-1/2}.

    r = z^{3/2} - v^{9/4} + A theta, all terms from scaled-integer
    roots (each exact to one scaled unit; the combination is exact to
    ~A * 10^{-digits} ~ 10^{-15}, seven orders below |r|).
    """

    scale = 10**digits
    worst_ratio = 0.0
    worst_n = 0
    max_abs_r = 0.0
    n_min = n_max // 2
    start = n_min + 1 if (n_min + 1) % 2 == 1 else n_min + 2
    for n in range(start, n_max + 1, 2):
        d = tower_data(n, digits)
        theta_scaled = d["r_b"] % scale
        # r = z^{3/2} - v^{9/4} + (3/2) v^{3/4} theta: combine as one exact
        # integer before any float division (big-int subtraction would
        # otherwise lose the ~10^{-14} signal to float rounding)
        num = 2 * scale * (d["r_z32"] - d["r_v94"]) + 3 * d["r_a34"] * theta_scaled
        r_val = num / (2 * scale * scale)
        theta = d["theta"]
        if theta > 1e-6:
            sqrt_z = d["r_z32"] / (d["z"] * scale)  # z^{3/2} / z = z^{1/2}
            ratio = abs(r_val) * sqrt_z / (theta * theta)
            if ratio > worst_ratio:
                worst_ratio = ratio
                worst_n = n
        max_abs_r = max(max_abs_r, abs(r_val))
    return {
        "n_max": n_max,
        "worst_taylor_ratio": worst_ratio,
        "worst_n": worst_n,
        "taylor_constant": TAYLOR_CONSTANT,
        "bound_holds": worst_ratio <= TAYLOR_CONSTANT * (1.0 + 1e-6),
        "max_abs_r": max_abs_r,
    }


def _collect(n_max: int, digits: int = DIGITS) -> dict[str, np.ndarray]:
    n_min = n_max // 2
    start = n_min + 1 if (n_min + 1) % 2 == 1 else n_min + 2
    ns = range(start, n_max + 1, 2)
    fa, fb, fc, vert, abel = [], [], [], [], []
    for n in ns:
        d = tower_data(n, digits)
        fa.append(d["frac_A"])
        fb.append(d["frac_B"])
        fc.append(d["frac_C"])
        vert.append(d["vertical"])
        abel.append(d["abelian"])
    return {
        "frac_A": np.array(fa),
        "frac_B": np.array(fb),
        "frac_C": np.array(fc),
        "vertical": np.array(vert),
        "abelian": np.array(abel),
    }


def _dev_cap(cells: int, total: int) -> float:
    return (math.sqrt(2.0 * math.log(cells)) + 1.5) * math.sqrt(cells / total)


def _census(coords: list[np.ndarray], bins: int) -> dict[str, Any]:
    total = len(coords[0])
    idx = np.zeros(total, dtype=np.int64)
    for c in coords:
        idx = idx * bins + np.minimum((c * bins).astype(np.int64), bins - 1)
    cells = bins ** len(coords)
    counts = np.bincount(idx, minlength=cells)
    expected = total / cells
    max_rel = float(np.max(np.abs(counts - expected)) / expected)
    return {
        "bins": bins,
        "samples": total,
        "occupied_cells": int(np.count_nonzero(counts)),
        "cells": cells,
        "max_rel_dev": max_rel,
        "rel_dev_cap": _dev_cap(cells, total),
        "uniform": bool(
            np.count_nonzero(counts) == cells and max_rel <= _dev_cap(cells, total)
        ),
    }


def weyl_grid(data: dict[str, np.ndarray], k_range: int = WEYL_RANGE) -> dict[str, Any]:
    """Fixed-harmonic Weyl sums over the horizontal triple.

    Reports max |S_k| / sqrt(N) over k in [-k_range, k_range]^3 \\ {0}
    — square-root cancellation means this stays O(1).
    """

    n = len(data["frac_A"])
    worst = 0.0
    worst_k = (0, 0, 0)
    for k1 in range(-k_range, k_range + 1):
        for k2 in range(-k_range, k_range + 1):
            for k3 in range(-k_range, k_range + 1):
                if k1 == k2 == k3 == 0:
                    continue
                phase = (
                    k1 * data["frac_A"] + k2 * data["frac_B"] + k3 * data["frac_C"]
                )
                s = np.exp(2j * np.pi * phase).sum()
                ratio = float(abs(s)) / math.sqrt(n)
                if ratio > worst:
                    worst = ratio
                    worst_k = (k1, k2, k3)
    return {
        "k_range": k_range,
        "harmonics": (2 * k_range + 1) ** 3 - 1,
        "max_ratio": worst,
        "worst_harmonic": list(worst_k),
        "square_root_scale": bool(worst <= 10.0),
    }


def build_summary(*, n_max: int = WINDOW) -> dict[str, Any]:
    data = _collect(n_max)
    horizontal = _census([data["frac_A"], data["frac_B"], data["frac_C"]], BINS3)
    heisenberg = _census([data["vertical"], data["abelian"]], BINS2)
    expansion = expansion_check(n_max)
    weyl = weyl_grid(data)
    summary: dict[str, Any] = {
        "experiment": "juggler_bracket_nil_lift",
        "anti_overclaim": ANTI,
        "expansion": expansion,
        "horizontal": horizontal,
        "weyl": weyl,
        "heisenberg": heisenberg,
        "notes": {
            "identity": (
                "{z^{3/2}} = {-(1/2) v^{9/4} + (3/2) v^{3/4} floor(v^{3/2})"
                " + r}, |r| <= (3/8) theta^2 v^{-3/4}; the middle term is"
                " the Heisenberg vertical Mal'cev coordinate of the orbit"
                " ((3/2) v^{3/4}, v^{3/2}, 0)"
            ),
            "consequence": (
                "the amplitude-product class dissolves into fixed-harmonic"
                " pair statements plus one ergodic transfer along a"
                " floor-Hardy orbit; GG's amplitude drift does not apply"
                " to the horizontal base by construction"
            ),
            "target": "conjectures/active/juggler_tower_rate_free_equidistribution.json",
        },
    }
    ok = (
        expansion["bound_holds"]
        and horizontal["uniform"]
        and weyl["square_root_scale"]
        and heisenberg["uniform"]
    )
    summary["decision"] = {
        "classification": CLASS_GREEN if ok else CLASS_VIOLATED
    }
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
    for key in ("decision", "expansion", "horizontal", "weyl", "heisenberg"):
        print(key, json.dumps(result[key], indent=2))

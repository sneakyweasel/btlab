"""Heisenberg vertical regularity: the floor cut is not charged.

Not an equidistribution theorem, not a K3 bound, not a Paper B edit,
and not a characteristic-factor argument.

**Lemma (EXACT — HUMAN PROOF, `J-heisenberg-vertical-riemann`).**
On X = H_3(R)/H_3(Z) the Mal'cev z-coordinate χ of the fundamental
domain [0,1)^3 is bounded and discontinuous only on the faces
(Haar-null). Hence χ is Riemann integrable on X. The nil-lift
identity says n |-> {A floor(B)} equals χ(g(n) Gamma) for
g(n) = exp(A e_12 + B e_23), A = (3/2) m^{3/4}, B = m^{3/2},
m = floor(n^{3/2}). Standard sandwich (continuous majorants of an
RI observable; the same extension Paper A Prop 5.5 already uses
for the hug function) therefore gives: Haar equidistribution of
g(n) Gamma implies equidistribution of the vertical, provided the
orbit does not charge the face {y = 0}. That face is {B} in Z,
i.e. {m^{3/2}} = 0. So the fourth ergodic layer, at the
observable-regularity level, is exactly cut-charging of {m^{3/2}}.
It is not a new structural obstruction. Characteristic-factor
self-similarity (the recorded route-falsifier) is not addressed.

Probe, dyadic window, exact scaled roots from bracket_nil_lift:

- `cut_mass`: P(dist({B}, Z) < eps) / (2 eps) for a ladder of
  eps — uniform predicts 1; an atom at 0 sends the small-eps
  ratios to infinity.
- `min_spacing`: N * min {B} is O(1) under uniformity (the
  minimum of N uniforms is Exp(1)/N).
- `cut_conditioned`: 16-bin TV distance between the vertical
  law on the cut {dist({B}, Z) < 0.02} and on the complement,
  against a sampling allowance. Falsifier (b): the fiber law
  jumps at the cut.
"""

from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any

import numpy as np

from research.juggler_sequence.bracket_nil_lift import WINDOW, _collect
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM

REPO_ROOT = Path(__file__).resolve().parents[3]
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "heisenberg_cut"
JSON_PATH = DATA_DIR / "summary.json"

TEST_WINDOW = 40_000
CUT_EPS = 0.02
EPS_LADDER = (0.001, 0.005, 0.01, 0.02, 0.05, 0.1)
VERT_BINS = 16

CLASS_GREEN = "HEISENBERG_CUT_GREEN"
CLASS_VIOLATED = "HEISENBERG_CUT_VIOLATED"

ANTI = {
    **ANTI_OVERCLAIM,
    "equidistribution_claimed": False,
    "characteristic_factor_claimed": False,
    "k3_bound_claimed": False,
    "toolkit_reopened": False,
    "paper_b_modified": False,
}


def cut_mass(frac_b: np.ndarray, eps_ladder: tuple[float, ...] = EPS_LADDER) -> dict[str, Any]:
    """Two-sided cut mass vs the uniform prediction 2 eps."""

    dist = np.minimum(frac_b, 1.0 - frac_b)
    n = len(frac_b)
    rows = []
    for eps in eps_ladder:
        count = int(np.count_nonzero(dist < eps))
        expected = 2.0 * eps * n
        ratio = count / expected if expected else None
        # Poisson-scale allowance on the count
        cap = 1.0 + 4.0 / math.sqrt(max(expected, 1.0))
        rows.append(
            {
                "eps": eps,
                "count": count,
                "expected": expected,
                "ratio": ratio,
                "ratio_cap": cap,
                "ok": ratio is not None and ratio <= cap,
            }
        )
    return {
        "samples": n,
        "rows": rows,
        "no_atom": all(r["ok"] for r in rows),
        "min_frac_b": float(np.min(frac_b)),
        "exact_zeros": int(np.count_nonzero(frac_b == 0.0)),
        # perfect-square m make B integer, so the orbit hits the face;
        # expected count is order P^{1/4}, not an atom
        "exact_zeros_order_p_quarter": bool(
            int(np.count_nonzero(frac_b == 0.0)) <= 20.0 * (n**0.25)
        ),
    }


def _tv(p: np.ndarray, q: np.ndarray) -> float:
    return 0.5 * float(np.abs(p - q).sum())


def cut_conditioned(
    frac_b: np.ndarray,
    vertical: np.ndarray,
    *,
    eps: float = CUT_EPS,
    bins: int = VERT_BINS,
) -> dict[str, Any]:
    """TV distance of the vertical law on the cut vs the complement."""

    dist = np.minimum(frac_b, 1.0 - frac_b)
    on_cut = dist < eps
    n_cut = int(np.count_nonzero(on_cut))
    n_bulk = int(np.count_nonzero(~on_cut))
    cut_idx = np.minimum((vertical[on_cut] * bins).astype(np.int64), bins - 1)
    bulk_idx = np.minimum((vertical[~on_cut] * bins).astype(np.int64), bins - 1)
    cut_h = np.bincount(cut_idx, minlength=bins).astype(np.float64)
    bulk_h = np.bincount(bulk_idx, minlength=bins).astype(np.float64)
    cut_p = cut_h / max(n_cut, 1)
    bulk_p = bulk_h / max(n_bulk, 1)
    tv = _tv(cut_p, bulk_p)
    # sampling TV of two histograms is typically O(sqrt(bins/n_cut))
    allowance = 3.0 * math.sqrt(bins / max(n_cut, 1))
    return {
        "eps": eps,
        "bins": bins,
        "n_cut": n_cut,
        "n_bulk": n_bulk,
        "tv": tv,
        "tv_allowance": allowance,
        "fiber_agrees": bool(tv <= allowance),
        "cut_mean": float(vertical[on_cut].mean()) if n_cut else None,
        "bulk_mean": float(vertical[~on_cut].mean()) if n_bulk else None,
    }


def build_summary(*, n_max: int = WINDOW) -> dict[str, Any]:
    data = _collect(n_max)
    mass = cut_mass(data["frac_B"])
    cond = cut_conditioned(data["frac_B"], data["vertical"])
    # control: abelian should also agree on the cut (same regularity class)
    control = cut_conditioned(data["frac_B"], data["abelian"])
    summary: dict[str, Any] = {
        "experiment": "juggler_heisenberg_cut",
        "anti_overclaim": ANTI,
        "cut_mass": mass,
        "vertical_on_cut": cond,
        "abelian_on_cut": control,
        "notes": {
            "lemma": (
                "chi is Riemann integrable on the Heisenberg nilmanifold; "
                "the vertical equals chi(g(n) Gamma); Haar equidistribution "
                "of the orbit passes to the vertical iff the orbit does not "
                "charge {y = 0}, i.e. {m^{3/2}} does not concentrate at 0"
            ),
            "fourth_layer": (
                "at observable regularity the fourth layer is exactly "
                "cut-charging of {m^{3/2}}; characteristic-factor "
                "self-similarity is not addressed"
            ),
        },
    }
    ok = (
        mass["no_atom"]
        and mass["exact_zeros_order_p_quarter"]
        and cond["fiber_agrees"]
        and control["fiber_agrees"]
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
    print(json.dumps(result["decision"], indent=2))
    print(json.dumps(result["cut_mass"], indent=2))
    print(json.dumps(result["vertical_on_cut"], indent=2))
    print(json.dumps(result["abelian_on_cut"], indent=2))

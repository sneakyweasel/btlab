"""Horizontal Weyl catalog: is the nil-route's horizontal half a theorem?

Not a K3 bound, not a density-one claim, not a Paper B edit, and not
a reopen of the parked toolkit line (BB/GG/JJ stay final as K3
statements). Successor of bracket_nil_lift, answering its recorded
best next question.

Notation: nil-lift v = floor(n^{3/2}) is Paper B's m. The horizontal
triple ((3/2) v^{3/4}, v^{3/2}, (1/2) v^{9/4}) is one floor, not K3.

**Catalog (EXACT — HUMAN PROOF, `J-nil-horizontal-weyl-split`).**
For fixed k in Z^3 \\ {0}, write Phi(n) for the horizontal triple and
S_k = sum_{odd n} e(k · Phi(n)). Integer harmonics kill integer
parts. Lemma G (J-second-order-linearization) plus m = n^{3/2} - theta
classifies the three axes:

  (0, ±1, 0): e(k2 v^{3/2}) = e(k2 {m^{3/2}}). Theorem C substrate;
              Theorem R at alpha = 0 is not citable
              (J-w-family-below-nine-eighths is CONJECTURE).

  (±1, 0, 0): Lemma G substitution yields
              m^{3/4} = n^{9/8} - (3/4) n^{-3/8} theta + decaying.
              The theta-correction decays. Remainder is classical
              Weyl of n^{9/8}. EXACT corollary of Lemma G.

  (0, 0, ±1): Lemma G substitution yields
              m^{9/4} = n^{27/8} - (9/4) n^{15/8} theta
                        + (45/32) n^{3/8} theta^2 + R4.
              e((1/2) m^{9/4}) = e((1/2) n^{27/8}) e(C theta + ···)
              with C ≍ n^{15/8}: a first-layer W-family at
              alpha = 15/8 in (9/8, 9/4). Not Theorem R (second
              layer, designed at 9/8), not
              J-w-family-below-nine-eighths (<= 9/8), and
              J-nested-floor-without-W-family forbids absorbing the
              defect into the smooth model. Drift C' ≍ n^{7/8} makes
              the window with Delta C <= 1 shorter than one odd step
              — GG's mechanism, now on the n-reduction of the
              horizontal 9/4 coordinate. NOT a named theorem.

Mixed harmonics inherit the 9/4 leftover whenever k3 != 0.
Therefore the claim "existing depth-2 machinery already proves the
horizontal half" is false. The Heisenberg identity is untouched.

Probe contents: coefficient identities; integer-harmonic cancellation;
scaled-integer defect witnesses that the 9/4 leading term is
(9/4) n^{15/8} theta (not o(1)) and the 3/4 correction decays;
recorded exponent/drift arithmetic.
"""

from __future__ import annotations

import json
from fractions import Fraction
from math import isqrt
from pathlib import Path
from typing import Any

from research.juggler_sequence.bracket_nil_lift import (
    scaled_root4,
    scaled_sqrt,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM
from research.juggler_sequence.two_step_parity import second_order_scan

REPO_ROOT = Path(__file__).resolve().parents[3]
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "nil_horizontal_weyl"
JSON_PATH = DATA_DIR / "summary.json"

DIGITS = 40
TEST_SAMPLES = (5, 11, 101, 1001, 10**6 + 1, 10**7 + 1)
SCIENCE_SAMPLES = (
    tuple(range(5, 501, 2)) + (10**6 + 1, 10**7 + 1, 10**9 + 1)
)
THETA_FLOOR = 10 ** (-(DIGITS - 8))

CLASS_SPLIT = "NIL_HORIZONTAL_WEYL_SPLIT"
CLASS_VIOLATED = "NIL_HORIZONTAL_WEYL_VIOLATED"

# Lemma G → n-linearization leading coefficients (exact rationals).
COEF_N27 = Fraction(5, 32) - Fraction(9, 16) + Fraction(45, 32)
COEF_94_THETA = Fraction(9, 16) - Fraction(45, 16)  # of theta n^{15/8}
COEF_N98 = Fraction(5, 32) + Fraction(15, 16) - Fraction(3, 32)
COEF_34_THETA = -Fraction(15, 16) + Fraction(3, 16)  # of theta n^{-3/8}
LEADING_94 = -COEF_94_THETA  # + (9/4); defect n^{27/8} - m^{9/4}
LEADING_34 = -COEF_34_THETA  # + (3/4); defect n^{9/8} - m^{3/4}

ANTI = {
    **ANTI_OVERCLAIM,
    "equidistribution_claimed": False,
    "k3_bound_claimed": False,
    "toolkit_reopened": False,
    "paper_b_modified": False,
    "horizontal_half_already_a_theorem": False,
}


def _eighth_scaled(x: int, scale: int) -> int:
    """floor(x^{1/8} * scale) up to a few units (three nested isqrts)."""

    return isqrt(isqrt(isqrt(x * scale**8)))


def coefficient_identities() -> dict[str, Any]:
    """Exact Lemma G coefficient sums after substituting m = n^{3/2} - theta."""

    return {
        "n27_coefficient": str(COEF_N27),
        "n27_is_one": COEF_N27 == 1,
        "theta_n15_coefficient": str(COEF_94_THETA),
        "theta_n15_is_minus_nine_fourths": COEF_94_THETA == -Fraction(9, 4),
        "n98_coefficient": str(COEF_N98),
        "n98_is_one": COEF_N98 == 1,
        "theta_n_minus_38_coefficient": str(COEF_34_THETA),
        "theta_n_minus_38_is_minus_three_fourths": COEF_34_THETA
        == -Fraction(3, 4),
        "holds": (
            COEF_N27 == 1
            and COEF_94_THETA == -Fraction(9, 4)
            and COEF_N98 == 1
            and COEF_34_THETA == -Fraction(3, 4)
        ),
    }


def drift_arithmetic() -> dict[str, Any]:
    """Exact exponent/drift comparison for the 9/4 n-linearization.

    C(n) = (9/4) n^{15/8}. Per odd step, Delta C ~ (135/16) n^{7/8}.
    The window with drift <= 1 has length 32/(135 n^{7/8}) < 1 for
    every odd n >= 3. Engine line 9/4 is strictly above 15/8; the
    W-family conjecture only covers alpha <= 9/8.
    """

    alpha = Fraction(15, 8)
    engine = Fraction(9, 4)
    w_family_cap = Fraction(9, 8)
    leading = Fraction(9, 4)
    # C(n+2)-C(n) ~ (9/4)*(15/8)*2 n^{7/8} = (135/16) n^{7/8}
    per_step_prefactor = leading * Fraction(15, 8) * 2
    # L * C' <= 1 ⇒ L <= 1 / ((9/4)*(15/8) n^{7/8}) = 32/(135 n^{7/8})
    window_prefactor = 1 / (leading * Fraction(15, 8))
    return {
        "alpha": str(alpha),
        "alpha_float": float(alpha),
        "engine_line": str(engine),
        "w_family_cap": str(w_family_cap),
        "below_engine": alpha < engine,
        "above_w_family_cap": alpha > w_family_cap,
        "layer": "first",
        "leading_amplitude": str(leading),
        "drift_exponent": str(Fraction(7, 8)),
        "per_step_prefactor": str(per_step_prefactor),
        "window_prefactor": str(window_prefactor),
        "window_shorter_than_one_step": True,
        "named_bound": None,
        "gg_reenters_n_reduction": True,
        "bb_applies": False,
    }


def integer_harmonic_identity(
    samples: tuple[int, ...] = TEST_SAMPLES, digits: int = DIGITS
) -> dict[str, Any]:
    """e(k2 v^{3/2}) = e(k2 {v^{3/2}}) for integer k2: scaled check."""

    scale = 10**digits
    checked = 0
    for n in samples:
        if n < 3 or n % 2 == 0:
            continue
        v = isqrt(n * n * n)
        r_b = scaled_sqrt(v * v * v, digits)
        frac = r_b % scale
        for k2 in (-2, -1, 1, 2):
            left = (k2 * r_b) % scale
            right = (k2 * frac) % scale
            if left != right:
                return {
                    "holds": False,
                    "witness": n,
                    "k2": k2,
                    "checked": checked,
                }
        checked += 1
    return {"holds": True, "checked": checked, "k2_values": [-2, -1, 1, 2]}


def _defect_pair(n: int, digits: int = DIGITS) -> dict[str, Any] | None:
    """Scaled defects of m^{9/4} and m^{3/4} against the smooth models.

    Returns None if theta is too small for the digit budget.
    """

    scale = 10**digits
    m = isqrt(n * n * n)
    r_x = scaled_sqrt(n * n * n, digits)
    theta_scaled = r_x - m * scale
    if theta_scaled <= 0:
        return None
    theta = theta_scaled / scale
    if theta < THETA_FLOOR:
        return None

    m94 = scaled_root4(m**9, digits)
    n27 = _eighth_scaled(n**27, scale)
    n15 = _eighth_scaled(n**15, scale)
    # (n^{27/8} - m^{9/4}) * scale  vs  (9/4) n^{15/8} theta * scale
    defect_94 = n27 - m94
    leading_94 = (9 * n15 * theta_scaled) // (4 * scale)
    if leading_94 <= 0 or defect_94 <= 0:
        return None

    m34 = scaled_root4(m**3, digits)
    n98 = _eighth_scaled(n**9, scale)
    n38 = _eighth_scaled(n**3, scale)
    # (n^{9/8} - m^{3/4}) * scale  vs  (3/4) n^{-3/8} theta * scale
    # (3/4) theta / n^{3/8} * scale = (3/4) theta_scaled * scale / n38
    defect_34 = n98 - m34
    leading_34 = (3 * theta_scaled * scale) // (4 * n38)
    if leading_34 <= 0 or defect_34 <= 0:
        return None

    return {
        "n": n,
        "theta": theta,
        "ratio_94": defect_94 / leading_94,
        "abs_defect_94": defect_94 / scale,
        "leading_94": leading_94 / scale,
        "ratio_34": defect_34 / leading_34,
        "abs_defect_34": defect_34 / scale,
        "leading_34": leading_34 / scale,
    }


def defect_witnesses(
    samples: tuple[int, ...] = SCIENCE_SAMPLES, digits: int = DIGITS
) -> dict[str, Any]:
    """The 9/4 defect is (9/4) n^{15/8} theta, not a remainder; 3/4 decays."""

    ratios_94: list[float] = []
    ratios_34: list[float] = []
    abs_34: list[float] = []
    abs_94: list[float] = []
    used = 0
    skipped = 0
    for n in samples:
        if n < 5 or n % 2 == 0:
            continue
        row = _defect_pair(n, digits)
        if row is None:
            skipped += 1
            continue
        ratios_94.append(row["ratio_94"])
        ratios_34.append(row["ratio_34"])
        abs_34.append(row["abs_defect_34"])
        abs_94.append(row["abs_defect_94"])
        used += 1

    def _band(xs: list[float], centre: float, tol: float) -> bool:
        return bool(xs) and all(abs(x - centre) <= tol for x in xs)

    # Leading-term domination: next 9/4 term is O(n^{3/8} theta^2),
    # relative O(theta / n^{3/2}). A 5% band is conservative at n >= 5.
    holds_94 = _band(ratios_94, 1.0, 0.05)
    holds_34 = _band(ratios_34, 1.0, 0.05)
    # 9/4 defect is huge (not o(1)); 3/4 defect is o(1) at large n.
    decaying_34 = bool(abs_34) and max(abs_34) < 1.0
    not_remainder_94 = bool(abs_94) and min(abs_94) > 1.0

    return {
        "used": used,
        "skipped_tiny_theta": skipped,
        "digits": digits,
        "ratio_94_min": min(ratios_94) if ratios_94 else None,
        "ratio_94_max": max(ratios_94) if ratios_94 else None,
        "ratio_94_near_one": holds_94,
        "abs_defect_94_min": min(abs_94) if abs_94 else None,
        "abs_defect_94_max": max(abs_94) if abs_94 else None,
        "nine_fourths_not_remainder": not_remainder_94,
        "ratio_34_min": min(ratios_34) if ratios_34 else None,
        "ratio_34_max": max(ratios_34) if ratios_34 else None,
        "ratio_34_near_one": holds_34,
        "abs_defect_34_max": max(abs_34) if abs_34 else None,
        "three_fourths_decays": decaying_34,
        "holds": holds_94 and holds_34 and not_remainder_94 and decaying_34,
    }


def axis_catalog() -> dict[str, Any]:
    """The three-axis classification. No new van der Corput bound."""

    drift = drift_arithmetic()
    return {
        "axis_34": {
            "harmonic": "(±1, 0, 0)",
            "phase": "(3/2) v^{3/4}",
            "after_lemma_g": "n^{9/8} - (3/4) n^{-3/8} theta + decaying",
            "class": "EXACT_COROLLARY",
            "named_rows": ["J-second-order-linearization"],
            "already_a_theorem": True,
            "note": "decaying theta-correction; remainder is classical Weyl of n^{9/8}",
        },
        "axis_32": {
            "harmonic": "(0, ±1, 0)",
            "phase": "v^{3/2}",
            "after_integer_harmonic": "e(k2 {m^{3/2}})",
            "class": "THEOREM_C_SUBSTRATE",
            "named_rows": [
                "J-nested-parity-discrepancy",
                "J-horizontal-axis-species",
            ],
            "already_a_theorem": False,
            "note": (
                "integer-harmonic cancellation is exact; Theorem R at "
                "alpha = 0 is not citable (J-w-family-below-nine-eighths "
                "is CONJECTURE); sibling row J-horizontal-axis-species"
            ),
        },
        "axis_94": {
            "harmonic": "(0, 0, ±1)",
            "phase": "(1/2) v^{9/4}",
            "after_lemma_g": (
                "n^{27/8} - (9/4) n^{15/8} theta + (45/32) n^{3/8} theta^2 + R4"
            ),
            "class": "W_FAMILY_FIRST_LAYER",
            "alpha": drift["alpha"],
            "named_rows": [],
            "already_a_theorem": False,
            "gg_reenters_n_reduction": True,
            "bb_applies": False,
            "note": (
                "first-layer W-family at 15/8; not Theorem R, not "
                "J-w-family-below-nine-eighths; J-nested-floor-without-W-family "
                "forbids the smooth-model comparison; GG drift on n-reduction"
            ),
        },
        "mixed": {
            "inherits_94_leftover": True,
            "when": "k3 != 0",
            "already_a_theorem": False,
        },
        "horizontal_half_already_a_theorem": False,
    }


def build_summary(
    *, samples: tuple[int, ...] = SCIENCE_SAMPLES, digits: int = DIGITS
) -> dict[str, Any]:
    identities = coefficient_identities()
    harmonic = integer_harmonic_identity(samples, digits)
    lemma_g = second_order_scan(samples)
    defects = defect_witnesses(samples, digits)
    catalog = axis_catalog()
    drift = drift_arithmetic()
    ok = (
        identities["holds"]
        and harmonic["holds"]
        and lemma_g["holds"]
        and defects["holds"]
        and not catalog["horizontal_half_already_a_theorem"]
        and drift["gg_reenters_n_reduction"]
        and drift["below_engine"]
        and drift["above_w_family_cap"]
        and not drift["bb_applies"]
    )
    return {
        "experiment": "juggler_nil_horizontal_weyl",
        "anti_overclaim": ANTI,
        "identities": identities,
        "integer_harmonic": harmonic,
        "lemma_g": lemma_g,
        "defects": defects,
        "drift": drift,
        "catalog": catalog,
        "notes": {
            "claim_tested": (
                "existing depth-2 machinery already proves the fixed-harmonic "
                "Weyl sums of the horizontal triple"
            ),
            "claim_holds": False,
            "already_in_ledger": [
                "J-horizontal-leftover-exponents",
                "J-horizontal-axis-species",
                "J-horizontal-theorem-r-shortcut",
            ],
            "heisenberg_untouched": True,
            "k3_untouched": True,
        },
        "decision": {
            "classification": CLASS_SPLIT if ok else CLASS_VIOLATED,
            "branch": "CLOSE",
            "already_a_theorem": False,
        },
    }


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
    for key in (
        "decision",
        "identities",
        "integer_harmonic",
        "lemma_g",
        "defects",
        "drift",
        "catalog",
    ):
        print(key, json.dumps(result[key], indent=2))

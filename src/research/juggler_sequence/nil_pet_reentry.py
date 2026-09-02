"""First PET difference of the Heisenberg lift: A{ΔB} re-entry.

Not an equidistribution theorem, not a K3 bound, not a Paper B edit,
and not a reopen of BB/GG/JJ as rated methods. The only question is
whether the first characteristic-factor / van der Corput step on the
floor-Hardy Heisenberg orbit keeps the floor-removal correction as a
Mal'cev coordinate, or re-expands it into an amplitude-product.

**Identity (EXACT — HUMAN PROOF, `J-nil-pet-reentry`).**
Write g(n) = (A(n), B(n), 0) in Mal'cev coordinates with the
Heisenberg law (x,y,z)*(x',y',z') = (x+x', y+y', z+z'+x y'),
A = (3/2) v^{3/4}, B = v^{3/2}, v = floor(n^{3/2}). Then

    g(n)^{-1} = (-A, -B, A B),
    g(n)^{-1} g(n+h) = (ΔA, ΔB, -A ΔB).

Right-reducing by Γ to the fundamental domain [0,1)^3 yields the
vertical coordinate

    χ_Δ = {-A ΔB - ΔA ⌊ΔB⌋} = {-A(n+h) ⌊ΔB⌋ - A(n){ΔB}}.

The first summand is integer dilation of {A(n+h)} (the cheap A-axis).
The second is the amplitude-product A{ΔB} with A ≍ n^{9/8} and
discrete increment A(n+2)-A(n) ≍ (27/8) n^{1/8} >> 1 (GG species).
Equivalently A{ΔB} is the vertical of a second Heisenberg lift of
(A(n), ΔB(n,h), 0) — the same group law as
`J-tower-heisenberg-coordinate`, not a degree drop. The entries of
that second lift are not o(1)-close to a Hardy-in-n pair: the leftover
of ΔB against (n+h)^{9/4}-n^{9/4} has size ≍ n^{3/4}.

This is a different identity from the v94 abelian difference
{v(n+h)^{9/4}-v(n)^{9/4}} = {Δv · { (9/4) ξ^{5/4} }}. Consequence:
PET / characteristic-factor induction re-enters the amplitude-product
class at the first step. The rate-free conjecture is unharmed — this
kills a method, not the statement.

Probe contents (exact Fraction group law; scaled-integer tower
witnesses of the species, not a Weyl census):

- `pet_identity_check`: Fraction witnesses of the unreduced product
  and of the reduced-vertical split.
- `species_check`: A-increment / n^{1/8} against 27/8; {ΔB} not
  concentrated at 0; leftover of ΔB versus the smooth increment
  stays ≍ n^{3/4}.
"""

from __future__ import annotations

import json
from fractions import Fraction
from math import floor
from pathlib import Path
from typing import Any

from research.juggler_sequence.bracket_nil_lift import scaled_root4, tower_data
from research.juggler_sequence.horizontal_weyl import scaled_eighth
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM

REPO_ROOT = Path(__file__).resolve().parents[3]
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "nil_pet_reentry"
JSON_PATH = DATA_DIR / "summary.json"

DIGITS = 22
H = 2
A_INCREMENT_LEADING = 27.0 / 8.0
SCIENCE_BLOCKS = (
    (10**4 + 1, 10**4 + 1 + 200),
    (10**6 + 1, 10**6 + 1 + 200),
)
TEST_BLOCKS = ((10**4 + 1, 10**4 + 1 + 80),)

CLASS_GREEN = "NIL_PET_REENTRY_GREEN"
CLASS_VIOLATED = "NIL_PET_REENTRY_VIOLATED"

ANTI = {
    **ANTI_OVERCLAIM,
    "equidistribution_claimed": False,
    "k3_bound_claimed": False,
    "toolkit_reopened": False,
    "paper_b_modified": False,
    "pet_proves_equidistribution": False,
    "conjecture_refuted": False,
}


def unit_frac(x: Fraction) -> Fraction:
    """Standard {x} in [0, 1)."""

    return x - floor(x)


def malcev_mul(
    g1: tuple[Fraction, Fraction, Fraction],
    g2: tuple[Fraction, Fraction, Fraction],
) -> tuple[Fraction, Fraction, Fraction]:
    x1, y1, z1 = g1
    x2, y2, z2 = g2
    return (x1 + x2, y1 + y2, z1 + z2 + x1 * y2)


def malcev_inv(
    g: tuple[Fraction, Fraction, Fraction],
) -> tuple[Fraction, Fraction, Fraction]:
    x, y, z = g
    return (-x, -y, -z + x * y)


def malcev_reduce(
    g: tuple[Fraction, Fraction, Fraction],
) -> tuple[Fraction, Fraction, Fraction]:
    """Right-reduce (x, y, z) to the fundamental domain [0, 1)^3."""

    x, y, z = g
    fy = floor(y)
    y = y - fy
    z = z - x * fy
    fx = floor(x)
    x = x - fx
    z = z - floor(z)
    return (x, y, z)


def pet_difference(
    a: Fraction, b: Fraction, ap: Fraction, bp: Fraction
) -> dict[str, Fraction]:
    """Unreduced PET difference and the two readings of the vertical."""

    g = (a, b, Fraction(0))
    gp = (ap, bp, Fraction(0))
    raw = malcev_mul(malcev_inv(g), gp)
    da, db = ap - a, bp - b
    predicted_raw = (da, db, -a * db)
    reduced = malcev_reduce(raw)
    split = unit_frac(-ap * floor(db) - a * unit_frac(db))
    return {
        "raw_x": raw[0],
        "raw_y": raw[1],
        "raw_z": raw[2],
        "pred_x": predicted_raw[0],
        "pred_y": predicted_raw[1],
        "pred_z": predicted_raw[2],
        "chi": reduced[2],
        "split": split,
    }


def pet_identity_check() -> dict[str, Any]:
    """Exact Fraction witnesses of the group law and the split."""

    pairs = (
        (Fraction(37, 13), Fraction(155, 17), Fraction(41, 13), Fraction(200, 17)),
        (Fraction(3, 2), Fraction(9, 4), Fraction(2), Fraction(3)),
        (Fraction(-5, 2), Fraction(11, 7), Fraction(-1, 4), Fraction(20, 7)),
        (Fraction(8, 5), Fraction(-3, 2), Fraction(11, 5), Fraction(7, 2)),
    )
    rows = []
    all_ok = True
    for a, b, ap, bp in pairs:
        d = pet_difference(a, b, ap, bp)
        raw_ok = (
            d["raw_x"] == d["pred_x"]
            and d["raw_y"] == d["pred_y"]
            and d["raw_z"] == d["pred_z"]
        )
        split_ok = d["chi"] == d["split"]
        all_ok = all_ok and raw_ok and split_ok
        rows.append(
            {
                "raw_ok": raw_ok,
                "split_ok": split_ok,
                "chi": str(d["chi"]),
            }
        )

    # one tower pair as exact rationals built from scaled roots
    n, h, digits = 1001, H, DIGITS
    scale = 10**digits
    d0 = tower_data(n, digits)
    d1 = tower_data(n + h, digits)
    a = Fraction(3 * d0["r_a34"], 2 * scale)
    b = Fraction(d0["r_b"], scale)
    ap = Fraction(3 * d1["r_a34"], 2 * scale)
    bp = Fraction(d1["r_b"], scale)
    tower = pet_difference(a, b, ap, bp)
    tower_ok = (
        tower["raw_x"] == tower["pred_x"]
        and tower["raw_y"] == tower["pred_y"]
        and tower["raw_z"] == tower["pred_z"]
        and tower["chi"] == tower["split"]
    )
    return {
        "exact_identity": all_ok,
        "scaled_identity": tower_ok,
        "rows": rows,
        "n": n,
        "h": h,
    }


def _odd_range(start: int, stop: int) -> list[int]:
    n = start if start % 2 == 1 else start + 1
    return list(range(n, stop + 1, 2))


def species_check(
    blocks: tuple[tuple[int, int], ...] = SCIENCE_BLOCKS,
    digits: int = DIGITS,
    h: int = H,
) -> dict[str, Any]:
    """A-increment, {ΔB} occupancy, and ΔB leftover versus the smooth model."""

    scale = 10**digits
    a_ratios: list[float] = []
    frac_db: list[float] = []
    leftover_ratios: list[float] = []
    amp_mod1: list[float] = []
    pairs = 0
    for start, stop in blocks:
        for n in _odd_range(start, stop):
            d0 = tower_data(n, digits)
            d1 = tower_data(n + h, digits)
            a = (3 * d0["r_a34"]) / (2 * scale)
            ap = (3 * d1["r_a34"]) / (2 * scale)
            b = d0["r_b"] / scale
            bp = d1["r_b"] / scale
            da = ap - a
            db = bp - b
            n18 = scaled_eighth(n, digits) / scale
            if n18 > 0:
                a_ratios.append(da / n18)
            frac = db - floor(db)
            frac_db.append(frac)
            amp_mod1.append((a * frac) - floor(a * frac))
            r_n14 = scaled_root4(n, digits)
            r_np14 = scaled_root4(n + h, digits)
            smooth = (n + h) * (n + h) * (r_np14 / scale) - n * n * (r_n14 / scale)
            n34 = scaled_root4(n * n * n, digits) / scale
            if n34 > 0:
                leftover_ratios.append(abs(db - smooth) / n34)
            pairs += 1

    a_ratios.sort()
    leftover_ratios.sort()
    frac_sorted = sorted(frac_db)
    mean_a = sum(a_ratios) / len(a_ratios) if a_ratios else 0.0
    mean_left = sum(leftover_ratios) / len(leftover_ratios) if leftover_ratios else 0.0
    median_frac = frac_sorted[len(frac_sorted) // 2] if frac_sorted else 0.0
    # GG: discrete A-increment grows; leftover of ΔB is not o(1)
    increment_gg = mean_a > 1.0
    leftover_not_o1 = mean_left > 0.05
    frac_not_tiny = median_frac > 0.05
    return {
        "pairs": pairs,
        "h": h,
        "mean_da_over_n18": mean_a,
        "median_da_over_n18": a_ratios[len(a_ratios) // 2] if a_ratios else 0.0,
        "leading": A_INCREMENT_LEADING,
        "min_da_over_n18": min(a_ratios) if a_ratios else 0.0,
        "max_da_over_n18": max(a_ratios) if a_ratios else 0.0,
        "increment_gg": increment_gg,
        "median_frac_db": median_frac,
        "min_frac_db": min(frac_db) if frac_db else 0.0,
        "max_frac_db": max(frac_db) if frac_db else 0.0,
        "frac_not_tiny": frac_not_tiny,
        "mean_leftover_over_n34": mean_left,
        "median_leftover_over_n34": leftover_ratios[len(leftover_ratios) // 2]
        if leftover_ratios
        else 0.0,
        "leftover_not_o1": leftover_not_o1,
        "mean_A_frac_db_mod1": sum(amp_mod1) / len(amp_mod1) if amp_mod1 else 0.0,
        "reentry": increment_gg and leftover_not_o1 and frac_not_tiny,
    }


def build_summary(
    blocks: tuple[tuple[int, int], ...] = SCIENCE_BLOCKS,
) -> dict[str, Any]:
    identity = pet_identity_check()
    species = species_check(blocks)
    identity_ok = identity["exact_identity"] and identity["scaled_identity"]
    if not identity_ok:
        classification = CLASS_VIOLATED
    elif species["reentry"]:
        classification = CLASS_GREEN
    else:
        classification = CLASS_VIOLATED
    return {
        "experiment": "juggler_nil_pet_reentry",
        "anti_overclaim": ANTI,
        "pet_identity": identity,
        "species": species,
        "decision": {
            "classification": classification,
            "branch": "PROMOTE",
            "method": "CLOSE",
            "conjecture": "ACTIVE",
            "notes": (
                "first PET difference of the Heisenberg lift has reduced "
                "vertical {-A(n+h) floor(ΔB) - A(n){ΔB}}; A{ΔB} is GG "
                "(A' ≍ n^{1/8}); the second lift is the same algebra, "
                "not a published Hardy-nil orbit; rate-free conjecture "
                "stays ACTIVE"
            ),
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
    for key in ("decision", "pet_identity", "species"):
        print(key, json.dumps(result[key], indent=2, default=str))

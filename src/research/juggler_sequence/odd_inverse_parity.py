"""Odd-inverse parity versus cube-block lanes.

Not a halt theorem, not a divergence exclusion, not a reopen of
odd-inverse width, empty-odd-cell forward laws, odd-landing sets,
odd towers, hug-cylinders, or fan-concat. Not a Paper A edit and
not a forward residue census of floor(x^{3/2}) mod 2.

Phase-0 question: is the parity of the unique inverse candidate
k = ceil(y^{2/3}) a law of the cube-block residue r = y - m^3, and
do nested cube-lane hits reformulate an infinite flight?
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.empty_odd_cell import ceil_cbrt, icbrt, odd_cell_kind
from research.juggler_sequence.floor_cells import odd_cell_integers
from research.juggler_sequence.lean_paths import JUGGLER_DIR, has_named, juggler_text
from research.juggler_sequence.power_words import ANTI_OVERCLAIM, floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "odd_inverse_parity"
JSON_PATH = DATA_DIR / "summary.json"
CELLS = JUGGLER_DIR / "Cells.lean"

CLASS_REPARAM = "ODD_INVERSE_PARITY_REPARAMETERIZATION"
CLASS_NEW_LAW = "ODD_INVERSE_PARITY_NEW_LAW"

IDENTITY_M = tuple(range(1, 41)) + (50, 80, 100)
SAMPLE_BLOCKS = (2, 3, 5, 10)
NEST_Y_MAX = 200
ODD_HITS = (3, 37, 365, 761)
RESIDUE_FIXED = (2, 3, 4, 8, 16)

EXISTING_LEAN = ("odd_cell_unique", "odd_cell_iff")
FORBIDDEN_THEOREMS = (
    "juggler_reaches_one",
    "no_juggler_escape",
    "all_finiteProgress",
)
NEW_LEAN_FILES = (
    JUGGLER_DIR / "OddInverseParity.lean",
    JUGGLER_DIR / "InverseCubicLanes.lean",
)


def inverse_candidate(y: int) -> int:
    """k = ceil(y^{2/3}), least integer with k^3 >= y^2."""

    if y < 0:
        raise ValueError("inverse_candidate requires a nonnegative integer")
    return ceil_cbrt(y * y)


def cube_block_index(y: int) -> int:
    if y < 0:
        raise ValueError("cube_block_index requires a nonnegative integer")
    return icbrt(y)


def type2_in_block(m: int) -> list[int]:
    """Type-2 y in B_m = [m^3, (m+1)^3)."""

    if m < 1:
        raise ValueError("type2_in_block requires m >= 1")
    lo = m * m * m
    hi = (m + 1) * (m + 1) * (m + 1)
    return [y for y in range(lo, hi) if odd_cell_kind(y) == 2]


def odd_images_in_annulus(m: int) -> list[int]:
    """{T(x) : x odd, m^2 <= x < (m+1)^2}."""

    if m < 1:
        raise ValueError("odd_images_in_annulus requires m >= 1")
    lo = m * m
    hi = (m + 1) * (m + 1)
    return [floor_power(x) for x in range(lo, hi) if x % 2 == 1]


def block_identity(m: int) -> dict[str, Any]:
    """Type-2 set in B_m equals T of the odd square annulus."""

    type2 = type2_in_block(m)
    images = odd_images_in_annulus(m)
    occupants = [inverse_candidate(y) for y in type2]
    odds = [x for x in range(m * m, (m + 1) * (m + 1)) if x % 2 == 1]
    occupant_ok = occupants == odds
    image_ok = type2 == images
    return {
        "m": m,
        "block_len": 3 * m * m + 3 * m + 1,
        "n_type2": len(type2),
        "n_odds": len(odds),
        "identity_ok": image_ok and occupant_ok,
        "sets_equal": image_ok,
        "occupants_are_annulus_odds": occupant_ok,
    }


def _gcd_list(values: list[int]) -> int:
    acc = 0
    for value in values:
        a, b = acc, abs(value)
        while b:
            a, b = b, a % b
        acc = a
    return acc


def offset_hunt(m: int) -> dict[str, Any]:
    """Residue / AP hunt on Type-2 offsets r = y - m^3."""

    type2 = type2_in_block(m)
    cube = m * m * m
    offsets = [y - cube for y in type2]
    gaps = [offsets[i + 1] - offsets[i] for i in range(len(offsets) - 1)]
    is_ap = len(gaps) >= 2 and all(gap == gaps[0] for gap in gaps)
    moduli = list(RESIDUE_FIXED) + [m, 2 * m + 1]
    residue_rows: list[dict[str, Any]] = []
    deciding = False
    single_class = False
    for modulus in moduli:
        if modulus <= 1:
            continue
        occupied = sorted({r % modulus for r in offsets})
        full_classes: list[int] = []
        for residue in occupied:
            block_hits = [
                y
                for y in range(cube, cube + 3 * m * m + 3 * m + 1)
                if (y - cube) % modulus == residue
            ]
            if block_hits and all(odd_cell_kind(y) == 2 for y in block_hits):
                full_classes.append(residue)
        is_single = len(occupied) == 1
        # Two-point congruences on a tiny block (m=1, r=0,4) are not a law.
        is_deciding = (
            is_single
            and bool(full_classes)
            and occupied == full_classes
            and len(offsets) >= 3
        )
        single_class = single_class or is_single
        deciding = deciding or is_deciding
        residue_rows.append(
            {
                "modulus": modulus,
                "n_occupied": len(occupied),
                "occupied": occupied,
                "single_class": is_single,
                "full_type2_classes": full_classes,
                "deciding": is_deciding,
            }
        )
    return {
        "m": m,
        "n_type2": len(type2),
        "offsets": offsets if m in SAMPLE_BLOCKS else None,
        "n_offsets_stored": len(offsets),
        "gaps": gaps if m in SAMPLE_BLOCKS else None,
        "gap_min": min(gaps) if gaps else None,
        "gap_max": max(gaps) if gaps else None,
        "n_unique_gaps": len(set(gaps)),
        "gap_gcd": _gcd_list(gaps) if gaps else None,
        "is_ap": is_ap,
        "single_residue_class": single_class,
        "deciding_residue": deciding,
        "residues": residue_rows,
    }


def named_hit_row(x: int) -> dict[str, Any]:
    if x % 2 == 0:
        raise ValueError("named_hit_row requires an odd start")
    image = floor_power(x)
    m = cube_block_index(image)
    k = inverse_candidate(image)
    occupants = odd_cell_integers(image)
    return {
        "x": x,
        "T_x": image,
        "m": m,
        "r": image - m * m * m,
        "k": k,
        "kind": odd_cell_kind(image),
        "occupants": occupants,
        "self_preimage": occupants == [x],
        "k_equals_x": k == x,
        "image_odd": image % 2 == 1,
    }


def backward_odd_spine(y: int, cap: int = 64) -> dict[str, Any]:
    """Type-2 occupant chain. Stops at Type 0/1 or the fixed point 1."""

    chain = [y]
    cur = y
    for _ in range(cap):
        if odd_cell_kind(cur) != 2:
            break
        pred = inverse_candidate(cur)
        if pred == cur:
            break
        chain.append(pred)
        cur = pred
    descends = all(chain[i + 1] < chain[i] for i in range(len(chain) - 1))
    return {
        "start": y,
        "depth": len(chain) - 1,
        "chain": chain,
        "terminal": chain[-1],
        "terminal_kind": odd_cell_kind(chain[-1]),
        "descends": descends,
        "hit_cap": len(chain) - 1 >= cap,
    }


def nest_sanity(n_max: int = NEST_Y_MAX) -> dict[str, Any]:
    depths = []
    first_ascent = None
    for y in range(1, n_max + 1):
        if odd_cell_kind(y) != 2:
            continue
        row = backward_odd_spine(y)
        depths.append(row["depth"])
        if not row["descends"] and first_ascent is None:
            first_ascent = y
    return {
        "n_max": n_max,
        "n_type2": len(depths),
        "max_depth": max(depths) if depths else 0,
        "all_descend": first_ascent is None,
        "first_ascent": first_ascent,
    }


def lean_api_present() -> dict[str, Any]:
    text = juggler_text()
    cells = CELLS.read_text(encoding="utf-8")
    return {
        "odd_cell_unique": has_named(cells, "odd_cell_unique"),
        "odd_cell_iff": has_named(cells, "odd_cell_iff"),
        "sorry_free": "sorry" not in text and "admit" not in text,
        "new_lean_file": any(path.exists() for path in NEW_LEAN_FILES),
        **{f"has_{name}": has_named(text, name) for name in FORBIDDEN_THEOREMS},
    }


def classify(summary: dict[str, Any]) -> str:
    identity = summary["identity"]
    hunts = summary["offset_hunts"]
    hits = summary["named_hits"]
    nest = summary["nest"]
    identity_ok = all(row["identity_ok"] for row in identity)
    no_ap = all(not row["is_ap"] for row in hunts if row["n_type2"] >= 3)
    no_deciding = all(not row["deciding_residue"] for row in hunts)
    hits_ok = all(row["kind"] == 2 and row["self_preimage"] for row in hits)
    nest_ok = nest["all_descend"] and not nest["first_ascent"]
    known = (
        identity_ok
        and no_ap
        and no_deciding
        and hits_ok
        and nest_ok
        and summary["lean"]["odd_cell_unique"]
    )
    if known:
        return CLASS_REPARAM
    return CLASS_NEW_LAW


def build_summary() -> dict[str, Any]:
    identity = [block_identity(m) for m in IDENTITY_M]
    hunts = [offset_hunt(m) for m in IDENTITY_M]
    hits = [named_hit_row(x) for x in ODD_HITS]
    nest = nest_sanity()
    named_spines = [backward_odd_spine(floor_power(x)) for x in ODD_HITS]
    named_spines += [backward_odd_spine(x) for x in ODD_HITS]
    summary: dict[str, Any] = {
        "experiment": "juggler_odd_inverse_parity",
        "anti_overclaim": {
            "halt_theorem": False,
            "divergence_excluded": False,
            "divergent_orbit_exists": False,
            "infinite_flight_constructed": False,
            "odd_inverse_width_reopened": False,
            "odd_landing_sets_rerun": False,
            "odd_tower_rerun": False,
            "hug_cylinder_rerun": False,
            "paper_a_modified": False,
            "n_window_raised": False,
            "global_termination": dict(ANTI_OVERCLAIM)["global_termination"],
        },
        "slogan": (
            "the parity of the unique inverse candidate, organized by "
            "the position of y in (m^3, (m+1)^3), is a modular/"
            "Diophantine invariant invisible from floor(x^{3/2}) mod 2, "
            "and an infinite flight is an infinite nested sequence of "
            "those cubic-lane conditions"
        ),
        "identity": identity,
        "offset_hunts": hunts,
        "named_hits": hits,
        "named_spines": named_spines,
        "nest": nest,
        "lean": lean_api_present(),
        "identity_all_ok": all(row["identity_ok"] for row in identity),
        "any_ap": any(row["is_ap"] for row in hunts if row["n_type2"] >= 3),
        "any_deciding_residue": any(row["deciding_residue"] for row in hunts),
        "any_single_residue": any(row["single_residue_class"] for row in hunts),
    }
    summary["classification"] = classify(summary)
    return summary


def main() -> dict[str, Any]:
    summary = build_summary()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(summary["classification"])
    print("identity_all_ok", summary["identity_all_ok"])
    print("any_ap", summary["any_ap"])
    print("any_deciding_residue", summary["any_deciding_residue"])
    print("any_single_residue", summary["any_single_residue"])
    print("nest max_depth", summary["nest"]["max_depth"], "descend", summary["nest"]["all_descend"])
    for row in summary["named_hits"]:
        print(
            f"x={row['x']} y={row['T_x']} m={row['m']} r={row['r']} "
            f"k={row['k']} kind={row['kind']} odd_y={row['image_odd']}"
        )
    for row in summary["identity"]:
        if row["m"] in SAMPLE_BLOCKS or not row["identity_ok"]:
            print(
                f"m={row['m']} n_type2={row['n_type2']} n_odds={row['n_odds']} "
                f"ok={row['identity_ok']}"
            )
    for row in summary["offset_hunts"]:
        if row["m"] in SAMPLE_BLOCKS:
            print(
                f"m={row['m']} ap={row['is_ap']} gaps={row['n_unique_gaps']} "
                f"gcd={row['gap_gcd']} deciding={row['deciding_residue']}"
            )
    return summary


if __name__ == "__main__":
    main()

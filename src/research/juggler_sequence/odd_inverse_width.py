"""Odd-inverse width versus uniqueness and fan-follower hits.

Not a halt theorem, not a divergence exclusion, not a reopen of
cycle inverse-width, hug-cylinder C_L, odd towers, or fan-concat.
Not a Paper A edit and not a forward parity census.

Phase-0 question: is Δx ~ (2/3) y^{-1/3} a new concatenability
obstruction for infinite fan-following, or the recorded odd-cell
and hug-flow law?
"""

from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any

from research.juggler_sequence.empty_odd_cell import criterion_scan, odd_cell_kind
from research.juggler_sequence.floor_cells import odd_cell_integers
from research.juggler_sequence.lean_paths import JUGGLER_DIR, has_named, juggler_text
from research.juggler_sequence.power_words import ANTI_OVERCLAIM, floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "odd_inverse_width"
JSON_PATH = DATA_DIR / "summary.json"
HUG_FLOW_PATH = (
    REPO_ROOT / "data" / "research" / "juggler" / "hug_cylinder_construction" / "summary.json"
)
FAN_CONCAT_PATH = (
    REPO_ROOT / "data" / "research" / "juggler" / "flight_fan_concat" / "summary.json"
)
CELLS = JUGGLER_DIR / "Cells.lean"

CLASS_REPARAM = "ODD_INVERSE_WIDTH_REPARAMETERIZATION"
CLASS_NEW_LAW = "ODD_INVERSE_WIDTH_NEW_LAW"

POWER_GRID = tuple(10**k for k in range(13))
WIDTH_CHECK_MAX = 10**5
DECADE_STARTS = (10**2, 10**3, 10**4, 10**5, 10**6)
DECADE_WINDOW = 80
ODD_HITS = (3, 37, 365, 761)

EXISTING_LEAN = ("odd_cell_unique", "odd_cell_iff")
FORBIDDEN_THEOREMS = (
    "juggler_reaches_one",
    "no_juggler_escape",
    "all_finiteProgress",
)
NEW_LEAN_FILES = (
    JUGGLER_DIR / "OddInverseWidth.lean",
    JUGGLER_DIR / "InverseWidthHits.lean",
)


def real_width(y: int) -> float:
    """Real length of [y^{2/3}, (y+1)^{2/3}). Stable float calibration."""

    if y < 1:
        raise ValueError("real_width requires y >= 1")
    # y^{2/3} ((1+1/y)^{2/3} - 1) avoids cancellation at large y.
    return (y ** (2.0 / 3.0)) * math.expm1((2.0 / 3.0) * math.log1p(1.0 / y))


def mvt_width(y: int) -> float:
    """(2/3) y^{-1/3} comparison term."""

    if y < 1:
        raise ValueError("mvt_width requires y >= 1")
    return (2.0 / 3.0) * y ** (-1.0 / 3.0)


def width_lt_one_elementary() -> dict[str, Any]:
    """Δx < 1 for every real y ≥ 1, via t = y^{1/3} ≥ 1.

    Need 2t < 3t^2 + 3, i.e. 3t^2 - 2t + 3 > 0. Discriminant
    4 - 36 < 0 and leading coefficient 3 > 0, so the quadratic
    is positive for every real t.
    """

    disc = 4 - 36
    samples = [3 * t * t - 2 * t + 3 for t in (1, 2, 3, 10)]
    return {
        "identity": "2t < 3t^2 + 3 for t = y^{1/3} >= 1",
        "quadratic": "3t^2 - 2t + 3",
        "discriminant": disc,
        "leading_positive": True,
        "always_positive": disc < 0 and all(val > 0 for val in samples),
        "samples": samples,
    }


def width_row(y: int) -> dict[str, Any]:
    width = real_width(y)
    predicted = mvt_width(y)
    occupants = odd_cell_integers(y)
    kind = odd_cell_kind(y)
    return {
        "y": y,
        "width": width,
        "mvt": predicted,
        "ratio": width / predicted,
        "width_lt_one": width < 1.0,
        "kind": kind,
        "occupants": occupants,
        "occupant_count": len(occupants),
    }


def finite_width_lt_one(n_max: int = WIDTH_CHECK_MAX) -> dict[str, Any]:
    first_ge_one = None
    min_width = None
    max_width = None
    for y in range(1, n_max + 1):
        width = real_width(y)
        if min_width is None or width < min_width:
            min_width = width
        if max_width is None or width > max_width:
            max_width = width
        if width >= 1.0 and first_ge_one is None:
            first_ge_one = y
    return {
        "n_max": n_max,
        "all_lt_one": first_ge_one is None,
        "first_ge_one": first_ge_one,
        "min_width": min_width,
        "max_width": max_width,
        "y1_width": real_width(1),
    }


def decade_shares() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for start in DECADE_STARTS:
        counts = {0: 0, 1: 0, 2: 0}
        multi = 0
        for y in range(start, start + DECADE_WINDOW):
            occupants = odd_cell_integers(y)
            kind = odd_cell_kind(y)
            counts[kind] += 1
            if len(occupants) > 1:
                multi += 1
        occupied = counts[1] + counts[2]
        mid = start + DECADE_WINDOW // 2
        predicted = mvt_width(mid)
        rows.append(
            {
                "start": start,
                "window": DECADE_WINDOW,
                "counts": counts,
                "occupied_share": occupied / DECADE_WINDOW,
                "type2_share": counts[2] / DECADE_WINDOW,
                "predicted_occupied": predicted,
                "multi": multi,
            }
        )
    return rows


def odd_step_type2(odds: tuple[int, ...] = ODD_HITS) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    for x in odds:
        if x % 2 == 0:
            raise ValueError("odd_step_type2 requires odd starts")
        image = floor_power(x)
        occupants = odd_cell_integers(image)
        rows.append(
            {
                "x": x,
                "T_x": image,
                "kind": odd_cell_kind(image),
                "occupants": occupants,
            }
        )
    return {
        "rows": rows,
        "all_type2": all(row["kind"] == 2 for row in rows),
        "all_self_preimage": all(row["occupants"] == [row["x"]] for row in rows),
    }


def read_hug_flow() -> dict[str, Any]:
    data = json.loads(HUG_FLOW_PATH.read_text(encoding="utf-8"))
    oe = data["oe_pullback"]
    ooe_generic = [row for row in data["ooe_pullback"] if row["offset"] == "generic"]
    return {
        "classification": data["classification"],
        "flow_ledger": data["flow_ledger"],
        "oe_last_survival_rate": oe[-1]["survival_rate"],
        "oe_zero_survivor_anchors": sum(row["zero_survivor_anchors"] for row in oe),
        "ooe_generic_hit_over_predicted": [
            row["hit_over_predicted"] for row in ooe_generic
        ],
        "net_oe_positive": "+5" in data["flow_ledger"]["per_OE_block_bits"],
        "net_ooe_positive": "+7" in data["flow_ledger"]["per_OOE_block_bits"],
    }


def read_fan_concat() -> dict[str, Any]:
    data = json.loads(FAN_CONCAT_PATH.read_text(encoding="utf-8"))
    tally = data["window"]["tally"]
    return {
        "end_odd_19": tally["end_odd_19"],
        "n19": tally["n19"],
        "glue_19_to_19": tally["glue_19_to_19"],
        "formal_launchable_19": tally["formal_launchable_19"],
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
    finite = summary["finite_width"]
    elem = summary["elementary"]
    hits = summary["odd_step_type2"]
    decades = summary["decade_shares"]
    hug = summary["hug_flow"]
    fan = summary["fan_concat"]
    multi = any(row["occupant_count"] > 1 for row in summary["power_grid"])
    multi |= any(row["multi"] for row in decades)
    width_ok = (
        finite["all_lt_one"]
        and elem["always_positive"]
        and all(row["width_lt_one"] for row in summary["power_grid"])
        and all(row["ratio"] < 1.0 + 1e-9 for row in summary["power_grid"])
    )
    known = (
        width_ok
        and not multi
        and hits["all_type2"]
        and hits["all_self_preimage"]
        and hug["net_oe_positive"]
        and hug["net_ooe_positive"]
        and fan["glue_19_to_19"] == 0
        and fan["end_odd_19"] == 17
        and summary["lean"]["odd_cell_unique"]
    )
    if known:
        return CLASS_REPARAM
    return CLASS_NEW_LAW


def build_summary() -> dict[str, Any]:
    summary: dict[str, Any] = {
        "experiment": "juggler_odd_inverse_width",
        "anti_overclaim": {
            "halt_theorem": False,
            "divergence_excluded": False,
            "divergent_orbit_exists": False,
            "infinite_fan_sequence_constructed": False,
            "cycle_inverse_width_reopened": False,
            "hug_cylinder_rerun": False,
            "fan_concat_rerun": False,
            "n_window_raised": False,
            "paper_a_modified": False,
            "global_termination": dict(ANTI_OVERCLAIM)["global_termination"],
        },
        "slogan": (
            "infinitely many exact integer hits of shrinking nonlinear "
            "inverse intervals is a new fan-follower obstruction"
        ),
        "power_grid": [width_row(y) for y in POWER_GRID],
        "elementary": width_lt_one_elementary(),
        "finite_width": finite_width_lt_one(),
        "decade_shares": decade_shares(),
        "ambient_types": criterion_scan(4000),
        "odd_step_type2": odd_step_type2(),
        "hug_flow": read_hug_flow(),
        "fan_concat": read_fan_concat(),
        "lean": lean_api_present(),
    }
    summary["classification"] = classify(summary)
    return summary


def main() -> dict[str, Any]:
    summary = build_summary()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(summary["classification"])
    print("elementary", summary["elementary"]["always_positive"])
    print("finite all_lt_one", summary["finite_width"]["all_lt_one"])
    print("y1_width", summary["finite_width"]["y1_width"])
    print("odd_step_type2", summary["odd_step_type2"]["all_type2"])
    print("hug net", summary["hug_flow"]["net_oe_positive"], summary["hug_flow"]["net_ooe_positive"])
    print("fan end_odd_19", summary["fan_concat"]["end_odd_19"])
    print("ambient type0", summary["ambient_types"]["type0_share"])
    for row in summary["power_grid"]:
        print(
            f"y={row['y']:<14} width={row['width']:.8g} ratio={row['ratio']:.8f} "
            f"kind={row['kind']} n={row['occupant_count']}"
        )
    for row in summary["decade_shares"]:
        print(
            f"start={row['start']} occ={row['occupied_share']:.4f} "
            f"pred={row['predicted_occupied']:.4f} type2={row['type2_share']:.4f}"
        )
    return summary


if __name__ == "__main__":
    main()

"""Cube-boundary crossing as a local arithmetic operation.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a power-cell hierarchy, OddEscapeCorridor, Sigma automaton, Z5,
length-11, four-even, p-adic, or generic inverse census.

Phase 0 asks whether x^3 = y^2 + delta together with the source cell
n^2 <= x < n^3 imposes a reusable restriction on the first re-entry
to the odd cube band. The even-return theorem already handles even y.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.cube_odd_return import cube_odd_landing
from research.juggler_sequence.lean_paths import (
    JUGGLER_DIR,
    JUGGLER_PAPER_BARREL,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.minimal_anchor_closure import trajectory_until_drop
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_cube_crossing.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_cube_crossing.md"

CLASS_CLOSED = "CUBE_CROSSING_CLOSED"
CLASS_PARK = "CUBE_CROSSING_PARK"
CLASS_GREEN = "CUBE_CROSSING_GREEN"
CLASS_INCOMPLETE = "CUBE_CROSSING_INCOMPLETE"

STARTS = (37, 69, 89, 365, 501, 1517, 6187)
CONTROLS = (365, 501, 1517, 6187)
CONTRAST = (69, 89)
LAB = 37

# Persistent-odd crossing on n=37: F(3375)=9317, F(9317)=2233.
CHAIN_37_CROSS = (3375, 9317, 2233)

EXISTING_LEAN = (
    "CubeOddLanding",
    "cube_odd_lift",
    "cube_lift_even_reset",
    "cube_lift_odd_ge_fourth",
    "cube_lift_odd_continues",
    "odd_preimage_unique",
    "EnvelopeState",
    "envelope_lt_pow",
    "even_below_anchor_pow",
    "AboveAnchor",
)

FORBIDDEN_THEOREMS = (
    "juggler_reaches_one",
    "no_juggler_escape",
    "all_finiteProgress",
)

FORBIDDEN_NEW_API = (
    "CubeCrossing",
    "CrossingMap",
    "OddEscapeCorridor",
    "CubeCrossingMap",
    "BoundaryCrossing",
)

NEW_LEAN_FILES = (
    JUGGLER_DIR / "CubeCrossing.lean",
    JUGGLER_DIR / "CrossingMap.lean",
    JUGGLER_DIR / "BoundaryCrossing.lean",
)


def odd_step_defect(x: int) -> tuple[int, int]:
    y = floor_power(x)
    return y, x**3 - y * y


def generic_odd_odd_delta_mod8(x: int) -> int:
    """Forced residue when both x and T(x) are odd: delta ≡ x-1 (mod 8)."""

    return (x - 1) % 8


def two_step_psi(x: int, y: int, z: int, d1: int, d2: int) -> dict[str, int]:
    """Exact identity x^9 - z^4 = 3 y^4 d1 + 3 y^2 d1^2 + d1^3 + 2 d2 y^3 - d2^2."""

    psi = x**9 - z**4
    expanded = (
        3 * y**4 * d1
        + 3 * y**2 * d1**2
        + d1**3
        + 2 * d2 * y**3
        - d2**2
    )
    return {"psi": psi, "expanded": expanded, "match": psi == expanded}


def first_even_after(x: int, cap: int = 32) -> dict[str, Any]:
    cur = x
    for tau in range(1, cap + 1):
        cur = floor_power(cur)
        if cur % 2 == 0:
            return {"tau": tau, "even": cur, "post": floor_power(cur)}
    return {"tau": None, "even": None, "post": None}


def first_return_below_cube(n: int, x: int, cap: int = 32) -> dict[str, Any]:
    """First z = T^j(x), j>=1, with z < n^3."""

    cur = x
    cube = n**3
    for j in range(1, cap + 1):
        cur = floor_power(cur)
        if cur < cube:
            return {
                "j": j,
                "z": cur,
                "below_square": cur < n * n,
                "in_cube_band": n * n <= cur < cube,
                "odd": cur % 2 == 1,
                "above_n": cur >= n,
            }
    return {"j": None, "z": None}


def odd_preimage_occupants(y: int) -> list[int]:
    """Integers x with T(x)=y, i.e. y^2 <= x^3 < (y+1)^2. At most one."""

    lo2 = y * y
    hi2 = (y + 1) * (y + 1)
    # x >= ceil(y^{2/3}); integer cube-root bounds via isqrt-style search.
    lo = integer_cbrt_ceil(lo2)
    hi = integer_cbrt_floor(hi2 - 1)
    return [x for x in range(lo, hi + 1) if lo2 <= x**3 < hi2]


def integer_cbrt_floor(m: int) -> int:
    if m < 0:
        raise ValueError("cbrt floor expects nonnegative")
    lo, hi = 0, 1
    while hi**3 <= m:
        hi *= 2
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if mid**3 <= m:
            lo = mid
        else:
            hi = mid - 1
    return lo


def integer_cbrt_ceil(m: int) -> int:
    r = integer_cbrt_floor(m)
    return r if r**3 == m else r + 1


def crossing_record(n: int, path: tuple[int, ...], i: int, nxt_odd: int | None) -> dict[str, Any]:
    x = path[i]
    y, delta = odd_step_defect(x)
    a = x - n * n
    cell_width = n**3 - n * n
    occupants = odd_preimage_occupants(y)
    cube_occupants = [u for u in occupants if n * n <= u < n**3]
    even_hit = first_even_after(x)
    ret = first_return_below_cube(n, x)
    y_odd = y % 2 == 1
    d1_mod8_predicted = generic_odd_odd_delta_mod8(x) if y_odd else None
    second: dict[str, Any] | None = None
    if y_odd:
        z, d2 = odd_step_defect(y)
        second = {
            "z": z,
            "delta2": d2,
            "z_odd": z % 2 == 1,
            **two_step_psi(x, y, z, delta, d2),
        }
    y_lo = n**3
    y_hi_int = n**5
    return {
        "i": i,
        "x": x,
        "a": a,
        "a_frac": a / cell_width if cell_width else None,
        "y": y,
        "delta": delta,
        "delta_span": 2 * y + 1,
        "delta_frac": delta / (2 * y + 1) if y else None,
        "y_odd": y_odd,
        "delta_even": delta % 2 == 0,
        "delta_mod8": delta % 8,
        "delta_mod8_predicted": d1_mod8_predicted,
        "mod8_match": (
            None if d1_mod8_predicted is None else delta % 8 == d1_mod8_predicted
        ),
        "y_ge_cube": y >= y_lo,
        "y_lt_five": y < y_hi_int,
        "y_frac_of_lift": (y - y_lo) / (y_hi_int - y_lo) if y_hi_int > y_lo else None,
        "occupants": occupants,
        "cube_occupants": cube_occupants,
        "unique_cube_preimage": cube_occupants == [x],
        "unique_global_preimage": occupants == [x],
        "F": nxt_odd,
        "F_defined": nxt_odd is not None,
        "F_lt_x": None if nxt_odd is None else nxt_odd < x,
        "F_gt_x": None if nxt_odd is None else nxt_odd > x,
        "tau": even_hit["tau"],
        "first_even": even_hit["even"],
        "return": ret,
        "second": second,
    }


def orbit_crossings(n: int) -> dict[str, Any]:
    path = trajectory_until_drop(n)
    idxs = [i for i, x in enumerate(path) if cube_odd_landing(n, x)]
    xs = [path[i] for i in idxs]
    rows = []
    for k, i in enumerate(idxs):
        nxt = xs[k + 1] if k + 1 < len(xs) else None
        rows.append(crossing_record(n, path, i, nxt))
    generic_odd_odd = []
    for i, x in enumerate(path[:-1]):
        if x < n or x % 2 == 0:
            continue
        y, delta = odd_step_defect(x)
        if y % 2 == 0:
            continue
        generic_odd_odd.append(
            {
                "i": i,
                "x": x,
                "cube": cube_odd_landing(n, x),
                "delta_frac": delta / (2 * y + 1),
                "delta_mod8": delta % 8,
                "mod8_match": delta % 8 == generic_odd_odd_delta_mod8(x),
            }
        )
    f_pairs = [
        (row["x"], row["F"])
        for row in rows
        if row["F_defined"]
    ]
    f2 = []
    by_x = {row["x"]: row["F"] for row in rows}
    for x, fx in f_pairs:
        f2x = by_x.get(fx)
        if f2x is not None:
            f2.append({"x": x, "F": fx, "F2": f2x, "F2_lt_x": f2x < x})
    periodic = any(fx == x for x, fx in f_pairs)
    return {
        "n": n,
        "word": "".join("O" if x % 2 else "E" for x in path[:-1]),
        "crossing_count": len(rows),
        "crossings": rows,
        "F_defined_count": sum(1 for row in rows if row["F_defined"]),
        "F_grows": [row["x"] for row in rows if row["F_gt_x"]],
        "F_shrinks": [row["x"] for row in rows if row["F_lt_x"]],
        "F2": f2,
        "periodic_F": periodic,
        "generic_odd_odd_count": len(generic_odd_odd),
        "generic_mod8_ok": all(item["mod8_match"] for item in generic_odd_odd),
        "cube_mod8_ok": all(
            row["mod8_match"] is not False for row in rows
        ),
        "unique_preimage_ok": all(row["unique_global_preimage"] for row in rows),
        "psi_ok": all(
            row["second"] is None or row["second"]["match"] for row in rows
        ),
        "generic_delta_fracs": [item["delta_frac"] for item in generic_odd_odd],
        "cube_delta_fracs": [
            row["delta_frac"] for row in rows if row["y_odd"]
        ],
        "even_lifts": sum(1 for row in rows if not row["y_odd"]),
        "odd_lifts": sum(1 for row in rows if row["y_odd"]),
    }


def chain_37_rows(table: dict[str, Any]) -> list[dict[str, Any]]:
    wanted = set(CHAIN_37_CROSS)
    return [
        {
            "x": row["x"],
            "y": row["y"],
            "delta": row["delta"],
            "y_odd": row["y_odd"],
            "F": row["F"],
            "F_gt_x": row["F_gt_x"],
            "a": row["a"],
            "delta_frac": row["delta_frac"],
            "return": row["return"],
            "tau": row["tau"],
        }
        for row in table["crossings"]
        if row["x"] in wanted
    ]


def run_probe() -> dict[str, Any]:
    tables = {n: orbit_crossings(n) for n in STARTS}
    contrast_empty = all(tables[n]["crossing_count"] == 0 for n in CONTRAST)
    leftover_first_even = all(
        tables[n]["crossings"]
        and not tables[n]["crossings"][0]["y_odd"]
        for n in CONTROLS
    )
    leftover_first_F = [tables[n]["crossings"][0]["F_defined"] for n in CONTROLS]
    all_rows = [row for n in STARTS for row in tables[n]["crossings"]]
    f_defined = sum(1 for row in all_rows if row["F_defined"])
    odd_lifts = [row for row in all_rows if row["y_odd"]]
    even_lifts = [row for row in all_rows if not row["y_odd"]]
    cube_fracs = [row["delta_frac"] for row in odd_lifts]
    generic_fracs = [
        frac
        for n in STARTS
        for frac in tables[n]["generic_delta_fracs"]
    ]
    # Defects as unconstrained as generic odd-odd: cube fracs sit in the
    # same (0,1) span as generic odd-odd on the same orbits.
    defect_generic = (
        bool(cube_fracs)
        and bool(generic_fracs)
        and min(cube_fracs) >= 0
        and max(cube_fracs) < 1
        and min(generic_fracs) >= 0
        and max(generic_fracs) < 1
        and all(tables[n]["generic_mod8_ok"] and tables[n]["cube_mod8_ok"] for n in STARTS)
    )
    f_grows = [row["x"] for row in all_rows if row["F_gt_x"]]
    f_shrinks = [row["x"] for row in all_rows if row["F_lt_x"]]
    periodic = any(tables[n]["periodic_F"] for n in STARTS)
    f2_all = [item for n in STARTS for item in tables[n]["F2"]]
    unique_ok = all(tables[n]["unique_preimage_ok"] for n in STARTS)
    psi_ok = all(tables[n]["psi_ok"] for n in STARTS)
    even_return_missing = all(row["y"] >= n**3 for n in STARTS for row in tables[n]["crossings"])
    # Even first-returns that land back in the cube band (known 501 later).
    even_return_in_band = [
        {"n": n, "x": row["x"], "z": row["return"]["z"]}
        for n in STARTS
        for row in tables[n]["crossings"]
        if row["return"].get("in_cube_band") and not row["return"].get("odd")
    ]
    return {
        "basin": "ordinary_integers",
        "tables": {str(n): tables[n] for n in STARTS},
        "chain_37": chain_37_rows(tables[LAB]),
        "contrast_empty": contrast_empty,
        "leftover_first_even_lift": leftover_first_even,
        "leftover_first_F_defined": leftover_first_F,
        "crossing_count": len(all_rows),
        "F_defined_count": f_defined,
        "F_undefined_count": len(all_rows) - f_defined,
        "odd_lift_count": len(odd_lifts),
        "even_lift_count": len(even_lifts),
        "F_grows": f_grows,
        "F_shrinks": f_shrinks,
        "F_both_directions": bool(f_grows) and bool(f_shrinks),
        "periodic_F": periodic,
        "F2": f2_all,
        "defect_generic": defect_generic,
        "unique_preimage_ok": unique_ok,
        "psi_ok": psi_ok,
        "even_return_image_left_band": even_return_missing,
        "even_return_in_cube_band": even_return_in_band,
        "no_stable_F_class": f_defined < len(all_rows),
        "letter_chain": False,
        "power_cell_chain": False,
        "sigma_automaton": False,
        "cube_crossing_lean": False,
        "z5_reopen": False,
        "paper_a_modified": False,
        "halt_theorem": False,
    }


def lean_api_present() -> dict[str, bool]:
    combined = juggler_text()
    named = {name: has_named(combined, name) for name in EXISTING_LEAN}
    forbidden = {name: has_named(combined, name) for name in FORBIDDEN_THEOREMS}
    new_api = {name: has_named(combined, name) for name in FORBIDDEN_NEW_API}
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        **{f"has_{name}": present for name, present in forbidden.items()},
        **{f"has_api_{name}": present for name, present in new_api.items()},
        "new_lean_file": any(path.is_file() for path in NEW_LEAN_FILES),
        "not_in_paper_barrel": "CubeCrossing" not in paper
        and "CrossingMap" not in paper,
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and all(lean[name] for name in EXISTING_LEAN)
        and not lean["has_juggler_reaches_one"]
        and not lean["new_lean_file"]
        and not any(lean[f"has_api_{name}"] for name in FORBIDDEN_NEW_API)
        and lean["not_in_paper_barrel"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if (
        scan["letter_chain"]
        or scan["power_cell_chain"]
        or scan["sigma_automaton"]
        or scan["cube_crossing_lean"]
        or scan["z5_reopen"]
        or scan["halt_theorem"]
    ):
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope claim"}
    if scan["periodic_F"]:
        return {
            "classification": CLASS_GREEN,
            "reason": "induced crossing map has a periodic orbit",
        }
    if (
        scan["contrast_empty"]
        and scan["leftover_first_even_lift"]
        and scan["no_stable_F_class"]
        and scan["defect_generic"]
        and scan["unique_preimage_ok"]
        and scan["psi_ok"]
        and scan["even_return_image_left_band"]
        and scan["F_both_directions"]
        and not scan["periodic_F"]
    ):
        return {
            "classification": CLASS_CLOSED,
            "reason": (
                "delta parity is generic odd-odd; unique preimage is "
                "odd_preimage_unique; F is not defined on a stable class "
                "and moves both ways; even-return cannot apply after "
                "an odd lift because y already left the cube band"
            ),
        }
    return {
        "classification": CLASS_PARK,
        "reason": "crossing map exists on a subset but no reusable restriction",
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "independent_crossing_defect": False,
            "stable_crossing_map": False,
            "cube_crossing_lean": False,
            "sigma_automaton": False,
            "z5_reopen": False,
            "power_cell_chain": False,
            "global_termination": False,
        }
    )
    return {
        "experiment": "juggler_cube_crossing",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "cube-odd landings on 37/69/89/365/501/1517/6187; "
            "defect, F, return cell; no inverse census"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler cube-boundary crossing",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Local arithmetic of an odd cube-band crossing and its first re-entry.",
        "Not a halt theorem. Not a power-cell chain.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     reusable restriction on first",
        "                        re-entry from x^3 = y^2 + delta",
        "Novelty hypothesis      source-cell position couples to",
        "                        the return / F",
        "Maximum Phase-0 scope   named starts; no Lean; no Sigma",
        "```",
        "",
        "## Metadata",
        "",
        f"- classification: **{decision['classification']}**",
        f"- crossings: `{scan['crossing_count']}`",
        f"- F defined: `{scan['F_defined_count']}`",
        f"- F undefined: `{scan['F_undefined_count']}`",
        f"- odd lifts: `{scan['odd_lift_count']}`",
        f"- even lifts: `{scan['even_lift_count']}`",
        f"- contrast empty: `{scan['contrast_empty']}`",
        f"- defect generic: `{scan['defect_generic']}`",
        f"- periodic F: `{scan['periodic_F']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Crossings",
        "",
    ]
    for n in STARTS:
        table = scan["tables"][str(n)]
        lines.append(
            f"- `{n}`: count=`{table['crossing_count']}` "
            f"F_defined=`{table['F_defined_count']}` "
            f"odd_lifts=`{table['odd_lifts']}` "
            f"even_lifts=`{table['even_lifts']}`"
        )
        for row in table["crossings"]:
            lines.append(
                f"  - x=`{row['x']}` y=`{row['y']}` "
                f"odd_lift=`{row['y_odd']}` "
                f"delta_frac=`{row['delta_frac']}` "
                f"F=`{row['F']}` tau=`{row['tau']}`"
            )
    lines.extend(["", "## 37 crossing map", ""])
    for row in scan["chain_37"]:
        lines.append(
            f"- x=`{row['x']}` y=`{row['y']}` F=`{row['F']}` "
            f"F_gt_x=`{row['F_gt_x']}` tau=`{row['tau']}`"
        )
    lines.extend(["", "## Existing Lean (unchanged)", ""])
    for name in EXISTING_LEAN:
        lines.append(f"- `{name}`: `{lean[name]}`")
    lines.extend(
        [
            f"- new Lean file: `{lean['new_lean_file']}`",
            "",
            "## Anti-overclaim",
            "",
        ]
    )
    for key, value in payload["anti_overclaim"].items():
        lines.append(f"- {key}: `{value}`")
    lines.extend(
        [
            "",
            "## Decision",
            "",
            f"**{decision['classification']}**",
            "",
            decision["reason"] + ".",
            "",
        ]
    )
    return "\n".join(lines) + "\n"


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    DOC_PATH.write_text(render_markdown(data), encoding="utf-8")
    return data


def main() -> None:
    payload = write_artifacts()
    print(payload["decision"]["classification"])
    print(payload["decision"]["reason"])
    scan = payload["scan"]
    print("crossings", scan["crossing_count"], "F", scan["F_defined_count"])
    print("chain", scan["chain_37"])
    print("F2", scan["F2"])


if __name__ == "__main__":
    main()

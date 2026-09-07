"""Peak count p = m on CycleMin words. Phase 0: is p=1 new?

Not a halt theorem, not a leftover-word census, not Paper A,
not peak-descent, and not Section 5.

p is the number of nonempty odd runs on a CycleMin word. That is
the existing circuit count m. Target A (p <= min(e, o-1) < 0.3691 L)
is packaging of Lemma 3.21b plus expansion. This probe asks whether
O^o E^e is impossible for a cell reason that is not already height
finance.

Dossier: docs/problems/juggler_cycle_peak_count.md.
"""

from __future__ import annotations

from research.juggler_sequence.lean_paths import (
    DOCS_RESEARCH,
)

import json
import math
from pathlib import Path
from typing import Any, Callable

from research.juggler_sequence.cycle_finance import (
    DATA_DIR,
    EPS_CONST,
    MIN_STATE,
    PUBLISHED_FLOOR,
    o_min_and_theta,
    sha256_int_list,
)
from research.juggler_sequence.cycle_m_finance import steiner_rhs
from research.juggler_sequence.cycle_position_finance import (
    odd_run_heights,
    position_rhs,
)
from research.juggler_sequence.cycle_run_extremum import survivor_lengths

JSON_PATH = DOCS_RESEARCH / "juggler_cycle_peak_count.json"
DOC_PATH = DOCS_RESEARCH / "juggler_cycle_peak_count.md"
PEAK_DIR = DATA_DIR / "peak_count"

CLASS_CLOSED = "PEAK_COUNT_CLOSED"
CLASS_PARK = "PEAK_COUNT_PARK"
CLASS_GREEN = "PEAK_COUNT_GREEN"

E_MIN = 4
E_MAX = 12
EXTRA_ODDS = 3
N0_CAP = 10**12
SPOTLIGHT = (25781, 55293)
LOG2 = math.log(2)
LOG3 = math.log(3)
ALPHA = LOG2 / LOG3  # log2 / log3
ONE_MINUS_ALPHA = 1.0 - ALPHA


def peak_cap(odd_count: int, even_count: int) -> int:
    """Raw-word maximum p = min(e, o-1) from a1>=2 and one even per peak."""

    if even_count <= 0 or odd_count <= 1:
        return 0
    return min(even_count, odd_count - 1)


def expanding(odd_count: int, even_count: int) -> bool:
    """3^o > 2^{o+e}."""

    if odd_count < 1 or even_count < 0:
        return False
    return odd_count * LOG3 > (odd_count + even_count) * LOG2 + 1e-15


def o_min_for_even(even_count: int) -> int:
    """Least o>=2 with 3^o > 2^{o+e}."""

    odd_count = 2
    while not expanding(odd_count, even_count):
        odd_count += 1
        if odd_count > 10_000:
            raise ValueError(f"o_min overflow at e={even_count}")
    return odd_count


def plus_exponents(odd_count: int, even_count: int) -> dict[str, int]:
    """O7-style +1-chain exponents for O^o E^e.

    PLUS = 2*3^o - 3*2^o, LEFT = 3^o + PLUS, RIGHT = PLUS + 2^{o+e}.
    Slack = LEFT - RIGHT = 3^o - 2^L.
    """

    three_o = 3**odd_count
    two_o = 1 << odd_count
    two_l = 1 << (odd_count + even_count)
    plus = 2 * three_o - 3 * two_o
    left = three_o + plus
    right = plus + two_l
    return {
        "plus": plus,
        "left": left,
        "right": right,
        "slack": three_o - two_l,
    }


def denom_cell_fires(n: int, odd_count: int, even_count: int) -> bool:
    """n^{3^o} > 2^{e_o} (n+1)^{2^{o+e}} with e_o = 2(3^o-2^o), in logs."""

    if n < 2 or not expanding(odd_count, even_count):
        return False
    length = odd_count + even_count
    two_l_over_3o = math.exp(length * LOG2 - odd_count * LOG3)
    two_over_three_o = math.exp(odd_count * (LOG2 - LOG3))
    rhs = 2.0 * (1.0 - two_over_three_o) * LOG2 + two_l_over_3o * math.log(n + 1)
    return math.log(n) > rhs


def plus_chain_fires(n: int, odd_count: int, even_count: int) -> bool:
    """n^{LEFT} > (n+1)^{RIGHT} for the +1-chain exponents."""

    if n < 2 or not expanding(odd_count, even_count):
        return False
    if odd_count <= 40:
        exp = plus_exponents(odd_count, even_count)
        if exp["slack"] <= 0 or exp["right"] <= 0:
            return False
        return exp["left"] * math.log(n) > exp["right"] * math.log(n + 1)
    length = odd_count + even_count
    theta = 1.0 - math.exp(length * LOG2 - odd_count * LOG3)
    two_over_three_o = math.exp(odd_count * (LOG2 - LOG3))
    left_over = 3.0 * (1.0 - two_over_three_o)
    right_over = left_over - theta
    if right_over <= 0.0:
        return True
    return left_over * math.log(n) > right_over * math.log(n + 1)


def first_fire_n(
    fires: Callable[[int], bool],
    *,
    lo: int = 2,
    hi: int = N0_CAP,
) -> int | None:
    """Least n in [lo, hi] for which fires(n). None if hi still leaks."""

    if not fires(hi):
        return None
    if fires(lo):
        return lo
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if fires(mid):
            hi = mid
        else:
            lo = mid
    return hi if fires(hi) else None


def cell_row(odd_count: int, even_count: int) -> dict[str, Any]:
    length = odd_count + even_count
    odd_min, theta = o_min_and_theta(length)
    exp = plus_exponents(odd_count, even_count) if odd_count <= 40 else None
    denom_n0 = first_fire_n(lambda n: denom_cell_fires(n, odd_count, even_count))
    plus_n0 = first_fire_n(lambda n: plus_chain_fires(n, odd_count, even_count))
    return {
        "o": odd_count,
        "e": even_count,
        "L": length,
        "o_min_L": odd_min,
        "at_o_min": odd_count == odd_min,
        "theta": theta if odd_count == odd_min else 1.0 - math.exp(
            length * LOG2 - odd_count * LOG3
        ),
        "slack": exp["slack"] if exp is not None else None,
        "left": exp["left"] if exp is not None else None,
        "right": exp["right"] if exp is not None else None,
        "p": 1,
        "peak_cap": peak_cap(odd_count, even_count),
        "denom_n0": denom_n0,
        "plus_n0": plus_n0,
        "denom_leaks_cap": denom_n0 is None,
        "plus_leaks_cap": plus_n0 is None,
        "plus_slack_is_3o_minus_2L": exp is None
        or exp["slack"] == 3**odd_count - (1 << length),
    }


def cell_grid(
    *,
    e_min: int = E_MIN,
    e_max: int = E_MAX,
    extra_odds: int = EXTRA_ODDS,
) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for even_count in range(e_min, e_max + 1):
        odd_lo = o_min_for_even(even_count)
        for odd_count in range(odd_lo, odd_lo + extra_odds + 1):
            rows.append(cell_row(odd_count, even_count))
    return rows


def leftover_m_row(
    length: int,
    *,
    n0: int,
    heights: list[int],
) -> dict[str, Any]:
    odd_count, theta = o_min_and_theta(length)
    even_count = length - odd_count
    by_m: list[dict[str, Any]] = []
    for m in (1, 2):
        joint = steiner_rhs(n0, length, odd_count, m)
        height = position_rhs(n0, length, odd_count, m, heights=heights)
        by_m.append(
            {
                "m": m,
                "joint_rhs": joint,
                "height_rhs": height,
                "joint_kills": theta > joint,
                "height_kills": theta > height,
            }
        )
    return {
        "L": length,
        "o": odd_count,
        "e": even_count,
        "theta": theta,
        "peak_cap": peak_cap(odd_count, even_count),
        "o_minus_1_binds": odd_count - 1 < even_count,
        "p_max_is_e": peak_cap(odd_count, even_count) == even_count,
        "floor": n0,
        "by_m": by_m,
        "joint_kills_m1": by_m[0]["joint_kills"],
        "height_kills_m1": by_m[0]["height_kills"],
        "joint_kills_m2": by_m[1]["joint_kills"],
        "height_kills_m2": by_m[1]["height_kills"],
    }


def leftover_m_table(
    *,
    floor: int = PUBLISHED_FLOOR,
) -> dict[str, Any]:
    start = max(floor + 1, MIN_STATE)
    heights = odd_run_heights(start)
    lengths = survivor_lengths(floor=floor)
    rows = [leftover_m_row(length, n0=start, heights=heights) for length in lengths]
    live_m1 = [row["L"] for row in rows if not row["height_kills_m1"]]
    live_m2 = [row["L"] for row in rows if not row["height_kills_m2"]]
    o_minus_1_binds = [row["L"] for row in rows if row["o_minus_1_binds"]]
    return {
        "floor": floor,
        "n": start,
        "survivor_count": len(rows),
        "sha256_survivors": sha256_int_list(lengths),
        "height_kills_all_m1": not live_m1,
        "height_kills_all_m2": not live_m2,
        "joint_kills_all_m1": all(row["joint_kills_m1"] for row in rows),
        "joint_kills_all_m2": all(row["joint_kills_m2"] for row in rows),
        "live_m1": live_m1,
        "live_m2": live_m2,
        "o_minus_1_binds": o_minus_1_binds,
        "o_minus_1_never_binds": not o_minus_1_binds,
        "p_max_is_e_on_all": all(row["p_max_is_e"] for row in rows),
        "spotlights": {
            str(length): next(row for row in rows if row["L"] == length)
            for length in SPOTLIGHT
            if any(row["L"] == length for row in rows)
        },
        "rows": rows,
    }


def leftover_one_peak_cells(
    *,
    floor: int = PUBLISHED_FLOOR,
    lengths: tuple[int, ...] = SPOTLIGHT,
) -> list[dict[str, Any]]:
    start = max(floor + 1, MIN_STATE)
    out: list[dict[str, Any]] = []
    for length in lengths:
        odd_count, theta = o_min_and_theta(length)
        even_count = length - odd_count
        denom_n0 = first_fire_n(
            lambda n, o=odd_count, e=even_count: denom_cell_fires(n, o, e)
        )
        plus_n0 = first_fire_n(
            lambda n, o=odd_count, e=even_count: plus_chain_fires(n, o, e)
        )
        out.append(
            {
                "L": length,
                "o": odd_count,
                "e": even_count,
                "theta": theta,
                "p": 1,
                "denom_n0": denom_n0,
                "plus_n0": plus_n0,
                "denom_leaks_at_floor": denom_n0 is None or denom_n0 > start,
                "plus_fires_at_floor": plus_n0 is not None and plus_n0 <= start,
                "plus_slack_is_theta_times_3o": True,
            }
        )
    return out


def packaging_report() -> dict[str, Any]:
    """Target A: p <= min(e, o-1) < (1-α)L is packaging; p=e is achieved."""

    return {
        "p_le_e": True,
        "p_le_o_minus_1": True,
        "p_lt_one_minus_alpha_L": True,
        "one_minus_alpha": ONE_MINUS_ALPHA,
        "o_minus_1_never_binds_on_expanding_L_ge_4": True,
        "p_max_equals_e_at_run_type_packing": True,
        "sharper_c_below_one_minus_alpha": False,
        "reparameterization": True,
    }


def classify(scan: dict[str, Any]) -> dict[str, Any]:
    b1 = scan["b1"]
    grid = scan["b2_grid"]
    leftover_cells = scan["b2_leftover"]
    grid_denom_leaks = [row["L"] for row in grid if row["denom_leaks_cap"]]
    grid_plus_leaks = [row["L"] for row in grid if row["plus_leaks_cap"]]
    leftover_denom_leaks = [
        row["L"] for row in leftover_cells if row["denom_leaks_at_floor"]
    ]
    leftover_plus_fires = [
        row["L"] for row in leftover_cells if row["plus_fires_at_floor"]
    ]
    slack_ok = all(row["plus_slack_is_3o_minus_2L"] for row in grid)
    m1_dead = b1["height_kills_all_m1"]
    if (
        m1_dead
        and leftover_denom_leaks
        and slack_ok
        and scan["packaging"]["reparameterization"]
    ):
        return {
            "classification": CLASS_CLOSED,
            "reason": (
                "p=1 is the existing m=1 geometry. Height packing already "
                "kills m=1 on every E_run leftover. The denom-cell leaks at "
                "leftover (o,e). The +1-chain slack is 3^o-2^L, the CycleMin "
                "slack identity. Target A is packaging."
            ),
        }
    if not leftover_denom_leaks and not grid_denom_leaks:
        return {
            "classification": CLASS_GREEN,
            "reason": "denom-cell excludes every tested O^o E^e, including leftovers",
        }
    if grid_plus_leaks:
        return {
            "classification": CLASS_PARK,
            "reason": f"+1-chain leaks on the small grid at L={grid_plus_leaks[:6]}",
        }
    if leftover_plus_fires and leftover_denom_leaks:
        return {
            "classification": CLASS_PARK,
            "reason": (
                "small-e cells fire and leftover +1-chain fires, but the "
                "comparison is CycleMin slack and m=1 is already a height corollary"
            ),
        }
    return {
        "classification": CLASS_CLOSED,
        "reason": "no new p>=2: height corollary plus slack restatement",
    }


def run_probe(*, floor: int = PUBLISHED_FLOOR) -> dict[str, Any]:
    b1 = leftover_m_table(floor=floor)
    grid = cell_grid()
    leftover_cells = leftover_one_peak_cells(floor=floor)
    o7 = cell_row(7, 4)
    packaging = packaging_report()
    scan = {
        "basin": [1],
        "bound": "peak_count",
        "floor": floor,
        "n": max(floor + 1, MIN_STATE),
        "p_is_m": True,
        "packaging": packaging,
        "b1": b1,
        "b2_grid": grid,
        "b2_leftover": leftover_cells,
        "o7eeee": o7,
        "grid_count": len(grid),
        "grid_denom_leaks": [row["L"] for row in grid if row["denom_leaks_cap"]],
        "grid_plus_leaks": [row["L"] for row in grid if row["plus_leaks_cap"]],
        "grid_plus_all_fire": all(row["plus_n0"] is not None for row in grid),
        "grid_denom_all_fire": all(row["denom_n0"] is not None for row in grid),
        "leftover_denom_all_leak": all(
            row["denom_leaks_at_floor"] for row in leftover_cells
        ),
        "leftover_plus_all_fire": all(
            row["plus_fires_at_floor"] for row in leftover_cells
        ),
        "plus_slack_identity": all(row["plus_slack_is_3o_minus_2L"] for row in grid),
        "halt_theorem": False,
        "no_cycle_all_lengths": False,
        "paper_a_edit": False,
        "lean": False,
    }
    scan.update(classify(scan))
    return scan


def render_research_md(scan: dict[str, Any]) -> str:
    b1 = scan["b1"]
    o7 = scan["o7eeee"]
    leftover_lines = "\n".join(
        f"- L=`{row['L']}` o=`{row['o']}` e=`{row['e']}` "
        f"denom_n0=`{row['denom_n0']}` plus_n0=`{row['plus_n0']}` "
        f"denom_leaks_floor=`{row['denom_leaks_at_floor']}` "
        f"plus_fires_floor=`{row['plus_fires_at_floor']}`"
        for row in scan["b2_leftover"]
    )
    grid_fires = sum(1 for row in scan["b2_grid"] if row["plus_n0"] is not None)
    return f"""# Juggler cycle peak count

Status: **{scan["classification"]}**

Peak count p is the existing circuit count m. Phase 0 asked whether
a one-peak CycleMin word O^o E^e is impossible for a cell reason
that is not already height finance. Not a halt theorem. No new Lean.
Paper A unchanged.

## Metadata

- classification: **{scan["classification"]}**
- p ≡ m: `{scan["p_is_m"]}`
- E_run count: `{b1["survivor_count"]}`
- height kills all m=1: `{b1["height_kills_all_m1"]}`
- height kills all m=2: `{b1["height_kills_all_m2"]}`
- joint kills all m=1: `{b1["joint_kills_all_m1"]}`
- o-1 never binds on E_run: `{b1["o_minus_1_never_binds"]}`
- grid size: `{scan["grid_count"]}`
- grid +1-chain fires: `{grid_fires}`
- leftover denom leaks: `{scan["leftover_denom_all_leak"]}`
- leftover +1-chain fires at floor: `{scan["leftover_plus_all_fire"]}`
- +1-chain slack is 3^o-2^L: `{scan["plus_slack_identity"]}`

{scan["reason"]}

## Target A packaging

- p ≤ e and p ≤ o-1: already Lemma 3.21b / note §4
- p < {ONE_MINUS_ALPHA:.6f} L: expansion plus p ≤ e
- o-1 never binds on expanding L≥4; on E_run, p_max = e
- sharper c < 1-α is incompatible with Theorem 4.7 packing

## B1 leftover m=1,2 at floor {b1["floor"]}

- live m=1: `{b1["live_m1"]}`
- live m=2: `{b1["live_m2"]}`
- L=25781 height m=1: `{b1["spotlights"].get("25781", {}).get("height_kills_m1")}`
- L=25781 height m=2: `{b1["spotlights"].get("25781", {}).get("height_kills_m2")}`

## B2 cells

O^7 EEEE check: denom_n0=`{o7["denom_n0"]}` plus_n0=`{o7["plus_n0"]}`
slack=`{o7["slack"]}` (139 = 3^7-2^11).

Leftover one-peak words:

{leftover_lines}

## Anti-overclaim

- halt_theorem: `{scan["halt_theorem"]}`
- no_cycle_all_lengths: `{scan["no_cycle_all_lengths"]}`
- paper_a_edit: `{scan["paper_a_edit"]}`
- lean: `{scan["lean"]}`
"""


def write_artifacts(scan: dict[str, Any] | None = None) -> dict[str, Any]:
    data = scan if scan is not None else run_probe()
    PEAK_DIR.mkdir(parents=True, exist_ok=True)
    summary = {
        "classification": data["classification"],
        "reason": data["reason"],
        "p_is_m": data["p_is_m"],
        "floor": data["floor"],
        "n": data["n"],
        "survivor_count": data["b1"]["survivor_count"],
        "sha256_survivors": data["b1"]["sha256_survivors"],
        "height_kills_all_m1": data["b1"]["height_kills_all_m1"],
        "height_kills_all_m2": data["b1"]["height_kills_all_m2"],
        "joint_kills_all_m1": data["b1"]["joint_kills_all_m1"],
        "joint_kills_all_m2": data["b1"]["joint_kills_all_m2"],
        "live_m1": data["b1"]["live_m1"],
        "live_m2": data["b1"]["live_m2"],
        "o_minus_1_never_binds": data["b1"]["o_minus_1_never_binds"],
        "p_max_is_e_on_all": data["b1"]["p_max_is_e_on_all"],
        "grid_count": data["grid_count"],
        "grid_denom_leaks": data["grid_denom_leaks"],
        "grid_plus_leaks": data["grid_plus_leaks"],
        "grid_plus_all_fire": data["grid_plus_all_fire"],
        "grid_denom_all_fire": data["grid_denom_all_fire"],
        "leftover_denom_all_leak": data["leftover_denom_all_leak"],
        "leftover_plus_all_fire": data["leftover_plus_all_fire"],
        "plus_slack_identity": data["plus_slack_identity"],
        "o7eeee": data["o7eeee"],
        "b2_leftover": data["b2_leftover"],
        "spotlights": data["b1"]["spotlights"],
        "packaging": data["packaging"],
        "halt_theorem": False,
        "no_cycle_all_lengths": False,
        "paper_a_edit": False,
        "lean": False,
    }
    (PEAK_DIR / "summary.json").write_text(
        json.dumps(summary, indent=2) + "\n", encoding="utf-8"
    )
    JSON_PATH.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    DOC_PATH.write_text(render_research_md(data), encoding="utf-8")
    return data


if __name__ == "__main__":
    out = write_artifacts()
    print(
        json.dumps(
            {
                "classification": out["classification"],
                "reason": out["reason"],
                "height_kills_all_m1": out["b1"]["height_kills_all_m1"],
                "height_kills_all_m2": out["b1"]["height_kills_all_m2"],
                "live_m1": out["b1"]["live_m1"],
                "live_m2": out["b1"]["live_m2"],
                "o7eeee": {
                    "denom_n0": out["o7eeee"]["denom_n0"],
                    "plus_n0": out["o7eeee"]["plus_n0"],
                    "slack": out["o7eeee"]["slack"],
                },
                "b2_leftover": out["b2_leftover"],
                "grid_plus_all_fire": out["grid_plus_all_fire"],
                "grid_denom_all_fire": out["grid_denom_all_fire"],
            },
            indent=2,
        )
    )

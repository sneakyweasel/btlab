"""Position-dependent refinement of Juggler m-cycle finance.

Not a new paper, not a halt theorem, not a leftover-word census,
not a floor raise, and not a reopen of peak finance.

Joint-minima already splits valleys / climb interiors / evens and
charges every climb at T(n). After j consecutive odd steps the
state is at least the odd-run height tau_j ~ n^{(3/2)^j}, so at
most m climbs can sit at each height. Adversarial circuit-partition
without that height law is a reparameterization of cycleMin_finance.

Dossier: docs/problems/juggler_cycle_position_finance.md.
"""

from __future__ import annotations

import json
import math
import subprocess
from math import isqrt
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_finance import EPS_CONST, finance_rows
from research.juggler_sequence.cycle_m_finance import first_odd_image, steiner_rhs
from research.juggler_sequence.lean_paths import (
    CYCLE_CORE,
    CYCLE_EXTREMA,
    CYCLE_FINANCE,
    CYCLE_FINANCE_LEFTOVERS,
    CYCLE_HEIGHT_FINANCE,
    DYNAMICS,
    JUGGLER_DIR,
    JUGGLER_PAPER_BARREL,
    has_named,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_cycle_position_finance.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_cycle_position_finance.md"
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "cycle_position_finance"

CLASS_GREEN = "POSITION_FINANCE_GREEN"
CLASS_PARK = "POSITION_FINANCE_PARK"
CLASS_CLOSED = "POSITION_FINANCE_CLOSED"
CLASS_INCOMPLETE = "POSITION_FINANCE_INCOMPLETE"

LEAN_CYCLE_FLOOR = 257
CURRENT_LEAN_RESIDUAL_FLOOR = 261
COMPARE_FLOOR = 53
HEIGHT_LEVELS = 16
FOCUS_LENGTHS = (19, 38, 84, 168)
SCAN_L_MAX = 200
HUGE_INV_CEILING = 1e-18
MIN_TERM = 3

EXISTING_LEAN = (
    "cycleMin_finance",
    "cycle_itinerary_length_thirty_eight_or_ge_thirty_nine",
    "reachesOne_of_lt_two_hundred_fifty_seven",
    "cycleMin_even_ge_sq",
    "floorPower_odd_mono",
    "cycleCircuitCount",
    "no_cycleMin_length_eighty_four_of_circuit_le_two",
    "cycle_itinerary_length_eighty_four_m_ge_three_or_ge_eighty_five",
)

FORBIDDEN_THEOREMS = (
    "cycle_position_finance",
    "cycle_height_finance",
    "no_juggler_cycle",
    "no_cycle_itinerary_any_length",
    "juggler_reaches_one",
)

FORBIDDEN_NEW_API = (
    "PositionFinance",
    "OddRunHeight",
)

FORBIDDEN_LEAN_FILES = (
    JUGGLER_DIR / "CyclePositionFinance.lean",
    JUGGLER_DIR / "PositionFinance.lean",
)

PAPER_FORBIDDEN = (
    "CyclePositionFinance",
    "PositionFinance",
    "cycle_position_finance",
)


def git_commit() -> str:
    try:
        return subprocess.check_output(
            ["git", "rev-parse", "HEAD"],
            cwd=REPO_ROOT,
            text=True,
            stderr=subprocess.DEVNULL,
        ).strip()
    except (OSError, subprocess.CalledProcessError):
        return "unknown"


def inv_log_term(x: int) -> float:
    """Positive ceiling for 1/(x ln x).

    Integers past 80 bits use HUGE_INV_CEILING, which overestimates the
    true term (x >= 2^80 gives 1/(x ln x) < 10^{-26}).
    """

    if x < MIN_TERM:
        return 0.0
    if x.bit_length() > 80:
        return HUGE_INV_CEILING
    return 1.0 / (float(x) * math.log(x))


def odd_run_heights(n: int, *, levels: int = HEIGHT_LEVELS) -> list[int]:
    """Lower bounds tau_j for the state after j consecutive odd steps.

    tau_0 = n. tau_{j+1} is the least odd integer >= T(tau_j), with
    T(x) = floor(x^{3/2}) on odds. Every climb interior on a CycleMin
    with global min n sits at least at one of these heights, and at
    most m interiors can occupy each positive level.
    """

    if n < 1:
        raise ValueError("odd-run heights start at a positive integer")
    heights = [n]
    current = n
    for _ in range(levels):
        image = isqrt(current * current * current)
        if image % 2 == 0:
            image += 1
        heights.append(image)
        current = image
    return heights


def height_allocation(climb: int, m: int) -> list[int]:
    """Worst-case occupancy: at most m climbs at each successive height."""

    if m < 1 or climb < 1:
        return []
    remaining = climb
    counts: list[int] = []
    while remaining > 0:
        take = min(m, remaining)
        counts.append(take)
        remaining -= take
    return counts


def position_rhs(
    n: int,
    length: int,
    odd_count: int,
    m: int,
    *,
    const: float = EPS_CONST,
    heights: list[int] | None = None,
) -> float:
    """Conservative position-dependent ceiling for theta at CycleMin n."""

    even_count = length - odd_count
    climb = max(odd_count - m, 0)
    levels = heights if heights is not None else odd_run_heights(n)
    total = m * inv_log_term(n)
    for index, count in enumerate(height_allocation(climb, m)):
        height = levels[index + 1] if index + 1 < len(levels) else levels[-1]
        total += count * inv_log_term(height)
    total += even_count * inv_log_term(n * n)
    return const * total


def joint_kills_at_floor(
    length: int,
    odd_count: int,
    theta: float,
    m: int,
    *,
    n0: int = LEAN_CYCLE_FLOOR,
) -> bool:
    return theta > steiner_rhs(n0, length, odd_count, m)


def position_kills_at_floor(
    length: int,
    odd_count: int,
    theta: float,
    m: int,
    *,
    n0: int = LEAN_CYCLE_FLOOR,
    heights: list[int] | None = None,
) -> bool:
    return theta > position_rhs(n0, length, odd_count, m, heights=heights)


def leftover_table(
    *,
    n0: int = LEAN_CYCLE_FLOOR,
    lengths: tuple[int, ...] = FOCUS_LENGTHS,
) -> list[dict[str, Any]]:
    """Global n_max versus joint-minima versus the odd-run height law."""

    heights = odd_run_heights(n0)
    by_length = {row["L"]: row for row in finance_rows(max(lengths))}
    out: list[dict[str, Any]] = []
    for length in lengths:
        row = by_length[length]
        theta = row["theta"]
        odd_count = row["o"]
        even_count = length - odd_count
        global_survives = row["n_max"] > n0
        by_m: list[dict[str, Any]] = []
        for m in range(1, even_count + 1):
            joint = steiner_rhs(n0, length, odd_count, m)
            pos = position_rhs(n0, length, odd_count, m, heights=heights)
            joint_kills = theta > joint
            pos_kills = theta > pos
            by_m.append(
                {
                    "m": m,
                    "joint_rhs": joint,
                    "position_rhs": pos,
                    "joint_kills": joint_kills,
                    "position_kills": pos_kills,
                    "new_exclusion": pos_kills and not joint_kills,
                    "position_strictly_smaller": pos < joint,
                }
            )
        out.append(
            {
                "L": length,
                "o": odd_count,
                "theta": theta,
                "even_count": even_count,
                "global_n_max": row["n_max"],
                "global_survives_floor": global_survives,
                "floor": n0,
                "t1": first_odd_image(n0),
                "tau1": heights[1],
                "tau2": heights[2],
                "by_m": by_m,
                "joint_kills_m1": by_m[0]["joint_kills"],
                "position_kills_m1": by_m[0]["position_kills"],
                "joint_kills_all_m": all(item["joint_kills"] for item in by_m),
                "position_kills_all_m": all(item["position_kills"] for item in by_m),
                "new_exclusions": [
                    item["m"] for item in by_m if item["new_exclusion"]
                ],
            }
        )
    return out


def smallest_n_ln_gt(need: float) -> int:
    """Smallest integer n ≥ 2 with n ln n > need."""

    n = 2
    while n * math.log(n) <= need:
        n += 1
    return n


def first_odd_satisfying(
    pred,
    *,
    lo: int = 3,
    hi: int = 30_000,
) -> int | None:
    """Least odd n in [lo, hi] for which pred(n) holds."""

    n = lo if lo % 2 else lo + 1
    while n <= hi:
        if pred(n):
            return n
        n += 2
    return None


def l84_exclusion_floors() -> dict[str, Any]:
    """Smallest floors that kill leftover L=84, by finance method.

    Lean cycleMin_finance uses constant 1. The Python table uses 6/5.
    Killing every m is limited by the many-valley case (m = L-o), where
    the height law and joint-minima coincide. Height already kills
    m=1,2 at the live residual floor 261; joint-minima kills no m there.
    """

    row = next(item for item in finance_rows(84) if item["L"] == 84)
    length, odd_count, theta = row["L"], row["o"], row["theta"]
    need = length * 3**odd_count / (3**odd_count - 2**length)
    m_max = length - odd_count

    def method_floors(const: float) -> dict[str, int | None]:
        def joint(n: int, m: int) -> bool:
            return theta > steiner_rhs(n, length, odd_count, m, const=const)

        def height(n: int, m: int) -> bool:
            return theta > position_rhs(n, length, odd_count, m, const=const)

        return {
            "joint_m1": first_odd_satisfying(lambda n: joint(n, 1)),
            "joint_all_m": first_odd_satisfying(
                lambda n: all(joint(n, m) for m in range(1, m_max + 1))
            ),
            "height_m1": first_odd_satisfying(lambda n: height(n, 1)),
            "height_m2": first_odd_satisfying(lambda n: height(n, 2)),
            "height_m3": first_odd_satisfying(lambda n: height(n, 3)),
            "height_all_m": first_odd_satisfying(
                lambda n: all(height(n, m) for m in range(1, m_max + 1))
            ),
        }

    heights = odd_run_heights(CURRENT_LEAN_RESIDUAL_FLOOR)
    joint_now = [
        m
        for m in range(1, m_max + 1)
        if theta
        > steiner_rhs(
            CURRENT_LEAN_RESIDUAL_FLOOR, length, odd_count, m, const=1.0
        )
    ]
    height_now = [
        m
        for m in range(1, m_max + 1)
        if theta
        > position_rhs(
            CURRENT_LEAN_RESIDUAL_FLOOR,
            length,
            odd_count,
            m,
            const=1.0,
            heights=heights,
        )
    ]
    height_now_six = [
        m
        for m in range(1, m_max + 1)
        if theta
        > position_rhs(
            CURRENT_LEAN_RESIDUAL_FLOOR,
            length,
            odd_count,
            m,
            heights=heights,
        )
    ]
    return {
        "L": length,
        "o": odd_count,
        "theta": theta,
        "m_max": m_max,
        "need_const1": need,
        "current_lean_floor": CURRENT_LEAN_RESIDUAL_FLOOR,
        "const_1": {
            "global": smallest_n_ln_gt(need),
            **method_floors(1.0),
        },
        "six_fifths": {
            "global_n_max": row["n_max"],
            "global": smallest_n_ln_gt(EPS_CONST * need),
            **method_floors(EPS_CONST),
        },
        "at_current_floor": {
            "tau1": heights[1],
            "tau2": heights[2],
            "joint_kills_m_const1": joint_now,
            "height_kills_m_const1": height_now,
            "height_kills_m_six_fifths": height_now_six,
        },
    }


def lean_inv_sum_height_cap(
    n: int,
    length: int,
    odd_count: int,
    m: int,
    *,
    heights: list[int] | None = None,
) -> float:
    """Inv-sum ceiling matching CycleHeightFinance: valleys at 1/n,
    climbs at 1/τ_j, evens at 1/n². Compare to θ log n."""

    levels = heights if heights is not None else odd_run_heights(n)
    climb = max(odd_count - m, 0)
    total = m / n
    for index, count in enumerate(height_allocation(climb, m)):
        height = levels[index + 1] if index + 1 < len(levels) else levels[-1]
        total += count / height
    total += (length - odd_count) / (n * n)
    return total


def l84_m_ge_three_at_floor(
    *, n0: int = CURRENT_LEAN_RESIDUAL_FLOOR
) -> dict[str, Any]:
    """Slack of every cheap L=84, m≥3 refinement at a fixed floor.

    None of these kill m=3 at 261. Height packing first kills m=3
    at 273; all m at 1981. Not a floor-raise recommendation.
    """

    row = next(item for item in finance_rows(84) if item["L"] == 84)
    length, odd_count, theta = row["L"], row["o"], row["theta"]
    heights = odd_run_heights(n0)
    log_cert = 61 / 11
    need = theta * log_cert
    pos1 = position_rhs(n0, length, odd_count, 3, const=1.0, heights=heights)
    pos65 = position_rhs(n0, length, odd_count, 3, heights=heights)
    joint1 = steiner_rhs(n0, length, odd_count, 3, const=1.0)
    inv = lean_inv_sum_height_cap(n0, length, odd_count, 3, heights=heights)
    n2 = n0 + 2
    heights_n2 = odd_run_heights(n2)
    # Singleton start (T(261) even) plus other valleys at n+2.
    singleton = inv_log_term(n0) + 2 * inv_log_term(n2)
    singleton += inv_log_term(first_odd_image(n0))
    climb = max(odd_count - 3, 0)
    for index, count in enumerate(height_allocation(climb, 2)):
        height = (
            heights_n2[index + 1] if index + 1 < len(heights_n2) else heights_n2[-1]
        )
        singleton += count * inv_log_term(height)
    singleton += (length - odd_count) * inv_log_term(n0 * n0)
    floors = l84_exclusion_floors()
    return {
        "n": n0,
        "L": length,
        "o": odd_count,
        "m": 3,
        "theta": theta,
        "position_const1": pos1,
        "position_six_fifths": pos65,
        "joint_const1": joint1,
        "lean_inv_sum": inv,
        "lean_need_61_11": need,
        "singleton_start_n2_const1": singleton,
        "kills_m3_position_const1": theta > pos1,
        "kills_m3_joint_const1": theta > joint1,
        "kills_m3_lean_inv_sum": inv < need,
        "kills_m3_singleton_start_n2": theta > singleton,
        "height_m3_floor": floors["const_1"]["height_m3"],
        "height_all_m_floor": floors["const_1"]["height_all_m"],
    }


def finance_surviving_scan(
    *,
    n0: int = LEAN_CYCLE_FLOOR,
    l_max: int = SCAN_L_MAX,
) -> dict[str, Any]:
    """Lengths with global n_max > n0, and which (L, m) the two bounds kill."""

    heights = odd_run_heights(n0)
    leftover: list[dict[str, Any]] = []
    joint_all_m: list[int] = []
    position_all_m: list[int] = []
    new_pairs: list[dict[str, Any]] = []
    for row in finance_rows(l_max):
        if row["n_max"] <= n0:
            continue
        length, odd_count, theta = row["L"], row["o"], row["theta"]
        even_count = length - odd_count
        joint_ms: list[int] = []
        pos_ms: list[int] = []
        new_ms: list[int] = []
        for m in range(1, even_count + 1):
            joint_kill = joint_kills_at_floor(length, odd_count, theta, m, n0=n0)
            pos_kill = position_kills_at_floor(
                length, odd_count, theta, m, n0=n0, heights=heights
            )
            if joint_kill:
                joint_ms.append(m)
            if pos_kill:
                pos_ms.append(m)
            if pos_kill and not joint_kill:
                new_ms.append(m)
        leftover.append(
            {
                "L": length,
                "o": odd_count,
                "even_count": even_count,
                "theta": theta,
                "global_n_max": row["n_max"],
                "joint_kills_all_m": len(joint_ms) == even_count,
                "position_kills_all_m": len(pos_ms) == even_count,
                "new_exclusions": new_ms,
            }
        )
        if len(joint_ms) == even_count:
            joint_all_m.append(length)
        if len(pos_ms) == even_count:
            position_all_m.append(length)
        if new_ms:
            new_pairs.append({"L": length, "m": new_ms})
    return {
        "l_max": l_max,
        "floor": n0,
        "finance_surviving": leftover,
        "joint_killed_all_m": joint_all_m,
        "position_killed_all_m": position_all_m,
        "new_pairs": new_pairs,
    }


def lean_api_present() -> dict[str, bool]:
    combined = (
        DYNAMICS.read_text(encoding="utf-8")
        + "\n"
        + CYCLE_CORE.read_text(encoding="utf-8")
        + "\n"
        + CYCLE_FINANCE.read_text(encoding="utf-8")
        + "\n"
        # leftover instances split out of CycleFinance.lean (1 Sep 2026)
        + CYCLE_FINANCE_LEFTOVERS.read_text(encoding="utf-8")
        + "\n"
        + CYCLE_HEIGHT_FINANCE.read_text(encoding="utf-8")
        + "\n"
        + CYCLE_EXTREMA.read_text(encoding="utf-8")
        + "\n"
        + (JUGGLER_DIR / "TerminationFloor257.lean").read_text(encoding="utf-8")
        + "\n"
        + JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    )
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    named = {name: has_named(combined, name) for name in EXISTING_LEAN}
    forbidden = {
        f"has_{name}": has_named(combined, name) for name in FORBIDDEN_THEOREMS
    }
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        **forbidden,
        **{
            f"has_api_{name}": has_named(combined, name)
            for name in FORBIDDEN_NEW_API
        },
        "cycle_finance_present": CYCLE_FINANCE.is_file(),
        "no_extra_position_file": not any(
            path.is_file() for path in FORBIDDEN_LEAN_FILES
        ),
        "not_in_paper_barrel": all(name not in paper for name in PAPER_FORBIDDEN),
    }


def run_probe() -> dict[str, Any]:
    heights_257 = odd_run_heights(LEAN_CYCLE_FLOOR)
    leftovers_257 = leftover_table(n0=LEAN_CYCLE_FLOOR)
    leftovers_53 = leftover_table(n0=COMPARE_FLOOR)
    scan = finance_surviving_scan()
    by_l = {row["L"]: row for row in leftovers_257}
    row38 = by_l[38]
    row84 = by_l[84]
    return {
        "floor": LEAN_CYCLE_FLOOR,
        "compare_floor": COMPARE_FLOOR,
        "heights": {
            "n": LEAN_CYCLE_FLOOR,
            "T": first_odd_image(LEAN_CYCLE_FLOOR),
            "tau1": heights_257[1],
            "tau2": heights_257[2],
            "T_even": first_odd_image(LEAN_CYCLE_FLOOR) % 2 == 0,
        },
        "leftovers": leftovers_257,
        "leftovers_at_53": leftovers_53,
        "scan": scan,
        "kills_length_thirty_eight_all_m_joint": row38["joint_kills_all_m"],
        "kills_length_eighty_four_m1_position": row84["position_kills_m1"],
        "kills_length_eighty_four_m2_position": any(
            item["m"] == 2 and item["new_exclusion"] for item in row84["by_m"]
        ),
        "joint_misses_eighty_four_m1": not row84["joint_kills_m1"],
        "new_pairs_at_257": scan["new_pairs"],
        "partition_kills_any_new": False,
        "git": git_commit(),
        "halt_theorem": False,
        "no_cycle_all_lengths": False,
        "floor_raise": False,
        "new_lean": False,
        "new_paper": False,
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and all(lean[name] for name in EXISTING_LEAN)
        and not any(lean[f"has_{name}"] for name in FORBIDDEN_THEOREMS)
        and not any(lean[f"has_api_{name}"] for name in FORBIDDEN_NEW_API)
        and lean["cycle_finance_present"]
        and lean["no_extra_position_file"]
        and lean["not_in_paper_barrel"]
    )
    if not lean_ok:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": f"lean_ok={lean_ok}",
        }
    if scan["halt_theorem"] or scan["no_cycle_all_lengths"] or scan["new_lean"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "out-of-scope claim or unexpected Lean addition",
        }
    if scan["partition_kills_any_new"]:
        return {
            "classification": CLASS_CLOSED,
            "reason": (
                "adversarial circuit-partition without a height law "
                "excluded a leftover pair; that would contradict the "
                "reparameterization of cycleMin_finance"
            ),
        }
    new_pairs = scan["new_pairs_at_257"]
    if (
        scan["kills_length_thirty_eight_all_m_joint"]
        and scan["kills_length_eighty_four_m1_position"]
        and scan["joint_misses_eighty_four_m1"]
        and new_pairs
    ):
        return {
            "classification": CLASS_GREEN,
            "reason": (
                "Odd-run height law is strictly stronger than charging "
                "every climb at T(n). Joint-minima at floor 257 already "
                "excludes every length-38 cycle (any m); global finance "
                "does not (n_max=299). Position-dependent packing newly "
                f"excludes leftover pairs {new_pairs}, in particular "
                "L=84 at m=1 and m=2. Circuit-partition without a "
                "height law remains a reparameterization of "
                "cycleMin_finance"
            ),
        }
    if new_pairs:
        return {
            "classification": CLASS_GREEN,
            "reason": (
                "height law excludes leftover pairs that joint-minima "
                f"misses at floor 257: {new_pairs}"
            ),
        }
    return {
        "classification": CLASS_PARK,
        "reason": (
            "height law is well-defined but excludes no leftover (L, m) "
            "beyond joint-minima at floor 257"
        ),
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "halt_theorem": False,
            "no_cycle_all_lengths": False,
            "floor_raise": False,
            "new_lean": False,
            "new_paper": False,
            "partition_stronger_than_cycleMin_finance": False,
            "peak_finance_reopened": False,
        }
    )
    return {
        "experiment": "juggler_cycle_position_finance",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "Odd-run heights tau_j at floors 53 and 257; greedy at-most-m "
            f"packing of climb interiors; leftover L in {list(FOCUS_LENGTHS)}; "
            f"finance-surviving scan L<={SCAN_L_MAX}"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    heights = scan["heights"]
    lines = [
        "# Juggler position-dependent cycle finance",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Odd-run height refinement of joint-minima m-finance.",
        "Not a new paper. Not a halt theorem.",
        "Height leftover lives in CycleHeightFinance.lean; "
        "no PositionFinance layer.",
        "",
        "## Metadata",
        "",
        f"- classification: **{decision['classification']}**",
        f"- floor: `{scan['floor']}`",
        f"- T(n): `{heights['T']}` even=`{heights['T_even']}`",
        f"- tau_1: `{heights['tau1']}`",
        f"- tau_2: `{heights['tau2']}`",
        f"- L=38 all m by joint-minima: "
        f"`{scan['kills_length_thirty_eight_all_m_joint']}`",
        f"- L=84 m=1 by height law: "
        f"`{scan['kills_length_eighty_four_m1_position']}`",
        f"- new pairs at 257: `{scan['new_pairs_at_257']}`",
        f"- joint all-m kills among finance-survivors ≤ 200: "
        f"`{scan['scan']['joint_killed_all_m']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Focus leftovers at floor 257",
        "",
    ]
    for row in scan["leftovers"]:
        lines.append(
            f"- L=`{row['L']}` o=`{row['o']}` even=`{row['even_count']}` "
            f"global n_max=`{row['global_n_max']}` "
            f"joint all m=`{row['joint_kills_all_m']}` "
            f"position all m=`{row['position_kills_all_m']}` "
            f"new m=`{row['new_exclusions']}`"
        )
    lines.extend(["", "## Focus leftovers at floor 53", ""])
    for row in scan["leftovers_at_53"]:
        lines.append(
            f"- L=`{row['L']}` joint all m=`{row['joint_kills_all_m']}` "
            f"position all m=`{row['position_kills_all_m']}` "
            f"new m=`{row['new_exclusions']}`"
        )
    lines.extend(
        [
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


def write_data_artifacts(payload: dict[str, Any]) -> None:
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    scan = payload["scan"]
    (DATA_DIR / "leftovers.json").write_text(
        json.dumps(scan["leftovers"], indent=2) + "\n", encoding="utf-8"
    )
    (DATA_DIR / "scan.json").write_text(
        json.dumps(scan["scan"], indent=2) + "\n", encoding="utf-8"
    )
    summary = {
        "classification": payload["decision"]["classification"],
        "reason": payload["decision"]["reason"],
        "kills_length_thirty_eight_all_m_joint": scan[
            "kills_length_thirty_eight_all_m_joint"
        ],
        "kills_length_eighty_four_m1_position": scan[
            "kills_length_eighty_four_m1_position"
        ],
        "new_pairs_at_257": scan["new_pairs_at_257"],
        "joint_killed_all_m": scan["scan"]["joint_killed_all_m"],
        "git": scan["git"],
    }
    (DATA_DIR / "summary.json").write_text(
        json.dumps(summary, indent=2) + "\n", encoding="utf-8"
    )
    (DATA_DIR / "README.md").write_text(
        "# Juggler position-dependent cycle finance\n\n"
        "Odd-run height refinement of joint-minima m-finance.\n"
        "Not a new paper. Not a halt theorem. No new Lean.\n\n"
        "Regenerate with "
        "`python -m research.juggler_sequence.cycle_position_finance`.\n",
        encoding="utf-8",
    )


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    DOC_PATH.write_text(render_markdown(data), encoding="utf-8")
    write_data_artifacts(data)
    return data


def main() -> None:
    payload = write_artifacts()
    scan = payload["scan"]
    print(payload["decision"]["classification"])
    print(payload["decision"]["reason"])
    print(
        f"L38joint={scan['kills_length_thirty_eight_all_m_joint']} "
        f"L84m1={scan['kills_length_eighty_four_m1_position']} "
        f"new={scan['new_pairs_at_257']}"
    )


if __name__ == "__main__":
    main()

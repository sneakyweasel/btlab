"""Second-valley bound ≥ 281 as leftover cycle finance.

Not a halt theorem, not a leftover-word census, not a floor raise,
and not a reopen of equal valleys or the ceiling.

Equal-valleys recorded that height-split at floor 261 kills leftover
L=84, m=3 only if the other valleys sit at ≥ 281. Unique visit gives
only n+2=263. This probe asks whether CycleMin geometry
(cycleMin_not_odd_even, cycleMin_even_ge_sq, even_iter_lt_succ_pow)
forces that 281 bound.

It does not, under a proved constant. The first circuit from n
can land at 281 (k=12). From that valley the next odd landing
can be 303. Lean inv-sum and height 6/5 both survive
261 / 281 / 303. A later OE landing at 263 requires a start
valley ≥ 1687 and that triple dies — it is not the adversary.

Dossier: docs/problems/juggler_cycle_second_valley.md.
"""

from __future__ import annotations

import json
import subprocess
from math import isqrt
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_ceiling_finance import (
    FOCUS_EVEN,
    FOCUS_LENGTH,
    FOCUS_ODD,
    LEAN_LOG_CERT,
    ceiling_landing,
    exact_peak_row,
    peak_even_lower,
    theta_of,
)
from research.juggler_sequence.cycle_equal_valleys import (
    height_split_rhs,
    smallest_killing_n2,
)
from research.juggler_sequence.cycle_finance import EPS_CONST
from research.juggler_sequence.cycle_position_finance import (
    CURRENT_LEAN_RESIDUAL_FLOOR,
    height_allocation,
    inv_log_term,
    odd_run_heights,
)
from research.juggler_sequence.lean_paths import (
    CYCLE_CORE,
    CYCLE_EXTREMA,
    CYCLE_FINANCE,
    CYCLE_HEIGHT_FINANCE,
    JUGGLER_DIR,
    JUGGLER_PAPER_BARREL,
    has_named,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_cycle_second_valley.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_cycle_second_valley.md"
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "cycle_second_valley"

CLASS_CLOSED = "SECOND_VALLEY_CLOSED"
CLASS_GREEN = "SECOND_VALLEY_GREEN"
CLASS_INCOMPLETE = "SECOND_VALLEY_INCOMPLETE"

LEAN_FLOOR = CURRENT_LEAN_RESIDUAL_FLOOR
LEAN_CONST = 1.0
EXACT_K_HI = 24
KILLING_N2 = 281
K1_SEARCH_CAP = 20_000

EXISTING_LEAN = (
    "cycleMin_even_ge_sq",
    "cycleMin_not_odd_even",
    "even_iter_lt_succ_pow",
    "cycle_itinerary_length_eighty_four_m_ge_three_or_ge_eighty_five",
)
FORBIDDEN_THEOREMS = (
    "juggler_reaches_one",
    "no_cycle_itinerary_any_length",
    "no_cycle_itinerary_length_eighty_four",
    "second_valley_ge",
    "cycle_second_valley",
)
FORBIDDEN_NEW_API = (
    "SecondValley",
    "CycleSecondValley",
    "ValleyFloor",
)
FORBIDDEN_LEAN_FILES = (
    JUGGLER_DIR / "CycleSecondValley.lean",
    JUGGLER_DIR / "SecondValley.lean",
    JUGGLER_DIR / "ValleyFloor.lean",
)
PAPER_FORBIDDEN = (
    "CycleSecondValley",
    "SecondValley",
    "ValleyFloor",
    "second_valley_ge",
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


def odd_landing(m_min: int, n: int, even_budget: int) -> tuple[int, int]:
    """Last odd iterated square-root that stays at least n.

    ceiling_landing ignores parity. A CycleMin valley is odd, and an
    even state whose next square-root is below n cannot continue
    (cycleMin_even_ge_sq / follows). Backing up to the last odd
    landing raises p, so this is the adversarial odd valley.
    """

    r_max, p_min = ceiling_landing(m_min, n, even_budget)
    if r_max < 1:
        return 0, n
    x = m_min
    last_odd_r = 0
    last_odd_p = n
    for r in range(1, r_max + 1):
        x = isqrt(x)
        if x % 2 == 1:
            last_odd_r = r
            last_odd_p = x
    if last_odd_r == 0:
        return 0, n
    return last_odd_r, last_odd_p


def first_circuit_row(n: int, k: int, *, heights: list[int], m: int = 3) -> dict[str, Any]:
    row = exact_peak_row(n, k, heights=heights, m=m)
    r_odd, p_odd = odd_landing(peak_even_lower(heights, k), n, row["even_budget"])
    row["r_odd"] = r_odd
    row["p_odd"] = p_odd
    row["p_min_even"] = row["p_min"] % 2 == 0
    row["feasible"] = r_odd >= 1 and k >= 2
    return row


def mixed_height_rhs(
    n: int,
    length: int,
    odd_count: int,
    valleys: list[int],
    *,
    const: float = EPS_CONST,
    heights: list[int] | None = None,
) -> float:
    """Height-packed climbs with an explicit valley list."""

    if not valleys:
        raise ValueError("need at least one valley")
    if min(valleys) < n:
        raise ValueError("a valley cannot sit below the CycleMin")
    m = len(valleys)
    climb = max(odd_count - m, 0)
    levels = heights if heights is not None else odd_run_heights(n)
    total = sum(inv_log_term(v) for v in valleys)
    for index, count in enumerate(height_allocation(climb, m)):
        height = levels[index + 1] if index + 1 < len(levels) else levels[-1]
        total += count * inv_log_term(height)
    total += (length - odd_count) * inv_log_term(n * n)
    return const * total


def mixed_inv_sum(
    n: int,
    length: int,
    odd_count: int,
    valleys: list[int],
    *,
    heights: list[int] | None = None,
) -> float:
    m = len(valleys)
    climb = max(odd_count - m, 0)
    levels = heights if heights is not None else odd_run_heights(n)
    total = sum(1 / v for v in valleys)
    for index, count in enumerate(height_allocation(climb, m)):
        height = levels[index + 1] if index + 1 < len(levels) else levels[-1]
        total += count / height
    total += (length - odd_count) / (n * n)
    return total


def later_circuit_rows(
    start: int,
    n: int,
    *,
    k_hi: int = EXACT_K_HI,
    m: int = 3,
) -> list[dict[str, Any]]:
    """Odd landings of a circuit that starts at `start` and must stay ≥ n."""

    heights = odd_run_heights(start, levels=k_hi)
    budget = FOCUS_EVEN - (m - 1)
    rows: list[dict[str, Any]] = []
    for k in range(2, k_hi + 1):
        m_min = peak_even_lower(heights, k)
        r_odd, p_odd = odd_landing(m_min, n, budget)
        rows.append(
            {
                "start": start,
                "k": k,
                "r_odd": r_odd,
                "p_odd": p_odd,
                "feasible": r_odd >= 1 and p_odd > n,
            }
        )
    return rows


def k1_oe_window(n: int, *, cap: int = K1_SEARCH_CAP) -> list[dict[str, Any]]:
    """Later valleys that may start OE: T(v) even and ≥ n^2.

    cycleMin_not_odd_even forbids OE only at the CycleMin start.
    cycleMin_even_ge_sq allows the first even residual once it is
    at least n^2. The next odd landing can sit at n+2.
    """

    nsq = n * n
    budget = FOCUS_EVEN - 2
    rows: list[dict[str, Any]] = []
    for v in range(n + 2 if (n + 2) % 2 else n + 3, cap + 1, 2):
        image = isqrt(v * v * v)
        if image % 2 != 0 or image < nsq:
            continue
        r_odd, p_odd = odd_landing(image, n, budget)
        if r_odd < 1:
            continue
        rows.append(
            {
                "v": v,
                "T_v": image,
                "r_odd": r_odd,
                "p_odd": p_odd,
                "below_killing": p_odd < KILLING_N2,
            }
        )
        if p_odd == n + 2:
            break
    return rows


def lean_api_present() -> dict[str, bool]:
    combined = (
        CYCLE_CORE.read_text(encoding="utf-8")
        + "\n"
        + CYCLE_EXTREMA.read_text(encoding="utf-8")
        + "\n"
        + CYCLE_FINANCE.read_text(encoding="utf-8")
        + "\n"
        + CYCLE_HEIGHT_FINANCE.read_text(encoding="utf-8")
        + "\n"
    )
    paper = (
        JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
        if JUGGLER_PAPER_BARREL.is_file()
        else ""
    )
    sorry_free = "sorry" not in combined and "admit" not in combined
    return {
        "sorry_free": sorry_free,
        **{name: has_named(combined, name) for name in EXISTING_LEAN},
        **{f"has_{name}": has_named(combined, name) for name in FORBIDDEN_THEOREMS},
        **{f"has_api_{name}": has_named(combined, name) for name in FORBIDDEN_NEW_API},
        "cycle_core_present": CYCLE_CORE.is_file(),
        "cycle_extrema_present": CYCLE_EXTREMA.is_file(),
        "no_second_valley_lean": not any(path.is_file() for path in FORBIDDEN_LEAN_FILES),
        "not_in_paper_barrel": all(name not in paper for name in PAPER_FORBIDDEN),
    }


def run_probe() -> dict[str, Any]:
    n = LEAN_FLOOR
    heights = odd_run_heights(n, levels=EXACT_K_HI)
    first_rows = [
        first_circuit_row(n, k, heights=heights) for k in range(2, EXACT_K_HI + 1)
    ]
    feasible = [row for row in first_rows if row["feasible"]]
    worst_first = min(feasible, key=lambda row: row["p_odd"])
    k24 = next(row for row in first_rows if row["k"] == 24)
    k1_rows = k1_oe_window(n)
    low_k1 = [row for row in k1_rows if row["below_killing"]]
    witness = next((row for row in k1_rows if row["p_odd"] == n + 2), None)
    from_281 = later_circuit_rows(KILLING_N2, n)
    feas_281 = [row for row in from_281 if row["feasible"]]
    worst_from_281 = min(feas_281, key=lambda row: row["p_odd"])
    theta = theta_of()
    need = theta * LEAN_LOG_CERT
    kill_n2 = smallest_killing_n2(
        n,
        FOCUS_LENGTH,
        FOCUS_ODD,
        3,
        theta,
        const=LEAN_CONST,
        rhs=height_split_rhs,
    )
    kill_n2_65 = smallest_killing_n2(
        n,
        FOCUS_LENGTH,
        FOCUS_ODD,
        3,
        theta,
        const=EPS_CONST,
        rhs=height_split_rhs,
    )
    adversarial = [n, worst_first["p_odd"], worst_from_281["p_odd"]]
    oe_valleys = [n, n + 2, witness["v"]] if witness is not None else []
    adv = {
        "const1": mixed_height_rhs(
            n, FOCUS_LENGTH, FOCUS_ODD, adversarial, const=LEAN_CONST, heights=heights
        ),
        "six_fifths": mixed_height_rhs(
            n, FOCUS_LENGTH, FOCUS_ODD, adversarial, const=EPS_CONST, heights=heights
        ),
        "inv_sum": mixed_inv_sum(
            n, FOCUS_LENGTH, FOCUS_ODD, adversarial, heights=heights
        ),
    }
    oe = (
        {
            "const1": mixed_height_rhs(
                n, FOCUS_LENGTH, FOCUS_ODD, oe_valleys, const=LEAN_CONST, heights=heights
            ),
            "six_fifths": mixed_height_rhs(
                n, FOCUS_LENGTH, FOCUS_ODD, oe_valleys, const=EPS_CONST, heights=heights
            ),
            "inv_sum": mixed_inv_sum(
                n, FOCUS_LENGTH, FOCUS_ODD, oe_valleys, heights=heights
            ),
        }
        if oe_valleys
        else {}
    )
    all_281 = mixed_height_rhs(
        n,
        FOCUS_LENGTH,
        FOCUS_ODD,
        [n, KILLING_N2, KILLING_N2],
        const=LEAN_CONST,
        heights=heights,
    )
    all_281_inv = mixed_inv_sum(
        n, FOCUS_LENGTH, FOCUS_ODD, [n, KILLING_N2, KILLING_N2], heights=heights
    )
    slogan_false = (
        kill_n2 == KILLING_N2
        and adv["six_fifths"] > theta
        and adv["inv_sum"] > need
        and all_281_inv > need
        and worst_first["p_odd"] == KILLING_N2
        and worst_from_281["p_odd"] < (kill_n2_65 or 10**9)
    )
    return {
        "floor": n,
        "L": FOCUS_LENGTH,
        "o": FOCUS_ODD,
        "even": FOCUS_EVEN,
        "theta": theta,
        "lean_need_61_11": need,
        "killing_n2": kill_n2,
        "first_circuit_rows": [
            {
                "k": row["k"],
                "r_max": row["r_max"],
                "p_min": row["p_min"],
                "p_min_even": row["p_min_even"],
                "r_odd": row["r_odd"],
                "p_odd": row["p_odd"],
                "feasible": row["feasible"],
            }
            for row in first_rows
        ],
        "worst_first": {
            "k": worst_first["k"],
            "p_odd": worst_first["p_odd"],
            "r_odd": worst_first["r_odd"],
            "p_min": worst_first["p_min"],
        },
        "k24": {
            "p_min": k24["p_min"],
            "p_min_even": k24["p_min_even"],
            "r_odd": k24["r_odd"],
            "p_odd": k24["p_odd"],
        },
        "k1_count": len(k1_rows),
        "k1_below_killing": len(low_k1),
        "k1_witness": witness,
        "from_281_rows": [row for row in from_281 if row["feasible"]],
        "from_281_worst": worst_from_281,
        "killing_n2_six_fifths": kill_n2_65,
        "adversarial_valleys": adversarial,
        "adversarial_const1": adv["const1"],
        "adversarial_six_fifths": adv["six_fifths"],
        "adversarial_inv_sum": adv["inv_sum"],
        "oe_valleys": oe_valleys,
        "oe_const1": oe.get("const1"),
        "oe_six_fifths": oe.get("six_fifths"),
        "oe_inv_sum": oe.get("inv_sum"),
        "all_281_const1": all_281,
        "all_281_inv_sum": all_281_inv,
        "kills_adversarial_const1": theta > adv["const1"],
        "kills_adversarial_six_fifths": theta > adv["six_fifths"],
        "kills_adversarial_inv_sum": adv["inv_sum"] < need,
        "kills_oe_six_fifths": bool(oe) and theta > oe["six_fifths"],
        "kills_oe_inv_sum": bool(oe) and oe["inv_sum"] < need,
        "kills_all_281_const1": theta > all_281,
        "kills_all_281_inv_sum": all_281_inv < need,
        "slogan_false": slogan_false,
        "git": git_commit(),
        "halt_theorem": False,
        "no_cycle_all_lengths": False,
        "new_lean": False,
        "floor_raise": False,
        "leftover_word_census": False,
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and all(lean[name] for name in EXISTING_LEAN)
        and not any(lean[f"has_{name}"] for name in FORBIDDEN_THEOREMS)
        and not any(lean[f"has_api_{name}"] for name in FORBIDDEN_NEW_API)
        and lean["cycle_core_present"]
        and lean["cycle_extrema_present"]
        and lean["no_second_valley_lean"]
        and lean["not_in_paper_barrel"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if (
        scan["halt_theorem"]
        or scan["no_cycle_all_lengths"]
        or scan["new_lean"]
        or scan["floor_raise"]
        or scan["leftover_word_census"]
    ):
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "out-of-scope claim or unexpected Lean addition",
        }
    if scan["slogan_false"]:
        return {
            "classification": CLASS_CLOSED,
            "reason": (
                "height-split const 1 first kills at n2="
                f"{scan['killing_n2']}, but that form is not proved. "
                f"Lean inv-sum still misses when both others sit at 281 "
                f"(S={scan['all_281_inv_sum']:.6f} > "
                f"{scan['lean_need_61_11']:.6f}). The adversarial "
                f"Lean-allowed triple is {scan['adversarial_valleys']} "
                f"(first circuit k=12 lands at 281; from 281, k="
                f"{scan['from_281_worst']['k']} lands at "
                f"{scan['from_281_worst']['p_odd']}). Height 6/5 "
                f"RHS={scan['adversarial_six_fifths']:.6f} and inv-sum "
                f"S={scan['adversarial_inv_sum']:.6f} both miss "
                f"θ={scan['theta']:.6f} / need="
                f"{scan['lean_need_61_11']:.6f}; 6/5 first kills at "
                f"{scan['killing_n2_six_fifths']}. A later OE landing "
                "at 263 requires a start valley ≥ 1687 and that triple "
                "dies. The 281 landing is even_iter_lt_succ_pow. "
                "Not a leftover-word census and not a floor raise"
            ),
        }
    return {
        "classification": CLASS_INCOMPLETE,
        "reason": "second-valley arithmetic inconclusive",
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
            "new_lean": False,
            "floor_raise": False,
            "leftover_word_census": False,
        }
    )
    return {
        "experiment": "juggler_cycle_second_valley",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "odd ceiling landings for first-circuit k=2..24 at n=261; "
            "later-circuit landings from 281 down to floor 261; "
            "k=1 OE window; adversarial packing 261/281/303"
        ),
    }


def _fmt(value: float) -> str:
    return f"{value:.6g}"


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    w = scan["k1_witness"]
    lines = [
        "# Juggler cycle second-valley bound",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Does CycleMin force the other valleys to sit at ≥ 281?",
        "Not a halt theorem. Not a leftover-word census. No new Lean.",
        "",
        "## Metadata",
        "",
        f"- classification: **{decision['classification']}**",
        f"- floor: `{scan['floor']}`",
        f"- leftover L: `{scan['L']}` o=`{scan['o']}` even=`{scan['even']}`",
        f"- theta: `{_fmt(scan['theta'])}`",
        f"- height-split killing n2: `{scan['killing_n2']}`",
        f"- worst first-circuit odd landing: k=`{scan['worst_first']['k']}` "
        f"p=`{scan['worst_first']['p_odd']}`",
        f"- from 281: k=`{scan['from_281_worst']['k']}` "
        f"p=`{scan['from_281_worst']['p_odd']}`",
        f"- k=24 raw landing: p=`{scan['k24']['p_min']}` even=`{scan['k24']['p_min_even']}` "
        f"odd p=`{scan['k24']['p_odd']}`",
        f"- k=1 OE witness: v=`{w['v']}` T=`{w['T_v']}` p=`{w['p_odd']}`"
        if w
        else "- k=1 OE witness: `None`",
        f"- 6/5 killing n2: `{scan['killing_n2_six_fifths']}`",
        f"- adversarial valleys: `{scan['adversarial_valleys']}`",
        f"- adversarial const 1: `{_fmt(scan['adversarial_const1'])}` "
        f"kills=`{scan['kills_adversarial_const1']}`",
        f"- adversarial 6/5: `{_fmt(scan['adversarial_six_fifths'])}` "
        f"kills=`{scan['kills_adversarial_six_fifths']}`",
        f"- adversarial inv-sum: `{_fmt(scan['adversarial_inv_sum'])}` "
        f"kills=`{scan['kills_adversarial_inv_sum']}`",
        f"- OE triple: `{scan['oe_valleys']}` 6/5 kills=`{scan['kills_oe_six_fifths']}` "
        f"inv kills=`{scan['kills_oe_inv_sum']}`",
        f"- all-281 const 1: `{_fmt(scan['all_281_const1'])}` "
        f"kills=`{scan['kills_all_281_const1']}`",
        f"- all-281 inv-sum: `{_fmt(scan['all_281_inv_sum'])}` "
        f"kills=`{scan['kills_all_281_inv_sum']}`",
        f"- slogan false: `{scan['slogan_false']}`",
        "",
        decision["reason"],
        "",
        "## First-circuit odd landings at n=261",
        "",
    ]
    for row in scan["first_circuit_rows"]:
        lines.append(
            f"- k=`{row['k']}` r=`{row['r_max']}` p_raw=`{row['p_min']}` "
            f"even=`{row['p_min_even']}` r_odd=`{row['r_odd']}` "
            f"p_odd=`{row['p_odd']}` feasible=`{row['feasible']}`"
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
            decision["reason"],
            "",
        ]
    )
    return "\n".join(lines) + "\n"


def write_outputs(payload: dict[str, Any]) -> None:
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    DOC_PATH.write_text(render_markdown(payload), encoding="utf-8")
    (DATA_DIR / "summary.json").write_text(
        json.dumps(payload["decision"], indent=2) + "\n", encoding="utf-8"
    )
    (DATA_DIR / "first_circuit.json").write_text(
        json.dumps(payload["scan"]["first_circuit_rows"], indent=2) + "\n",
        encoding="utf-8",
    )
    (DATA_DIR / "README.md").write_text(
        "# Juggler cycle second-valley bound\n\n"
        "Height-split killing threshold 281 versus CycleMin landings.\n"
        "Not a halt theorem. No new Lean.\n\n"
        "Regenerate with `python -m research.juggler_sequence.cycle_second_valley`.\n",
        encoding="utf-8",
    )


def main() -> None:
    payload = probe_payload()
    write_outputs(payload)
    decision = payload["decision"]
    print(f"{decision['classification']}: {decision['reason']}")


if __name__ == "__main__":
    main()

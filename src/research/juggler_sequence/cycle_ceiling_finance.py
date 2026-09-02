"""Upper-cell ceiling as leftover cycle finance.

Not a halt theorem, not a leftover-word census, not a floor raise,
and not a reopen of peak finance.

The named even-run upper cell M < (p+1)^{2^r} (`even_iter_lt_succ_pow`)
was recorded and then left unused. Combined with an odd-run height
lower bound on the peak it forces the landing
p >= iterated_isqrt(M_min, r). Height packing still charges that
valley at n. The slogan is that this coupling puts enough
1/(x ln x) mass into the top window that leftover theta dies.

It does not. The adversarial peak-run length k=24 lands at 304,
below every proved threshold (6/5 needs 659; Lean inv-sum needs
367). Large m is worse.

Dossier: docs/problems/juggler_cycle_ceiling_finance.md.
"""

from __future__ import annotations

import json
import math
import subprocess
from math import isqrt
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_finance import EPS_CONST
from research.juggler_sequence.cycle_position_finance import (
    CURRENT_LEAN_RESIDUAL_FLOOR,
    height_allocation,
    inv_log_term,
    odd_run_heights,
    position_rhs,
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
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_cycle_ceiling_finance.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_cycle_ceiling_finance.md"
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "cycle_ceiling_finance"

CLASS_CLOSED = "CEILING_FINANCE_CLOSED"
CLASS_GREEN = "CEILING_FINANCE_GREEN"
CLASS_INCOMPLETE = "CEILING_FINANCE_INCOMPLETE"

LEAN_FLOOR = CURRENT_LEAN_RESIDUAL_FLOOR
FOCUS_LENGTH = 84
FOCUS_ODD = 53
FOCUS_EVEN = 31
LEAN_CONST = 1.0
LEAN_LOG_CERT = 61 / 11
EXACT_K_HI = 24
LOG_K_HI = 51

EXISTING_LEAN = (
    "even_iter_lt_succ_pow",
    "cycleMin_even_ge_sq",
    "cycleMin_not_odd_even",
    "cycle_itinerary_length_eighty_four_m_ge_three_or_ge_eighty_five",
)
FORBIDDEN_THEOREMS = (
    "juggler_reaches_one",
    "no_cycle_itinerary_any_length",
    "no_cycle_itinerary_length_eighty_four",
    "cycle_ceiling_finance",
    "ceiling_finance",
)
FORBIDDEN_NEW_API = (
    "CycleCeilingFinance",
    "CeilingFinance",
    "TopWindowFinance",
)
FORBIDDEN_LEAN_FILES = (
    JUGGLER_DIR / "CycleCeilingFinance.lean",
    JUGGLER_DIR / "CeilingFinance.lean",
    JUGGLER_DIR / "TopWindowFinance.lean",
)
PAPER_FORBIDDEN = (
    "CycleCeilingFinance",
    "CeilingFinance",
    "TopWindowFinance",
    "cycle_ceiling_finance",
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


def ceil_div(num: int, den: int) -> int:
    return (num + den - 1) // den


def iterated_isqrt(x: int, r: int) -> int:
    for _ in range(r):
        x = isqrt(x)
    return x


def peak_even_lower(heights: list[int], k: int) -> int:
    """Least even reachable as the image of the k-th odd step.

    After k-1 odds the state is at least tau_{k-1}. The next odd step
    produces T(tau_{k-1}). If that image is odd, a CycleMin block
    ending in E needs the next even integer.
    """

    if k < 1 or k > len(heights) - 1:
        raise ValueError("peak run length must lie inside the height table")
    image = isqrt(heights[k - 1] ** 3)
    return image if image % 2 == 0 else image + 1


def ceiling_landing(m_min: int, n: int, even_budget: int) -> tuple[int, int]:
    """Adversarial (largest r, smallest p) landing allowed by the ceiling.

    even_iter_lt_succ_pow gives M < (p+1)^{2^r}. Monotone isqrt then
    gives p >= iterated_isqrt(M, r) once M >= m_min. CycleMin forces
    p >= n, so r cannot exceed the last root that stays >= n.
    """

    if even_budget < 1:
        return 0, n
    r_max = 0
    p_min = n
    for r in range(1, even_budget + 1):
        landing = iterated_isqrt(m_min, r)
        if landing >= n:
            r_max = r
            p_min = landing
        else:
            break
    return r_max, p_min


def ceiling_rhs(
    n: int,
    length: int,
    odd_count: int,
    m: int,
    p_min: int,
    *,
    const: float = EPS_CONST,
    heights: list[int] | None = None,
    other_valley: int | None = None,
) -> float:
    """Height packing with one valley at the forced landing p_min."""

    if m < 1:
        raise ValueError("m must be at least 1")
    if p_min < n:
        raise ValueError("ceiling landing cannot sit below the CycleMin")
    other = n if other_valley is None else other_valley
    levels = heights if heights is not None else odd_run_heights(n)
    climb = max(odd_count - m, 0)
    total = inv_log_term(p_min) + (m - 1) * inv_log_term(other)
    for index, count in enumerate(height_allocation(climb, m)):
        height = levels[index + 1] if index + 1 < len(levels) else levels[-1]
        total += count * inv_log_term(height)
    total += (length - odd_count) * inv_log_term(n * n)
    return const * total


def ceiling_inv_sum(
    n: int,
    length: int,
    odd_count: int,
    m: int,
    p_min: int,
    *,
    heights: list[int] | None = None,
    other_valley: int | None = None,
) -> float:
    """Lean inv-sum cap with one valley charged at p_min."""

    other = n if other_valley is None else other_valley
    levels = heights if heights is not None else odd_run_heights(n)
    climb = max(odd_count - m, 0)
    total = 1 / p_min + (m - 1) / other
    for index, count in enumerate(height_allocation(climb, m)):
        height = levels[index + 1] if index + 1 < len(levels) else levels[-1]
        total += count / height
    total += (length - odd_count) / (n * n)
    return total


def theta_of(length: int = FOCUS_LENGTH, odd_count: int = FOCUS_ODD) -> float:
    return 1.0 - (1 << length) / float(3**odd_count)


def finance_pack(
    n: int,
    p_min: int,
    m: int,
    *,
    heights: list[int],
    other_valley: int | None = None,
) -> dict[str, Any]:
    theta = theta_of()
    need = theta * LEAN_LOG_CERT
    c1 = ceiling_rhs(
        n,
        FOCUS_LENGTH,
        FOCUS_ODD,
        m,
        p_min,
        const=LEAN_CONST,
        heights=heights,
        other_valley=other_valley,
    )
    c65 = ceiling_rhs(
        n,
        FOCUS_LENGTH,
        FOCUS_ODD,
        m,
        p_min,
        const=EPS_CONST,
        heights=heights,
        other_valley=other_valley,
    )
    inv = ceiling_inv_sum(
        n,
        FOCUS_LENGTH,
        FOCUS_ODD,
        m,
        p_min,
        heights=heights,
        other_valley=other_valley,
    )
    return {
        "theta": theta,
        "lean_need_61_11": need,
        "const1": c1,
        "six_fifths": c65,
        "inv_sum": inv,
        "kills_const1": theta > c1,
        "kills_six_fifths": theta > c65,
        "kills_inv_sum": inv < need,
    }


def exact_peak_row(
    n: int,
    k: int,
    *,
    heights: list[int],
    m: int = 3,
    even_budget: int | None = None,
) -> dict[str, Any]:
    budget = FOCUS_EVEN - (m - 1) if even_budget is None else even_budget
    m_min = peak_even_lower(heights, k)
    r_max, p_min = ceiling_landing(m_min, n, budget)
    pack = finance_pack(n, p_min, m, heights=heights)
    return {
        "n": n,
        "k": k,
        "m": m,
        "m_min_bits": m_min.bit_length(),
        "m_min_even": m_min % 2 == 0,
        "r_max": r_max,
        "p_min": p_min,
        "even_budget": budget,
        **pack,
    }


def log_peak_row(n: int, k: int, log2_tau_base: float, base_index: int) -> dict[str, Any]:
    """Lower bound on p from log2(tau_{base}) * (3/2)^{k-1-base}."""

    steps = (k - 1) - base_index
    log2_tau = log2_tau_base * (1.5**steps)
    log2_m = 1.5 * log2_tau
    log2_n = math.log(n) / math.log(2)
    r_max = 0
    expo = 0.0
    for r in range(1, FOCUS_EVEN + 1):
        if (1 << r) * log2_n <= log2_m:
            r_max = r
            expo = log2_m / (1 << r)
        else:
            break
    p_lower = 2**expo
    return {
        "n": n,
        "k": k,
        "source": "log2_lower",
        "r_max": r_max,
        "p_lower": p_lower,
        "above_exact_k24": p_lower > 304,
    }


def killing_thresholds(n: int, *, heights: list[int], m: int = 3) -> dict[str, int]:
    """Least odd p that kills m=3 under each proved constant."""

    theta = theta_of()
    need = theta * LEAN_LOG_CERT
    six_p = None
    inv_p = None
    start = n if n % 2 else n + 1
    for p in range(start, 20_000, 2):
        pack = finance_pack(n, p, m, heights=heights)
        if six_p is None and pack["kills_six_fifths"]:
            six_p = p
        if inv_p is None and pack["kills_inv_sum"]:
            inv_p = p
        if six_p is not None and inv_p is not None:
            break
    if six_p is None or inv_p is None:
        raise RuntimeError("killing threshold search exceeded 20000")
    return {"six_fifths": six_p, "inv_sum": inv_p}


def pigeonhole_m_table(n: int, *, heights: list[int]) -> list[dict[str, Any]]:
    """One row per m>=3 using only the pigeonhole k = ceil(o/m).

    This is not the leftover-killer scan: m=3 must also face every
    longer peak run. It is the large-m census.
    """

    rows = []
    for m in range(3, FOCUS_EVEN + 1):
        k_min = ceil_div(FOCUS_ODD, m)
        row = exact_peak_row(n, k_min, heights=heights, m=m)
        row["k_min"] = k_min
        rows.append(row)
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
        "cycle_extrema_present": CYCLE_EXTREMA.is_file(),
        "cycle_finance_present": CYCLE_FINANCE.is_file(),
        "no_ceiling_lean": not any(path.is_file() for path in FORBIDDEN_LEAN_FILES),
        "not_in_paper_barrel": all(name not in paper for name in PAPER_FORBIDDEN),
    }


def run_probe() -> dict[str, Any]:
    n = LEAN_FLOOR
    heights = odd_run_heights(n, levels=EXACT_K_HI)
    exact_rows = [
        exact_peak_row(n, k, heights=heights) for k in range(18, EXACT_K_HI + 1)
    ]
    worst = min(exact_rows, key=lambda row: row["p_min"])
    log2_tau = heights[EXACT_K_HI].bit_length() - 1
    log_rows = [
        log_peak_row(n, k, float(log2_tau), EXACT_K_HI)
        for k in range(EXACT_K_HI + 1, LOG_K_HI + 1)
    ]
    thresholds = killing_thresholds(n, heights=heights)
    m_rows = pigeonhole_m_table(n, heights=heights)
    height_plain = position_rhs(
        n, FOCUS_LENGTH, FOCUS_ODD, 3, const=LEAN_CONST, heights=heights
    )
    theta = theta_of()
    k18 = next(row for row in exact_rows if row["k"] == 18)
    k24 = next(row for row in exact_rows if row["k"] == 24)
    slogan_false = (
        not k24["kills_six_fifths"]
        and not k24["kills_inv_sum"]
        and not all(row["kills_six_fifths"] for row in m_rows)
    )
    return {
        "floor": n,
        "L": FOCUS_LENGTH,
        "o": FOCUS_ODD,
        "even": FOCUS_EVEN,
        "theta": theta,
        "T_n": isqrt(n**3),
        "T_n_even": isqrt(n**3) % 2 == 0,
        "height_plain_m3": height_plain,
        "exact_peak_rows": exact_rows,
        "log_peak_rows": log_rows,
        "worst_exact": {
            "k": worst["k"],
            "r_max": worst["r_max"],
            "p_min": worst["p_min"],
            "six_fifths": worst["six_fifths"],
            "inv_sum": worst["inv_sum"],
        },
        "k18": {
            "p_min": k18["p_min"],
            "r_max": k18["r_max"],
            "kills_six_fifths": k18["kills_six_fifths"],
            "kills_inv_sum": k18["kills_inv_sum"],
        },
        "k24": {
            "p_min": k24["p_min"],
            "r_max": k24["r_max"],
            "const1": k24["const1"],
            "six_fifths": k24["six_fifths"],
            "inv_sum": k24["inv_sum"],
            "kills_six_fifths": k24["kills_six_fifths"],
            "kills_inv_sum": k24["kills_inv_sum"],
        },
        "killing_p": thresholds,
        "log_rows_above_k24": all(row["above_exact_k24"] for row in log_rows),
        "m_table": [
            {
                "m": row["m"],
                "k_min": row["k_min"],
                "p_min": row["p_min"],
                "r_max": row["r_max"],
                "kills_six_fifths": row["kills_six_fifths"],
                "kills_inv_sum": row["kills_inv_sum"],
            }
            for row in m_rows
        ],
        "m3_pigeonhole_only_kills": m_rows[0]["kills_six_fifths"],
        "all_m_killed": all(row["kills_six_fifths"] for row in m_rows),
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
        and lean["cycle_extrema_present"]
        and lean["cycle_finance_present"]
        and lean["no_ceiling_lean"]
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
    if scan["slogan_false"] and scan["k24"]["p_min"] < scan["killing_p"]["inv_sum"]:
        k24 = scan["k24"]
        return {
            "classification": CLASS_CLOSED,
            "reason": (
                "the upper cell forces a landing p >= iterated_isqrt(M_min, r), "
                "which is a corollary of even_iter_lt_succ_pow, but the "
                f"adversarial peak run k={scan['worst_exact']['k']} lands at "
                f"p={k24['p_min']}. Proved 6/5 RHS={k24['six_fifths']:.6f} "
                f"and Lean inv-sum S={k24['inv_sum']:.6f} both miss "
                f"θ={scan['theta']:.6f} / need={scan['theta'] * LEAN_LOG_CERT:.6f}. "
                f"6/5 needs p>={scan['killing_p']['six_fifths']}; inv-sum needs "
                f"p>={scan['killing_p']['inv_sum']}. Pigeonhole k=18 lands at "
                f"{scan['k18']['p_min']} and would kill; the leftover can "
                "choose k=24. Large m is worse. Not a leftover-word census "
                "and not a floor raise"
            ),
        }
    return {
        "classification": CLASS_INCOMPLETE,
        "reason": "ceiling arithmetic inconclusive",
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
            "peak_finance_reopened": False,
        }
    )
    return {
        "experiment": "juggler_cycle_ceiling_finance",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "even_iter_lt_succ_pow plus odd-run height lower bound on the "
            "peak; adversarial r = max even-run with landing >= n; height "
            f"packing with one valley at p_min; exact k=18..{EXACT_K_HI} "
            f"and log2 lower bounds through k={LOG_K_HI}; pigeonhole m-table"
        ),
    }


def _fmt(value: float) -> str:
    return f"{value:.6g}"


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lines = [
        "# Juggler cycle ceiling finance",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "The upper cell (p+1)^{2^r} as leftover finance.",
        "Not a halt theorem. Not a leftover-word census. No new Lean.",
        "",
        "## Metadata",
        "",
        f"- classification: **{decision['classification']}**",
        f"- floor: `{scan['floor']}`",
        f"- leftover L: `{scan['L']}` o=`{scan['o']}` even=`{scan['even']}`",
        f"- theta: `{_fmt(scan['theta'])}`",
        f"- T(n) even: `{scan['T_n_even']}`",
        f"- plain height m=3: `{_fmt(scan['height_plain_m3'])}`",
        f"- k=18 landing: p=`{scan['k18']['p_min']}` r=`{scan['k18']['r_max']}` "
        f"6/5 kills=`{scan['k18']['kills_six_fifths']}`",
        f"- k=24 landing: p=`{scan['k24']['p_min']}` r=`{scan['k24']['r_max']}` "
        f"6/5=`{_fmt(scan['k24']['six_fifths'])}` "
        f"inv-sum=`{_fmt(scan['k24']['inv_sum'])}`",
        f"- 6/5 killing p: `{scan['killing_p']['six_fifths']}`",
        f"- inv-sum killing p: `{scan['killing_p']['inv_sum']}`",
        f"- slogan false: `{scan['slogan_false']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Exact peak-run landings at n=261, m=3",
        "",
    ]
    for row in scan["exact_peak_rows"]:
        lines.append(
            f"- k=`{row['k']}` r=`{row['r_max']}` p=`{row['p_min']}` "
            f"bits=`{row['m_min_bits']}` "
            f"const1=`{_fmt(row['const1'])}` "
            f"6/5=`{_fmt(row['six_fifths'])}` "
            f"inv=`{_fmt(row['inv_sum'])}` "
            f"6/5 kills=`{row['kills_six_fifths']}` "
            f"inv kills=`{row['kills_inv_sum']}`"
        )
    lines.extend(
        [
            "",
            "## Pigeonhole m-table (k = ceil(53/m) only)",
            "",
        ]
    )
    for row in scan["m_table"]:
        lines.append(
            f"- m=`{row['m']}` kmin=`{row['k_min']}` r=`{row['r_max']}` "
            f"p=`{row['p_min']}` 6/5 kills=`{row['kills_six_fifths']}` "
            f"inv kills=`{row['kills_inv_sum']}`"
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


def write_outputs(payload: dict[str, Any]) -> None:
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    DOC_PATH.write_text(render_markdown(payload), encoding="utf-8")
    (DATA_DIR / "summary.json").write_text(
        json.dumps(payload["decision"], indent=2) + "\n", encoding="utf-8"
    )
    (DATA_DIR / "exact_peak_rows.json").write_text(
        json.dumps(payload["scan"]["exact_peak_rows"], indent=2) + "\n",
        encoding="utf-8",
    )
    (DATA_DIR / "m_table.json").write_text(
        json.dumps(payload["scan"]["m_table"], indent=2) + "\n",
        encoding="utf-8",
    )
    (DATA_DIR / "README.md").write_text(
        "# Juggler cycle ceiling finance\n\n"
        "Upper cell (p+1)^{2^r} as leftover finance.\n"
        "Not a halt theorem. No new Lean.\n\n"
        "Regenerate with "
        "`python -m research.juggler_sequence.cycle_ceiling_finance`.\n",
        encoding="utf-8",
    )


def main() -> None:
    payload = probe_payload()
    write_outputs(payload)
    decision = payload["decision"]
    print(f"{decision['classification']}: {decision['reason']}")


if __name__ == "__main__":
    main()

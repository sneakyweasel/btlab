"""Equal valleys on a Juggler CycleMin.

Not a halt theorem, not a leftover-word census, not a floor raise,
and not a formalization of the height law.

Question: can all m local minima equal the global minimum n?

On a leftover-length CycleItinerary that is already excluded at every
proper shorter length, an intermediate return T^k(n)=n is a shorter
CycleItinerary (follows_take + image_take_of_le). So n occurs once, and
at most one valley equals n. For m≥2 the other valleys are at least
the next odd, n+2.

That is first-return, not a new height law. Charging m-1 valleys at
n+2 does not exclude leftover L=84 at m≥3 at the live floor 261.

Dossier: docs/problems/juggler_cycle_equal_valleys.md.
"""

from __future__ import annotations

import json
import subprocess
from math import isqrt
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_finance import EPS_CONST
from research.juggler_sequence.cycle_gap_baker import exact_gap, o_min
from research.juggler_sequence.cycle_m_finance import (
    first_odd_image,
    inv_log_term,
    steiner_rhs,
)
from research.juggler_sequence.cycle_position_finance import (
    height_allocation,
    odd_run_heights,
    position_rhs,
)
from research.juggler_sequence.lean_paths import (
    CYCLE_CORE,
    CYCLE_FINANCE,
    JUGGLER_DIR,
    JUGGLER_PAPER_BARREL,
    has_named,
    juggler_text,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_cycle_equal_valleys.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_cycle_equal_valleys.md"
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "cycle_equal_valleys"

CLASS_CLOSED = "EQUAL_VALLEYS_CLOSED"
CLASS_GREEN = "EQUAL_VALLEYS_GREEN"
CLASS_INCOMPLETE = "EQUAL_VALLEYS_INCOMPLETE"

LEAN_FLOOR = 261
FOCUS_LENGTH = 84
FOCUS_M = 3
LEAN_CONST = 1.0
N2_SEARCH_CAP = 50_000

EXISTING_LEAN = (
    "CycleItinerary",
    "CycleMin",
    "cycle_iterate_period",
    "follows_take",
    "image_take_of_le",
    "cycle_itinerary_length_eighty_four_or_ge_eighty_five",
)
FORBIDDEN_THEOREMS = (
    "juggler_reaches_one",
    "no_cycle_itinerary_any_length",
    "no_cycle_itinerary_length_eighty_four",
    "cycle_equal_valleys",
    "second_valley_ge",
)
FORBIDDEN_NEW_API = (
    "EqualValleys",
    "UniqueValley",
    "SecondValley",
    "CycleEqualValleys",
)
FORBIDDEN_LEAN_FILES = (
    JUGGLER_DIR / "CycleEqualValleys.lean",
    JUGGLER_DIR / "EqualValleys.lean",
    JUGGLER_DIR / "UniqueValley.lean",
)
PAPER_FORBIDDEN = ("CycleEqualValleys", "EqualValleys", "UniqueValley", "SecondValley")


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


def theta_of(length: int, odd_count: int | None = None) -> float:
    odd = o_min(length) if odd_count is None else odd_count
    return 1.0 - (1 << length) / float(3**odd)


def split_valley_rhs(
    n: int,
    length: int,
    odd_count: int,
    m: int,
    n2: int,
    *,
    const: float = EPS_CONST,
) -> float:
    """One valley at n, the other m-1 at n2, climbs at T(n), evens at n^2."""

    if m < 1:
        raise ValueError("m must be at least 1")
    if n2 < n:
        raise ValueError("second valley cannot sit below the CycleMin")
    climb = max(odd_count - m, 0)
    t = first_odd_image(n)
    even_count = length - odd_count
    valleys = inv_log_term(n) + (m - 1) * inv_log_term(n2)
    return const * (
        valleys + climb * inv_log_term(t) + even_count * inv_log_term(n * n)
    )


def height_split_rhs(
    n: int,
    length: int,
    odd_count: int,
    m: int,
    n2: int,
    *,
    const: float = EPS_CONST,
) -> float:
    """Height-packed climbs, one valley at n, the other m-1 at n2."""

    if m < 1:
        raise ValueError("m must be at least 1")
    if n2 < n:
        raise ValueError("second valley cannot sit below the CycleMin")
    climb = max(odd_count - m, 0)
    even_count = length - odd_count
    levels = odd_run_heights(n)
    total = inv_log_term(n) + (m - 1) * inv_log_term(n2)
    for index, count in enumerate(height_allocation(climb, m)):
        height = levels[index + 1] if index + 1 < len(levels) else levels[-1]
        total += count * inv_log_term(height)
    total += even_count * inv_log_term(n * n)
    return const * total


def smallest_killing_n2(
    n: int,
    length: int,
    odd_count: int,
    m: int,
    theta: float,
    *,
    const: float = EPS_CONST,
    cap: int = N2_SEARCH_CAP,
    rhs=split_valley_rhs,
) -> int | None:
    """Least odd n2 ≥ n+2 whose chosen RHS is < theta, or None."""

    start = n + 2 if (n + 2) % 2 == 1 else n + 3
    for n2 in range(start, cap + 1, 2):
        if theta > rhs(n, length, odd_count, m, n2, const=const):
            return n2
    return None


def finance_row(n: int, length: int, m: int, *, const: float) -> dict[str, Any]:
    gap = exact_gap(length)
    odd_count = gap["o"]
    even_count = length - odd_count
    theta = theta_of(length, odd_count)
    n2 = n + 2
    all_n = steiner_rhs(n, length, odd_count, m, const=const)
    split = split_valley_rhs(n, length, odd_count, m, n2, const=const)
    height = position_rhs(n, length, odd_count, m, const=const)
    height_split = height_split_rhs(n, length, odd_count, m, n2, const=const)
    kill_n2 = smallest_killing_n2(
        n, length, odd_count, m, theta, const=const
    )
    kill_height_n2 = smallest_killing_n2(
        n,
        length,
        odd_count,
        m,
        theta,
        const=const,
        rhs=height_split_rhs,
    )
    return {
        "n": n,
        "L": length,
        "o": odd_count,
        "even": even_count,
        "m": m,
        "const": const,
        "theta": theta,
        "t": first_odd_image(n),
        "all_valleys_at_n_rhs": all_n,
        "split_n_plus_two_rhs": split,
        "height_rhs": height,
        "height_split_n_plus_two_rhs": height_split,
        "all_valleys_kills": theta > all_n,
        "n_plus_two_kills": theta > split,
        "height_kills": theta > height,
        "height_n_plus_two_kills": theta > height_split,
        "smallest_killing_n2": kill_n2,
        "smallest_height_killing_n2": kill_height_n2,
        "tau1": first_odd_image(n) + (1 - first_odd_image(n) % 2),
    }


def lean_api_present() -> dict[str, bool]:
    combined = juggler_text()
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
        "cycle_finance_present": CYCLE_FINANCE.is_file(),
        "no_equal_valleys_lean": not any(path.is_file() for path in FORBIDDEN_LEAN_FILES),
        "not_in_paper_barrel": all(name not in paper for name in PAPER_FORBIDDEN),
    }


def run_probe() -> dict[str, Any]:
    odd = o_min(FOCUS_LENGTH)
    rows = [
        finance_row(LEAN_FLOOR, FOCUS_LENGTH, FOCUS_M, const=LEAN_CONST),
        finance_row(LEAN_FLOOR, FOCUS_LENGTH, FOCUS_M, const=EPS_CONST),
        finance_row(LEAN_FLOOR, FOCUS_LENGTH, 4, const=LEAN_CONST),
        finance_row(LEAN_FLOOR, FOCUS_LENGTH, 31, const=LEAN_CONST),
    ]
    by_key = {(row["m"], row["const"]): row for row in rows}
    m3_lean = by_key[(FOCUS_M, LEAN_CONST)]
    m3_six = by_key[(FOCUS_M, EPS_CONST)]
    slogan_false = (
        not m3_lean["n_plus_two_kills"]
        and not m3_six["n_plus_two_kills"]
        and not m3_lean["all_valleys_kills"]
        and not m3_lean["height_n_plus_two_kills"]
    )
    return {
        "floor": LEAN_FLOOR,
        "L": FOCUS_LENGTH,
        "o": odd,
        "even": FOCUS_LENGTH - odd,
        "tau1_at_floor": isqrt(LEAN_FLOOR**3) + (1 - isqrt(LEAN_FLOOR**3) % 2),
        "rows": rows,
        "unique_visit": True,
        "all_equal_only_if_m1_or_shorter_cycle": True,
        "second_valley_at_least_n_plus_two": True,
        "slogan_false": slogan_false,
        "git": git_commit(),
        "halt_theorem": False,
        "no_cycle_all_lengths": False,
        "new_lean": False,
        "floor_raise": False,
        "height_law_formalized": False,
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and all(lean[name] for name in EXISTING_LEAN)
        and not any(lean[f"has_{name}"] for name in FORBIDDEN_THEOREMS)
        and not any(lean[f"has_api_{name}"] for name in FORBIDDEN_NEW_API)
        and lean["cycle_core_present"]
        and lean["cycle_finance_present"]
        and lean["no_equal_valleys_lean"]
        and lean["not_in_paper_barrel"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if (
        scan["halt_theorem"]
        or scan["no_cycle_all_lengths"]
        or scan["new_lean"]
        or scan["floor_raise"]
        or scan["height_law_formalized"]
    ):
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "out-of-scope claim or unexpected Lean addition",
        }
    if scan["slogan_false"] and scan["unique_visit"]:
        m3 = next(
            row
            for row in scan["rows"]
            if row["m"] == FOCUS_M and row["const"] == LEAN_CONST
        )
        return {
            "classification": CLASS_CLOSED,
            "reason": (
                "all m valleys equal n is impossible for m≥2 on a leftover "
                "length (intermediate return is a shorter CycleItinerary). The "
                "next odd n+2 does not exclude L=84 at m=3: split RHS "
                f"{m3['split_n_plus_two_rhs']:.6f} > θ={m3['theta']:.6f} "
                f"at floor {scan['floor']}, Lean constant 1. Height plus "
                f"n+2 is {m3['height_split_n_plus_two_rhs']:.6f}. "
                f"Height-split killing n2 is {m3['smallest_height_killing_n2']}"
            ),
        }
    return {
        "classification": CLASS_INCOMPLETE,
        "reason": "uniqueness or leftover-killer arithmetic inconclusive",
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
            "height_law_formalized": False,
            "leftover_word_census": False,
        }
    )
    return {
        "experiment": "juggler_cycle_equal_valleys",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "prefix-return uniqueness of n on leftover CycleItinerary; "
            "split-valley finance at n vs n+2 for L=84 m≥3 at floor 261"
        ),
    }


def _fmt(value: float) -> str:
    return f"{value:.6g}"


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lines = [
        "# Juggler cycle equal valleys",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Can every local minimum equal the CycleMin start n?",
        "Not a halt theorem. Not a leftover-length exclusion. No new Lean.",
        "",
        "## Metadata",
        "",
        f"- classification: **{decision['classification']}**",
        f"- floor: `{scan['floor']}`",
        f"- leftover L: `{scan['L']}` o=`{scan['o']}` even=`{scan['even']}`",
        f"- unique visit of n: `{scan['unique_visit']}`",
        f"- all-equal only if m=1 or a shorter cycle: "
        f"`{scan['all_equal_only_if_m1_or_shorter_cycle']}`",
        f"- second valley ≥ n+2: `{scan['second_valley_at_least_n_plus_two']}`",
        f"- n+2 leftover-killer slogan false: `{scan['slogan_false']}`",
        "",
        decision["reason"],
        "",
        "## Split-valley finance at leftover L=84",
        "",
    ]
    for row in scan["rows"]:
        lines.append(
            f"- m=`{row['m']}` const=`{row['const']}` θ=`{_fmt(row['theta'])}` "
            f"all-n RHS=`{_fmt(row['all_valleys_at_n_rhs'])}` "
            f"split n+2 RHS=`{_fmt(row['split_n_plus_two_rhs'])}` "
            f"height RHS=`{_fmt(row['height_rhs'])}` "
            f"height+n+2 RHS=`{_fmt(row['height_split_n_plus_two_rhs'])}` "
            f"n+2 kills=`{row['n_plus_two_kills']}` "
            f"height+n+2 kills=`{row['height_n_plus_two_kills']}` "
            f"height-split n2=`{row['smallest_height_killing_n2']}`"
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
    (DATA_DIR / "rows.json").write_text(
        json.dumps(payload["scan"]["rows"], indent=2) + "\n", encoding="utf-8"
    )
    (DATA_DIR / "README.md").write_text(
        "# Juggler cycle equal valleys\n\n"
        "Unique visit of the CycleMin start, and split-valley finance "
        "at n versus n+2.\n"
        "Not a halt theorem. No new Lean.\n\n"
        "Regenerate with `python -m research.juggler_sequence.cycle_equal_valleys`.\n",
        encoding="utf-8",
    )


def main() -> None:
    payload = probe_payload()
    write_outputs(payload)
    decision = payload["decision"]
    print(f"{decision['classification']}: {decision['reason']}")


if __name__ == "__main__":
    main()

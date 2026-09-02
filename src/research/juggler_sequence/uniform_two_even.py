"""Uniform two-even leftover tails O^{k-2}EE and O^{k-3}EOE.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a length-8 census, not a three-even programme, and not induction
on period or on n.

Both leftover families are expanding for every k >= 6. After the
last-even cell (EE) or the last-odd cube trick (EOE) they share the
comparison

    n^{3^{k-2}} > 2^{e_{k-2}} (n+1)^{2^k},

where e_a = 2*3^a - 2^{a+1} is log2(lowerDenom(O^a)). The EOE
auxiliary (y+1)^3 < 2(n+1)^4 holds for every n >= 2, so it does not
raise the cutoff.
"""

from __future__ import annotations

import json
from math import log
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_length_seven import (
    cycle_itinerary_hits,
    y_succ_cube_lt_two_a4,
)
from research.juggler_sequence.cycle_length_nine import odd_log2_C
from research.juggler_sequence.lean_paths import (
    CYCLES,
    LEFTOVER_CYCLES,
    MINIMAL,
    SMALL_CYCLE_CENSUS,
    engine_floor_text,
    has_named,
    pre_finance_text,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_uniform_two_even.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_uniform_two_even.md"

CLASS_GREEN = "TWO_EVEN_UNIFORM_TAIL_GREEN"
CLASS_REMAINS = "TWO_EVEN_UNIFORM_TAIL_REMAINS"
CLASS_INCOMPLETE = "TWO_EVEN_UNIFORM_INCOMPLETE"

K_MIN = 6
K_MAX = 24
N0_SEARCH_CAP = 500
EXACT_K_MAX = 8

# First integer n at which the shared tail fires. Lean uses the
# cleaner algebraic cutoffs 256 (k=6) and 14 (k=7).
EXPECTED_N0 = {
    6: 205,
    7: 14,
    8: 8,
    9: 6,
    10: 6,
}

LEAN_THEOREMS = (
    "cycle_itinerary_formally_expanding",
    "cycle_last_even_interval",
    "cycle_trailing_evens_lt",
    "no_cycle_itinerary_ooooee",
    "no_cycle_itinerary_oooeoe",
    "no_cycle_itinerary_oooooee",
    "no_cycle_itinerary_ooooeoe",
    "no_cycle_itinerary_length_le_seven",
    "no_cycle_itinerary_two_even_ee",
    "no_cycle_itinerary_two_even_eoe",
    "shared_two_even_tail",
    "denomBits",
)


def denom_bits(a: int) -> int:
    """log2(lowerDenom(O^a)). Closed form 2*3^a - 2^{a+1}."""
    if a < 0:
        raise ValueError("odd-run length must be nonnegative")
    return 2 * 3**a - 2 ** (a + 1)


def word_ee(k: int) -> str:
    return "O" * (k - 2) + "EE"


def word_eoe(k: int) -> str:
    return "O" * (k - 3) + "EOE"


def expanding_two_even(k: int) -> bool:
    return 3 ** (k - 2) > 2**k


def shared_tail_holds_exact(n: int, k: int) -> bool:
    a = k - 2
    return n ** (3**a) > (1 << denom_bits(a)) * (n + 1) ** (1 << k)


def shared_tail_holds_log(n: int, k: int) -> bool:
    a = k - 2
    left = (3**a) * log(n)
    right = denom_bits(a) * log(2) + (1 << k) * log(n + 1)
    return left > right


def shared_tail_holds(n: int, k: int) -> bool:
    if k <= EXACT_K_MAX:
        return shared_tail_holds_exact(n, k)
    return shared_tail_holds_log(n, k)


def first_shared_cutoff(k: int) -> int | None:
    for n in range(2, N0_SEARCH_CAP + 1):
        if shared_tail_holds(n, k):
            return n
    return None


def expected_n0(k: int) -> int:
    if k in EXPECTED_N0:
        return EXPECTED_N0[k]
    return 5


def row_for_k(k: int) -> dict[str, Any]:
    n0 = first_shared_cutoff(k)
    ee = word_ee(k)
    eoe = word_eoe(k)
    table_ee = None if n0 is None else cycle_itinerary_hits(ee, 2, n0)
    table_eoe = None if n0 is None else cycle_itinerary_hits(eoe, 2, n0)
    return {
        "k": k,
        "a_ee": k - 2,
        "a_eoe": k - 3,
        "word_ee": ee,
        "word_eoe": eoe,
        "expanding": expanding_two_even(k),
        "denom_bits": denom_bits(k - 2),
        "left_exp": 3 ** (k - 2),
        "succ_exp": 1 << k,
        "n0": n0,
        "n0_expected": expected_n0(k),
        "fires_at_n0": None if n0 is None else shared_tail_holds(n0, k),
        "fails_before_n0": None
        if n0 is None
        else not shared_tail_holds(n0 - 1, k),
        "never_n_le_4": not any(shared_tail_holds(n, k) for n in (2, 3, 4)),
        "table_ee": table_ee,
        "table_eoe": table_eoe,
    }


def y_succ_holds_from_two() -> bool:
    return all(y_succ_cube_lt_two_a4(n) for n in range(2, 64))


def run_probe() -> dict[str, Any]:
    rows = [row_for_k(k) for k in range(K_MIN, K_MAX + 1)]
    n0s = [row["n0"] for row in rows]
    return {
        "basin": [1],
        "k_min": K_MIN,
        "k_max": K_MAX,
        "rows": rows,
        "all_expanding": all(row["expanding"] for row in rows),
        "all_tails_fire": all(row["n0"] is not None for row in rows),
        "n0_matches_expected": all(row["n0"] == row["n0_expected"] for row in rows),
        "max_n0": max((row["n0"] or 0) for row in rows),
        "n0_at_six": rows[0]["n0"] if rows else None,
        "n0_from_eleven": [row["n0"] for row in rows if row["k"] >= 11],
        "plateau_is_five": all(row["n0"] == 5 for row in rows if row["k"] >= 11),
        "never_n_le_4": all(row["never_n_le_4"] for row in rows),
        "denom_closed_form": all(
            denom_bits(a) == odd_log2_C(a) for a in range(0, K_MAX)
        ),
        "y_succ_from_two": y_succ_holds_from_two(),
        "all_tables_empty": all(
            row["table_ee"] is not None
            and row["table_ee"]["hit_count"] == 0
            and row["table_eoe"] is not None
            and row["table_eoe"]["hit_count"] == 0
            for row in rows
        ),
        "n0_sequence": n0s,
        "length_eight_census": False,
        "three_even": False,
        "n_search": False,
        "cycle_state_search": False,
        "induction_on_period": False,
        "induction_on_n": False,
    }


def lean_api_present() -> dict[str, bool]:
    leftover = LEFTOVER_CYCLES.read_text(encoding="utf-8")
    census = SMALL_CYCLE_CENSUS.read_text(encoding="utf-8")
    cycles = CYCLES.read_text(encoding="utf-8")
    combined = leftover + census + cycles + pre_finance_text()
    named = {name: has_named(combined, name) for name in LEAN_THEOREMS}
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        "no_global_termination_theorem": "theorem juggler_reaches_one"
        not in combined,
        "no_all_cycles_impossible": "theorem no_juggler_cycle" not in combined,
        "no_cycle_engine": "def CycleSearch" not in combined
        and "def CycleStates" not in combined,
        "length_eight_open_in_census": "Length eight is open" in census,
        "no_length_eight_theorem": "theorem no_cycle_itinerary_length_eight"
        not in combined,
        "no_length_nine_theorem": "theorem no_cycle_itinerary_length_nine"
        not in combined,
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
        "Minimal_untouched": "uniform_two_even" not in MINIMAL.read_text(
            encoding="utf-8"
        ),
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["no_cycle_itinerary_ooooee"]
        and lean["no_cycle_itinerary_oooooee"]
        and lean["no_cycle_itinerary_length_le_seven"]
        and lean["no_cycle_itinerary_two_even_ee"]
        and lean["no_cycle_itinerary_two_even_eoe"]
        and lean["shared_two_even_tail"]
        and lean["no_length_eight_theorem"]
        and lean["length_eight_open_in_census"]
        and lean["no_all_cycles_impossible"]
        and lean["no_cycle_engine"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if (
        scan["length_eight_census"]
        or scan["three_even"]
        or scan["n_search"]
        or scan["cycle_state_search"]
        or scan["induction_on_period"]
        or scan["induction_on_n"]
    ):
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope search"}
    if not scan["denom_closed_form"] or not scan["all_expanding"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "closed form or expansion failed",
        }
    if not scan["all_tails_fire"] or not scan["n0_matches_expected"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": f"tail N0={scan['n0_sequence']}",
        }
    if not scan["never_n_le_4"] or not scan["plateau_is_five"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "N0 not bounded by the n=5 plateau",
        }
    if not scan["y_succ_from_two"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "EOE auxiliary (y+1)^3 < 2(n+1)^4 fails",
        }
    if not scan["all_tables_empty"]:
        return {"classification": CLASS_REMAINS, "reason": "finite table hit"}
    return {
        "classification": CLASS_GREEN,
        "reason": (
            "both leftover families are Lean-excluded for every "
            "k>=6 and n>=2 by the shared tail at n>=256 plus the "
            "seven-odd obstruction and three Fin 256 tables below "
            "256; N0(6)=205 then 14,8,6,6 and N0=5 for k>=11; not "
            "a length-8 census"
        ),
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "cycles_impossible": False,
            "two_even_cycles_impossible": False,
            "two_even_leftover_families_excluded": True,
            "length_eight_census": False,
            "induction_on_period": False,
            "induction_on_n": False,
            "no_escape_orbits": False,
        }
    )
    return {
        "experiment": "juggler_uniform_two_even",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "shared two-even leftover comparison for k=6..24; Lean "
            "exclusion of both families for every k>=6 at n>=256 "
            "plus seven-odd/Fin 256 tables below 256; no length-8 "
            "census; no three-even; no halt"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler uniform two-even leftover tails",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. The two leftover families",
        "`O^{k-2}EE` and `O^{k-3}EOE` only; not a length-8 census and",
        "not induction on period or on n.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Do both two-even leftover tails fire",
        "                        for every k>=6 with N0 bounded in k?",
        "Novelty hypothesis      Cutoffs get easier; N0 drops to 5",
        "Falsifier               A k that never fires, or N0(k)->inf",
        "Existing machinery      Lemma 3.5/3.7 cells; lowerDenom(O^a)",
        "Maximum Phase-0 scope   N0(k) for k=6..24; empty tables;",
        "                        no Lean, no length-8 census, no halt",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Shared tail",
        "",
        "- comparison: `n^{3^{k-2}} > 2^{e_{k-2}} (n+1)^{2^k}`",
        "- `e_a = 2*3^a - 2^{a+1} = log2(lowerDenom(O^a))`",
        f"- closed form matches recurrence: `{scan['denom_closed_form']}`",
        f"- both families expanding for k=6..24: `{scan['all_expanding']}`",
        f"- never holds for n<=4: `{scan['never_n_le_4']}`",
        f"- EOE auxiliary from n=2: `{scan['y_succ_from_two']}`",
        f"- max N0: `{scan['max_n0']}`",
        f"- plateau N0=5 for k>=11: `{scan['plateau_is_five']}`",
        f"- all tables empty: `{scan['all_tables_empty']}`",
        "",
        "## Cutoffs",
        "",
    ]
    for row in scan["rows"]:
        ee_hits = None if row["table_ee"] is None else row["table_ee"]["hits"]
        eoe_hits = None if row["table_eoe"] is None else row["table_eoe"]["hits"]
        lines.append(
            f"- k=`{row['k']}` words=`{row['word_ee']}` / `{row['word_eoe']}` "
            f"N0=`{row['n0']}` e=`{row['denom_bits']}` "
            f"ee_hits=`{ee_hits}` eoe_hits=`{eoe_hits}`"
        )
    lines.extend(
        [
            "",
            "## Lean",
            "",
        ]
    )
    for name in LEAN_THEOREMS:
        lines.append(f"- `{name}`: `{lean.get(name)}`")
    lines.extend(
        [
            f"- length eight open in census: `{lean.get('length_eight_open_in_census')}`",
            f"- no length-eight theorem: `{lean.get('no_length_eight_theorem')}`",
            f"- no all-cycles-impossible theorem: `{lean.get('no_all_cycles_impossible')}`",
            f"- no cycle engine: `{lean.get('no_cycle_engine')}`",
            f"- no global halt theorem: `{lean.get('no_global_termination_theorem')}`",
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
            "This is not a halt result and not a length-8 census.",
            "The two leftover families are Lean-excluded for every",
            "k>=6. Other two-even words and three-even leftovers",
            "were not opened.",
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
    decision = payload["decision"]
    scan = payload["scan"]
    print(decision["classification"])
    print(decision["reason"])
    print(f"max_N0={scan['max_n0']} plateau={scan['plateau_is_five']}")
    for row in scan["rows"]:
        print(f"  k={row['k']} N0={row['n0']}")


if __name__ == "__main__":
    main()

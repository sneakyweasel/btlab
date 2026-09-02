"""Uniform prefix-cell tails for bunched last-cluster leftovers.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a length-8 or length-9 census, not first-E at e>=4, and not
induction on period or on n.

After bootstrap and first-E transport, the surviving three-even
CycleMin leftovers are O^a E O^b E O^c E with a>=2, c in {0,1},
and b short: b<=3 (EE) or b<=2 (EOE). Those are seven families
O^a ++ tail, one type per fixed mixed tail. The comparison is the
length-9 prefix-cell tail in a:

    n^{3^a} > 2^{e_a} Z(n,b,c)^{2^a},

where e_a = log2(lowerDenom(O^a)) and Z is the last-even / last-odd
bound on T_{O^a}(n) through the tail. Phase 0 asks whether each
family fires for every expanding a, with N0 bounded in a.
"""

from __future__ import annotations

import json
from functools import lru_cache
from math import log
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_length_nine import (
    cycle_itinerary_hits,
    odd_log2_C,
    tail_fires,
    z_upper,
)
from research.juggler_sequence.lean_paths import (
    BUNCHED_EEE,
    BUNCHED_EEOE,
    BUNCHED_EOEE,
    BUNCHED_EOEOE,
    BUNCHED_EOOEE,
    BUNCHED_EOOEOE,
    BUNCHED_EOOOEE,
    BUNCHED_TIGHT,
    CYCLES,
    FIRST_E_TRANSPORT,
    LEFTOVER_CYCLES,
    MINIMAL,
    SMALL_CYCLE_CENSUS,
    engine_floor_text,
    has_named,
    pre_finance_text,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM
from research.juggler_sequence.uniform_two_even import denom_bits

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_bunched_last_cluster.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_bunched_last_cluster.md"

CLASS_GREEN = "BUNCHED_LAST_CLUSTER_GREEN"
CLASS_REMAINS = "BUNCHED_LAST_CLUSTER_REMAINS"
CLASS_INCOMPLETE = "BUNCHED_LAST_CLUSTER_INCOMPLETE"

A_MAX = 20
EXACT_A_MAX = 6
N0_SEARCH_CAP = 500
EEE_CUBE_FROM = 73
EOEE_CUBE_FROM = 314
EOEE_K = 6
EOOEE_CUBE_FROM = 205
EOOEE_K = 4

FAMILIES: tuple[dict[str, Any], ...] = (
    {"name": "EEE", "b": 0, "c": 0, "a_min": 6, "first_n0": 73, "plateau_from": 11},
    {"name": "EOEE", "b": 1, "c": 0, "a_min": 5, "first_n0": 89, "plateau_from": 10},
    {"name": "EOOEE", "b": 2, "c": 0, "a_min": 4, "first_n0": 120, "plateau_from": 9},
    {"name": "EOOOEE", "b": 3, "c": 0, "a_min": 3, "first_n0": 188, "plateau_from": 8},
    {"name": "EEOE", "b": 0, "c": 1, "a_min": 5, "first_n0": 60, "plateau_from": 9},
    {"name": "EOEOE", "b": 1, "c": 1, "a_min": 4, "first_n0": 81, "plateau_from": 9},
    {"name": "EOOEOE", "b": 2, "c": 1, "a_min": 3, "first_n0": 126, "plateau_from": 8},
)

LEAN_THEOREMS = (
    "cycle_trailing_evens_lt",
    "no_cycle_itinerary_ooooooeee",
    "no_cycle_itinerary_two_even_ee",
    "no_cycle_itinerary_two_even_eoe",
    "no_cycleMin_gapped_three_even_ee",
    "no_cycleMin_gapped_three_even_eoe",
    "no_cycle_itinerary_length_le_seven",
    "CycleMin",
    "no_cycle_itinerary_three_even_eee",
    "three_even_eee_tail",
    "no_cycle_itinerary_three_even_eoee",
    "three_even_eoee_tail_of_five",
    "no_cycle_itinerary_three_even_eooee",
    "three_even_eooee_tail",
    "no_cycle_itinerary_three_even_eoooee",
    "no_cycle_itinerary_three_even_eeoe",
    "no_cycle_itinerary_three_even_eoeoe",
    "no_cycle_itinerary_three_even_eooeoe",
)


def tail_word(b: int, c: int) -> str:
    return "E" + "O" * b + "E" + "O" * c + "E"


def family_word(a: int, b: int, c: int) -> str:
    return "O" * a + tail_word(b, c)


def expanding_family(a: int, b: int, c: int) -> bool:
    odd = a + b + c
    length = odd + 3
    return 3**odd > 2**length


def first_expanding_a(b: int, c: int) -> int:
    a = 2
    while a <= A_MAX and not expanding_family(a, b, c):
        a += 1
    return a


@lru_cache(maxsize=None)
def z_upper_cached(n: int, b: int, c: int) -> int:
    return z_upper(n, b, c)


def tail_holds_exact(n: int, a: int, b: int, c: int) -> bool:
    return tail_fires(n, a, b, c)


def tail_holds_log(n: int, a: int, b: int, c: int) -> bool:
    if n < 2:
        return False
    z_u = z_upper_cached(n, b, c)
    if z_u <= 0:
        return False
    left = (3**a) * log(n)
    right = denom_bits(a) * log(2) + (1 << a) * log(z_u)
    return left > right


def tail_holds(n: int, a: int, b: int, c: int) -> bool:
    if a <= EXACT_A_MAX:
        return tail_holds_exact(n, a, b, c)
    return tail_holds_log(n, a, b, c)


def first_cutoff(a: int, b: int, c: int) -> int | None:
    for n in range(2, N0_SEARCH_CAP + 1):
        if tail_holds(n, a, b, c):
            return n
    return None


def eee_coarse_holds(n: int, a: int) -> bool:
    """O^a EEE with the algebraic cell z < (n+1)^8."""
    if n < 2:
        return False
    left = (3**a) * log(n)
    right = denom_bits(a) * log(2) + (1 << (a + 3)) * log(n + 1)
    return left > right


def eee_cubes_from(n0: int = EEE_CUBE_FROM, a_lo: int = 6) -> bool:
    for a in range(a_lo, A_MAX):
        for n in range(n0, n0 + 80):
            if eee_coarse_holds(n, a) and not eee_coarse_holds(n, a + 1):
                return False
    return True


def eoee_coarse_holds(n: int, a: int) -> bool:
    """O^a EOEE with the algebraic cell z < (n+1)^6."""
    if n < 2:
        return False
    left = (3**a) * log(n)
    right = denom_bits(a) * log(2) + EOEE_K * (1 << a) * log(n + 1)
    return left > right


def eoee_cubes_from(n0: int = EOEE_CUBE_FROM, a_lo: int = 5) -> bool:
    for a in range(a_lo, A_MAX):
        for n in range(n0, n0 + 80):
            if eoee_coarse_holds(n, a) and not eoee_coarse_holds(n, a + 1):
                return False
    return True


def eooee_coarse_holds(n: int, a: int) -> bool:
    """O^a EOOEE with the algebraic cell z < (n+1)^4."""
    if n < 2:
        return False
    left = (3**a) * log(n)
    right = denom_bits(a) * log(2) + EOOEE_K * (1 << a) * log(n + 1)
    return left > right


def eooee_cubes_from(n0: int = EOOEE_CUBE_FROM, a_lo: int = 4) -> bool:
    for a in range(a_lo, A_MAX):
        for n in range(n0, n0 + 80):
            if eooee_coarse_holds(n, a) and not eooee_coarse_holds(n, a + 1):
                return False
    return True


def row_for(family: dict[str, Any], a: int) -> dict[str, Any]:
    b = family["b"]
    c = family["c"]
    word = family_word(a, b, c)
    n0 = first_cutoff(a, b, c)
    table = None if n0 is None else cycle_itinerary_hits(word, 2, n0)
    return {
        "name": family["name"],
        "a": a,
        "b": b,
        "c": c,
        "word": word,
        "tail": tail_word(b, c),
        "expanding": expanding_family(a, b, c),
        "denom_bits": denom_bits(a),
        "n0": n0,
        "fires_at_n0": None if n0 is None else tail_holds(n0, a, b, c),
        "fails_before_n0": None if n0 is None else not tail_holds(n0 - 1, a, b, c),
        "never_n_le_4": not any(tail_holds(n, a, b, c) for n in (2, 3, 4)),
        "table": table,
    }


def family_block(family: dict[str, Any]) -> dict[str, Any]:
    rows = [row_for(family, a) for a in range(family["a_min"], A_MAX + 1)]
    n0s = [row["n0"] for row in rows]
    plateau_from = family["plateau_from"]
    return {
        "name": family["name"],
        "b": family["b"],
        "c": family["c"],
        "tail": tail_word(family["b"], family["c"]),
        "a_min": family["a_min"],
        "a_min_computed": first_expanding_a(family["b"], family["c"]),
        "first_n0": family["first_n0"],
        "plateau_from": plateau_from,
        "rows": rows,
        "n0_sequence": n0s,
        "all_expanding": all(row["expanding"] for row in rows),
        "all_tails_fire": all(row["n0"] is not None for row in rows),
        "first_n0_matches": bool(rows) and rows[0]["n0"] == family["first_n0"],
        "plateau_is_five": all(
            row["n0"] == 5 for row in rows if row["a"] >= plateau_from
        ),
        "never_n_le_4": all(row["never_n_le_4"] for row in rows),
        "all_tables_empty": all(
            row["table"] is not None and row["table"]["hit_count"] == 0 for row in rows
        ),
        "max_n0": max((row["n0"] or 0) for row in rows),
    }


def run_probe() -> dict[str, Any]:
    blocks = [family_block(family) for family in FAMILIES]
    return {
        "basin": [1],
        "a_max": A_MAX,
        "families": [family["name"] for family in FAMILIES],
        "blocks": blocks,
        "family_count": len(blocks),
        "all_expanding": all(block["all_expanding"] for block in blocks),
        "all_tails_fire": all(block["all_tails_fire"] for block in blocks),
        "first_n0_matches": all(block["first_n0_matches"] for block in blocks),
        "a_min_matches": all(
            block["a_min"] == block["a_min_computed"] for block in blocks
        ),
        "plateau_is_five": all(block["plateau_is_five"] for block in blocks),
        "never_n_le_4": all(block["never_n_le_4"] for block in blocks),
        "all_tables_empty": all(block["all_tables_empty"] for block in blocks),
        "max_n0": max(block["max_n0"] for block in blocks),
        "denom_closed_form": all(
            denom_bits(a) == odd_log2_C(a) for a in range(0, A_MAX + 1)
        ),
        "eee_cubes": eee_cubes_from(),
        "eee_coarse_n0_at_six": next(
            n for n in range(2, N0_SEARCH_CAP + 1) if eee_coarse_holds(n, 6)
        ),
        "eoee_cubes": eoee_cubes_from(),
        "eoee_coarse_n0_at_five": next(
            n for n in range(2, N0_SEARCH_CAP + 1) if eoee_coarse_holds(n, 5)
        ),
        "eooee_cubes": eooee_cubes_from(),
        "eooee_coarse_n0_at_four": next(
            n for n in range(2, N0_SEARCH_CAP + 1) if eooee_coarse_holds(n, 4)
        ),
        "uniform_coarse_K": False,
        "length_eight_census": False,
        "length_nine_census": False,
        "first_e_at_four": False,
        "induction_on_period": False,
        "induction_on_n": False,
    }


def lean_api_present() -> dict[str, bool]:
    combined = (
        LEFTOVER_CYCLES.read_text(encoding="utf-8")
        + BUNCHED_EEE.read_text(encoding="utf-8")
        + BUNCHED_EOEE.read_text(encoding="utf-8")
        + BUNCHED_EOOEE.read_text(encoding="utf-8")
        + BUNCHED_EEOE.read_text(encoding="utf-8")
        + BUNCHED_EOEOE.read_text(encoding="utf-8")
        + BUNCHED_EOOOEE.read_text(encoding="utf-8")
        + BUNCHED_TIGHT.read_text(encoding="utf-8")
        + BUNCHED_EOOEOE.read_text(encoding="utf-8")
        + FIRST_E_TRANSPORT.read_text(encoding="utf-8")
        + CYCLES.read_text(encoding="utf-8")
        + SMALL_CYCLE_CENSUS.read_text(encoding="utf-8")
        + pre_finance_text()
    )
    named = {name: has_named(combined, name) for name in LEAN_THEOREMS}
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        "no_global_termination_theorem": "theorem juggler_reaches_one"
        not in combined,
        "no_all_cycles_impossible": "theorem no_juggler_cycle" not in combined,
        "no_cycle_engine": "def CycleSearch" not in combined
        and "def CycleStates" not in combined,
        "length_eight_open_in_census": "Length eight is open"
        in SMALL_CYCLE_CENSUS.read_text(encoding="utf-8"),
        "no_length_eight_theorem": "theorem no_cycle_itinerary_length_eight"
        not in combined,
        "no_length_nine_theorem": "theorem no_cycle_itinerary_length_nine"
        not in combined,
        "no_bunched_tail_theorem": "theorem no_cycle_itinerary_bunched" not in combined
        and "theorem no_cycleMin_bunched" not in combined
        and "theorem no_cycle_itinerary_last_cluster" not in combined,
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
        "Minimal_untouched": "bunched_last_cluster" not in MINIMAL.read_text(
            encoding="utf-8"
        ),
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["no_cycle_itinerary_ooooooeee"]
        and lean["no_cycle_itinerary_two_even_ee"]
        and lean["no_cycleMin_gapped_three_even_ee"]
        and lean["no_cycle_itinerary_three_even_eee"]
        and lean["three_even_eee_tail"]
        and lean["no_cycle_itinerary_three_even_eoee"]
        and lean["three_even_eoee_tail_of_five"]
        and lean["no_cycle_itinerary_three_even_eooee"]
        and lean["three_even_eooee_tail"]
        and lean["no_cycle_itinerary_three_even_eoooee"]
        and lean["no_cycle_itinerary_three_even_eeoe"]
        and lean["no_cycle_itinerary_three_even_eoeoe"]
        and lean["no_cycle_itinerary_three_even_eooeoe"]
        and lean["no_length_eight_theorem"]
        and lean["length_eight_open_in_census"]
        and lean["no_bunched_tail_theorem"]
        and lean["no_all_cycles_impossible"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if (
        scan["length_eight_census"]
        or scan["length_nine_census"]
        or scan["first_e_at_four"]
        or scan["induction_on_period"]
        or scan["induction_on_n"]
    ):
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope search"}
    if not scan["denom_closed_form"] or not scan["all_expanding"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "closed form or expansion failed",
        }
    if not scan["a_min_matches"] or not scan["first_n0_matches"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "a_min or first N0 mismatch",
        }
    if not scan["all_tails_fire"]:
        return {"classification": CLASS_REMAINS, "reason": "a family tail never fires"}
    if not scan["never_n_le_4"] or not scan["plateau_is_five"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "N0 not bounded by the n=5 plateau",
        }
    if not scan["eee_cubes"] or scan["eee_coarse_n0_at_six"] != 73:
        return {
            "classification": CLASS_REMAINS,
            "reason": "EEE coarse cell does not cube from N0=73",
        }
    if (
        not scan["eoee_cubes"]
        or scan["eoee_coarse_n0_at_five"] != EOEE_CUBE_FROM
        or scan["uniform_coarse_K"]
    ):
        return {
            "classification": CLASS_REMAINS,
            "reason": "EOEE coarse cell does not cube from N0=314",
        }
    if (
        not scan["eooee_cubes"]
        or scan["eooee_coarse_n0_at_four"] != EOOEE_CUBE_FROM
    ):
        return {
            "classification": CLASS_REMAINS,
            "reason": "EOOEE coarse cell does not cube from N0=205",
        }
    if not scan["all_tables_empty"]:
        return {"classification": CLASS_REMAINS, "reason": "finite table hit"}
    return {
        "classification": CLASS_GREEN,
        "reason": (
            "seven bunched last-cluster families fire with N0 bounded "
            "in a; Lean excludes all seven as CycleItinerary families; a "
            "uniform coarse (n+1)^K cell for the last four is refuted "
            "and those four use a tight last-odd cell; not a "
            "length-8/9 census"
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
            "three_even_cycles_impossible": False,
            "bunched_lean": False,
            "eee_lean": True,
            "eoee_lean": True,
            "eooee_lean": True,
            "eoooee_lean": True,
            "eeoe_lean": True,
            "eoeoe_lean": True,
            "eooeoe_lean": True,
            "uniform_coarse_K": False,
            "length_eight_census": False,
            "length_nine_census": False,
            "first_e_at_four": False,
            "induction_on_period": False,
            "induction_on_n": False,
        }
    )
    return {
        "experiment": "juggler_bunched_last_cluster",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "prefix-cell N0(a) for the seven bunched last-cluster "
            "families through a=20; empty CycleItinerary tables below N0; "
            "EEE coarse cubing from n>=73; Lean O^a EEE for a>=6; "
            "EOEE coarse cubing from n>=314; Lean O^a EOEE for a>=5; "
            "EOOEE coarse cubing from n>=205, Lean via the two-even "
            "tail at n>=256; Lean O^a EEOE, EOEOE, EOOOEE, EOOEOE "
            "by the same cells or a tight last-odd split at a=3; "
            "uniform coarse K refuted; no length-8/9 census"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler bunched last-cluster leftover tails",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. Seven bunched last-cluster",
        "families only; not a length-8/9 census and not first-E at",
        "e>=4.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Do the seven bunched last-cluster",
        "                        tails fire for every large a, with",
        "                        N0 bounded in a?",
        "Novelty hypothesis      Fixed mixed tail plus C_{O^a};",
        "                        cutoffs drop as a grows",
        "Falsifier               A tail whose N0 grows with a",
        "Existing machinery      prefix-cell Z; denomBits; OOOOOOEEE",
        "Maximum Phase-1 scope   Lean all seven bunched families;",
        "                        no length-8/9 census",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        f"- family count: `{scan['family_count']}`",
        f"- max N0: `{scan['max_n0']}`",
        f"- plateau N0=5: `{scan['plateau_is_five']}`",
        f"- tables empty: `{scan['all_tables_empty']}`",
        f"- EEE cubes from 73: `{scan['eee_cubes']}`",
        f"- EOEE cubes from 314: `{scan['eoee_cubes']}`",
        f"- EOOEE cubes from 205: `{scan['eooee_cubes']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Families",
        "",
    ]
    for block in scan["blocks"]:
        lines.append(
            f"- `{block['name']}` tail=`{block['tail']}` a>=`{block['a_min']}` "
            f"N0=`{block['n0_sequence']}`"
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
            f"- no bunched-tail theorem: `{lean.get('no_bunched_tail_theorem')}`",
            f"- length eight open in census: `{lean.get('length_eight_open_in_census')}`",
            f"- no length-nine theorem: `{lean.get('no_length_nine_theorem')}`",
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
            "This is not a halt result, not a length-8/9 census, and",
            "not a Lean theorem no_cycle_itinerary_bunched.",
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
    for block in scan["blocks"]:
        print(f"  {block['name']} N0={block['n0_sequence']}")


if __name__ == "__main__":
    main()

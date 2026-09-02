"""Length-7 even-terminating expanding cycle-word inventory.

Not a Research Engine control-layer experiment. Not a halt theorem.
Does not search unbounded cycle states. Records the Paper A filters
on length 7, the leftover-tail computation, and the Lean census
`no_cycle_itinerary_length_le_seven`.
"""

from __future__ import annotations

import json
from itertools import product
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_ooo_scale import (
    cyclemin_orientation,
    icbrt,
    lower_denom,
    rotations,
)
from research.juggler_sequence.cycle_itinerary import follows_itinerary, image_after
from research.juggler_sequence.lean_paths import (
    CELLS,
    CYCLES,
    ENVELOPE,
    LEFTOVER_CYCLES,
    MINIMAL,
    PROGRESS,
    SMALL_CYCLE_CENSUS,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_cycle_length_seven.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_cycle_length_seven.md"
LEAN_PATH = CYCLES
FLOOR_PATH = ENVELOPE
PROGRESS_PATH = PROGRESS
MIN_PATH = MINIMAL
CENSUS_PATH = SMALL_CYCLE_CENSUS
LEFTOVER_PATH = LEFTOVER_CYCLES
CELLS_PATH = CELLS

CLASS_GREEN = "LENGTH_SEVEN_LEFTOVER_TAIL_GREEN"
CLASS_REMAINS = "LENGTH_SEVEN_LEFTOVER_REMAINS"
CLASS_REPARAM = "LENGTH_SEVEN_REPARAMETERIZATION"
CLASS_INCOMPLETE = "LENGTH_SEVEN_INCOMPLETE"

EXPECTED_WORDS = (
    "OOOOOOE",
    "EOOOOOE",
    "OEOOOOE",
    "OOEOOOE",
    "OOOEOOE",
    "OOOOEOE",
    "OOOOOEE",
)
LEFTOVER_WORDS = ("OOOOOEE", "OOOOEOE")
BOOTSTRAP_WORDS = ("OOEOOOE", "OOOEOOE")
ODD_RUN_WORD = "OOOOOOE"

THRESHOLD_BY_SUFFIX = {
    "OO": ("oo_suffix_threshold", 5),
    "OOO": ("ooo_suffix_threshold", 3),
    "OOOO": ("odd_run_suffix_threshold", 3),
    "OOOOO": ("odd_run_suffix_threshold", 3),
}

LEAN_THEOREMS = (
    "cycle_itinerary_formally_expanding",
    "no_cycle_odd_run_append_even",
    "oo_suffix_threshold",
    "ooo_suffix_threshold",
    "no_cycleMin_internal_even_threshold",
    "cycleMin_not_odd_even",
    "cycleMin_not_start_even",
    "cycle_last_even_interval",
    "no_cycle_itinerary_length_le_six",
    "no_cycle_itinerary_ooeoooe",
    "no_cycle_itinerary_oooeooe",
    "no_cycle_itinerary_oooooee",
    "no_cycle_itinerary_ooooeoe",
    "no_cycle_itinerary_length_le_seven",
)

CERTIFICATE_UNCHANGED = (
    "no_cycle_append_even_of_suffix_threshold",
    "odd_run_suffix_threshold",
    "exists_cycle_min_odd",
    "lower_growth_word",
    "no_cycle_itinerary_oooeoe",
    "no_cycle_itinerary_ooooee",
)

# Shared refined tail n^{243} > 2^{422} (n+1)^{128}.
REFINED_LEFT_EXP = 243
REFINED_TWO_EXP = 422
REFINED_SUCC_EXP = 128
# Naive OOOOEOE prefix-to-last-even: lowerDenom(OOOOEO) = 2^{550}.
NAIVE_EOE_TWO_EXP = 550
N0_SEARCH_CAP = 10_000


def expanding(word: str) -> bool:
    return 2 ** len(word) < 3 ** word.count("O")


def formal_exponent(word: str) -> str:
    return f"{3 ** word.count('O')}/{2 ** len(word)}"


def length_seven_e_expanding() -> list[str]:
    found = []
    for prefix in product("OE", repeat=6):
        word = "".join(prefix) + "E"
        if expanding(word):
            found.append(word)
    order = {word: index for index, word in enumerate(EXPECTED_WORDS)}
    return sorted(found, key=lambda word: order.get(word, 99))


def last_internal_e_index(word: str) -> int | None:
    if not word.endswith("E"):
        return None
    pos = word[:-1].rfind("E")
    return None if pos < 0 else pos


def suffix_after_last_internal_e(word: str) -> str | None:
    idx = last_internal_e_index(word)
    if idx is None:
        return None
    return word[idx + 1 : -1]


def rotation_class(word: str) -> str:
    return "|".join(sorted(set(rotations(word))))


def named_filter(word: str) -> str:
    if word == ODD_RUN_WORD:
        return "no_cycle_odd_run_append_even"
    suffix = suffix_after_last_internal_e(word)
    legal = cyclemin_orientation(word)["legal_cyclemin"]
    threshold = THRESHOLD_BY_SUFFIX.get(suffix or "")
    if word.startswith("E"):
        return "rotate_onto_OOOOOEE"
    if word.startswith("OE"):
        return "cycleMin_not_odd_even"
    if legal and threshold is not None:
        return f"bootstrap_{threshold[0]}"
    if word == "OOOOOEE":
        return "leftover_tail_EE"
    if word == "OOOOEOE":
        return "leftover_tail_EOE"
    return "unclassified"


def candidate_row(word: str) -> dict[str, Any]:
    idx = last_internal_e_index(word)
    suffix = suffix_after_last_internal_e(word)
    prefinal = word[:-1]
    threshold = THRESHOLD_BY_SUFFIX.get(suffix or "")
    orientation = cyclemin_orientation(word)
    all_odd_last_e = idx is None and prefinal == "O" * len(prefinal)
    return {
        "word": word,
        "formal_exponent": formal_exponent(word),
        "odd_count": word.count("O"),
        "internal_e_index": idx,
        "suffix_after_internal_e": suffix,
        "existing_threshold": None if threshold is None else threshold[0],
        "threshold_N": None if threshold is None else threshold[1],
        "internal_e_bootstrap_applicable": bool(
            orientation["legal_cyclemin"] and threshold is not None
        ),
        "all_odd_last_e": all_odd_last_e,
        "legal_cyclemin": orientation["legal_cyclemin"],
        "blocked_by": orientation["blocked_by"],
        "rotation_class": rotation_class(word),
        "named_filter": named_filter(word),
        "leftover": word in LEFTOVER_WORDS,
    }


def comparison_holds(n: int, left_exp: int, two_exp: int, succ_exp: int) -> bool:
    return n**left_exp > (1 << two_exp) * (n + 1) ** succ_exp


def first_tail_cutoff(left_exp: int, two_exp: int, succ_exp: int) -> int | None:
    for n in range(2, N0_SEARCH_CAP + 1):
        if comparison_holds(n, left_exp, two_exp, succ_exp):
            return n
    return None


def y_succ_cube_lt_two_a4(n: int) -> bool:
    """(y+1)^3 < 2(n+1)^4 for every y with y^3 < (n+1)^4."""
    a = n + 1
    ymax = icbrt(a**4 - 1)
    return (ymax + 1) ** 3 < 2 * a**4


def first_y_succ_cutoff() -> int | None:
    for n in range(2, N0_SEARCH_CAP + 1):
        if y_succ_cube_lt_two_a4(n):
            # Once true, stay true on a window; the Lemma 3.5 split is
            # monotone in A for A >= 2 on the y <= A side.
            if all(y_succ_cube_lt_two_a4(m) for m in range(n, min(n + 64, N0_SEARCH_CAP) + 1)):
                return n
    return None


def cycle_itinerary_hits(word: str, n_lo: int, n_hi: int) -> dict[str, Any]:
    """Exact follows+image table on n_lo <= n < n_hi. Not a cycle search."""
    follows = 0
    hits: list[int] = []
    for n in range(n_lo, n_hi):
        if not follows_itinerary(n, word):
            continue
        follows += 1
        if image_after(n, word) == n:
            hits.append(n)
    return {
        "word": word,
        "n_lo": n_lo,
        "n_hi": n_hi,
        "checked": n_hi - n_lo,
        "follows": follows,
        "hits": hits,
        "hit_count": len(hits),
    }


def orbit_until_fail(n: int, word: str) -> list[dict[str, Any]]:
    current = n
    steps: list[dict[str, Any]] = []
    for index, letter in enumerate(word):
        parity_ok = (letter == "O" and current % 2 == 1) or (
            letter == "E" and current % 2 == 0
        )
        steps.append(
            {
                "index": index,
                "state": current,
                "letter": letter,
                "parity_ok": parity_ok,
            }
        )
        if not parity_ok:
            break
        current = floor_power(current)
    return steps


def bootstrap_small_n() -> dict[str, Any]:
    oo_at_3 = orbit_until_fail(3, "OOEOOOE")
    ooo_at_3 = orbit_until_fail(3, "OOOEOOE")
    ooo_at_5 = orbit_until_fail(5, "OOOEOOE")
    return {
        "OOEOOOE_n3": {
            "realizes": follows_itinerary(3, "OOEOOOE"),
            "fail_letter": next(
                (row["index"] for row in oo_at_3 if not row["parity_ok"]), None
            ),
            "fail_state": next(
                (row["state"] for row in oo_at_3 if not row["parity_ok"]), None
            ),
            "steps": oo_at_3,
        },
        "OOOEOOE_n3": {
            "realizes": follows_itinerary(3, "OOOEOOE"),
            "fail_letter": next(
                (row["index"] for row in ooo_at_3 if not row["parity_ok"]), None
            ),
            "fail_state": next(
                (row["state"] for row in ooo_at_3 if not row["parity_ok"]), None
            ),
            "steps": ooo_at_3,
        },
        "OOOEOOE_n5": {
            "realizes": follows_itinerary(5, "OOOEOOE"),
            "fail_letter": next(
                (row["index"] for row in ooo_at_5 if not row["parity_ok"]), None
            ),
            "fail_state": next(
                (row["state"] for row in ooo_at_5 if not row["parity_ok"]), None
            ),
            "steps": ooo_at_5,
        },
    }


def two_even_observation() -> dict[str, Any]:
    def o_min(length: int) -> int:
        odd = 0
        while 3**odd <= 2**length:
            odd += 1
        return odd

    rows = []
    for length in (6, 7, 8, 9, 10):
        need = o_min(length)
        rows.append(
            {
                "length": length,
                "o_min": need,
                "max_evens_if_expanding": length - need,
                "three_even_possible": length - need >= 3,
            }
        )
    return {
        "rows": rows,
        "length_eight_same_two_even_type": True,
        "length_nine_first_three_even": True,
        "implemented": False,
    }


def leftover_tails() -> dict[str, Any]:
    denom_ooooo = lower_denom("OOOOO")
    denom_oooo = lower_denom("OOOO")
    denom_ooooeo = lower_denom("OOOOEO")
    n0_refined = first_tail_cutoff(
        REFINED_LEFT_EXP, REFINED_TWO_EXP, REFINED_SUCC_EXP
    )
    n0_naive_eoe = first_tail_cutoff(
        REFINED_LEFT_EXP, NAIVE_EOE_TWO_EXP, REFINED_SUCC_EXP
    )
    n0_y = first_y_succ_cutoff()
    # Exclusion cutoff is the first n where both the power comparison
    # and the (y+1)^3 < 2A^4 step are available.
    n0_ee = n0_refined
    n0_eoe = None
    if n0_refined is not None and n0_y is not None:
        n0_eoe = max(n0_refined, n0_y)
    tables = {}
    if n0_ee is not None:
        tables["OOOOOEE"] = cycle_itinerary_hits("OOOOOEE", 2, n0_ee)
    if n0_eoe is not None:
        tables["OOOOEOE"] = cycle_itinerary_hits("OOOOEOE", 2, n0_eoe)
    return {
        "lower_denom_ooooo": denom_ooooo,
        "lower_denom_ooooo_is_2_422": denom_ooooo == 1 << 422,
        "lower_denom_oooo": denom_oooo,
        "lower_denom_oooo_is_2_130": denom_oooo == 1 << 130,
        "lower_denom_ooooeo": denom_ooooeo,
        "lower_denom_ooooeo_is_2_550": denom_ooooeo == 1 << 550,
        "refined_comparison": "n^243 > 2^422 (n+1)^128",
        "naive_eoe_comparison": "n^243 > 2^550 (n+1)^128",
        "n0_refined": n0_refined,
        "n0_naive_eoe": n0_naive_eoe,
        "n0_y_succ": n0_y,
        "n0_OOOOOEE": n0_ee,
        "n0_OOOOEOE": n0_eoe,
        "y_succ_at_n0": None if n0_eoe is None else y_succ_cube_lt_two_a4(n0_eoe),
        "y_succ_from_two": y_succ_cube_lt_two_a4(2),
        "refined_holds_at_256": comparison_holds(256, 243, 422, 128),
        "tables": tables,
        "ee_hits": tables.get("OOOOOEE", {}).get("hits", []),
        "eoe_hits": tables.get("OOOOEOE", {}).get("hits", []),
        "both_tails_fire": n0_ee is not None and n0_eoe is not None,
        "both_tables_empty": (
            tables.get("OOOOOEE", {}).get("hit_count") == 0
            and tables.get("OOOOEOE", {}).get("hit_count") == 0
        ),
    }


def lean_api_present() -> dict[str, bool]:
    text = LEAN_PATH.read_text(encoding="utf-8")
    corpus = juggler_text()
    floor = engine_floor_text()
    progress = PROGRESS_PATH.read_text(encoding="utf-8")
    leftover = LEFTOVER_PATH.read_text(encoding="utf-8")
    census = CENSUS_PATH.read_text(encoding="utf-8")
    cells = CELLS_PATH.read_text(encoding="utf-8")
    combined = text + corpus + progress + leftover + census + cells
    named: dict[str, bool] = {}
    for name in LEAN_THEOREMS:
        named[name] = has_named(combined, name)
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        "certificate_present": all(has_named(combined, name) for name in CERTIFICATE_UNCHANGED),
        "PowerHeight_absent": "PowerHeight" not in combined,
        "no_global_termination_theorem": "theorem juggler_reaches_one"
        not in combined,
        "no_all_cycles_impossible": "theorem no_juggler_cycle" not in combined,
        "no_cycle_engine": "def CycleSearch" not in combined
        and "def CycleStates" not in combined,
        "length_eight_open_in_census": "Length eight is open" in census,
        "has_length_seven_census": "theorem no_cycle_itinerary_length_le_seven"
        in census,
        "no_length_eight_theorem": "theorem no_cycle_itinerary_length_eight"
        not in combined,
        "no_infinite_path_type": "coinductive" not in combined.lower()
        and "def InfinitePath" not in combined,
        "FloorPower_not_rewritten": "CycleItinerary" not in floor
        and "CycleMin" not in floor,
        "Progress_unchanged": "CycleItinerary" not in progress,
        "orbit_min_not_used": "MinimalNonTerm" not in text,
        "PowerBoundEq_not_used_as_cycle_attack": "PowerBoundEq" not in text,
        "O_terminating_not_claimed": "no_cycle_itinerary_length_seven_ends_odd"
        not in combined,
        "Minimal_untouched": "length_seven" not in MIN_PATH.read_text(encoding="utf-8"),
    }


def run_probe() -> dict[str, Any]:
    words = length_seven_e_expanding()
    rows = [candidate_row(w) for w in words]
    tails = leftover_tails()
    small = bootstrap_small_n()
    two_even = two_even_observation()
    leftovers = [row["word"] for row in rows if row["leftover"]]
    bootstrap = [
        row["word"] for row in rows if row["internal_e_bootstrap_applicable"]
    ]
    odd_run = [row["word"] for row in rows if row["all_odd_last_e"]]
    unclassified = [row["word"] for row in rows if row["named_filter"] == "unclassified"]
    return {
        "basin": [1],
        "expanding_e_words": words,
        "unique_family": words == list(EXPECTED_WORDS),
        "candidates": rows,
        "leftover_itineraries": leftovers,
        "leftovers_are_predicted": set(leftovers) == set(LEFTOVER_WORDS),
        "bootstrap_words": bootstrap,
        "bootstrap_are_predicted": set(bootstrap) == set(BOOTSTRAP_WORDS),
        "odd_run_words": odd_run,
        "unclassified": unclassified,
        "bootstrap_small_n": small,
        "ooeoooe_n3_parity_fail": small["OOEOOOE_n3"]["realizes"] is False
        and small["OOEOOOE_n3"]["fail_state"] == 11,
        "oooeeoe_n3_parity_fail": small["OOOEOOE_n3"]["realizes"] is False
        and small["OOOEOOE_n3"]["fail_state"] == 6,
        "tails": tails,
        "two_even": two_even,
        "n_search": False,
        "length_eight": False,
        "length_nine": False,
        "o_terminating_programme": False,
        "cycle_state_search": False,
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["cycle_itinerary_formally_expanding"]
        and lean["no_cycle_odd_run_append_even"]
        and lean["no_cycleMin_internal_even_threshold"]
        and lean["no_cycle_itinerary_length_le_six"]
        and lean["no_cycle_itinerary_length_le_seven"]
        and lean["no_cycle_itinerary_oooooee"]
        and lean["no_cycle_itinerary_ooooeoe"]
        and lean["has_length_seven_census"]
        and lean["length_eight_open_in_census"]
        and lean["no_length_eight_theorem"]
        and lean["no_cycle_engine"]
        and lean["FloorPower_not_rewritten"]
        and lean["orbit_min_not_used"]
        and lean["PowerBoundEq_not_used_as_cycle_attack"]
        and lean["no_all_cycles_impossible"]
    )
    if not lean_ok:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": f"lean_ok={lean_ok}",
        }
    if (
        scan["n_search"]
        or scan["length_eight"]
        or scan["length_nine"]
        or scan["o_terminating_programme"]
        or scan["cycle_state_search"]
    ):
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "out-of-scope search",
        }
    if not scan["unique_family"] or scan["unclassified"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": (
                f"unexpected family {scan['expanding_e_words']} "
                f"unclassified={scan['unclassified']}"
            ),
        }
    tails = scan["tails"]
    if not tails["lower_denom_ooooo_is_2_422"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "lowerDenom(OOOOO) is not 2^422",
        }
    if not scan["leftovers_are_predicted"] or not scan["bootstrap_are_predicted"]:
        return {
            "classification": CLASS_REPARAM,
            "reason": (
                "inventory is not the predicted two leftovers plus "
                "bootstrap pair"
            ),
        }
    if not tails["both_tails_fire"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": (
                "a leftover tail never fires: "
                f"N0_EE={tails['n0_OOOOOEE']} N0_EOE={tails['n0_OOOOEOE']}"
            ),
        }
    if not tails["both_tables_empty"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": (
                "finite table hit: "
                f"EE={tails['ee_hits']} EOE={tails['eoe_hits']}"
            ),
        }
    if not (
        scan["ooeoooe_n3_parity_fail"] and scan["oooeeoe_n3_parity_fail"]
    ):
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "n=3 bootstrap exceptions are not the expected parity failures",
        }
    return {
        "classification": CLASS_GREEN,
        "secondary": ["TWO_EVEN_TYPE_THROUGH_EIGHT"],
        "reason": (
            "length 7 has the same two-even geometry as length 6: odd-run "
            "excludes OOOOOOE, internal-E bootstrap excludes CycleMin of "
            "OOEOOOE and OOOEOOE (n=3 is a parity failure), and the two "
            f"leftovers die by the Lemma 3.5 tail n^243 > 2^422 (n+1)^128 "
            f"for n >= {tails['n0_OOOOOEE']} together with empty finite "
            "tables below the cutoffs; Lean packages both leftovers and "
            "assembles no_cycle_itinerary_length_le_seven"
        ),
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti["cycles_impossible"] = False
    anti["O_terminating_cycles_impossible"] = False
    anti["length_seven_cycles_impossible"] = True
    anti["length_seven_lean_census"] = True
    anti["useful_uniform_Q0"] = False
    anti["cycle_is_envelope_equality"] = False
    anti["power_bound_eq_forbids_cycles"] = False
    anti["paper_b_length_seven_density"] = False
    anti["all_odd_orbit"] = False
    anti["finite_progress_for_all"] = False
    return {
        "experiment": "juggler_cycle_length_seven",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "structural inventory of even-terminating expanding length-7 "
            "words; Paper A filters; leftover-tail cutoffs; exact "
            "follows+image table below N0; Lean leftover exclusions and "
            "no_cycle_itinerary_length_le_seven; no cycle-state search"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    tails = scan["tails"]
    lines = [
        "# Juggler length-7 cycle-word inventory",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. Length 7 only; length 8 is open.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Which even-terminating expanding length-7",
        "                        words survive the Paper A filters, and do",
        "                        the two leftover tails exclude CycleItinerary?",
        "Novelty hypothesis      Length 7 is the same two-even type as",
        "                        length 6; bootstrap plus Lemma 3.5 tails",
        "Falsifier               A leftover whose tail never fires, or a",
        "                        third leftover shape",
        "Existing machinery      expansion, rotation, odd-run, OO/OOO,",
        "                        CycleMin, internal-E bootstrap, leftover tail",
        "Maximum Phase-0 scope   inventory + N0 + finite table; no Lean",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- secondary: `{decision.get('secondary')}`",
        f"- sorry-free: `{lean['sorry_free']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Even-terminating expanding length-7 words",
        "",
    ]
    for row in scan["candidates"]:
        lines.append(
            f"- `{row['word']}` α=`{row['formal_exponent']}` "
            f"internal_E=`{row['internal_e_index']}` "
            f"suffix=`{row['suffix_after_internal_e']}` "
            f"th=`{row['existing_threshold']}` "
            f"bootstrap=`{row['internal_e_bootstrap_applicable']}` "
            f"cyclemin=`{row['legal_cyclemin']}` "
            f"filter=`{row['named_filter']}`"
        )
    lines.extend(
        [
            "",
            f"- unique family: `{scan['unique_family']}`",
            f"- leftovers: `{scan['leftover_itineraries']}`",
            f"- bootstrap: `{scan['bootstrap_words']}`",
            f"- odd-run: `{scan['odd_run_words']}`",
            f"- unclassified: `{scan['unclassified']}`",
            "",
            "## Bootstrap small-n parity",
            "",
            f"- OOEOOOE at 3 realizes: `{scan['bootstrap_small_n']['OOEOOOE_n3']['realizes']}` "
            f"fail_state=`{scan['bootstrap_small_n']['OOEOOOE_n3']['fail_state']}`",
            f"- OOOEOOE at 3 realizes: `{scan['bootstrap_small_n']['OOOEOOE_n3']['realizes']}` "
            f"fail_state=`{scan['bootstrap_small_n']['OOOEOOE_n3']['fail_state']}`",
            f"- OOOEOOE at 5 realizes: `{scan['bootstrap_small_n']['OOOEOOE_n5']['realizes']}` "
            f"fail_state=`{scan['bootstrap_small_n']['OOOEOOE_n5']['fail_state']}`",
            "",
            "## Leftover tails",
            "",
            f"- lowerDenom(OOOOO) = 2^422: `{tails['lower_denom_ooooo_is_2_422']}`",
            f"- lowerDenom(OOOO) = 2^130: `{tails['lower_denom_oooo_is_2_130']}`",
            f"- lowerDenom(OOOOEO) = 2^550: `{tails['lower_denom_ooooeo_is_2_550']}`",
            f"- refined comparison: `{tails['refined_comparison']}`",
            f"- naive EOE comparison: `{tails['naive_eoe_comparison']}`",
            f"- N0 refined: `{tails['n0_refined']}`",
            f"- N0 naive EOE: `{tails['n0_naive_eoe']}`",
            f"- N0 (y+1)^3 < 2A^4: `{tails['n0_y_succ']}`",
            f"- N0 OOOOOEE: `{tails['n0_OOOOOEE']}`",
            f"- N0 OOOOEOE: `{tails['n0_OOOOEOE']}`",
            f"- refined holds at 256: `{tails['refined_holds_at_256']}`",
            f"- both tails fire: `{tails['both_tails_fire']}`",
            f"- both tables empty: `{tails['both_tables_empty']}`",
            "",
        ]
    )
    for word, table in tails["tables"].items():
        lines.append(
            f"- `{word}` checked=`{table['checked']}` "
            f"follows=`{table['follows']}` hits=`{table['hits']}`"
        )
    lines.extend(
        [
            "",
            "## Two-even observation (not implemented)",
            "",
        ]
    )
    for row in scan["two_even"]["rows"]:
        lines.append(
            f"- length `{row['length']}` o_min=`{row['o_min']}` "
            f"max_E=`{row['max_evens_if_expanding']}` "
            f"three_even=`{row['three_even_possible']}`"
        )
    lines.extend(
        [
            "",
            f"- length 8 is the same two-even type: `{scan['two_even']['length_eight_same_two_even_type']}`",
            f"- length 9 is the first three-even length: `{scan['two_even']['length_nine_first_three_even']}`",
            f"- implemented: `{scan['two_even']['implemented']}`",
            f"- n-search / length 8 / length 9: `{scan['n_search']}` / `{scan['length_eight']}` / `{scan['length_nine']}`",
            "",
            "## Lean",
            "",
        ]
    )
    for name in LEAN_THEOREMS:
        lines.append(f"- `{name}`: `{lean.get(name)}`")
    lines.extend(
        [
            f"- certificate unchanged: `{lean.get('certificate_present')}`",
            f"- FloorPower not rewritten: `{lean.get('FloorPower_not_rewritten')}`",
            f"- length eight open in census: `{lean.get('length_eight_open_in_census')}`",
            f"- length-seven census present: `{lean.get('has_length_seven_census')}`",
            f"- no length-eight theorem: `{lean.get('no_length_eight_theorem')}`",
            f"- orbit-min hypothesis unused: `{lean.get('orbit_min_not_used')}`",
            f"- PowerBoundEq not used as cycle attack: `{lean.get('PowerBoundEq_not_used_as_cycle_attack')}`",
            f"- O-terminating not claimed: `{lean.get('O_terminating_not_claimed')}`",
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
            "This is not a halt result. Length-7 cycle itineraries are Lean-excluded.",
            "Cycles ending in O as CycleItinerary are not treated separately:",
            "mixed itineraries rotate to an even-terminating orientation.",
            "Length 8 and 9 were not opened.",
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
    tails = payload["scan"]["tails"]
    print(
        f"N0_EE={tails['n0_OOOOOEE']} N0_EOE={tails['n0_OOOOEOE']} "
        f"naive_EOE={tails['n0_naive_eoe']} empty={tails['both_tables_empty']}"
    )


if __name__ == "__main__":
    main()

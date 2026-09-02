"""Length-9 three-even leftover argument.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a length-9 census and not induction on period or on n.

Even-terminating expanding length-9 words need at least six odds
(2^9 = 512 < 729 = 3^6), so at most three evens. The last two E's of
an even-terminating word are always separated by O^c. Last-internal
bootstrap still kills c >= 2. The new leftovers are the nine words
O^a E O^b E O^c E with a >= 2, c in {0, 1}, a+b+c = 6.

Those are not the two-even families O^{k-2}EE and O^{k-3}EOE. The
argument that replaces those families is Lemma 3.5 with the extra E
kept in the cell chain: LowerPowerBound on the leading odd run O^a
against a last-even / last-odd bound through the mixed tail
E O^b E O^c E. For a = 2 the remaining word after the first E is a
length-6 leftover, so first-E transport of Lemma 3.5 is available on
a cycle minimum; the prefix-cell comparison already excludes both
a = 2 words as CycleItinerary, so the transport is not required.
"""

from __future__ import annotations

import json
from itertools import product
from math import log2
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_length_seven import (
    THRESHOLD_BY_SUFFIX,
    expanding,
    orbit_until_fail,
    suffix_after_last_internal_e,
)
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
    LEFTOVER_CYCLES,
    MINIMAL,
    PROGRESS,
    SMALL_CYCLE_CENSUS,
    engine_floor_text,
    has_named,
    pre_finance_text,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_cycle_length_nine.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_cycle_length_nine.md"

CLASS_GREEN = "THREE_EVEN_PREFIX_CELL_GREEN"
CLASS_REMAINS = "THREE_EVEN_LEFTOVER_REMAINS"
CLASS_REPARAM = "THREE_EVEN_REPARAMETERIZATION"
CLASS_INCOMPLETE = "THREE_EVEN_INCOMPLETE"

EXPECTED_LEFTOVERS = (
    "OOOOOOEEE",
    "OOOOOEOEE",
    "OOOOOEEOE",
    "OOOOEOOEE",
    "OOOOEOEOE",
    "OOOEOOOEE",
    "OOOEOOEOE",
    "OOEOOOOEE",
    "OOEOOOEOE",
)
BOOTSTRAP_WORDS = (
    "OOOOEEOOE",
    "OOOEOEOOE",
    "OOOEEOOOE",
    "OOEOOEOOE",
    "OOEOEOOOE",
    "OOEEOOOOE",
)
TRANSPORT_WORDS = ("OOEOOOOEE", "OOEOOOEOE")
TRANSPORT_REMAINING = {
    "OOEOOOOEE": "OOOOEE",
    "OOEOOOEOE": "OOOEOE",
}
ODD_RUN_WORD = "OOOOOOOOE"

LEAN_THEOREMS = (
    "cycle_itinerary_formally_expanding",
    "no_cycle_odd_run_append_even",
    "oo_suffix_threshold",
    "ooo_suffix_threshold",
    "no_cycleMin_internal_even_threshold",
    "cycleMin_not_odd_even",
    "cycleMin_not_start_even",
    "cycle_last_even_interval",
    "cycle_trailing_evens_lt",
    "no_cycle_itinerary_length_le_six",
    "no_cycle_itinerary_oooeoe",
    "no_cycle_itinerary_ooooee",
    "no_cycle_itinerary_oooooee",
    "no_cycle_itinerary_ooooeoe",
    "no_cycle_itinerary_length_le_seven",
    "no_cycle_itinerary_ooooooeee",
)

N0_SEARCH_CAP = 500


def o_min(length: int) -> int:
    odd = 0
    while 3**odd <= 2**length:
        odd += 1
    return odd


def odd_log2_C(a: int) -> int:
    """log2(lowerDenom(O^a)). Recurrence e_{k+1} = 3 e_k + 2^{k+1}."""
    exponent = 0
    for k in range(a):
        exponent = 3 * exponent + 2 ** (k + 1)
    return exponent


def abc(word: str) -> tuple[int, int, int]:
    """Unique (a, b, c) with word = O^a E O^b E O^c E."""
    if not word.endswith("E") or word.count("E") != 3:
        raise ValueError(f"expected a three-even even-terminating word, got {word}")
    parts = word[:-1].split("E")
    if len(parts) != 3 or any(set(part) - {"O"} for part in parts):
        raise ValueError(f"not of the form O^a E O^b E O^c E: {word}")
    return len(parts[0]), len(parts[1]), len(parts[2])


def remaining_after_first_e(word: str) -> str:
    a, _b, _c = abc(word)
    return word[a + 1 :]


def suffix_after_last_internal_e_has_e(word: str) -> bool:
    suffix = suffix_after_last_internal_e(word)
    return suffix is not None and "E" in suffix


def length_nine_e_expanding() -> list[str]:
    found = []
    for prefix in product("OE", repeat=8):
        word = "".join(prefix) + "E"
        if expanding(word):
            found.append(word)
    return found


def named_filter(word: str) -> str:
    if word == ODD_RUN_WORD:
        return "no_cycle_odd_run_append_even"
    if word.count("E") == 2:
        suffix = suffix_after_last_internal_e(word)
        orientation = cyclemin_orientation(word)
        threshold = THRESHOLD_BY_SUFFIX.get(suffix or "")
        if word.startswith("E"):
            return "rotate_onto_two_even_leftover"
        if word.startswith("OE"):
            return "cycleMin_not_odd_even"
        if orientation["legal_cyclemin"] and threshold is not None:
            return f"bootstrap_{threshold[0]}"
        if suffix == "":
            return "two_even_leftover_EE"
        if suffix == "O":
            return "two_even_leftover_EOE"
        return "two_even_unclassified"
    if word.count("E") != 3:
        return "unclassified"
    a, _b, c = abc(word)
    suffix = suffix_after_last_internal_e(word)
    orientation = cyclemin_orientation(word)
    threshold = THRESHOLD_BY_SUFFIX.get(suffix or "")
    if a == 0:
        return "starts_E"
    if a == 1:
        return "cycleMin_not_odd_even"
    if c >= 2 and orientation["legal_cyclemin"] and threshold is not None:
        return f"bootstrap_{threshold[0]}"
    if c in (0, 1) and a >= 2:
        return "leftover_prefix_preimage_EE" if c == 0 else "leftover_prefix_preimage_EOE"
    return "unclassified"


def candidate_row(word: str) -> dict[str, Any]:
    orientation = cyclemin_orientation(word)
    suffix = suffix_after_last_internal_e(word)
    threshold = THRESHOLD_BY_SUFFIX.get(suffix or "")
    three = word.count("E") == 3
    parsed = abc(word) if three else None
    remaining = remaining_after_first_e(word) if three else None
    return {
        "word": word,
        "length": len(word),
        "odd_count": word.count("O"),
        "even_count": word.count("E"),
        "abc": parsed,
        "suffix_after_internal_e": suffix,
        "suffix_contains_E": suffix_after_last_internal_e_has_e(word),
        "existing_threshold": None if threshold is None else threshold[0],
        "legal_cyclemin": orientation["legal_cyclemin"],
        "blocked_by": orientation["blocked_by"],
        "remaining_after_first_e": remaining,
        "remaining_is_lemma35": remaining in TRANSPORT_REMAINING.values(),
        "named_filter": named_filter(word),
        "leftover": word in EXPECTED_LEFTOVERS,
        "bootstrap": word in BOOTSTRAP_WORDS,
        "rotation_class": "|".join(sorted(set(rotations(word)))),
    }


def ymax_from_odd_bound(c_bits: int, rhs: int, odd_exp: int) -> int:
    """Largest y with y^{odd_exp} <= 2^{c_bits} * rhs."""
    if rhs <= 0:
        return 1
    bound = (1 << c_bits) * rhs
    logy = (c_bits + log2(rhs)) / odd_exp
    ymax = max(1, int(2**logy) + 2)
    while ymax > 1 and ymax**odd_exp > bound:
        ymax -= 1
    while (ymax + 1) ** odd_exp <= bound:
        ymax += 1
    return ymax


def z_upper_cells_ee(n: int, b: int) -> int:
    """Upper bound on T_{O^a}(n) for a CycleItinerary tail E O^b EE.

    Last two evens give p < (n+1)^4. The tail always starts with E,
    so z --E--> y --O^b--> p. If b = 0 the tail is EEE and
    z < (p+1)^2 < (n+1)^8, not z = p. If b >= 1 then
    y^{3^b} <= C_{O^b} p^{2^b} and z < (y+1)^2.
    """
    cap = (n + 1) ** 4
    if b == 0:
        return (n + 1) ** 8 - 1
    ymax = ymax_from_odd_bound(odd_log2_C(b), cap ** (1 << b), 3**b)
    return (ymax + 1) ** 2 - 1


def z_upper_cells_eoe(n: int, b: int) -> int:
    """Upper bound on T_{O^a}(n) for a CycleItinerary tail E O^b EOE.

    Last-odd cell y^3 < (n+1)^4, then one even back to s < (y+1)^2.
    If b = 0 the tail is EEOE and z < (s+1)^2. If b >= 1 then
    u^{3^b} <= C_{O^b} s^{2^b} and z < (u+1)^2.
    """
    y_last = icbrt((n + 1) ** 4 - 1)
    s_max = (y_last + 1) ** 2 - 1
    if b == 0:
        return (s_max + 1) ** 2 - 1
    umax = ymax_from_odd_bound(odd_log2_C(b), s_max ** (1 << b), 3**b)
    return (umax + 1) ** 2 - 1


def z_upper(n: int, b: int, c: int) -> int:
    if c == 0:
        return z_upper_cells_ee(n, b)
    if c == 1:
        return z_upper_cells_eoe(n, b)
    raise ValueError("prefix-cell leftover tails have c in {0, 1}")


def tail_fires(n: int, a: int, b: int, c: int) -> bool:
    z_u = z_upper(n, b, c)
    return n ** (3**a) > (1 << odd_log2_C(a)) * z_u ** (1 << a)


def first_tail_cutoff(a: int, b: int, c: int) -> int | None:
    for n in range(2, N0_SEARCH_CAP + 1):
        if tail_fires(n, a, b, c):
            return n
    return None


def cycle_itinerary_hits(word: str, n_lo: int, n_hi: int) -> dict[str, Any]:
    follows = 0
    hits: list[int] = []
    follow_starts: list[int] = []
    for n in range(n_lo, n_hi):
        if not follows_itinerary(n, word):
            continue
        follows += 1
        follow_starts.append(n)
        if image_after(n, word) == n:
            hits.append(n)
    return {
        "word": word,
        "n_lo": n_lo,
        "n_hi": n_hi,
        "checked": n_hi - n_lo,
        "follows": follows,
        "follow_starts": follow_starts,
        "hits": hits,
        "hit_count": len(hits),
    }


def leftover_tails() -> dict[str, Any]:
    rows = []
    for word in EXPECTED_LEFTOVERS:
        a, b, c = abc(word)
        n0 = first_tail_cutoff(a, b, c)
        remaining = remaining_after_first_e(word)
        table = None if n0 is None else cycle_itinerary_hits(word, 2, n0)
        rows.append(
            {
                "word": word,
                "abc": [a, b, c],
                "prefix_C_bits": odd_log2_C(a),
                "full_C_bits": lower_denom(word).bit_length() - 1,
                "remaining": remaining,
                "remaining_expanding": expanding(remaining),
                "remaining_is_lemma35": remaining in TRANSPORT_REMAINING.values(),
                "n0": n0,
                "fires_at_n0": None if n0 is None else tail_fires(n0, a, b, c),
                "fails_before_n0": None
                if n0 is None
                else not tail_fires(n0 - 1, a, b, c),
                "table": table,
            }
        )
    return {
        "rows": rows,
        "all_tails_fire": all(row["n0"] is not None for row in rows),
        "all_tables_empty": all(
            row["table"] is not None and row["table"]["hit_count"] == 0 for row in rows
        ),
        "max_n0": max((row["n0"] or 0) for row in rows),
        "follows_witness": next(
            (
                {
                    "word": row["word"],
                    "n": row["table"]["follow_starts"][0],
                    "image": image_after(
                        row["table"]["follow_starts"][0], row["word"]
                    ),
                }
                for row in rows
                if row["table"] and row["table"]["follow_starts"]
            ),
            None,
        ),
    }


def bootstrap_small_n() -> dict[str, Any]:
    out: dict[str, Any] = {}
    for word in BOOTSTRAP_WORDS:
        word_row = {}
        for n in (3, 5):
            steps = orbit_until_fail(n, word)
            fail = next((row for row in steps if not row["parity_ok"]), None)
            word_row[f"n{n}"] = {
                "realizes": follows_itinerary(n, word),
                "fail_index": None if fail is None else fail["index"],
                "fail_state": None if fail is None else fail["state"],
            }
        out[word] = word_row
    return out


def even_type_rows() -> list[dict[str, Any]]:
    rows = []
    for length in (6, 7, 8, 9, 10, 11, 12):
        need = o_min(length)
        rows.append(
            {
                "length": length,
                "o_min": need,
                "max_evens_if_expanding": length - need,
                "three_even_possible": length - need >= 3,
                "four_even_possible": length - need >= 4,
            }
        )
    return rows


def lean_api_present() -> dict[str, bool]:
    text = CYCLES.read_text(encoding="utf-8")
    corpus = pre_finance_text()
    leftover = LEFTOVER_CYCLES.read_text(encoding="utf-8")
    census = SMALL_CYCLE_CENSUS.read_text(encoding="utf-8")
    combined = (
        text
        + corpus
        + leftover
        + census
        + CELLS.read_text(encoding="utf-8")
        + PROGRESS.read_text(encoding="utf-8")
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
        "length_eight_open_in_census": "Length eight is open" in census,
        "no_length_nine_theorem": "theorem no_cycle_itinerary_length_nine"
        not in combined,
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text()
        and "CycleMin" not in engine_floor_text(),
        "orbit_min_not_used": "MinimalNonTerm" not in text,
        "PowerBoundEq_not_used_as_cycle_attack": "PowerBoundEq" not in text,
        "Minimal_untouched": "length_nine" not in MINIMAL.read_text(encoding="utf-8"),
    }


def run_probe() -> dict[str, Any]:
    words = length_nine_e_expanding()
    rows = [candidate_row(w) for w in words]
    three = [row for row in rows if row["even_count"] == 3]
    two = [row for row in rows if row["even_count"] == 2]
    leftovers = [row["word"] for row in three if row["leftover"]]
    bootstrap = [row["word"] for row in three if row["bootstrap"]]
    unclassified = [row["word"] for row in rows if row["named_filter"] == "unclassified"]
    suffix_e = [row["word"] for row in three if row["suffix_contains_E"]]
    tails = leftover_tails()
    return {
        "basin": [1],
        "expanding_e_words": words,
        "expanding_count": len(words),
        "three_even_count": len(three),
        "two_even_count": len(two),
        "candidates": rows,
        "leftover_itineraries": leftovers,
        "leftovers_are_predicted": set(leftovers) == set(EXPECTED_LEFTOVERS),
        "bootstrap_words": bootstrap,
        "bootstrap_are_predicted": set(bootstrap) == set(BOOTSTRAP_WORDS),
        "odd_run_words": [row["word"] for row in rows if row["word"] == ODD_RUN_WORD],
        "unclassified": unclassified,
        "last_internal_suffix_never_contains_E": suffix_e == [],
        "bootstrap_small_n": bootstrap_small_n(),
        "tails": tails,
        "even_type": even_type_rows(),
        "n_search": False,
        "length_ten": False,
        "four_even": False,
        "o_terminating_programme": False,
        "cycle_state_search": False,
        "induction_on_period": False,
        "induction_on_n": False,
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["cycle_itinerary_formally_expanding"]
        and lean["no_cycleMin_internal_even_threshold"]
        and lean["no_cycle_itinerary_length_le_six"]
        and lean["no_length_nine_theorem"]
        and lean["length_eight_open_in_census"]
        and lean["no_cycle_itinerary_length_le_seven"]
        and lean["cycle_trailing_evens_lt"]
        and lean["no_cycle_itinerary_ooooooeee"]
        and lean["no_cycle_engine"]
        and lean["no_all_cycles_impossible"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if (
        scan["n_search"]
        or scan["length_ten"]
        or scan["four_even"]
        or scan["o_terminating_programme"]
        or scan["cycle_state_search"]
        or scan["induction_on_period"]
        or scan["induction_on_n"]
    ):
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope search"}
    if (
        scan["expanding_count"] != 37
        or scan["three_even_count"] != 28
        or scan["two_even_count"] != 8
        or scan["unclassified"]
        or not scan["last_internal_suffix_never_contains_E"]
    ):
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": (
                f"unexpected family count={scan['expanding_count']} "
                f"three={scan['three_even_count']} "
                f"unclassified={scan['unclassified']} "
                f"suffix_E={not scan['last_internal_suffix_never_contains_E']}"
            ),
        }
    if not scan["leftovers_are_predicted"] or not scan["bootstrap_are_predicted"]:
        return {
            "classification": CLASS_REPARAM,
            "reason": "inventory is not the predicted nine leftovers plus bootstrap six",
        }
    tails = scan["tails"]
    if not tails["all_tails_fire"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": f"a leftover tail never fires: {[row['word'] for row in tails['rows'] if row['n0'] is None]}",
        }
    if not tails["all_tables_empty"]:
        hits = {
            row["word"]: row["table"]["hits"]
            for row in tails["rows"]
            if row["table"] and row["table"]["hit_count"]
        }
        return {"classification": CLASS_REMAINS, "reason": f"finite table hit: {hits}"}
    return {
        "classification": CLASS_GREEN,
        "secondary": [
            "FIRST_E_TRANSPORT_FOR_A2",
            "LAST_INTERNAL_SUFFIX_ALWAYS_O_RUN",
        ],
        "reason": (
            "length 9 has 28 three-even even-terminating expanding itineraries; "
            "last-internal suffix is always O^c so bootstrap still kills c>=2; "
            "the nine leftovers O^a E O^b E O^c E with a>=2 and c in {0,1} "
            "die by the odd-prefix cell tail (N0<=374) with empty CycleItinerary "
            "tables; a=2 remainders are the Lemma 3.5 words OOOOEE / OOOEOE"
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
            "length_nine_cycles_impossible": False,
            "length_nine_lean_census": False,
            "four_even_opened": False,
            "induction_on_period": False,
            "induction_on_n": False,
            "no_escape_orbits": False,
        }
    )
    return {
        "experiment": "juggler_cycle_length_nine",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "structural inventory of even-terminating expanding length-9 "
            "words; last-internal vs first-E split; odd-prefix cell tails "
            "on the nine three-even leftovers; exact follows+image table "
            "below N0 only; Lean excludes OOOOOOEEE only; no length-9 "
            "census; no cycle-state search; no length-10"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    tails = scan["tails"]
    lines = [
        "# Juggler length-9 three-even leftovers",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. Three-even leftovers only; not a",
        "length-9 Lean census and not induction on period or on n.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     What argument excludes the length-9",
        "                        three-even leftover CycleItineraries?",
        "Novelty hypothesis      Last-internal suffix is always O^c;",
        "                        leftovers are nine words O^a E O^b E O^c E;",
        "                        odd-prefix + mixed-tail cells replace the",
        "                        two-even families",
        "Falsifier               A leftover whose prefix-cell tail never",
        "                        fires, or a CycleItinerary realization below N0",
        "Existing machinery      expansion, CycleMin, last-internal",
        "                        bootstrap, Lemma 3.5 cells, lowerDenom",
        "Maximum Phase-0 scope   inventory + prefix-cell N0 + finite table;",
        "                        no Lean, no length 10, no halt",
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
        "## Counts",
        "",
        f"- expanding even-terminating length-9 words: `{scan['expanding_count']}`",
        f"- odd-run: `{scan['odd_run_words']}`",
        f"- two-even: `{scan['two_even_count']}` (same type as lengths 6-8; not opened)",
        f"- three-even: `{scan['three_even_count']}`",
        f"- leftovers: `{scan['leftover_itineraries']}`",
        f"- bootstrap: `{scan['bootstrap_words']}`",
        f"- unclassified: `{scan['unclassified']}`",
        f"- last-internal suffix contains E: `{not scan['last_internal_suffix_never_contains_E']}`",
        "",
        "## Three-even leftovers",
        "",
    ]
    for row in tails["rows"]:
        table = row["table"]
        follows = None if table is None else table["follows"]
        hits = None if table is None else table["hits"]
        lines.append(
            f"- `{row['word']}` abc=`{row['abc']}` "
            f"Cbits=`{row['prefix_C_bits']}` "
            f"v=`{row['remaining']}` "
            f"v_exp=`{row['remaining_expanding']}` "
            f"lemma35=`{row['remaining_is_lemma35']}` "
            f"N0=`{row['n0']}` follows=`{follows}` hits=`{hits}`"
        )
    witness = tails.get("follows_witness")
    lines.extend(
        [
            "",
            f"- all tails fire: `{tails['all_tails_fire']}`",
            f"- all tables empty: `{tails['all_tables_empty']}`",
            f"- max N0: `{tails['max_n0']}`",
            f"- follows witness (not a return): `{witness}`",
            "",
            "## Even-type observation (length 10/12 not opened)",
            "",
        ]
    )
    for row in scan["even_type"]:
        lines.append(
            f"- length `{row['length']}` o_min=`{row['o_min']}` "
            f"max_E=`{row['max_evens_if_expanding']}` "
            f"three_even=`{row['three_even_possible']}` "
            f"four_even=`{row['four_even_possible']}`"
        )
    lines.extend(
        [
            "",
            f"- length 10 / four-even / n-search: `{scan['length_ten']}` / `{scan['four_even']}` / `{scan['n_search']}`",
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
            f"- no length-nine theorem: `{lean.get('no_length_nine_theorem')}`",
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
            "This is not a halt result and not a length-9 census.",
            "Two-even length-9 leftovers were not opened. Length 10 and",
            "four-even words were not opened. Lean excludes `OOOOOOEEE`",
            "only (`cycle_trailing_evens_lt`, `no_cycle_itinerary_ooooooeee`).",
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
    print(f"max_N0={tails['max_n0']} empty={tails['all_tables_empty']}")
    for row in tails["rows"]:
        print(f"  {row['word']} N0={row['n0']}")


if __name__ == "__main__":
    main()

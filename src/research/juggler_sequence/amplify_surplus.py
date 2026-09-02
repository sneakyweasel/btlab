"""Amplify versus formal surplus on the thirty length-11 leftovers.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a length-11 census, not a leftover cell, and not the O^7 EEEE
+1-chain. The question is whether first-defect Amplify beats
G = n^{3^7} - n^{2^{11}} below the leftover-cell cutoff.

The linear term after a first-letter insertion has exponent 2184
against surplus 2187. Even letters do not change that product, so
every short-gap shape has the same n^3 gap.
"""

from __future__ import annotations

import json
from math import log
from pathlib import Path
from typing import Any

from research.juggler_sequence.defect_lower_bound import first_defect_payload
from research.juggler_sequence.e4_tight_pullback import EEEE_WORD
from research.juggler_sequence.first_e_e4 import (
    FORBIDDEN_THEOREMS as E4_FORBIDDEN,
    first_expanding_a0,
    remainder_shapes,
    word_e4,
)
from research.juggler_sequence.global_defect import follows_itinerary
from research.juggler_sequence.lean_paths import (
    DEFECT_LOWER_BOUND,
    SMALL_CYCLE_CENSUS,
    has_named,
    pre_finance_text,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_amplify_surplus.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_amplify_surplus.md"

CLASS_REFUTED = "AMPLIFY_SURPLUS_REFUTED"
CLASS_REMAINS = "AMPLIFY_SURPLUS_REMAINS"
CLASS_INCOMPLETE = "AMPLIFY_SURPLUS_INCOMPLETE"

ODD_COUNT = 7
WORD_LEN = 11
SURPLUS_EXP = 3**ODD_COUNT
LINEAR_EXP = 2184
GAP_EXP = SURPLUS_EXP - LINEAR_EXP
SEVEN_ODD = 256
REALIZED_N_MAX = 400
CHECK_NS = (12, 256, 289, 10**8, 828_484_394)

LEAN_THEOREMS = (
    "amplifyDefect",
    "firstDefect",
    "odd_defect_lift_lower_bound",
    "power_bound_compensated_contracts",
)

FORBIDDEN_THEOREMS = tuple(
    name
    for name in E4_FORBIDDEN
    + (
        "no_cycle_itinerary_length_eleven",
        "no_cycle_itinerary_amplify_surplus",
        "no_cycle_itinerary_four_even_amplify",
    )
    if name != "no_cycle_itinerary_oooooooeeee"
)


def length11_words() -> list[dict[str, Any]]:
    rows = []
    for shape in remainder_shapes():
        a0 = first_expanding_a0(int(shape["a1"]), int(shape["a2"]), int(shape["a3"]))
        assert a0 is not None
        word = word_e4(a0, int(shape["a1"]), int(shape["a2"]), int(shape["a3"]))
        rows.append(
            {
                "family": shape["family"],
                "a0": a0,
                "a1": int(shape["a1"]),
                "a2": int(shape["a2"]),
                "a3": int(shape["a3"]),
                "word": word,
            }
        )
    return rows


def linear_amplify_exponent(word: str, first_j: int = 0, rho_exp: float = 0.0) -> float:
    """Tight-scale exponent of n in the linear Amplify term.

    After the first positive remainder is inserted, each later odd
    letter multiplies D by 3 x^{2^{k+1}}. Even letters halve x and
    increment k, so the product 2^{k+1} x_exp is invariant.
    """
    x_exp = 1.0
    k = 0
    d_exp = 0.0
    inserted = False
    for i, letter in enumerate(word):
        if i < first_j:
            x_exp *= 1.5 if letter == "O" else 0.5
            k += 1
            continue
        if i == first_j:
            d_exp = rho_exp
            x_exp *= 1.5 if letter == "O" else 0.5
            k += 1
            inserted = True
            continue
        if letter == "O":
            d_exp = d_exp + (2 ** (k + 1)) * x_exp
            x_exp *= 1.5
        else:
            x_exp *= 0.5
        k += 1
    if not inserted:
        return 0.0
    return d_exp


def log_surplus(n: int) -> float:
    if n < 2:
        return float("-inf")
    # G = n^{2048}(n^{139}-1); avoid materialising n^{139}.
    return 2187.0 * log(n) + log(1.0 - n ** (-139))


def logsumexp(values: list[float]) -> float:
    top = max(values)
    if top == float("-inf"):
        return top
    total = 0.0
    for value in values:
        gap = value - top
        if gap < -40.0:
            continue
        total += 2.718281828459045**gap
    return top + log(total) if total > 0.0 else top


def log_amplify_linear_then_cubic(
    n: int, word: str, *, rho: float, first_j: int = 0
) -> float:
    """Log Amplify with tight scales and the full cubic lift."""
    if n < 2:
        return float("-inf")
    log_x = log(n)
    log_d = log(rho) if rho > 0 else float("-inf")
    k = 0
    for i, letter in enumerate(word):
        if i < first_j:
            log_x *= 1.5 if letter == "O" else 0.5
            k += 1
            continue
        if i == first_j:
            log_x *= 1.5 if letter == "O" else 0.5
            k += 1
            continue
        if letter == "O":
            t1 = log(3.0) + (2 ** (k + 1)) * log_x + log_d
            t2 = log(3.0) + (2**k) * log_x + 2.0 * log_d
            t3 = 3.0 * log_d
            log_d = logsumexp([t1, t2, t3])
            log_x *= 1.5
        else:
            log_x *= 0.5
        k += 1
    return log_d


def beats_surplus(n: int, word: str, *, rho: float) -> bool:
    return log_amplify_linear_then_cubic(n, word, rho=rho) > log_surplus(n)


def realized_log_amplify(n: int, word: str) -> float | None:
    if not follows_itinerary(n, word):
        return None
    j, current, rho, d_after, suffix = first_defect_payload(n, word)
    if j == len(word) or rho <= 0 or d_after <= 0:
        return 0.0
    log_d = log(d_after)
    x = floor_power(current)
    k = j + 1
    for letter in suffix:
        if letter == "O":
            t1 = log(3.0) + (2 ** (k + 1)) * log(x) + log_d
            t2 = log(3.0) + (2**k) * log(x) + 2.0 * log_d
            t3 = 3.0 * log_d
            log_d = logsumexp([t1, t2, t3])
        x = floor_power(x)
        k += 1
    return log_d


def word_row(shape: dict[str, Any]) -> dict[str, Any]:
    word = str(shape["word"])
    rho1 = linear_amplify_exponent(word, 0, 0.0)
    rho_max = linear_amplify_exponent(word, 0, 1.5)
    late = [linear_amplify_exponent(word, j, 0.0) for j in range(len(word)) if word[j] == "O"]
    return {
        **shape,
        "linear_exp_rho1": rho1,
        "linear_exp_rhomax": rho_max,
        "max_late_rho1": max(late) if late else 0.0,
        "gap_rho1": SURPLUS_EXP - rho1,
        "gap_rhomax": SURPLUS_EXP - rho_max,
        "rho1_beats_at_12": beats_surplus(12, word, rho=1.0),
        "rhomax_beats_at_12": beats_surplus(12, word, rho=2.0 * (12**1.5)),
        "rhomax_beats_at_256": beats_surplus(
            SEVEN_ODD, word, rho=2.0 * (SEVEN_ODD**1.5)
        ),
        "rho1_beats_at_n0": beats_surplus(828_484_394, word, rho=1.0),
    }


def realized_rows(words: list[str], n_max: int = REALIZED_N_MAX) -> list[dict[str, Any]]:
    rows = []
    for n in range(2, n_max + 1):
        for word in words:
            amp = realized_log_amplify(n, word)
            if amp is None:
                continue
            gap = amp - log_surplus(n)
            rows.append(
                {
                    "n": n,
                    "word": word,
                    "log_amp_minus_log_G": gap,
                    "amplify_beats_G": gap > 0.0,
                }
            )
    return rows


def run_probe() -> dict[str, Any]:
    shapes = length11_words()
    rows = [word_row(shape) for shape in shapes]
    sample_words = [EEEE_WORD]
    mixed = next((row["word"] for row in rows if row["word"] != EEEE_WORD), EEEE_WORD)
    if mixed not in sample_words:
        sample_words.append(mixed)
    realized = realized_rows(sample_words)
    check = {
        str(n): {
            "logF_rho1_minus_logG": log_amplify_linear_then_cubic(
                n, EEEE_WORD, rho=1.0
            )
            - log_surplus(n),
            "beats": beats_surplus(n, EEEE_WORD, rho=1.0),
        }
        for n in CHECK_NS
    }
    return {
        "basin": [1],
        "shape_count": len(rows),
        "rows": rows,
        "surplus_exp": SURPLUS_EXP,
        "linear_exp": LINEAR_EXP,
        "gap_exp": GAP_EXP,
        "all_length_eleven": all(len(row["word"]) == 11 for row in rows),
        "all_seven_odds": all(row["word"].count("O") == 7 for row in rows),
        "all_linear_exp_2184": all(abs(row["linear_exp_rho1"] - LINEAR_EXP) < 1e-9 for row in rows),
        "all_rhomax_2185_5": all(
            abs(row["linear_exp_rhomax"] - (LINEAR_EXP + 1.5)) < 1e-9 for row in rows
        ),
        "all_late_le_2184": all(row["max_late_rho1"] <= LINEAR_EXP + 1e-9 for row in rows),
        "none_rho1_beats_at_12": all(row["rho1_beats_at_12"] is False for row in rows),
        "all_rhomax_beats_at_12": all(row["rhomax_beats_at_12"] is True for row in rows),
        "none_rhomax_beats_at_256": all(
            row["rhomax_beats_at_256"] is False for row in rows
        ),
        "none_rho1_beats_at_n0": all(row["rho1_beats_at_n0"] is False for row in rows),
        "eeee_in_list": any(row["word"] == EEEE_WORD for row in rows),
        "check_ns": check,
        "realized_count": len(realized),
        "realized_any_beats": any(row["amplify_beats_G"] for row in realized),
        "realized_min_gap": min((row["log_amp_minus_log_G"] for row in realized), default=None),
        "length_eight_census": False,
        "length_nine_census": False,
        "length_eleven_census": False,
        "four_even_lean": False,
        "induction_on_period": False,
        "induction_on_n": False,
    }


def lean_api_present() -> dict[str, bool]:
    combined = pre_finance_text()
    named = {name: has_named(combined, name) for name in LEAN_THEOREMS}
    forbidden = {
        name: f"theorem {name}" not in combined for name in FORBIDDEN_THEOREMS
    }
    census = SMALL_CYCLE_CENSUS.read_text(encoding="utf-8")
    defect = DEFECT_LOWER_BOUND.read_text(encoding="utf-8")
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        **forbidden,
        "amplify_does_not_claim_surplus": "exceeds the formal surplus" in defect,
        "length_eight_open_in_census": "Length eight is open" in census
        or "length 8" in census.lower()
        or "no_cycle_itinerary_length_le_seven" in census,
        "no_all_cycles_impossible": "theorem no_juggler_cycle" not in combined,
        "no_amplify_surplus_theorem": "theorem no_cycle_itinerary_amplify_surplus"
        not in combined,
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["amplifyDefect"]
        and lean["firstDefect"]
        and lean["power_bound_compensated_contracts"]
        and lean["no_cycle_itinerary_length_eleven"]
        and lean["no_cycle_itinerary_amplify_surplus"]
        and lean["no_all_cycles_impossible"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if (
        scan["length_eight_census"]
        or scan["length_nine_census"]
        or scan["length_eleven_census"]
        or scan["four_even_lean"]
        or scan["induction_on_period"]
        or scan["induction_on_n"]
    ):
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope search"}
    if (
        not scan["all_length_eleven"]
        or not scan["all_seven_odds"]
        or not scan["eeee_in_list"]
        or scan["shape_count"] != 30
    ):
        return {"classification": CLASS_INCOMPLETE, "reason": "length-11 list failed"}
    if (
        not scan["all_linear_exp_2184"]
        or not scan["all_rhomax_2185_5"]
        or not scan["all_late_le_2184"]
        or not scan["none_rho1_beats_at_12"]
        or not scan["all_rhomax_beats_at_12"]
        or not scan["none_rhomax_beats_at_256"]
        or not scan["none_rho1_beats_at_n0"]
        or scan["realized_any_beats"]
    ):
        return {
            "classification": CLASS_REMAINS,
            "reason": "an Amplify bound beat G past the seven-odd cutoff, or the n^3 gap failed",
        }
    return {
        "classification": CLASS_REFUTED,
        "reason": (
            "first-defect Amplify has exponent 2184 (rho=1) or 2185.5 "
            "(max rho) against surplus n^{2187}; the n^3 gap is invariant "
            "under even letters. Optimistic max-rho Amplify already loses "
            "at the seven-odd cutoff 256, which is where these itineraries can "
            "first be followed; leftover N0 is later still"
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
            "four_even_cycles_impossible": False,
            "length_eight_census": False,
            "length_nine_census": False,
            "length_eleven_census": False,
            "four_even_lean": False,
            "amplify_beats_surplus": False,
            "induction_on_period": False,
            "induction_on_n": False,
        }
    )
    return {
        "experiment": "juggler_amplify_surplus",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "tight-scale Amplify exponent versus 3^7; cubic-lift log "
            "comparison at n=12 and leftover N0; realized followers "
            f"n<={REALIZED_N_MAX} on two sample words"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler Amplify versus surplus on the thirty length-11 leftovers",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. First-defect Amplify versus the",
        "formal surplus on the thirty short-gap words only. Not a",
        "length-11 census and not the O^7 EEEE +1-chain.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Does Amplify beat G=n^{2187}-n^{2048}",
        "                        on the 30 length-11 leftovers below",
        "                        the leftover-cell cutoff?",
        "Novelty hypothesis      First-defect cubic lift eats the",
        "                        n^{139} surplus earlier than Z=(n+1)^{16}",
        "Falsifier               Best uniform F is n^{2184} rho against",
        "                        G~n^{2187}, or F>G is T_w<n rewritten",
        "Existing machinery      amplifyDefect; formal surplus;",
        "                        30-word list; compensated contraction",
        "Maximum Phase-0 scope   Exponent census plus log F vs log G;",
        "                        no Lean, no length-11 assembler",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- surplus exponent: `{scan['surplus_exp']}`",
        f"- linear Amplify exponent: `{scan['linear_exp']}`",
        f"- gap: `n^{scan['gap_exp']}`",
        f"- all 30 share exponent 2184: `{scan['all_linear_exp_2184']}`",
        f"- realized followers that beat G: `{scan['realized_any_beats']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Lean",
        "",
    ]
    for name in LEAN_THEOREMS:
        lines.append(f"- `{name}`: `{lean.get(name)}`")
    lines.extend(
        [
            f"- no Amplify-surplus theorem: `{lean.get('no_amplify_surplus_theorem')}`",
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
            "This is not a halt result and not a length-11 census.",
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
    print(
        f"linear_exp={scan['linear_exp']} surplus={scan['surplus_exp']} "
        f"realized_beats={scan['realized_any_beats']}"
    )


if __name__ == "__main__":
    main()

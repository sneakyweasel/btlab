"""First-E transport of the uniform two-even tail.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a length-8 or length-9 census, not a bunched-tail programme, and
not induction on period or on n.

On a CycleMin the word is O^{a0} E O^{a1} ... E O^{a_{e-1}} E.
Bootstrap already kills the last gap a_{e-1} >= 2. If the second gap
a1 is long enough that the remainder after the first E is a two-even
leftover family, that remainder starts at y >= n. The leftover cell
is measured against the cycle start n, so y >= n tightens it against
the shared tail at y.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_itinerary import follows_itinerary, image_after
from research.juggler_sequence.lean_paths import (
    CYCLES,
    FIRST_E_TRANSPORT,
    FIRST_E_TRANSPORT_EVAL,
    LEFTOVER_TWO_EVEN,
    MINIMAL,
    SMALL_CYCLE_CENSUS,
    engine_floor_text,
    has_named,
    pre_finance_text,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM
from research.juggler_sequence.uniform_two_even import (
    denom_bits,
    shared_tail_holds,
    word_ee as two_even_ee,
    word_eoe as two_even_eoe,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_first_e_transport.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_first_e_transport.md"

CLASS_GREEN = "FIRST_E_TRANSPORT_GREEN"
CLASS_REMAINS = "FIRST_E_TRANSPORT_REMAINS"
CLASS_INCOMPLETE = "FIRST_E_TRANSPORT_INCOMPLETE"

K_MIN = 9
K_FINITE_MAX = 16
K_MAX = 24
N_CUTOFF = 256
A_MIN = 2
B_EE_MIN = 4
B_EOE_MIN = 3
SEVEN = 7

LEAN_THEOREMS = (
    "CycleMin",
    "cycleMin_ge",
    "cycle_trailing_evens_lt",
    "shared_two_even_tail",
    "no_cycle_itinerary_two_even_ee",
    "no_cycle_itinerary_two_even_eoe",
    "no_cycleMin_internal_even_threshold",
    "no_cycle_itinerary_length_le_seven",
    "no_cycleMin_gapped_three_even_ee",
    "no_cycleMin_gapped_three_even_eoe",
)


def word_gapped_ee(a: int, b: int) -> str:
    return "O" * a + "E" + "O" * b + "EE"


def word_gapped_eoe(a: int, b: int) -> str:
    return "O" * a + "E" + "O" * b + "EOE"


def remaining_ee(b: int) -> str:
    return two_even_ee(b + 2)


def remaining_eoe(b: int) -> str:
    return two_even_eoe(b + 3)


def is_gapped_ee(a: int, b: int) -> bool:
    return a >= A_MIN and b >= B_EE_MIN


def is_gapped_eoe(a: int, b: int) -> bool:
    return a >= A_MIN and b >= B_EOE_MIN


def ee_pairs(k: int) -> list[tuple[int, int]]:
    """Leftover EE shapes O^a E O^b EE of length k (c = 0)."""
    if k < K_MIN:
        return []
    pairs = []
    for a in range(A_MIN, k - 2):
        b = k - 3 - a
        if b >= 0:
            pairs.append((a, b))
    return pairs


def eoe_pairs(k: int) -> list[tuple[int, int]]:
    """Leftover EOE shapes O^a E O^b EOE of length k (c = 1)."""
    if k < K_MIN:
        return []
    pairs = []
    for a in range(A_MIN, k - 3):
        b = k - 4 - a
        if b >= 0:
            pairs.append((a, b))
    return pairs


def gapped_ee_pairs(k: int) -> list[tuple[int, int]]:
    return [(a, b) for a, b in ee_pairs(k) if is_gapped_ee(a, b)]


def gapped_eoe_pairs(k: int) -> list[tuple[int, int]]:
    return [(a, b) for a, b in eoe_pairs(k) if is_gapped_eoe(a, b)]


def bunched_ee_pairs(k: int) -> list[tuple[int, int]]:
    return [(a, b) for a, b in ee_pairs(k) if not is_gapped_ee(a, b)]


def bunched_eoe_pairs(k: int) -> list[tuple[int, int]]:
    return [(a, b) for a, b in eoe_pairs(k) if not is_gapped_eoe(a, b)]


def seven_odd_covers_small_n(k: int) -> bool:
    """For leftover length k, a <= 6 and b <= 6 is impossible."""
    return k >= 17


def small_n_route(n: int, a: int, b: int) -> str:
    if n < 2:
        return "n_lt_two"
    if a >= SEVEN:
        return "seven_odds_prefix"
    prefix = "O" * a + "E"
    if not follows_itinerary(n, prefix):
        return "prefix_unrealized"
    y = image_after(n, prefix)
    if y >= N_CUTOFF:
        return "tail_at_y"
    if b >= SEVEN:
        return "seven_odds_remaining"
    return "finite_short"


def transport_contradiction(n: int, y: int, leftover_k: int) -> bool:
    """y >= n and the shared tail at y beat the cell measured at n."""
    if y < n or n < 2:
        return False
    if not shared_tail_holds(y, leftover_k):
        return False
    a = leftover_k - 2
    cell = (1 << denom_bits(a)) * (n + 1) ** (1 << leftover_k)
    tail = (1 << denom_bits(a)) * (y + 1) ** (1 << leftover_k)
    return y ** (3**a) > tail >= cell


def cycle_itinerary_hits(word: str, n_lo: int, n_hi: int) -> dict[str, Any]:
    hits: list[int] = []
    follows = 0
    for n in range(n_lo, n_hi):
        if not follows_itinerary(n, word):
            continue
        follows += 1
        if image_after(n, word) == n:
            hits.append(n)
    return {
        "word": word,
        "follows": follows,
        "hits": hits,
        "hit_count": len(hits),
    }


def finite_window_rows() -> list[dict[str, Any]]:
    rows = []
    for k in range(K_MIN, K_FINITE_MAX + 1):
        for kind, pairs, remaining_fn, word_fn, leftover_k_fn in (
            ("ee", gapped_ee_pairs(k), remaining_ee, word_gapped_ee, lambda b: b + 2),
            ("eoe", gapped_eoe_pairs(k), remaining_eoe, word_gapped_eoe, lambda b: b + 3),
        ):
            for a, b in pairs:
                word = word_fn(a, b)
                leftover_k = leftover_k_fn(b)
                table = cycle_itinerary_hits(word, 2, N_CUTOFF)
                rows.append(
                    {
                        "k": k,
                        "kind": kind,
                        "a": a,
                        "b": b,
                        "word": word,
                        "remaining": remaining_fn(b),
                        "leftover_k": leftover_k,
                        "table": table,
                    }
                )
    return rows


def large_k_small_n_sealed() -> bool:
    for k in range(K_FINITE_MAX + 1, K_MAX + 1):
        if not seven_odd_covers_small_n(k):
            return False
        for a, b in gapped_ee_pairs(k) + gapped_eoe_pairs(k):
            if a < SEVEN and b < SEVEN:
                return False
    return True


def bunched_inventory() -> dict[str, Any]:
    rows = []
    for k in range(K_MIN, K_MAX + 1):
        ee = bunched_ee_pairs(k)
        eoe = bunched_eoe_pairs(k)
        rows.append(
            {
                "k": k,
                "bunched_ee": [word_gapped_ee(a, b) for a, b in ee],
                "bunched_eoe": [word_gapped_eoe(a, b) for a, b in eoe],
                "bunched_count": len(ee) + len(eoe),
                "gapped_count": len(gapped_ee_pairs(k)) + len(gapped_eoe_pairs(k)),
            }
        )
    return {
        "rows": rows,
        "shapes_independent_of_k": True,
        "ee_b_max_bunched": B_EE_MIN - 1,
        "eoe_b_max_bunched": B_EOE_MIN - 1,
    }


def chain_samples() -> list[dict[str, Any]]:
    samples = []
    for n, y, leftover_k in (
        (256, 256, 6),
        (256, 300, 6),
        (256, 256, 8),
        (205, 256, 6),
        (14, 256, 7),
        (100, 80, 6),
    ):
        samples.append(
            {
                "n": n,
                "y": y,
                "leftover_k": leftover_k,
                "tail_at_y": shared_tail_holds(y, leftover_k),
                "contradiction": transport_contradiction(n, y, leftover_k),
                "y_ge_n": y >= n,
            }
        )
    return samples


def run_probe() -> dict[str, Any]:
    finite = finite_window_rows()
    samples = chain_samples()
    bunched = bunched_inventory()
    return {
        "basin": [1],
        "k_min": K_MIN,
        "k_finite_max": K_FINITE_MAX,
        "k_max": K_MAX,
        "n_cutoff": N_CUTOFF,
        "remaining_ee_is_family": all(
            remaining_ee(b) == "O" * b + "EE" for b in range(B_EE_MIN, 12)
        ),
        "remaining_eoe_is_family": all(
            remaining_eoe(b) == "O" * b + "EOE" for b in range(B_EOE_MIN, 12)
        ),
        "length_nine_transport_words": [
            word_gapped_ee(2, 4),
            word_gapped_eoe(2, 3),
        ],
        "chain_samples": samples,
        "chain_needs_y_ge_n": all(
            row["contradiction"] == (row["y_ge_n"] and row["tail_at_y"])
            for row in samples
        ),
        "finite_rows": finite,
        "finite_count": len(finite),
        "all_finite_tables_empty": all(row["table"]["hit_count"] == 0 for row in finite),
        "large_k_small_n_sealed": large_k_small_n_sealed(),
        "seven_odd_from": K_FINITE_MAX + 1,
        "bunched": bunched,
        "length_eight_census": False,
        "length_nine_census": False,
        "bunched_attack": False,
        "induction_on_period": False,
        "induction_on_n": False,
    }


def lean_api_present() -> dict[str, bool]:
    combined = (
        LEFTOVER_TWO_EVEN.read_text(encoding="utf-8")
        + FIRST_E_TRANSPORT.read_text(encoding="utf-8")
        + FIRST_E_TRANSPORT_EVAL.read_text(encoding="utf-8")
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
        "no_first_e_transport_theorem": "theorem no_cycleMin_gapped_three_even"
        not in combined
        and "theorem no_cycle_min_first_e_transport" not in combined,
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
        "Minimal_untouched": "first_e_transport" not in MINIMAL.read_text(
            encoding="utf-8"
        ),
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["no_cycle_itinerary_two_even_ee"]
        and lean["shared_two_even_tail"]
        and lean["CycleMin"]
        and lean["no_length_eight_theorem"]
        and lean["length_eight_open_in_census"]
        and lean["no_cycleMin_gapped_three_even_ee"]
        and lean["no_cycleMin_gapped_three_even_eoe"]
        and not lean["no_first_e_transport_theorem"]
        and lean["no_all_cycles_impossible"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if (
        scan["length_eight_census"]
        or scan["length_nine_census"]
        or scan["bunched_attack"]
        or scan["induction_on_period"]
        or scan["induction_on_n"]
    ):
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope search"}
    if not scan["remaining_ee_is_family"] or not scan["remaining_eoe_is_family"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "remainder is not a two-even leftover family",
        }
    if not scan["chain_needs_y_ge_n"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "transport chain does not match y>=n plus tail at y",
        }
    if not scan["all_finite_tables_empty"]:
        return {"classification": CLASS_REMAINS, "reason": "CycleItinerary hit in k=9..16"}
    if not scan["large_k_small_n_sealed"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "k>=17 small-n is not sealed by seven odds",
        }
    return {
        "classification": CLASS_GREEN,
        "reason": (
            "Lean excludes gapped three-even CycleMins by first-E "
            "transport of the two-even tail at y>=n; the finite window "
            "k=9..16 has empty CycleItinerary tables below 256; for k>=17 "
            "small n is seven-odd on the prefix or the remainder; "
            "bunched a1-short leftovers remain"
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
            "length_eight_census": False,
            "length_nine_census": False,
            "first_e_transport_lean": True,
            "induction_on_period": False,
            "induction_on_n": False,
        }
    )
    return {
        "experiment": "juggler_first_e_transport",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "CycleMin first-E transport of the uniform two-even tail; "
            "gapped leftovers only (b>=4 EE, b>=3 EOE); CycleItinerary "
            "tables for k=9..16 below 256; seven-odd seal for k>=17; "
            "no bunched-tail attack; no length-8/9 census; Lean "
            "CycleMin exclusion at y>=256"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    bunched = scan["bunched"]
    lines = [
        "# Juggler first-E transport of the two-even tail",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. Gapped three-even CycleMins",
        "only; not a length-8/9 census and not a bunched-tail attack.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Do gapped three-even CycleMins die",
        "                        by first-E transport of the two-even",
        "                        tail?",
        "Novelty hypothesis      y>=n tightens the leftover cell",
        "Falsifier               A CycleMin hit, or a k>=17 leak",
        "Existing machinery      uniform two-even Lean; CycleMin",
        "Maximum Phase-1 scope   Lean CycleMin exclusion; tables;",
        "                        seven-odd; no census, no bunched",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        f"- finite gapped words k=9..16: `{scan['finite_count']}`",
        f"- tables empty: `{scan['all_finite_tables_empty']}`",
        f"- k>=17 small-n sealed: `{scan['large_k_small_n_sealed']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Length-9 transport words",
        "",
    ]
    for word in scan["length_nine_transport_words"]:
        lines.append(f"- `{word}`")
    lines.extend(
        [
            "",
            "## Bunched remainder at each k",
            "",
        ]
    )
    for row in bunched["rows"][:8]:
        lines.append(
            f"- k=`{row['k']}` gapped=`{row['gapped_count']}` "
            f"bunched=`{row['bunched_count']}` "
            f"ee=`{row['bunched_ee']}` eoe=`{row['bunched_eoe']}`"
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
            f"- no first-E transport theorem: `{lean.get('no_first_e_transport_theorem')}`",
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
            "not an exclusion of bunched three-even leftovers.",
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
        f"finite={scan['finite_count']} empty={scan['all_finite_tables_empty']} "
        f"sealed={scan['large_k_small_n_sealed']}"
    )


if __name__ == "__main__":
    main()

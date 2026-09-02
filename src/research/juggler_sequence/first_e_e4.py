"""First-E transport of excluded three-even families at e=4.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a length-8 or length-9 census, not a four-even bunched-tail
programme, and not induction on period or on n.

After bootstrap the leftover is O^{a0} E O^{a1} E O^{a2} E O^{a3} E
with a0>=2 and a3 in {0,1}. First-E at e=3 transported a two-even
remainder. At e=4 the remainder after the first E has three evens.
This probe classifies expanding e=4 leftovers: gapped last-cluster
(Theorem 3.13 on the last two-even suffix), long-a1 bunched remainder
(Theorems 3.14--3.20 at y), or a short-first-gap remainder that
neither reduction hits.
"""

from __future__ import annotations

import json
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any

from research.juggler_sequence.bunched_last_cluster import (
    FAMILIES,
    tail_holds_log,
    tail_word,
)
from research.juggler_sequence.cycle_length_nine import z_upper
from research.juggler_sequence.lean_paths import (
    BUNCHED_EEE,
    CYCLES,
    FIRST_E_TRANSPORT,
    GAPPED_CYCLE_WORD,
    MINIMAL,
    SMALL_CYCLE_CENSUS,
    engine_floor_text,
    has_named,
    pre_finance_text,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_first_e_e4.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_first_e_e4.md"

CLASS_REPARAM = "FIRST_E_E4_REPARAMETERIZATION"
CLASS_REMAINS = "FIRST_E_E4_REMAINS"
CLASS_INCOMPLETE = "FIRST_E_E4_INCOMPLETE"

O_MIN = 7
O_MAX = 16
Z_MONOTONE_N = 80
A0_EXPAND_CAP = 20

GAPPED_EE_MIN = 4
GAPPED_EOE_MIN = 3

FAMILY_A_MIN: dict[tuple[int, int], int] = {
    (int(row["b"]), int(row["c"])): int(row["a_min"]) for row in FAMILIES
}
FAMILY_NAME: dict[tuple[int, int], str] = {
    (int(row["b"]), int(row["c"])): str(row["name"]) for row in FAMILIES
}
FAMILY_N0: dict[tuple[int, int], int] = {
    (int(row["b"]), int(row["c"])): int(row["first_n0"]) for row in FAMILIES
}

CLASSES = (
    "gapped_last_cluster",
    "bunched_remainder",
    "short_bunched_remainder",
    "leading_OE",
    "leading_even",
)

LEAN_THEOREMS = (
    "CycleMin",
    "no_cycleMin_gapped_three_even_ee",
    "no_cycleMin_gapped_three_even_eoe",
    "no_cycle_itinerary_gapped_three_even_ee",
    "no_cycle_itinerary_three_even_eee",
    "no_cycle_itinerary_three_even_eoee",
    "no_cycle_itinerary_three_even_eooee",
    "no_cycle_itinerary_three_even_eoooee",
    "no_cycle_itinerary_three_even_eeoe",
    "no_cycle_itinerary_three_even_eoeoe",
    "no_cycle_itinerary_three_even_eooeoe",
)

FORBIDDEN_THEOREMS = (
    "no_cycle_itinerary_length_eight",
    "no_cycle_itinerary_length_nine",
    "no_cycle_itinerary_four_even",
    "no_cycleMin_four_even",
    "no_cycle_itinerary_first_e_e4",
    "no_cycleMin_first_e_e4",
    "no_cycle_itinerary_bunched",
)


def expanding(a0: int, a1: int, a2: int, a3: int) -> bool:
    odd = a0 + a1 + a2 + a3
    return 3**odd > 2 ** (odd + 4)


def word_e4(a0: int, a1: int, a2: int, a3: int) -> str:
    return "O" * a0 + "E" + "O" * a1 + "E" + "O" * a2 + "E" + "O" * a3 + "E"


def last_cluster_gapped(a2: int, a3: int) -> bool:
    if a3 == 0:
        return a2 >= GAPPED_EE_MIN
    if a3 == 1:
        return a2 >= GAPPED_EOE_MIN
    return False


def classify_leftover(a0: int, a1: int, a2: int, a3: int) -> str:
    del a0
    if last_cluster_gapped(a2, a3):
        return "gapped_last_cluster"
    a_min = FAMILY_A_MIN[(a2, a3)]
    if a1 >= a_min:
        return "bunched_remainder"
    if a1 >= 2:
        return "short_bunched_remainder"
    if a1 == 1:
        return "leading_OE"
    return "leading_even"


def first_expanding_a0(a1: int, a2: int, a3: int) -> int | None:
    for a0 in range(2, A0_EXPAND_CAP + 1):
        if expanding(a0, a1, a2, a3):
            return a0
    return None


def remainder_shapes() -> list[dict[str, Any]]:
    rows = []
    for (a2, a3), a_min in sorted(FAMILY_A_MIN.items()):
        for a1 in range(a_min):
            if a1 == 0:
                kind = "leading_even"
            elif a1 == 1:
                kind = "leading_OE"
            else:
                kind = "short_bunched_remainder"
            a0 = first_expanding_a0(a1, a2, a3)
            rows.append(
                {
                    "a1": a1,
                    "a2": a2,
                    "a3": a3,
                    "family": FAMILY_NAME[(a2, a3)],
                    "a_min": a_min,
                    "kind": kind,
                    "first_expanding_a0": a0,
                    "example": None if a0 is None else word_e4(a0, a1, a2, a3),
                    "remainder": "O" * a1 + tail_word(a2, a3),
                }
            )
    return rows


def leftover_params(odd_max: int = O_MAX) -> list[tuple[int, int, int, int]]:
    rows = []
    for odd in range(O_MIN, odd_max + 1):
        for a3 in (0, 1):
            rest = odd - a3
            for a0 in range(2, rest + 1):
                mid = rest - a0
                for a1 in range(mid + 1):
                    a2 = mid - a1
                    if expanding(a0, a1, a2, a3):
                        rows.append((a0, a1, a2, a3))
    return rows


def z_monotone(n_hi: int = Z_MONOTONE_N) -> bool:
    for n in range(2, n_hi):
        for a2, a3 in FAMILY_A_MIN:
            if z_upper(n, a2, a3) > z_upper(n + 1, a2, a3):
                return False
    return True


def bunched_tail_at_family_n0() -> list[dict[str, Any]]:
    rows = []
    for row in FAMILIES:
        a1 = int(row["a_min"])
        a2 = int(row["b"])
        a3 = int(row["c"])
        n0 = int(row["first_n0"])
        rows.append(
            {
                "family": row["name"],
                "a1": a1,
                "a2": a2,
                "a3": a3,
                "n0": n0,
                "tail_holds": tail_holds_log(n0, a1, a2, a3),
            }
        )
    return rows


def run_probe() -> dict[str, Any]:
    params = leftover_params()
    class_counts: Counter[str] = Counter()
    by_odd: dict[int, dict[str, int]] = defaultdict(lambda: Counter())
    unclassified = 0
    for a0, a1, a2, a3 in params:
        kind = classify_leftover(a0, a1, a2, a3)
        if kind not in CLASSES:
            unclassified += 1
            continue
        class_counts[kind] += 1
        odd = a0 + a1 + a2 + a3
        by_odd[odd][kind] += 1
    shapes = remainder_shapes()
    tail_rows = bunched_tail_at_family_n0()
    remainder_count = (
        class_counts["short_bunched_remainder"]
        + class_counts["leading_OE"]
        + class_counts["leading_even"]
    )
    transportable = (
        class_counts["gapped_last_cluster"] + class_counts["bunched_remainder"]
    )
    first_bunched_odd = min(
        (
            a0 + a1 + a2 + a3
            for a0, a1, a2, a3 in params
            if classify_leftover(a0, a1, a2, a3) == "bunched_remainder"
        ),
        default=None,
    )
    return {
        "basin": [1],
        "o_min": O_MIN,
        "o_max": O_MAX,
        "leftover_count": len(params),
        "unclassified": unclassified,
        "class_counts": dict(class_counts),
        "counts_by_odd": {
            str(odd): dict(counts) for odd, counts in sorted(by_odd.items())
        },
        "remainder_count": remainder_count,
        "transportable_count": transportable,
        "remainder_shape_count": len(shapes),
        "remainder_shapes_expand": all(
            row["first_expanding_a0"] is not None for row in shapes
        ),
        "remainder_shapes": shapes,
        "z_monotone": z_monotone(),
        "bunched_tail_at_n0": tail_rows,
        "all_bunched_tails_hold": all(row["tail_holds"] for row in tail_rows),
        "first_bunched_remainder_odd": first_bunched_odd,
        "example_gapped_last": word_e4(2, 0, 4, 0),
        "example_bunched_remainder": word_e4(2, 6, 0, 0),
        "example_leading_even": word_e4(7, 0, 0, 0),
        "example_leading_OE": word_e4(6, 1, 0, 0),
        "example_short_bunched": word_e4(2, 5, 0, 0),
        "length_eight_census": False,
        "length_nine_census": False,
        "four_even_bunched_attack": False,
        "induction_on_period": False,
        "induction_on_n": False,
    }


def lean_api_present() -> dict[str, bool]:
    combined = (
        FIRST_E_TRANSPORT.read_text(encoding="utf-8")
        + GAPPED_CYCLE_WORD.read_text(encoding="utf-8")
        + BUNCHED_EEE.read_text(encoding="utf-8")
        + CYCLES.read_text(encoding="utf-8")
        + SMALL_CYCLE_CENSUS.read_text(encoding="utf-8")
        + pre_finance_text()
    )
    named = {name: has_named(combined, name) for name in LEAN_THEOREMS}
    forbidden = {
        name: f"theorem {name}" not in combined for name in FORBIDDEN_THEOREMS
    }
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        **forbidden,
        "no_all_cycles_impossible": "theorem no_juggler_cycle" not in combined,
        "length_eight_open_in_census": "Length eight is open"
        in SMALL_CYCLE_CENSUS.read_text(encoding="utf-8"),
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
        "Minimal_untouched": "first_e_e4" not in MINIMAL.read_text(encoding="utf-8"),
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["CycleMin"]
        and lean["no_cycleMin_gapped_three_even_ee"]
        and lean["no_cycle_itinerary_three_even_eee"]
        and lean["no_cycle_itinerary_length_eight"]
        and lean["no_cycle_itinerary_four_even"]
        and lean["no_cycle_itinerary_first_e_e4"]
        and lean["no_cycle_itinerary_bunched"]
        and lean["length_eight_open_in_census"]
        and lean["no_all_cycles_impossible"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if (
        scan["length_eight_census"]
        or scan["length_nine_census"]
        or scan["four_even_bunched_attack"]
        or scan["induction_on_period"]
        or scan["induction_on_n"]
    ):
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope search"}
    if scan["unclassified"] != 0:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "an e=4 leftover was unclassified",
        }
    if not scan["z_monotone"] or not scan["all_bunched_tails_hold"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "Z is not monotone or a bunched tail misses its N0",
        }
    if not scan["remainder_shapes_expand"] or scan["remainder_shape_count"] != 30:
        return {
            "classification": CLASS_REMAINS,
            "reason": "remainder shapes are not the expected 30 expanding families",
        }
    if scan["remainder_count"] == 0:
        return {
            "classification": CLASS_REMAINS,
            "reason": "no short-gap remainder; the method would not be thin",
        }
    if scan["class_counts"].get("bunched_remainder", 0) == 0:
        return {
            "classification": CLASS_REMAINS,
            "reason": "bunched remainder slice empty on the expanding window",
        }
    if scan["first_bunched_remainder_odd"] != 8:
        return {
            "classification": CLASS_REMAINS,
            "reason": "first bunched remainder is not o=8",
        }
    return {
        "classification": CLASS_REPARAM,
        "reason": (
            "gapped last-cluster is Theorem 3.13 on the last two-even "
            "suffix; long-a1 bunched remainder is the existing bunched "
            "tail at y after y>=n tightens Z(n)<=Z(y); 30 short-first-gap "
            "shapes remain; not a new e=4 theorem"
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
            "four_even_cycles_impossible": False,
            "length_eight_census": False,
            "length_nine_census": False,
            "first_e_e4_lean": False,
            "four_even_bunched_attack": False,
            "induction_on_period": False,
            "induction_on_n": False,
        }
    )
    return {
        "experiment": "juggler_first_e_e4",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "classify expanding e=4 leftovers through odd-count 16; "
            "gapped last-cluster vs bunched remainder vs short first gap; "
            "no length-8/9 census and no four-even tail list"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler first-E transport at four evens",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. Four-even leftovers only; not a",
        "length-8/9 census and not a four-even bunched-tail programme.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Do leftover CycleMins with e=4 even",
        "                        letters die by first-E transport of",
        "                        an excluded three-even family?",
        "Novelty hypothesis      A new infinite e=4 layer, not e=3 again",
        "Falsifier               Gapped last-cluster is Theorem 3.13;",
        "                        long-a1 bunched remainder is 3.14-3.20",
        "                        at y; a large class has short gaps",
        "Existing machinery      two-even tail; first-E; bunched Z;",
        "                        CycleMin y>=n",
        "Maximum Phase-0 scope   Classify expanding e=4 leftovers;",
        "                        no Lean, no census, no Paper A",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        f"- leftover count: `{scan['leftover_count']}`",
        f"- class counts: `{scan['class_counts']}`",
        f"- remainder count: `{scan['remainder_count']}`",
        f"- remainder shapes: `{scan['remainder_shape_count']}`",
        f"- first bunched remainder odd-count: `{scan['first_bunched_remainder_odd']}`",
        f"- Z monotone: `{scan['z_monotone']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Examples",
        "",
        f"- gapped last-cluster: `{scan['example_gapped_last']}`",
        f"- bunched remainder: `{scan['example_bunched_remainder']}`",
        f"- leading even: `{scan['example_leading_even']}`",
        f"- leading OE: `{scan['example_leading_OE']}`",
        f"- short bunched remainder: `{scan['example_short_bunched']}`",
        "",
        "## Lean",
        "",
    ]
    for name in LEAN_THEOREMS:
        lines.append(f"- `{name}`: `{lean.get(name)}`")
    lines.extend(
        [
            f"- no four-even theorem: `{lean.get('no_cycle_itinerary_four_even')}`",
            f"- no first-E e=4 theorem: `{lean.get('no_cycle_itinerary_first_e_e4')}`",
            f"- length eight open in census: `{lean.get('length_eight_open_in_census')}`",
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
            "This is not a halt result and not a length-8/9 census.",
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
    print(f"leftovers={scan['leftover_count']} remainder={scan['remainder_count']}")
    print(scan["class_counts"])


if __name__ == "__main__":
    main()

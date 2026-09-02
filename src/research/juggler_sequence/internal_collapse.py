"""Internal even-run collapse and scale renormalization.

Not a Research Engine control-layer experiment. A medial even run is
residual evaluation at its exit state. Bounded maxEvenRun is not a
useful family bound: nested E^3 O blocks still collapse onto 1. Not a
halt theorem.
"""

from __future__ import annotations

import json
from itertools import product
from math import isqrt
from pathlib import Path
from typing import Any

from research.juggler_sequence.compensated_contraction import follows_itinerary, image_after
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, LEAN_PATH, floor_power
from research.juggler_sequence.lean_paths import juggler_text

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_internal_collapse.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_internal_collapse.md"

CLASS_NORM = "INTERNAL_COLLAPSE_NORMALIZATION_GREEN"
CLASS_RUN = "BOUNDED_RUN_COUNTEREXAMPLE"
CLASS_NUMERIC = "NUMERIC_COLLAPSE_COUNTEREXAMPLE"
CLASS_COMPRESS = "COLLAPSE_COMPRESSION_GREEN"
CLASS_OBSTRUCT = "GLOBAL_COLLAPSE_OBSTRUCTION_GREEN"

LEAN_THEOREMS = (
    "maxEvenRun",
    "internal_even_collapse",
    "collapse_basin_one",
    "nested_even_collapse_2500",
    "nested_even_collapse_2500_superquadratic",
    "maxEvenRun_itineraryEE_OEEE12",
    "odd_even_tower_seven",
    "collapse_on_pow_two",
    "image_append",
    "eventually_no_first_even_contraction",
    "changing_suffix_unbounded_contraction",
    "first_even_freeze",
)

CERTIFICATE_UNCHANGED = (
    "power_bound_compensated_contracts",
    "eventually_no_first_even_contraction",
    "changing_suffix_unbounded_contraction",
)


def is_superquadratic(word: str) -> bool:
    return 3 ** word.count("O") > 2 ** (len(word) + 1)


def max_even_run(word: str) -> int:
    best = current = 0
    for letter in word:
        if letter == "E":
            current += 1
            best = max(best, current)
        else:
            current = 0
    return best


def even_runs(word: str) -> list[tuple[int, int]]:
    runs = []
    i = 0
    while i < len(word):
        if word[i] != "E":
            i += 1
            continue
        j = i
        while j < len(word) and word[j] == "E":
            j += 1
        runs.append((i, j - i))
        i = j
    return runs


def q_contracts(q: int, word: str) -> bool:
    return follows_itinerary(q, word) and image_after(q, word) + 1 < (q + 1) ** 2


def states_along(q: int, word: str) -> list[int]:
    current = q
    out = [q]
    for _ in word:
        current = floor_power(current)
        out.append(current)
    return out


def collapse_events(q: int, word: str) -> list[dict[str, Any]]:
    path = states_along(q, word)
    events = []
    for pos, run in even_runs(word):
        entry = path[pos]
        exit_state = path[pos + run]
        events.append(
            {
                "position": pos,
                "r": run,
                "entry": entry,
                "exit": exit_state,
                "ratio": entry // max(exit_state, 1),
                "sharp_envelope": exit_state ** (1 << run) <= entry,
            }
        )
    return events


def residual_at_small_y() -> list[dict[str, Any]]:
    rows = []
    for y in range(1, 6):
        for residual in ("", "O", "OO", "OOO", "E"):
            if not follows_itinerary(y, residual):
                continue
            rows.append({"y": y, "residual": residual, "T": image_after(y, residual)})
    return rows


def q_max_by_max_run(*, k_max: int = 8, q_cap: int = 80) -> list[dict[str, Any]]:
    best: dict[int, dict[str, Any]] = {}
    for length in range(1, k_max + 1):
        for letters in product("EO", repeat=length):
            word = "".join(letters)
            if not is_superquadratic(word):
                continue
            run = max_even_run(word)
            last = None
            last_t = None
            for q in range(1, q_cap + 1):
                if q_contracts(q, word):
                    last = q
                    last_t = image_after(q, word)
            if last is None:
                continue
            prev = best.get(run)
            if prev is None or last > prev["q_max"]:
                best[run] = {"max_even_run": run, "word": word, "q_max": last, "T": last_t}
    return [best[r] for r in sorted(best)]


def nested_r3_family() -> list[dict[str, Any]]:
    rows = []
    word7 = "OEEE" + "O" * 9
    rows.append(
        {
            "name": "OEEE_O9",
            "word": word7,
            "q": 7,
            "max_even_run": max_even_run(word7),
            "T": image_after(7, word7),
            "superquadratic": is_superquadratic(word7),
            "contracts": q_contracts(7, word7),
            "events": collapse_events(7, word7),
        }
    )
    word2500 = "EE" + "OEEE" + "O" * 12
    rows.append(
        {
            "name": "EE_OEEE_O12",
            "word": word2500,
            "q": 2500,
            "max_even_run": max_even_run(word2500),
            "T": image_after(2500, word2500),
            "superquadratic": is_superquadratic(word2500),
            "contracts": q_contracts(2500, word2500),
            "events": collapse_events(2500, word2500),
        }
    )
    word_big = "EEE" + "OEEE" + "O" * 12
    q_big = 2500 * 2500
    rows.append(
        {
            "name": "EEE_OEEE_O12",
            "word": word_big,
            "q": q_big,
            "max_even_run": max_even_run(word_big),
            "T": image_after(q_big, word_big),
            "superquadratic": is_superquadratic(word_big),
            "contracts": q_contracts(q_big, word_big),
            "events": collapse_events(q_big, word_big),
        }
    )
    z = 33933
    b = z * z + 1
    a = b * b
    q_bits = a * a
    word_bits = "EEE" + "O" + "EEE" + "O" + "EEE" + "O" * 16
    rows.append(
        {
            "name": "layer2_z33933",
            "word": word_bits,
            "q_bit_length": q_bits.bit_length(),
            "max_even_run": max_even_run(word_bits),
            "T": image_after(q_bits, word_bits),
            "superquadratic": is_superquadratic(word_bits),
            "contracts": q_contracts(q_bits, word_bits),
            "events": collapse_events(q_bits, word_bits),
        }
    )
    return rows


def lean_api_present() -> dict[str, bool]:
    text = juggler_text()
    return {
        "sorry_free": "sorry" not in text and "admit" not in text,
        **{
            name: (f"theorem {name}" in text or f"def {name}" in text)
            for name in LEAN_THEOREMS
        },
        "certificate_present": all(f"theorem {name}" in text for name in CERTIFICATE_UNCHANGED),
        "PowerHeight_absent": "PowerHeight" not in text,
        "no_lower_envelope_structure": "structure LowerEnvelope" not in text,
        "no_residual_automaton": "structure ResidualAutomaton" not in text,
    }


def classify(family: list[dict[str, Any]], lean: dict[str, bool]) -> dict[str, Any]:
    ok = all(row["contracts"] and row["T"] == 1 and row["max_even_run"] == 3 for row in family)
    growing = family[0]["q"] < family[1]["q"] < family[2]["q"]
    lean_ok = lean["sorry_free"] and lean["internal_even_collapse"] and lean["nested_even_collapse_2500"]
    if ok and growing:
        return {
            "classification": CLASS_RUN,
            "secondary": CLASS_COMPRESS,
            "reason": (
                "maxEvenRun=3 still admits nested E^3 O collapses onto 1 at "
                "q=7, 2500, 6250000, and a 121-bit q; the mechanism is "
                "numeric collapse to the inert basin 1"
            ),
            "lean_ok": lean_ok,
        }
    return {
        "classification": CLASS_NORM,
        "reason": "internal-run identity holds, but the nested family was not confirmed",
        "lean_ok": lean_ok,
    }


def run_probe() -> dict[str, Any]:
    family = nested_r3_family()
    t_gt_one = []
    for length in range(1, 8):
        for letters in product("EO", repeat=length):
            word = "".join(letters)
            if not is_superquadratic(word):
                continue
            for q in range(1, 81):
                if q_contracts(q, word) and image_after(q, word) > 1:
                    t_gt_one.append({"word": word, "q": q, "T": image_after(q, word)})
    return {
        "residual_at_small_y": residual_at_small_y(),
        "q_max_by_max_run": q_max_by_max_run(),
        "nested_family": family,
        "t_gt_one_short": t_gt_one,
        "only_non1_short": t_gt_one,
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan["nested_family"], lean)
    return {
        "experiment": "juggler_internal_collapse",
        "engine_control_layer_modified": False,
        "anti_overclaim": dict(ANTI_OVERCLAIM),
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "enumerate maximal even runs; integer entry/exit/ratio; "
            "nested E^3 O family onto basin 1; no logs, no huge envelopes"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler internal even-run collapse",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment and",
        "not a termination theorem. Internal even runs reduce to residual",
        "evaluation. Bounded max even-run length is not a useful family bound.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Does bounding internal even runs restore a family bound?",
        "Novelty hypothesis      Numeric collapse to a small basin is the obstruction",
        "Falsifier               maxEvenRun ≤ R with unbounded contracting q",
        "Existing machinery      image_append, collapse_on_pow_two, odd_even_tower_seven",
        "Maximum Phase-0 scope   Run census; nested R=3 family; Lean residual identity",
        "```",
        "",
        "## Metadata",
        "",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Nested `maxEvenRun = 3` family",
        "",
    ]
    for row in scan["nested_family"]:
        qrep = row.get("q", f"{row.get('q_bit_length')} bits")
        lines.append(
            f"- `{row['name']}` q=`{qrep}` T=`{row['T']}` "
            f"maxE=`{row['max_even_run']}` contracts=`{row['contracts']}`"
        )
    lines.extend(["", "## Short-word `q_max` by max even-run", ""])
    for row in scan["q_max_by_max_run"]:
        lines.append(
            f"- maxE=`{row['max_even_run']}` word=`{row['word']}` "
            f"q_max=`{row['q_max']}` T=`{row['T']}`"
        )
    lines.extend(["", "## Short contractions with T>1", ""])
    for row in scan["t_gt_one_short"]:
        lines.append(f"- `{row['word']}` q=`{row['q']}` T=`{row['T']}`")
    lines.extend(["", "## Lean", ""])
    for name in LEAN_THEOREMS:
        lines.append(f"- `{name}`: `{lean.get(name)}`")
    lines.extend(
        [
            f"- certificate unchanged: `{lean.get('certificate_present')}`",
            f"- `PowerHeight` absent: `{lean.get('PowerHeight_absent')}`",
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
            "The fixed-word theorem remains. This is not a halt result.",
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


if __name__ == "__main__":
    main()

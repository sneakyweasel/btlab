"""Collapse normalization of first-even contraction.

Not a Research Engine control-layer experiment. An initial even run is
a scale change: T_{E^r u}(a^{2^r}) = T_u(a). Bounded initial even-run
length does not restore family non-contraction. Not a halt theorem.
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
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_collapse_normalization.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_collapse_normalization.md"

CLASS_NORM = "COLLAPSE_NORMALIZATION_GREEN"
CLASS_DEPTH = "COLLAPSE_DEPTH_SUFFICIENT"
CLASS_WEAK = "COLLAPSE_DEPTH_TOO_WEAK"
CLASS_COUNTER = "COLLAPSE_COUNTEREXAMPLE"
CLASS_INSUFF = "COLLAPSE_NORMALIZATION_INSUFFICIENT"

LEAN_THEOREMS = (
    "initialEvenRun",
    "stripInitialEven",
    "initial_even_decomposition",
    "iterate_even_pow_two_eq",
    "collapse_residual_identity",
    "collapse_on_pow_two",
    "collapse_tower_contracts_iff",
    "even_tower_collapse_residual",
    "odd_then_even_collapse",
    "odd_even_tower_seven",
    "itineraryOEEE9",
    "odd_even_tower_seven_superquadratic",
    "floorPower_iterate_even_pow_two_eq",
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


def initial_even_run(word: str) -> int:
    run = 0
    for letter in word:
        if letter != "E":
            break
        run += 1
    return run


def strip_initial_even(word: str) -> str:
    return word[initial_even_run(word) :]


def max_even_run(word: str) -> int:
    best = current = 0
    for letter in word:
        if letter == "E":
            current += 1
            best = max(best, current)
        else:
            current = 0
    return best


def q_contracts(q: int, word: str) -> bool:
    return follows_itinerary(q, word) and image_after(q, word) + 1 < (q + 1) ** 2


def even_steps_to_one(start: int, *, k_max: int = 12) -> int | None:
    current = start
    steps = 0
    while current % 2 == 0 and current > 1 and steps < k_max:
        current = isqrt(current)
        steps += 1
    if current == 1:
        return steps
    return None


def collapse_on_pow_two(a: int, r: int, residual: str) -> dict[str, Any]:
    q = a ** (1 << r)
    word = "E" * r + residual
    return {
        "a": a,
        "r": r,
        "q": q,
        "residual": residual,
        "word": word,
        "follows_q": follows_itinerary(q, word),
        "follows_a": follows_itinerary(a, residual),
        "image_q": image_after(q, word) if follows_itinerary(q, word) else None,
        "image_a": image_after(a, residual) if follows_itinerary(a, residual) else None,
    }


def even_tower_residuals(*, k_max: int = 5) -> list[dict[str, Any]]:
    rows = []
    for k in range(2, k_max + 1):
        o = 3 * k
        word = "E" * k + "O" * o
        q = 2 ** (2 ** (k - 1))
        residual_state = image_after(q, "E" * k)
        rows.append(
            {
                "k": k,
                "word": word,
                "q": q,
                "initial_even_run": initial_even_run(word),
                "max_even_run": max_even_run(word),
                "residual_word": strip_initial_even(word),
                "residual_state": residual_state,
                "image": image_after(q, word),
                "contracts": q_contracts(q, word),
            }
        )
    return rows


def odd_internal_collapse(*, q_max: int = 20000) -> list[dict[str, Any]]:
    best: dict[int, dict[str, Any]] = {}
    for q in range(1, q_max + 1, 2):
        start = isqrt(q * q * q)
        steps = even_steps_to_one(start)
        if steps is None or steps < 2:
            continue
        word = "O" + "E" * steps + "O" * (3 * steps)
        if not is_superquadratic(word) or not q_contracts(q, word):
            continue
        row = {
            "k": steps,
            "q": q,
            "word": word,
            "initial_even_run": initial_even_run(word),
            "max_even_run": max_even_run(word),
            "residual_after_odd": start,
            "image": image_after(q, word),
        }
        prev = best.get(steps)
        if prev is None or q > prev["q"]:
            best[steps] = row
    return [best[k] for k in sorted(best)]


def short_word_by_initial_run(*, k_max: int = 7, q_cap: int = 40) -> list[dict[str, Any]]:
    rows = []
    for length in range(1, k_max + 1):
        for letters in product("EO", repeat=length):
            word = "".join(letters)
            if not is_superquadratic(word):
                continue
            last = None
            for q in range(1, q_cap + 1):
                if q_contracts(q, word):
                    last = q
            rows.append(
                {
                    "word": word,
                    "initial_even_run": initial_even_run(word),
                    "max_even_run": max_even_run(word),
                    "q_max": last,
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
        "no_bounded_collapse_theorem": "theorem bounded_collapse_eventual_noncontraction" not in text,
    }


def classify(
    identity_ok: bool,
    internal: list[dict[str, Any]],
    lean: dict[str, bool],
) -> dict[str, Any]:
    growing = len(internal) >= 2 and internal[-1]["q"] > internal[0]["q"]
    r_zero = all(row["initial_even_run"] == 0 for row in internal)
    lean_ok = lean["sorry_free"] and lean["collapse_on_pow_two"] and lean["odd_even_tower_seven"]
    if identity_ok and growing and r_zero:
        return {
            "classification": CLASS_WEAK,
            "secondary": CLASS_NORM,
            "reason": (
                "E^r u on a^{2^r} reduces to u on a, but initial even-run "
                "length 0 still admits O E^k O^{3k} contractions at "
                "arbitrarily large scanned q; the extra parameter is the "
                "longest even run"
            ),
            "lean_ok": lean_ok,
        }
    if identity_ok and lean_ok:
        return {
            "classification": CLASS_NORM,
            "reason": "collapse identity holds, but the bounded-depth test was inconclusive",
            "lean_ok": lean_ok,
        }
    return {
        "classification": CLASS_INSUFF,
        "reason": "collapse identity or internal-collapse scan failed",
        "lean_ok": lean_ok,
    }


def run_probe(*, q_max: int = 20000) -> dict[str, Any]:
    identities = []
    ok = True
    for a in range(2, 12, 2):
        for r in range(0, 4):
            for residual in ("", "O", "OO", "OOO"):
                row = collapse_on_pow_two(a, r, residual)
                identities.append(row)
                if row["follows_q"] and row["follows_a"] and row["image_q"] != row["image_a"]:
                    ok = False
    internal = odd_internal_collapse(q_max=q_max)
    return {
        "identity_ok": ok,
        "identities_checked": len(identities),
        "even_tower_residuals": even_tower_residuals(),
        "internal_collapse": internal,
        "short_words": short_word_by_initial_run(),
        "seven_oeee": {
            "q": 7,
            "word": "OEEE" + "O" * 9,
            "follows": follows_itinerary(7, "OEEE" + "O" * 9),
            "image": image_after(7, "OEEE" + "O" * 9),
            "superquadratic": is_superquadratic("OEEE" + "O" * 9),
        },
    }


def probe_payload(*, q_max: int = 20000) -> dict[str, Any]:
    scan = run_probe(q_max=q_max)
    lean = lean_api_present()
    decision = classify(scan["identity_ok"], scan["internal_collapse"], lean)
    return {
        "experiment": "juggler_collapse_normalization",
        "engine_control_layer_modified": False,
        "anti_overclaim": dict(ANTI_OVERCLAIM),
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "exact a^{2^r} identity; even-tower residual at 1; "
            "odd q whose odd-image falls into an even basin of 1; "
            "no logs, no huge envelopes"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler collapse normalization",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment and",
        "not a termination theorem. An initial even run is a scale change.",
        "Bounded initial even-run length is not enough to restore a family",
        "threshold.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     T_{E^r u}(a^{2^r})=T_u(a); does bounded r restore Q?",
        "Novelty hypothesis      Collapse depth is the missing family variable",
        "Falsifier               Bounded initial even-run with unbounded contracting q",
        "Existing machinery      iterate_even_pow_two_eq, image_append",
        "Maximum Phase-0 scope   Decomposition; residual identity; bounded-r scan",
        "```",
        "",
        "## Metadata",
        "",
        f"- identity ok: `{scan['identity_ok']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Even-tower residuals",
        "",
    ]
    for row in scan["even_tower_residuals"]:
        lines.append(
            f"- k=`{row['k']}` q=`{row['q']}` residual_state=`{row['residual_state']}` "
            f"T=`{row['image']}` r=`{row['initial_even_run']}`"
        )
    lines.extend(["", "## Internal collapse `O E^k O^{3k}`", ""])
    for row in scan["internal_collapse"]:
        lines.append(
            f"- k=`{row['k']}` q=`{row['q']}` r=`{row['initial_even_run']}` "
            f"maxE=`{row['max_even_run']}` T=`{row['image']}`"
        )
    seven = scan["seven_oeee"]
    lines.extend(
        [
            "",
            "## Lean witness `q=7`",
            "",
            f"- word=`{seven['word']}` follows=`{seven['follows']}` "
            f"T=`{seven['image']}` superquadratic=`{seven['superquadratic']}`",
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
            f"- `PowerHeight` absent: `{lean.get('PowerHeight_absent')}`",
            f"- no bounded-collapse theorem: `{lean.get('no_bounded_collapse_theorem')}`",
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


def write_artifacts(
    payload: dict[str, Any] | None = None,
    *,
    q_max: int = 20000,
) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload(q_max=q_max)
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

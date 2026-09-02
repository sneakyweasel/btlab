"""Eventual non-contraction for formally superquadratic suffixes.

Not a Research Engine control-layer experiment. For each fixed v with
3^#O(v) > 2^(|v|+1), Q_v is finite. Not a halt theorem and not a
generic lower-envelope theory.
"""

from __future__ import annotations

import json
from itertools import product
from pathlib import Path
from typing import Any

from research.juggler_sequence.compensated_contraction import follows_itinerary, image_after
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, LEAN_PATH
from research.juggler_sequence.lean_paths import juggler_text

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_superquadratic_suffixes.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_superquadratic_suffixes.md"

CLASS_EVENTUAL = "FIRST_E_EVENTUAL_NONCONTRACTION_GREEN"
CLASS_GROWTH = "LOWER_GROWTH_COMPOSITION_GREEN"
CLASS_COUNTER = "SUPERQUADRATIC_COUNTEREXAMPLE"
CLASS_WEAK = "LOWER_BOUND_TECHNIQUE_TOO_WEAK"

K_MAX = 5
Q_MAX = 200
Q_MAX_HEAVY = 80

LEAN_THEOREMS = (
    "LowerPowerBound",
    "lower_growth_word",
    "eventually_no_first_even_contraction",
    "alpha_ne_two",
    "four_mul_floorPower_even_sq",
    "four_mul_floorPower_odd_sq",
    "oo_lower_growth_eventual",
    "oo_suffix_threshold",
    "ooo_suffix_threshold",
    "first_even_freeze",
    "power_bound_compensated_contracts",
)

CERTIFICATE_UNCHANGED = (
    "power_bound_compensated_contracts",
    "power_bound_follows",
)


def is_superquadratic(word: str) -> bool:
    return 3 ** word.count("O") > 2 ** (len(word) + 1)


def superquadratic_words(*, k_max: int = K_MAX) -> list[str]:
    words = []
    for k in range(1, k_max + 1):
        for letters in product("EO", repeat=k):
            word = "".join(letters)
            if is_superquadratic(word):
                words.append(word)
    return words


def scan_suffix(v: str, *, q_max: int) -> dict[str, Any]:
    contracting = []
    first_expand = None
    last = None
    realized = 0
    for q in range(1, q_max + 1):
        if not follows_itinerary(q, v):
            continue
        realized += 1
        output = image_after(q, v)
        if output + 1 < (q + 1) ** 2:
            contracting.append(q)
            last = {"q": q, "output": output}
        elif first_expand is None:
            first_expand = q
    return {
        "word": v,
        "length": len(v),
        "odd_count": v.count("O"),
        "formal_exponent_num": 3 ** v.count("O"),
        "formal_exponent_den": 1 << len(v),
        "superquadratic": True,
        "realized": realized,
        "Q": contracting,
        "largest_contracting_q": None if last is None else last["q"],
        "largest_contracting_output": None if last is None else last["output"],
        "first_q_without_contraction": first_expand,
    }


def lean_api_present() -> dict[str, bool]:
    text = juggler_text()
    return {
        "sorry_free": "sorry" not in text and "admit" not in text,
        "LowerPowerBound": "def LowerPowerBound" in text,
        **{
            name: (f"theorem {name}" in text or f"def {name}" in text)
            for name in LEAN_THEOREMS
            if name != "LowerPowerBound"
        },
        "certificate_present": all(
            f"theorem {name}" in text for name in CERTIFICATE_UNCHANGED
        ),
        "PowerHeight_absent": "PowerHeight" not in text,
        "no_lower_envelope_structure": "structure LowerEnvelope" not in text,
        "mixed_word_power_lt_absent": "theorem mixed_word_power_lt" not in text,
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    huge = [
        item
        for item in scan["suffixes"]
        if item["largest_contracting_q"] is not None and item["largest_contracting_q"] >= 20
    ]
    lean_ok = lean["sorry_free"] and lean["LowerPowerBound"] and lean["eventually_no_first_even_contraction"]
    if huge:
        return {
            "classification": CLASS_COUNTER,
            "reason": "a superquadratic suffix had a contracting q ≥ 20 on the scan",
        }
    if not lean_ok:
        return {
            "classification": CLASS_WEAK,
            "reason": "no large Q_v appeared, but the Lean lower-growth theorem is incomplete",
        }
    return {
        "classification": CLASS_EVENTUAL,
        "secondary": CLASS_GROWTH,
        "reason": (
            "each fixed v with 3^#O(v) > 2^(|v|+1) has LowerPowerBound "
            "q^{3^o} ≤ D_v T_v(q)^{2^r} and therefore only finitely many "
            "first-even contraction cells; no finite word has α_v = 2"
        ),
    }


def run_probe(*, k_max: int = K_MAX, q_max: int = Q_MAX, q_max_heavy: int = Q_MAX_HEAVY) -> dict[str, Any]:
    suffixes = []
    for word in superquadratic_words(k_max=k_max):
        cap = q_max_heavy if word.count("O") >= 4 else q_max
        suffixes.append(scan_suffix(word, q_max=cap))
    return {
        "k_max": k_max,
        "q_max": q_max,
        "q_max_heavy": q_max_heavy,
        "suffixes": suffixes,
        "alpha_never_two": True,
    }


def probe_payload(*, k_max: int = K_MAX, q_max: int = Q_MAX) -> dict[str, Any]:
    scan = run_probe(k_max=k_max, q_max=q_max)
    lean = lean_api_present()
    decision = classify(scan, lean)
    return {
        "experiment": "juggler_superquadratic_suffixes",
        "engine_control_layer_modified": False,
        "anti_overclaim": dict(ANTI_OVERCLAIM),
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "realized q only; integer comparison T_v(q)+1 < (q+1)^2; "
            "no huge envelope powers"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler superquadratic suffixes",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment and",
        "not a termination theorem. Every fixed suffix with",
        "`3^#O(v) > 2^(|v|+1)` has only finitely many first-even contraction",
        "cells. The threshold depends on `v`.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     For each fixed v with α_v>2, is Q_v finite?",
        "Novelty hypothesis      Coarse 4T^2 bounds compose to a gap 3^o>2^{r+1}",
        "Falsifier               A large contracting q for a fixed superquadratic v",
        "Existing machinery      first_even_freeze, PowerBound (upper only)",
        "Maximum Phase-0 scope   LowerPowerBound; eventual non-contraction",
        "```",
        "",
        "## Metadata",
        "",
        f"- word length: `k <= {scan['k_max']}`",
        f"- q domain: `q <= {scan['q_max']}` (heavy `<= {scan['q_max_heavy']}`)",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Superquadratic scans",
        "",
    ]
    for item in scan["suffixes"]:
        lines.append(
            f"- `{item['word']}` α=`{item['formal_exponent_num']}/"
            f"{item['formal_exponent_den']}` Q=`{item['Q']}` "
            f"first_expand=`{item['first_q_without_contraction']}`"
        )
    lines.extend(
        [
            "",
            "## Lean",
            "",
            f"- `LowerPowerBound`: `{lean.get('LowerPowerBound')}`",
        ]
    )
    for name in LEAN_THEOREMS:
        if name == "LowerPowerBound":
            continue
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
            "This is a fixed-word threshold statement, not a global halt result.",
            "",
        ]
    )
    return "\n".join(lines) + "\n"


def write_artifacts(
    payload: dict[str, Any] | None = None,
    *,
    k_max: int = K_MAX,
    q_max: int = Q_MAX,
) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload(k_max=k_max, q_max=q_max)
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

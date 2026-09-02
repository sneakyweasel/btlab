"""Equality-word language: monochrome families versus mixed itineraries.

Not a Research Engine control-layer experiment. Equality is decided by
local integer-square exactness only. No cmp_pow on n^{3^o}. Not a
termination theorem and not an equality-word census.
"""

from __future__ import annotations

import json
from math import isqrt
from pathlib import Path
from typing import Any

from research.juggler_sequence.lean_paths import juggler_text
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, LEAN_PATH, itinerary
from research.juggler_sequence.saturation_budget import (
    has_pow_two_depth,
    saturation_prefix,
    saturates_word,
    scan_domain,
    tiny_global_eq,
    tower,
    tower_family,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_equality_language.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_equality_language.md"

CLASS_MIXED = "MIXED_EQUALITY_WORD_FOUND"
CLASS_MONO = "MONOCHROMATIC_EQUALITY_GREEN"
CLASS_EXTREMAL = "EXTREMAL_FAMILY_GREEN"
CLASS_INCOMPLETE = "EQUALITY_LANGUAGE_INCOMPLETE"

N_MAX = 10**4
K_MAX = 8
TOWER_R_MAX = 4

LEAN_THEOREMS = (
    "even_iff_pow_even",
    "floorPower_sq_preserves_parity",
    "floorPower_pow_two_depth_preserves_parity",
    "power_bound_eq_implies_monochrome",
    "floorPower_iterate_even_pow_two_eq",
    "floorPower_iterate_odd_pow_two_eq",
    "follows_replicate_even_pow_two",
    "follows_replicate_odd_pow_two",
    "power_bound_eq_iff_extremal",
    "two_pow_two_pow_extremal_even",
    "three_pow_two_pow_extremal_odd",
    "odd_equality_three_pow_le",
)

MONO_THEOREMS = (
    "even_iff_pow_even",
    "floorPower_sq_preserves_parity",
    "power_bound_eq_implies_monochrome",
)

FAMILY_THEOREMS = (
    "floorPower_iterate_even_pow_two_eq",
    "floorPower_iterate_odd_pow_two_eq",
    "power_bound_eq_iff_extremal",
)


def is_monochrome(word: str) -> bool:
    return (not word) or ("E" not in word) or ("O" not in word)


def peel_base(n: int, k: int) -> int:
    """Peel k exact square roots, recovering a from n = a^{2^k}."""

    if k < 0:
        raise ValueError("peel depth cannot be negative")
    current = n
    for _ in range(k):
        current = isqrt(current)
    return current


def mixed_record(rec: dict[str, Any]) -> dict[str, Any] | None:
    word = rec["word"]
    if rec["length"] == 0 or is_monochrome(word):
        return None
    start = rec["start"]
    return {
        "word": word,
        "start": start,
        "length": rec["length"],
        "square_depth": rec["square_depth"],
        "base": peel_base(start, rec["length"]),
        "base_parity": peel_base(start, rec["length"]) % 2,
        "trajectory": rec["trajectory"],
    }


def scan_mixed(n_max: int, k_max: int) -> dict[str, Any]:
    domain = scan_domain(n_max, k_max)
    mixed = [mixed_record(rec) for rec in domain["samples"] if mixed_record(rec)]
    # samples are truncated; use the domain mixed_count as the authority
    towers = tower_family(range(2, 31), TOWER_R_MAX)
    tower_mixed = [mixed_record(rec) for rec in towers if mixed_record(rec)]
    prescribed_mixed = 0
    for word in ("EO", "OE", "EOE", "OEO", "EEO", "OEE", "OOE", "EOO"):
        for n in range(2, min(n_max, 400) + 1):
            if saturates_word(n, word):
                prescribed_mixed += 1
                break
    return {
        "domain": {
            "saturation_count": domain["saturation_count"],
            "mixed_count": domain["mixed_count"],
            "max_saturation_length": domain["max_saturation_length"],
        },
        "sample_mixed": mixed[:8],
        "tower_mixed_count": len(tower_mixed),
        "prescribed_mixed_realized": prescribed_mixed,
        "mixed_found": (
            domain["mixed_count"] > 0 or tower_mixed or prescribed_mixed > 0
        ),
    }


def family_witness(base: int, k: int) -> dict[str, Any] | None:
    n = tower(base, k)
    if n is None:
        return None
    rec = saturation_prefix(n, k)
    expected = ("E" if base % 2 == 0 else "O") * k
    image = rec["trajectory"][-1]
    return {
        "base": base,
        "k": k,
        "start": n,
        "word": rec["word"],
        "expected_word": expected,
        "monochrome": is_monochrome(rec["word"]),
        "matches_family": rec["word"] == expected,
        "image": image,
        "even_image_is_base": base % 2 == 0 and image == base,
        "square_depth": rec["square_depth"],
        "has_pow_two_depth": has_pow_two_depth(n, k),
        "base_parity": peel_base(n, rec["length"]) % 2 if rec["length"] == k else None,
    }


def family_scan() -> dict[str, Any]:
    even = [family_witness(2, k) for k in range(1, 5)]
    odd = [family_witness(3, k) for k in range(1, 4)]
    extra = [family_witness(5, 2), family_witness(4, 2), family_witness(6, 1)]
    records = [rec for rec in even + odd + extra if rec is not None]
    return {
        "records": records,
        "all_match": all(rec["matches_family"] for rec in records),
        "all_monochrome": all(rec["monochrome"] for rec in records),
    }


def example_records() -> dict[str, Any]:
    nine = saturation_prefix(9, 1)
    nine["independent_global_eq"] = tiny_global_eq(9, "O", 27)
    nine["base"] = peel_base(9, 1)
    sixteen = saturation_prefix(16, 2)
    sixteen["independent_global_eq"] = tiny_global_eq(16, "EE", itinerary(16, 2)[2])
    sixteen["base"] = peel_base(16, 2)
    eighty_one = saturation_prefix(81, 2)
    eighty_one["base"] = peel_base(81, 2)
    return {
        "odd_square_nine": nine,
        "even_tower_sixteen": sixteen,
        "odd_fourth_eighty_one": eighty_one,
        "word_of_mixed_probe": saturates_word(9, "EO"),
    }


def lean_api_present() -> dict[str, bool]:
    text = juggler_text()
    return {
        "sorry_free": "sorry" not in text and "admit" not in text,
        **{name: f"theorem {name}" in text for name in LEAN_THEOREMS},
        "PowerHeight_absent": "PowerHeight" not in text,
        "mixed_word_power_lt_absent": "theorem mixed_word_power_lt" not in text,
    }


def classify(
    mixed: dict[str, Any],
    families: dict[str, Any],
    lean: dict[str, bool],
) -> dict[str, Any]:
    if mixed["mixed_found"]:
        return {
            "classification": CLASS_MIXED,
            "reason": "a realized equality word contains both E and O",
        }
    lean_ok = lean["sorry_free"] and all(lean[name] for name in LEAN_THEOREMS)
    family_ok = families["all_match"] and families["all_monochrome"]
    if lean_ok and family_ok:
        return {
            "classification": CLASS_EXTREMAL,
            "reason": (
                "Envelope equality is exactly the two monochrome towers "
                "a^{2^k} --E^k--> a and a^{2^k} --O^k--> a^{3^k}"
            ),
        }
    mono_ok = lean["sorry_free"] and all(lean[name] for name in MONO_THEOREMS)
    if mono_ok and not all(lean[name] for name in FAMILY_THEOREMS):
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": (
                "monochromaticity holds, but one or both reverse extremal "
                "families are not yet formalized"
            ),
        }
    if mono_ok:
        return {
            "classification": CLASS_MONO,
            "reason": "equality forces a monochrome word E^k or O^k",
        }
    return {
        "classification": CLASS_INCOMPLETE,
        "reason": "the equality-language Lean API is incomplete",
    }


def run_probe(*, n_max: int = N_MAX, k_max: int = K_MAX) -> dict[str, Any]:
    mixed = scan_mixed(n_max, k_max)
    families = family_scan()
    return {
        "n_max": n_max,
        "k_max": k_max,
        "mixed": mixed,
        "families": families,
        "examples": example_records(),
    }


def probe_payload(*, n_max: int = N_MAX, k_max: int = K_MAX) -> dict[str, Any]:
    scan = run_probe(n_max=n_max, k_max=k_max)
    lean = lean_api_present()
    decision = classify(scan["mixed"], scan["families"], lean)
    return {
        "experiment": "juggler_equality_language",
        "engine_control_layer_modified": False,
        "anti_overclaim": dict(ANTI_OVERCLAIM),
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "local tightness and repeated isqrt; mixed-word search only; "
            "no equality census and no cmp_pow on n^{3^o}"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    mixed = scan["mixed"]
    families = scan["families"]
    examples = scan["examples"]
    lines = [
        "# Juggler equality-word language and parity rigidity",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment and",
        "not a termination theorem. Mixed-word strictness remains REFUTED.",
        "This page records whether envelope equality can use both letters.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Must a realized equality word be E^k or O^k?",
        "Novelty hypothesis      Exact perfect-power states keep the base parity,",
        "                        so the word cannot switch letters.",
        "Falsifier               MIXED_EQUALITY_WORD_FOUND",
        "Existing machinery      HasPowTwoDepth, exact E/O transitions, rigidity,",
        "                        saturation budget, local-tightness probe",
        "Maximum Phase-0 scope   Parity lemmas; monochromatic theorem; exact E^k/O^k",
        "                        trajectories if cheap; mixed-word probe.",
        "```",
        "",
        "## Metadata",
        "",
        f"- domain layer: `n <= {scan['n_max']}`, `k <= {scan['k_max']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- domain saturations: `{mixed['domain']['saturation_count']}`",
        f"- mixed saturations: `{mixed['domain']['mixed_count']}`",
        f"- prescribed mixed itineraries realized: `{mixed['prescribed_mixed_realized']}`",
        f"- tower mixed count: `{mixed['tower_mixed_count']}`",
        f"- family witnesses match: `{families['all_match']}`",
        f"- sorry-free: `{lean['sorry_free']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Witnesses",
        "",
        f"- word `O` at 9: base `{examples['odd_square_nine']['base']}`,",
        f"  monochrome `{is_monochrome(examples['odd_square_nine']['word'])}`",
        f"- word `EE` at 16: base `{examples['even_tower_sixteen']['base']}`,",
        f"  trajectory `{examples['even_tower_sixteen']['trajectory']}`",
        f"- word `OO` at 81: base `{examples['odd_fourth_eighty_one']['base']}`",
        f"- mixed word `EO` at 9: `{examples['word_of_mixed_probe']}`",
        "",
        "Exact even towers contract (`3^0 < 2^k`). Exact odd towers expand",
        "(`3^k > 2^k`). Both saturate the one-sided envelope.",
        "",
        "## Lean",
        "",
    ]
    for name in LEAN_THEOREMS:
        lines.append(f"- `{name}`: `{lean.get(name)}`")
    lines.extend(
        [
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
            "This is a finite-word boundary statement, not a global halt result.",
            "",
        ]
    )
    return "\n".join(lines) + "\n"


def write_artifacts(
    payload: dict[str, Any] | None = None,
    *,
    n_max: int = N_MAX,
    k_max: int = K_MAX,
) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload(n_max=n_max, k_max=k_max)
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

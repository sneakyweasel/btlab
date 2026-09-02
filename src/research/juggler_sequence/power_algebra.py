"""Finite-word power algebra and equality rigidity.

Not a Research Engine control-layer experiment. Equality is tested by
local integer-square conditions, not by constructing n^{3^o} via cmp_pow.
"""

from __future__ import annotations

import json
from math import isqrt
from pathlib import Path
from typing import Any, Iterable

from research.juggler_sequence.equality_rigidity import powers_equal
from research.juggler_sequence.lean_paths import juggler_text
from research.juggler_sequence.power_itineraries import (
    ANTI_OVERCLAIM,
    LEAN_PATH,
    floor_power,
    itinerary,
    odd_count,
    word_of,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_power_algebra.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_power_algebra.md"

CLASS_GREEN = "EQUALITY_RIGIDITY_GREEN"
CLASS_LOCAL_FALSE = "LOCAL_SQUARE_EQ_FALSE"
CLASS_PROP_FALSE = "GLOBAL_EQ_PROPAGATION_FALSE"
CLASS_STRUCTURED = "MIXED_EQUALITY_STRUCTURED"

N_MAX = 10**4
K_MAX = 8
LOCAL_IFF_MAX = 10**6
SANITY_N_MAX = 200
SANITY_K_MAX = 4

LEAN_THEOREMS = (
    "power_bound_word",
    "floorPower_even_sq_eq_iff_square",
    "floorPower_odd_sq_eq_cube_iff_square",
    "power_bound_eq_of_append_even",
    "power_bound_eq_of_append_odd",
    "power_bound_eq_implies_local_eq",
    "power_bound_eq_implies_square",
    "power_bound_follows",
    "power_bound_contracts",
)


def is_square(n: int) -> bool:
    if n < 0:
        return False
    r = isqrt(n)
    return r * r == n


def local_even_eq(n: int) -> bool:
    return n % 2 == 0 and floor_power(n) ** 2 == n


def local_odd_eq(n: int) -> bool:
    return n % 2 == 1 and floor_power(n) ** 2 == n**3


def local_tight(n: int) -> bool:
    if n % 2 == 0:
        return local_even_eq(n)
    return local_odd_eq(n)


def chain_record(n: int, word: str, path: tuple[int, ...]) -> dict[str, Any]:
    states = list(path[: len(word)])
    local = [local_tight(x) for x in states]
    squares = [is_square(x) for x in states]
    predicted = bool(local) and all(local)
    return {
        "word": word,
        "start": n,
        "trajectory": list(path[: len(word) + 1]),
        "square_states": squares,
        "local_equality": local,
        "global_equality_predicted": predicted,
        "contains_odd": "O" in word,
        "contains_even": "E" in word,
    }


def local_square_mismatch(n: int) -> bool:
    """LOCAL_SQUARE_EQ_FALSE: local tightness disagrees with squareness."""

    return local_tight(n) != is_square(n)


def tiny_global_eq(n: int, word: str, image: int) -> bool | None:
    """Independent global equality, only when powers stay tiny. Else None."""

    k = len(word)
    o = odd_count(word)
    if k < 1:
        return True
    if n > SANITY_N_MAX or k > SANITY_K_MAX:
        return None
    if n.bit_length() * max(1, 3**o) > 64:
        return None
    return powers_equal(image, 1 << k, n, 3**o)


def scan_local_iff(n_max: int) -> dict[str, Any]:
    mismatches: list[int] = []
    even_eq = 0
    odd_eq = 0
    for n in range(1, n_max + 1):
        if local_square_mismatch(n):
            mismatches.append(n)
        elif local_tight(n):
            if n % 2 == 0:
                even_eq += 1
            else:
                odd_eq += 1
    return {
        "n_max": n_max,
        "mismatch_count": len(mismatches),
        "mismatches": mismatches[:16],
        "even_equal_count": even_eq,
        "odd_equal_count": odd_eq,
        "holds": not mismatches,
    }


def scan_itineraries(
    n_max: int,
    k_max: int,
    *,
    n_min: int = 1,
    states: Iterable[int] | None = None,
) -> dict[str, Any]:
    local_false: list[dict[str, Any]] = []
    prop_false: list[dict[str, Any]] = []
    structured: list[dict[str, Any]] = []
    domain: Iterable[int]
    if states is None:
        domain = range(n_min, n_max + 1)
    else:
        domain = states
    for n in domain:
        if n < 0:
            continue
        path = itinerary(n, k_max)
        reached = len(path) - 1
        for k in range(1, reached + 1):
            word = word_of(path[: k + 1])
            rec = chain_record(n, word, path)
            for x in rec["trajectory"][:-1]:
                if local_square_mismatch(x):
                    local_false.append(rec)
                    break
            independent = tiny_global_eq(n, word, path[k])
            if independent is not None and independent != rec["global_equality_predicted"]:
                rec["independent_global_eq"] = independent
                prop_false.append(rec)
            if rec["global_equality_predicted"]:
                structured.append(rec)
    return {
        "local_square_false": local_false[:16],
        "local_square_false_count": len(local_false),
        "propagation_false": prop_false[:16],
        "propagation_false_count": len(prop_false),
        "structured_equalities": structured[:24],
        "structured_count": len(structured),
        "structured_with_odd": sum(1 for rec in structured if rec["contains_odd"]),
        "structured_both_letters": sum(
            1 for rec in structured if rec["contains_odd"] and rec["contains_even"]
        ),
    }


def example_records() -> dict[str, Any]:
    nine = chain_record(9, "O", itinerary(9, 1))
    nine["independent_global_eq"] = tiny_global_eq(9, "O", 27)
    eighty_one = chain_record(81, "OO", itinerary(81, 2))
    sixteen = chain_record(16, "EE", itinerary(16, 2))
    sixteen["independent_global_eq"] = tiny_global_eq(16, "EE", itinerary(16, 2)[2])
    return {
        "odd_square_nine": nine,
        "odd_fourth_eighty_one": eighty_one,
        "even_tower_sixteen": sixteen,
    }


def lean_api_present() -> dict[str, bool]:
    text = juggler_text()
    return {
        "sorry_free": "sorry" not in text and "admit" not in text,
        **{name: f"theorem {name}" in text for name in LEAN_THEOREMS},
        "PowerBoundEq_def": "def PowerBoundEq" in text,
        "mixed_word_power_lt_absent": "theorem mixed_word_power_lt" not in text,
        "floorPower_odd_sq_lt_cube_absent": (
            "theorem floorPower_odd_sq_lt_cube" not in text
        ),
        "PowerBoundStrict_absent": (
            "structure PowerBoundStrict" not in text
            and "def PowerBoundStrict" not in text
            and "theorem PowerBoundStrict" not in text
        ),
        "PowerHeight_absent": "PowerHeight" not in text,
    }


def classify(
    local_iff: dict[str, Any],
    itinerary_scan: dict[str, Any],
    lean: dict[str, bool],
) -> dict[str, Any]:
    if local_iff["mismatch_count"] or itinerary_scan["local_square_false_count"]:
        return {
            "classification": CLASS_LOCAL_FALSE,
            "reason": "a local power bound is tight at a non-square, or a square fails tightness",
        }
    if itinerary_scan["propagation_false_count"]:
        return {
            "classification": CLASS_PROP_FALSE,
            "reason": "composite envelope equality disagrees with the local-tightness chain",
        }
    lean_ok = lean["sorry_free"] and all(lean[name] for name in LEAN_THEOREMS)
    if lean_ok:
        return {
            "classification": CLASS_GREEN,
            "reason": (
                "Local branch equality is equivalent to a perfect square, and "
                "global envelope equality forces every local inequality to be "
                "tight, hence every relevant state is a square"
            ),
        }
    return {
        "classification": CLASS_STRUCTURED,
        "reason": (
            "equalities exist and all searched witnesses satisfy the local "
            "square chain, but the Lean rigidity API is incomplete"
        ),
    }


def run_probe(*, n_max: int = N_MAX, k_max: int = K_MAX) -> dict[str, Any]:
    local_iff = scan_local_iff(min(LOCAL_IFF_MAX, 10**6) if n_max >= N_MAX else n_max)
    itinerary_scan = scan_itineraries(n_max, k_max)
    squares = [m * m for m in range(2, 51)]
    square_scan = scan_itineraries(0, min(k_max, 4), states=squares)
    return {
        "n_max": n_max,
        "k_max": k_max,
        "local_iff": local_iff,
        "itinerary": itinerary_scan,
        "square_starts": {
            "structured_count": square_scan["structured_count"],
            "propagation_false_count": square_scan["propagation_false_count"],
            "local_square_false_count": square_scan["local_square_false_count"],
        },
        "examples": example_records(),
    }


def probe_payload(*, n_max: int = N_MAX, k_max: int = K_MAX) -> dict[str, Any]:
    scan = run_probe(n_max=n_max, k_max=k_max)
    lean = lean_api_present()
    decision = classify(scan["local_iff"], scan["itinerary"], lean)
    return {
        "experiment": "juggler_power_algebra",
        "engine_control_layer_modified": False,
        "anti_overclaim": dict(ANTI_OVERCLAIM),
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": "local tightness and isqrt squares; powers_equal only as a tiny sanity check",
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    examples = scan["examples"]
    lines = [
        "# Juggler finite-word power algebra and equality rigidity",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment and",
        "not a termination theorem. Mixed-word strictness remains REFUTED.",
        "This page records local square characterizations and equality",
        "propagation of the one-sided envelope.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Does global envelope equality for a realized finite word",
        "                        force every local branch inequality to be tight, and is",
        "                        each local tightness equivalent to the branch input",
        "                        being a perfect square?",
        "Novelty hypothesis      Equality is a rigid chain of exact local square",
        "                        conditions, not mixed-word strictness (already REFUTED).",
        "Falsifier               LOCAL_SQUARE_EQ_FALSE or GLOBAL_EQ_PROPAGATION_FALSE.",
        "Existing machinery      PowerBound, power_bound_follows / power_bound_contracts,",
        "                        floorPower_odd_sq_eq_cube_of_sq, Nat.sqrt, powers_equal.",
        "Maximum Phase-0 scope   Local iff-square theorems; equality-propagation theorem;",
        "                        square-state corollary; square/root computational probe;",
        "                        thin power_bound_word alias.",
        "```",
        "",
        "## Metadata",
        "",
        f"- word layer: `n <= {scan['n_max']}`, `k <= {scan['k_max']}`",
        f"- local iff-square layer: `n <= {scan['local_iff']['n_max']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- local-square mismatches: `{scan['local_iff']['mismatch_count']}`",
        f"- propagation mismatches (tiny independent check): `{scan['itinerary']['propagation_false_count']}`",
        f"- predicted equalities: `{scan['itinerary']['structured_count']}`",
        f"- predicted equalities containing O: `{scan['itinerary']['structured_with_odd']}`",
        f"- predicted both-letter equalities: `{scan['itinerary']['structured_both_letters']}`",
        f"- sorry-free: `{lean['sorry_free']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Local equality",
        "",
        "Even `T(n)^2 = n` iff `n` is a square. Odd `T(n)^2 = n^3` iff `n` is a",
        "square. Search uses `isqrt` only; it does not construct `n^{3^o}`.",
        "",
        f"- even equal count on the iff layer: `{scan['local_iff']['even_equal_count']}`",
        f"- odd equal count on the iff layer: `{scan['local_iff']['odd_equal_count']}`",
        "",
        "## Structured witnesses",
        "",
        f"- word `O` at 9: predicted `{examples['odd_square_nine']['global_equality_predicted']}`,",
        f"  squares `{examples['odd_square_nine']['square_states']}`,",
        f"  independent `{examples['odd_square_nine'].get('independent_global_eq')}`",
        f"- word `EE` at 16: predicted `{examples['even_tower_sixteen']['global_equality_predicted']}`,",
        f"  squares `{examples['even_tower_sixteen']['square_states']}`,",
        f"  trajectory `{examples['even_tower_sixteen']['trajectory']}`",
        f"- word `OO` at 81: predicted `{examples['odd_fourth_eighty_one']['global_equality_predicted']}`,",
        f"  squares `{examples['odd_fourth_eighty_one']['square_states']}`",
        "",
        "Relevant states are branch inputs. The images `27` and `2` need not be squares.",
        "",
        "## Lean",
        "",
    ]
    for name in LEAN_THEOREMS:
        lines.append(f"- `{name}`: `{lean.get(name)}`")
    lines.extend(
        [
            f"- `PowerBoundEq` definition: `{lean.get('PowerBoundEq_def')}`",
            f"- `mixed_word_power_lt` absent: `{lean.get('mixed_word_power_lt_absent')}`",
            f"- `PowerBoundStrict` absent: `{lean.get('PowerBoundStrict_absent')}`",
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
            "Do not census equality words. Do not replace contraction by a strict floor theorem.",
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

"""Exact perfect-power depth versus finite-word envelope saturation.

Not a Research Engine control-layer experiment. Equality is decided by
local integer-square exactness only. No cmp_pow on n^{3^o}. Not a
termination theorem.
"""

from __future__ import annotations

import json
from math import isqrt
from pathlib import Path
from typing import Any, Iterable

from research.juggler_sequence.equality_rigidity import powers_equal
from research.juggler_sequence.power_algebra import is_square, local_tight
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
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_saturation_budget.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_saturation_budget.md"

CLASS_GREEN = "SATURATION_BUDGET_GREEN"
CLASS_DEPTH_GREEN = "POWER_TWO_DEPTH_GREEN"
CLASS_COUNTER = "POWER_TWO_DEPTH_COUNTEREXAMPLE"
CLASS_TOO_WEAK = "POWER_TWO_DEPTH_TOO_WEAK"

N_MAX = 10**4
K_MAX = 8
WORD_K_MAX = 6
TOWER_BITS = 256
SANITY_N_MAX = 200
SANITY_K_MAX = 4

LEAN_THEOREMS = (
    "floorPower_of_pow_two_depth_even",
    "floorPower_of_pow_two_depth_odd",
    "hasPowTwoDepth_even_exact",
    "hasPowTwoDepth_odd_exact",
    "hasPowTwoDepth_ge_two_image_square",
    "hasPowTwoDepth_of_cube",
    "localsTight_implies_power_bound_eq",
    "power_bound_eq_implies_pow_two_depth",
    "power_bound_eq_contracts_pow_two_lb",
)


def square_depth(n: int) -> int | None:
    """Maximal r such that n = a^{2^r} with a not a square.

    Returns None for the infinite-depth states 0 and 1.
    """

    if n < 0:
        raise ValueError("square_depth is defined on nonnegative integers")
    if n <= 1:
        return None
    r = 0
    current = n
    while is_square(current):
        current = isqrt(current)
        r += 1
        if current <= 1:
            return None
    return r


def has_pow_two_depth(n: int, r: int) -> bool:
    """Computational form of HasPowTwoDepth: depth at least r."""

    if r < 0:
        raise ValueError("depth cannot be negative")
    if r == 0 or n <= 1:
        return True
    depth = square_depth(n)
    return depth is not None and depth >= r


def tower(base: int, r: int, *, bit_limit: int = TOWER_BITS) -> int | None:
    """base^{2^r} by r successive squares, or None if the bit budget is hit."""

    if base < 0 or r < 0:
        raise ValueError("tower requires nonnegative base and depth")
    value = base
    for _ in range(r):
        if value.bit_length() * 2 > bit_limit:
            return None
        value *= value
    return value


def saturation_prefix(n: int, max_k: int) -> dict[str, Any]:
    """Longest exact-equality prefix starting at n, up to max_k steps."""

    if n < 1 or max_k < 0:
        raise ValueError("saturation_prefix requires n >= 1 and max_k >= 0")
    path = [n]
    letters: list[str] = []
    current = n
    for _ in range(max_k):
        if not local_tight(current):
            break
        letters.append("O" if current % 2 else "E")
        current = floor_power(current)
        path.append(current)
    word = "".join(letters)
    depth = square_depth(n)
    return {
        "start": n,
        "word": word,
        "length": len(word),
        "odd_count": odd_count(word),
        "square_depth": depth,
        "infinite_depth": depth is None,
        "trajectory": path,
        "contracts": bool(word) and 3 ** odd_count(word) < 2 ** len(word),
        "budget_ok": depth is None or depth >= len(word),
    }


def saturates_word(n: int, word: str) -> bool:
    """True iff every branch input along word is locally exact."""

    current = n
    for letter in word:
        if letter == "E":
            if current % 2 != 0 or not local_tight(current):
                return False
        elif letter == "O":
            if current % 2 != 1 or not local_tight(current):
                return False
        else:
            raise ValueError(f"unknown letter {letter!r}")
        current = floor_power(current)
    return True


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


def scan_domain(n_max: int, k_max: int, *, n_min: int = 2) -> dict[str, Any]:
    counterexamples: list[dict[str, Any]] = []
    saturations: list[dict[str, Any]] = []
    contracting: list[dict[str, Any]] = []
    mixed: list[dict[str, Any]] = []
    for n in range(n_min, n_max + 1):
        rec = saturation_prefix(n, k_max)
        if rec["length"] == 0:
            continue
        saturations.append(rec)
        if not rec["budget_ok"]:
            counterexamples.append(rec)
        if rec["contracts"]:
            contracting.append(rec)
        if "O" in rec["word"] and "E" in rec["word"]:
            mixed.append(rec)
    return {
        "n_min": n_min,
        "n_max": n_max,
        "k_max": k_max,
        "saturation_count": len(saturations),
        "counterexamples": counterexamples[:16],
        "counterexample_count": len(counterexamples),
        "contracting_equalities": contracting[:16],
        "contracting_count": len(contracting),
        "mixed_count": len(mixed),
        "max_saturation_length": max((rec["length"] for rec in saturations), default=0),
        "samples": saturations[:24],
    }


def smallest_word_hits(k_max: int, n_max: int) -> list[dict[str, Any]]:
    """Smallest n in 2..n_max that saturates each nonempty word of length <= k_max."""

    records: list[dict[str, Any]] = []
    for k in range(1, k_max + 1):
        for mask in range(1 << k):
            word = "".join("O" if (mask >> i) & 1 else "E" for i in range(k))
            hit: dict[str, Any] | None = None
            for n in range(2, n_max + 1):
                if saturates_word(n, word):
                    depth = square_depth(n)
                    hit = {
                        "word": word,
                        "length": k,
                        "odd_count": odd_count(word),
                        "start": n,
                        "square_depth": depth,
                        "budget_ok": depth is None or depth >= k,
                        "contracts": 3 ** odd_count(word) < 2**k,
                    }
                    break
            records.append(
                hit
                if hit is not None
                else {
                    "word": word,
                    "length": k,
                    "odd_count": odd_count(word),
                    "start": None,
                    "square_depth": None,
                    "budget_ok": True,
                    "contracts": 3 ** odd_count(word) < 2**k,
                    "unrealized_in_bound": True,
                }
            )
    return records


def tower_family(bases: Iterable[int], r_max: int) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    for base in bases:
        if base < 2:
            continue
        for r in range(1, r_max + 1):
            n = tower(base, r)
            if n is None:
                continue
            rec = saturation_prefix(n, r + 1)
            rec["tower_base"] = base
            rec["tower_r"] = r
            rec["has_pow_two_depth_r"] = has_pow_two_depth(n, r)
            records.append(rec)
    return records


def example_records() -> dict[str, Any]:
    nine = saturation_prefix(9, 1)
    nine["independent_global_eq"] = tiny_global_eq(9, "O", 27)
    eighty_one = saturation_prefix(81, 2)
    eighty_one["independent_global_eq"] = tiny_global_eq(81, "OO", itinerary(81, 2)[2])
    sixteen = saturation_prefix(16, 2)
    sixteen["independent_global_eq"] = tiny_global_eq(16, "EE", itinerary(16, 2)[2])
    two_fifty_six = saturation_prefix(256, 3)
    return {
        "odd_square_nine": nine,
        "odd_fourth_eighty_one": eighty_one,
        "even_tower_sixteen": sixteen,
        "even_tower_two_fifty_six": two_fifty_six,
        "depth_one_not_square_image": {
            "start": 36,
            "square_depth": square_depth(36),
            "prefix": saturation_prefix(36, 3),
        },
        "word_of_nine": word_of(itinerary(9, 1)),
        "word_of_sixteen": word_of(itinerary(16, 2)),
    }


def lean_api_present() -> dict[str, bool]:
    text = juggler_text()
    return {
        "sorry_free": "sorry" not in text and "admit" not in text,
        **{name: f"theorem {name}" in text for name in LEAN_THEOREMS},
        "HasPowTwoDepth_def": "def HasPowTwoDepth" in text,
        "PowerHeight_absent": "PowerHeight" not in text,
        "mixed_word_power_lt_absent": "theorem mixed_word_power_lt" not in text,
    }


def classify(
    domain: dict[str, Any],
    words: list[dict[str, Any]],
    towers: list[dict[str, Any]],
    lean: dict[str, bool],
) -> dict[str, Any]:
    word_counters = [rec for rec in words if not rec["budget_ok"]]
    tower_counters = [rec for rec in towers if not rec["budget_ok"]]
    if domain["counterexample_count"] or word_counters or tower_counters:
        return {
            "classification": CLASS_COUNTER,
            "depth_status": CLASS_COUNTER,
            "reason": (
                "a saturated word of length k starts at a state whose "
                "repeated-square depth is < k"
            ),
        }
    lean_ok = lean["sorry_free"] and lean["HasPowTwoDepth_def"] and all(
        lean[name] for name in LEAN_THEOREMS
    )
    if lean_ok:
        return {
            "classification": CLASS_GREEN,
            "depth_status": CLASS_DEPTH_GREEN,
            "reason": (
                "Each exact branch consumes one unit of 2-adic perfect-power "
                "depth, so a realized equality word of length k forces the "
                "start to be a 2^k-th power"
            ),
        }
    if domain["saturation_count"] and domain["counterexample_count"] == 0:
        return {
            "classification": CLASS_TOO_WEAK,
            "depth_status": CLASS_TOO_WEAK,
            "reason": (
                "no computational counterexample, but the Lean budget API "
                "is incomplete"
            ),
        }
    return {
        "classification": CLASS_TOO_WEAK,
        "depth_status": CLASS_TOO_WEAK,
        "reason": "the simple depth count is not yet confirmed",
    }


def run_probe(*, n_max: int = N_MAX, k_max: int = K_MAX) -> dict[str, Any]:
    domain = scan_domain(n_max, k_max)
    word_k = min(WORD_K_MAX, k_max)
    words = smallest_word_hits(word_k, n_max)
    towers = tower_family(range(2, 31), 4)
    odd_towers = tower_family(range(3, 32, 2), 4)
    return {
        "n_max": n_max,
        "k_max": k_max,
        "domain": domain,
        "words": {
            "k_max": word_k,
            "records": words,
            "realized": sum(1 for rec in words if rec["start"] is not None),
            "counterexample_count": sum(1 for rec in words if not rec["budget_ok"]),
            "mixed_realized": sum(
                1
                for rec in words
                if rec["start"] is not None and "O" in rec["word"] and "E" in rec["word"]
            ),
        },
        "towers": {
            "records": towers,
            "count": len(towers),
            "counterexample_count": sum(1 for rec in towers if not rec["budget_ok"]),
            "odd_count": len(odd_towers),
            "odd_counterexample_count": sum(
                1 for rec in odd_towers if not rec["budget_ok"]
            ),
        },
        "examples": example_records(),
    }


def probe_payload(*, n_max: int = N_MAX, k_max: int = K_MAX) -> dict[str, Any]:
    scan = run_probe(n_max=n_max, k_max=k_max)
    lean = lean_api_present()
    decision = classify(scan["domain"], scan["words"]["records"], scan["towers"]["records"], lean)
    return {
        "experiment": "juggler_saturation_budget",
        "engine_control_layer_modified": False,
        "anti_overclaim": dict(ANTI_OVERCLAIM),
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "local tightness and repeated isqrt depth; powers_equal only as a "
            "tiny sanity check; no cmp_pow on n^{3^o}"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    examples = scan["examples"]
    domain = scan["domain"]
    words = scan["words"]
    towers = scan["towers"]
    lines = [
        "# Juggler exact perfect-power dynamics and saturation budget",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment and",
        "not a termination theorem. Mixed-word strictness remains REFUTED.",
        "This page records the 2-adic perfect-power budget of envelope",
        "equality.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Does k consecutive exact envelope branches require",
        "                        the start to be a 2^k-th power?",
        "Novelty hypothesis      Each exact E/O step consumes one unit of 2-adic",
        "                        perfect-power depth.",
        "Falsifier               POWER_TWO_DEPTH_COUNTEREXAMPLE.",
        "Existing machinery      PowerBoundEq, power_bound_eq_implies_square,",
        "                        floorPower_of_even_sq / floorPower_of_odd_sq,",
        "                        isSquare_pow_three_iff.",
        "Maximum Phase-0 scope   Exact a^(2^r) transitions; HasPowTwoDepth drop",
        "                        lemmas; budget theorem if it holds; square-depth",
        "                        probe without cmp_pow or PowerHeight.",
        "```",
        "",
        "## Metadata",
        "",
        f"- domain layer: `n <= {scan['n_max']}`, `k <= {scan['k_max']}`",
        f"- prescribed-word layer: `k <= {words['k_max']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- depth status: **{decision['depth_status']}**",
        f"- domain saturations: `{domain['saturation_count']}`",
        f"- domain counterexamples: `{domain['counterexample_count']}`",
        f"- mixed saturations on the domain: `{domain['mixed_count']}`",
        f"- contracting saturations on the domain: `{domain['contracting_count']}`",
        f"- prescribed words realized in bound: `{words['realized']}`",
        f"- prescribed mixed realizations: `{words['mixed_realized']}`",
        f"- tower counterexamples: `{towers['counterexample_count']}`",
        f"- sorry-free: `{lean['sorry_free']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Local transitions",
        "",
        "If `n = a^{2^r}` and `r >= 1`, an exact even branch is",
        "`a^{2^{r-1}}` and an exact odd branch is `a^{3 · 2^{r-1}}`.",
        "Both drop one factor of `2` from the exponent. The next state is",
        "again a square iff `r >= 2`, or iff the remaining base is itself",
        "a square when `r = 1`.",
        "",
        f"- word `O` at 9: depth `{examples['odd_square_nine']['square_depth']}`,",
        f"  length `{examples['odd_square_nine']['length']}`,",
        f"  independent `{examples['odd_square_nine'].get('independent_global_eq')}`",
        f"- word `EE` at 16: depth `{examples['even_tower_sixteen']['square_depth']}`,",
        f"  length `{examples['even_tower_sixteen']['length']}`,",
        f"  trajectory `{examples['even_tower_sixteen']['trajectory']}`",
        f"- word `OO` at 81: depth `{examples['odd_fourth_eighty_one']['square_depth']}`,",
        f"  length `{examples['odd_fourth_eighty_one']['length']}`",
        f"- word `EEE` at 256: depth `{examples['even_tower_two_fifty_six']['square_depth']}`,",
        f"  length `{examples['even_tower_two_fifty_six']['length']}`",
        f"- depth 1 at 36: saturates `{examples['depth_one_not_square_image']['prefix']['word']}`",
        "  and then stops; the image 6 is not a square",
        "",
        "Exact steps preserve parity, so a mixed word cannot saturate.",
        "All-even equality is formally contracting and meets the lower",
        "bound `2^{2^k}` at the towers `2^{2^k}`.",
        "",
        "## Lean",
        "",
    ]
    for name in LEAN_THEOREMS:
        lines.append(f"- `{name}`: `{lean.get(name)}`")
    lines.extend(
        [
            f"- `HasPowTwoDepth` definition: `{lean.get('HasPowTwoDepth_def')}`",
            f"- `PowerHeight` absent: `{lean.get('PowerHeight_absent')}`",
            f"- `mixed_word_power_lt` absent: `{lean.get('mixed_word_power_lt_absent')}`",
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
            "This is a finite local budget, not a global halt result.",
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

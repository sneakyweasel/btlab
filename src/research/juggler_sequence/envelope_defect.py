"""First-defect propagation for the finite-word Juggler envelope.

Not a Research Engine control-layer experiment. Local defects use
isqrt only. Global Δ is computed only on a tiny bit budget. Not a
termination theorem and not an equality-word census.
"""

from __future__ import annotations

import json
from collections import defaultdict
from math import isqrt
from pathlib import Path
from typing import Any

from research.juggler_sequence.equality_language import is_monochrome
from research.juggler_sequence.power_algebra import is_square, local_tight
from research.juggler_sequence.power_itineraries import (
    ANTI_OVERCLAIM,
    LEAN_PATH,
    floor_power,
    itinerary,
    odd_count,
    word_of,
)
from research.juggler_sequence.saturation_budget import saturation_prefix
from research.juggler_sequence.lean_paths import juggler_text

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_envelope_defect.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_envelope_defect.md"

CLASS_QUANT = "DEFECT_QUANTITATIVE_GREEN"
CLASS_PROP = "DEFECT_PROPAGATION_GREEN"
CLASS_SUFFIX = "DEFECT_SUFFIX_DEPENDENT"
CLASS_NO_SIMPLE = "DEFECT_NO_SIMPLE_BOUND"
CLASS_INCOMPLETE = "DEFECT_INCOMPLETE"

N_MAX = 400
K_MAX = 6
BIT_LIMIT = 80
LOCAL_SCAN_MAX = 500

LEAN_THEOREMS = (
    "localDefectEven_eq_zero_iff",
    "localDefectOdd_eq_zero_iff",
    "strict_power_bound_append_even",
    "strict_power_bound_append_odd",
    "strict_power_bound_from",
    "power_bound_word_strict",
    "power_bound_defect_ge_one",
    "power_deficit_append_even",
    "power_deficit_append_odd",
    "power_deficit_from",
    "local_defect_even_le_suffix_deficit",
    "local_defect_odd_le_suffix_deficit",
)

PROP_THEOREMS = (
    "strict_power_bound_append_even",
    "strict_power_bound_append_odd",
    "strict_power_bound_from",
    "power_bound_word_strict",
    "power_bound_defect_ge_one",
)

QUANT_THEOREMS = (
    "power_deficit_append_even",
    "power_deficit_append_odd",
    "power_deficit_from",
    "local_defect_even_le_suffix_deficit",
    "local_defect_odd_le_suffix_deficit",
)


def local_defect_even(x: int) -> int:
    image = floor_power(x)
    return x - image * image


def local_defect_odd(x: int) -> int:
    image = floor_power(x)
    return x * x * x - image * image


def local_defect(x: int) -> int:
    if x % 2 == 0:
        return local_defect_even(x)
    return local_defect_odd(x)


def first_nonexact_index(path: tuple[int, ...]) -> int | None:
    for index, state in enumerate(path[:-1]):
        if not local_tight(state):
            return index
    return None


def tiny_deficit(n: int, image: int, k: int, o: int, *, bit_limit: int = BIT_LIMIT) -> int | None:
    """Δ = n^{3^o} - image^{2^k}, or None if either power exceeds the bit budget."""

    if k < 0 or o < 0:
        raise ValueError("tiny_deficit requires nonnegative exponents")
    if n < 0 or image < 0:
        raise ValueError("tiny_deficit requires nonnegative bases")
    left_bits = max(1, 3**o) * max(1, n.bit_length())
    right_bits = max(1, 1 << k) * max(1, image.bit_length())
    if left_bits > bit_limit or right_bits > bit_limit:
        return None
    return n ** (3**o) - image ** (1 << k)


def defect_record(n: int, k: int, *, bit_limit: int = BIT_LIMIT) -> dict[str, Any] | None:
    if n < 1 or k < 1:
        raise ValueError("defect_record requires n >= 1 and k >= 1")
    path = itinerary(n, k)
    word = word_of(path)
    index = first_nonexact_index(path)
    if index is None:
        return None
    state = path[index]
    image = path[-1]
    odds = odd_count(word)
    gap = tiny_deficit(n, image, k, odds, bit_limit=bit_limit)
    return {
        "word": word,
        "n": n,
        "first_nonexact_position": index,
        "first_nonexact_branch": word[index],
        "local_state": state,
        "local_defect": local_defect(state),
        "suffix_length": k - 1 - index,
        "global_deficit": gap,
        "odd_count": odds,
        "monochrome": is_monochrome(word),
        "length": k,
    }


def scan_defects(
    n_max: int,
    k_max: int,
    *,
    n_min: int = 2,
    bit_limit: int = BIT_LIMIT,
) -> dict[str, Any]:
    records: list[dict[str, Any]] = []
    unit_false = 0
    local_false = 0
    computed = 0
    mixed_computed = 0
    skipped = 0
    mixed_total = 0
    for n in range(n_min, n_max + 1):
        for k in range(1, k_max + 1):
            rec = defect_record(n, k, bit_limit=bit_limit)
            if rec is None:
                continue
            if not rec["monochrome"]:
                mixed_total += 1
            gap = rec["global_deficit"]
            if gap is None:
                skipped += 1
                continue
            computed += 1
            if not rec["monochrome"]:
                mixed_computed += 1
                if gap < 1:
                    unit_false += 1
            if gap < rec["local_defect"]:
                local_false += 1
            if len(records) < 24:
                records.append(rec)
    return {
        "n_min": n_min,
        "n_max": n_max,
        "k_max": k_max,
        "bit_limit": bit_limit,
        "computed_count": computed,
        "mixed_total": mixed_total,
        "mixed_computed": mixed_computed,
        "skipped_bit_budget": skipped,
        "unit_false_count": unit_false,
        "local_false_count": local_false,
        "samples": records,
    }


def suffix_amplification(
    n_max: int,
    k_max: int,
    *,
    n_min: int = 2,
    bit_limit: int = BIT_LIMIT,
) -> dict[str, Any]:
    """Same first defect, longer realized suffixes: Δ should not fall."""

    decreases = 0
    compared = 0
    examples: list[dict[str, Any]] = []
    for n in range(n_min, n_max + 1):
        long = defect_record(n, k_max, bit_limit=bit_limit)
        if long is None:
            continue
        start = long["first_nonexact_position"] + 1
        prev: int | None = None
        for k in range(start, k_max + 1):
            rec = defect_record(n, k, bit_limit=bit_limit)
            if rec is None or rec["global_deficit"] is None:
                prev = None
                continue
            if prev is not None:
                compared += 1
                if rec["global_deficit"] < prev:
                    decreases += 1
                    if len(examples) < 4:
                        examples.append(
                            {
                                "n": n,
                                "k": k,
                                "previous": prev,
                                "global_deficit": rec["global_deficit"],
                            }
                        )
            prev = rec["global_deficit"]
    return {
        "compared": compared,
        "decreases": decreases,
        "examples": examples,
    }


def permutation_compare(
    n_max: int,
    k: int,
    *,
    n_min: int = 2,
    bit_limit: int = BIT_LIMIT,
) -> dict[str, Any]:
    """Same (k, o), different first-defect position: no assumed order."""

    buckets: dict[tuple[int, int], list[dict[str, Any]]] = defaultdict(list)
    for n in range(n_min, n_max + 1):
        rec = defect_record(n, k, bit_limit=bit_limit)
        if rec is None or rec["global_deficit"] is None or rec["monochrome"]:
            continue
        key = (rec["length"], rec["odd_count"])
        buckets[key].append(rec)
    disagreements = 0
    compared = 0
    samples: list[dict[str, Any]] = []
    for key, group in buckets.items():
        positions = {item["first_nonexact_position"] for item in group}
        if len(positions) < 2:
            continue
        by_pos: dict[int, list[int]] = defaultdict(list)
        for item in group:
            by_pos[item["first_nonexact_position"]].append(item["global_deficit"])
        pos_list = sorted(by_pos)
        for left, right in zip(pos_list, pos_list[1:]):
            compared += 1
            min_left = min(by_pos[left])
            min_right = min(by_pos[right])
            if min_left == min_right:
                continue
            disagreements += 1
            if len(samples) < 6:
                samples.append(
                    {
                        "k": key[0],
                        "odd_count": key[1],
                        "position_a": left,
                        "position_b": right,
                        "min_delta_a": min_left,
                        "min_delta_b": min_right,
                        "order": "later_larger" if min_right > min_left else "later_smaller",
                    }
                )
    return {
        "groups_with_split_positions": compared,
        "mean_order_disagreements": disagreements,
        "samples": samples,
    }


def local_structure(n_max: int) -> dict[str, Any]:
    even_min = None
    odd_min = None
    even_r_is_defect = True
    odd_remainder_ok = True
    odd_one = None
    for n in range(2, n_max + 1):
        if is_square(n):
            continue
        if n % 2 == 0:
            q = isqrt(n)
            remainder = n - q * q
            defect = local_defect_even(n)
            if remainder != defect:
                even_r_is_defect = False
            if not (0 < remainder < 2 * q + 1):
                even_r_is_defect = False
            if even_min is None or defect < even_min["local_defect"]:
                even_min = {"n": n, "local_defect": defect, "q": q, "r": remainder}
        else:
            cube = n * n * n
            q = isqrt(cube)
            remainder = cube - q * q
            defect = local_defect_odd(n)
            if remainder != defect:
                odd_remainder_ok = False
            if not (0 < remainder < 2 * q + 1):
                odd_remainder_ok = False
            if defect == 1 and odd_one is None:
                odd_one = n
            if odd_min is None or defect < odd_min["local_defect"]:
                odd_min = {"n": n, "local_defect": defect, "q": q, "r": remainder}
    return {
        "n_max": n_max,
        "even_remainder_is_defect": even_r_is_defect,
        "odd_cube_remainder_is_defect": odd_remainder_ok,
        "even_min": even_min,
        "odd_min": odd_min,
        "odd_defect_one": odd_one,
    }


def example_records() -> dict[str, Any]:
    ten = defect_record(10, 2)
    fifteen = defect_record(15, 2)
    nine_mixed = defect_record(9, 3)
    thirty_six = defect_record(36, 4)
    two = defect_record(2, 1)
    return {
        "even_start_ten": ten,
        "odd_start_fifteen": fifteen,
        "exact_odd_prefix_nine": nine_mixed,
        "exact_even_prefix_thirty_six": thirty_six,
        "unit_even_two": two,
        "saturation_nine": saturation_prefix(9, 1),
        "word_O_at_nine_is_exact": defect_record(9, 1) is None,
    }


def lean_api_present() -> dict[str, bool]:
    text = juggler_text()
    return {
        "sorry_free": "sorry" not in text and "admit" not in text,
        **{name: f"theorem {name}" in text for name in LEAN_THEOREMS},
        "localDefectEven_def": "def localDefectEven" in text,
        "localDefectOdd_def": "def localDefectOdd" in text,
        "StrictPowerBound_def": "def StrictPowerBound" in text,
        "powerDeficit_def": "def powerDeficit" in text,
        "PowerHeight_absent": "PowerHeight" not in text,
        "PowerBoundStrict_absent": (
            "structure PowerBoundStrict" not in text
            and "def PowerBoundStrict" not in text
            and "theorem PowerBoundStrict" not in text
        ),
        "mixed_word_power_lt_absent": "theorem mixed_word_power_lt" not in text,
    }


def classify(
    scan: dict[str, Any],
    suffixes: dict[str, Any],
    lean: dict[str, bool],
) -> dict[str, Any]:
    if scan["unit_false_count"]:
        return {
            "classification": CLASS_NO_SIMPLE,
            "reason": "a computed non-monochrome deficit was smaller than 1",
        }
    if scan["local_false_count"]:
        return {
            "classification": CLASS_SUFFIX,
            "reason": (
                "positivity held, but a computed global deficit fell "
                "below the first local defect"
            ),
        }
    if suffixes["decreases"]:
        return {
            "classification": CLASS_SUFFIX,
            "reason": (
                "a longer realized suffix decreased the numeric deficit, "
                "so magnitude is not monotone in suffix length"
            ),
        }
    lean_ok = lean["sorry_free"] and all(lean[name] for name in LEAN_THEOREMS)
    lean_quant = all(lean[name] for name in QUANT_THEOREMS)
    lean_prop = all(lean[name] for name in PROP_THEOREMS)
    if lean_ok and lean_quant and scan["computed_count"]:
        return {
            "classification": CLASS_QUANT,
            "reason": (
                "A positive first local defect persists through every realized "
                "suffix, and the final envelope deficit is at least that defect"
            ),
        }
    if lean["sorry_free"] and lean_prop:
        return {
            "classification": CLASS_PROP,
            "reason": (
                "StrictPowerBound appends preserve positivity, so a "
                "non-monochrome realized word lies strictly below the envelope"
            ),
        }
    return {
        "classification": CLASS_INCOMPLETE,
        "reason": "the defect Lean API is incomplete",
    }


def run_probe(*, n_max: int = N_MAX, k_max: int = K_MAX) -> dict[str, Any]:
    scan = scan_defects(n_max, k_max)
    suffixes = suffix_amplification(n_max, k_max)
    perms = permutation_compare(n_max, min(4, k_max))
    return {
        "n_max": n_max,
        "k_max": k_max,
        "scan": scan,
        "suffixes": suffixes,
        "permutations": perms,
        "local_structure": local_structure(LOCAL_SCAN_MAX),
        "examples": example_records(),
    }


def probe_payload(*, n_max: int = N_MAX, k_max: int = K_MAX) -> dict[str, Any]:
    scan = run_probe(n_max=n_max, k_max=k_max)
    lean = lean_api_present()
    decision = classify(scan["scan"], scan["suffixes"], lean)
    return {
        "experiment": "juggler_envelope_defect",
        "engine_control_layer_modified": False,
        "anti_overclaim": dict(ANTI_OVERCLAIM),
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "first non-exact branch via local tightness and isqrt; "
            "global Δ only inside a tiny bit budget; no cmp_pow census"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    defects = scan["scan"]
    examples = scan["examples"]
    local = scan["local_structure"]
    suffixes = scan["suffixes"]
    perms = scan["permutations"]
    lines = [
        "# Juggler finite-word envelope defect and strictness",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment and",
        "not a termination theorem. Mixed-word *local* strictness remains",
        "REFUTED. This page records the distance from the one-sided envelope",
        "after the first non-exact branch.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Can the first non-exact branch produce a",
        "                        compositional lower bound on Δ_w(n)?",
        "Novelty hypothesis      A local defect δ>0 persists through suffix",
        "                        power maps and yields a reusable strict bound.",
        "Falsifier               DEFECT_NO_SIMPLE_BOUND",
        "Existing machinery      PowerBound, PowerBoundEq, extremal iff,",
        "                        local even/odd square inequalities",
        "Maximum Phase-0 scope   Local defects; StrictPowerBound + append;",
        "                        non-monochrome ⇒ strict; first-defect probe",
        "                        without huge powers. No PowerHeight, no engine edits.",
        "```",
        "",
        "## Metadata",
        "",
        f"- domain layer: `n <= {scan['n_max']}`, `k <= {scan['k_max']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- computed deficits: `{defects['computed_count']}`",
        f"- mixed computed: `{defects['mixed_computed']}`",
        f"- bit-budget skips: `{defects['skipped_bit_budget']}`",
        f"- unit falsifiers: `{defects['unit_false_count']}`",
        f"- Δ < δ_j falsifiers: `{defects['local_false_count']}`",
        f"- suffix decreases: `{suffixes['decreases']}`",
        f"- sorry-free: `{lean['sorry_free']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Local defects",
        "",
        "Even: `δ_E(x) = x - T(x)^2`. If `x = q^2 + r` with `0 < r < 2q+1`,",
        "then `T(x) = q` and `δ_E(x) = r`.",
        "",
        "Odd: `δ_O(x) = x^3 - T(x)^2`, the integer remainder of `x^3`",
        "under `isqrt`.",
        "",
        f"- even remainder identity: `{local['even_remainder_is_defect']}`",
        f"- odd cube-remainder identity: `{local['odd_cube_remainder_is_defect']}`",
        f"- smallest even non-square defect: `{local['even_min']}`",
        f"- smallest odd non-square defect: `{local['odd_min']}`",
        f"- odd defect 1 in the local window: `{local['odd_defect_one']}`",
        "",
        "## Witnesses",
        "",
        f"- word `EO` at 10: first defect `{examples['even_start_ten']['local_defect']}`,",
        f"  Δ `{examples['even_start_ten']['global_deficit']}`",
        f"- word `OE` at 15: first defect `{examples['odd_start_fifteen']['local_defect']}`,",
        f"  Δ `{examples['odd_start_fifteen']['global_deficit']}`",
        f"- word `OOE` at 9: first defect at 27, δ `{examples['exact_odd_prefix_nine']['local_defect']}`,",
        f"  Δ `{examples['exact_odd_prefix_nine']['global_deficit']}`",
        f"- word `EEEO` at 36: first defect at 6, δ `{examples['exact_even_prefix_thirty_six']['local_defect']}`,",
        f"  Δ `{examples['exact_even_prefix_thirty_six']['global_deficit']}`",
        f"- word `E` at 2: unit defect, Δ `{examples['unit_even_two']['global_deficit']}`",
        f"- word `O` at 9 has no first defect: `{examples['word_O_at_nine_is_exact']}`",
        "",
        "Same-count mixed itineraries with different first-defect positions do not",
        "obey a position-only order. The certified lower bound uses the first",
        f"local defect, not the letter counts. Split groups: `{perms['groups_with_split_positions']}`.",
        "",
        "## Lean",
        "",
    ]
    for name in LEAN_THEOREMS:
        lines.append(f"- `{name}`: `{lean.get(name)}`")
    lines.extend(
        [
            f"- `StrictPowerBound` definition: `{lean.get('StrictPowerBound_def')}`",
            f"- `powerDeficit` definition: `{lean.get('powerDeficit_def')}`",
            f"- `PowerHeight` absent: `{lean.get('PowerHeight_absent')}`",
            f"- `PowerBoundStrict` absent: `{lean.get('PowerBoundStrict_absent')}`",
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
            "This is a finite-word defect statement, not a global halt result.",
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

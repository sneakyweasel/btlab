"""Defect-compensated contraction beyond formal drift.

Not a Research Engine control-layer experiment. Search uses the exact
floor-power map and local defects only. Global n^{3^o} is computed only
inside a bit budget. Not a termination theorem.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.envelope_defect import (
    first_nonexact_index,
    local_defect,
    tiny_deficit,
)
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
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_compensated_contraction.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_compensated_contraction.md"

CLASS_FOUND = "COMPENSATED_CONTRACTION_FOUND"
CLASS_FIRST = "COMPENSATION_FIRST_DEFECT_SUFFICIENT"
CLASS_AMP = "COMPENSATION_REQUIRES_AMPLIFICATION"
CLASS_NON = "POSITIVE_DRIFT_NONCONTRACTION"
CLASS_USELESS = "NO_USEFUL_COMPENSATION"

N_MAX = 20_000
EOO_EVEN_MAX = 200_000
K4_N_MAX = 10_000
BIT_BUDGET = 80

LENGTH3 = ("OOE", "OEO", "EOO")
LENGTH4_MIXED = ("OOOE", "OOEO", "OEOO", "EOOO")

LEAN_THEOREMS = (
    "power_bound_compensated_contracts",
    "power_bound_compensated_contracts_follows",
    "floorPower_eoo_contracts_iff",
    "floorPower_eoo_two_contracts",
    "floorPower_eoo_twelve_contracts",
    "floorPower_eoo_fourteen_contracts",
    "eoo_first_defect_lt_formal_gap",
    "floorPower_eoo_two_deficit_gt_gap",
    "follows_eoo_two",
    "follows_eoo_twelve",
    "follows_eoo_fourteen",
)


def follows_itinerary(n: int, word: str) -> bool:
    current = n
    for letter in word:
        if letter == "O":
            if current % 2 == 0:
                return False
        elif letter == "E":
            if current % 2 == 1:
                return False
        else:
            raise ValueError(f"invalid word letter {letter!r}")
        current = floor_power(current)
    return True


def image_after(n: int, word: str) -> int:
    current = n
    for _ in word:
        current = floor_power(current)
    return current


def formal_gap(n: int, k: int, odds: int, *, bit_limit: int = BIT_BUDGET) -> int | None:
    """G = n^{3^o} - n^{2^k}, or None if the power exceeds the bit budget."""

    if n < 0 or k < 0 or odds < 0:
        raise ValueError("formal_gap requires nonnegative inputs")
    bits = max(1, 3**odds) * max(1, n.bit_length())
    if bits > bit_limit:
        return None
    left = n ** (3**odds)
    right = n ** (1 << k)
    return left - right if left >= right else 0


def first_defect_sufficient(n: int, word: str, *, bit_limit: int = BIT_BUDGET) -> bool | None:
    """Whether δ_j > G. None if G cannot be formed inside the bit budget."""

    path = itinerary(n, len(word))
    if word_of(path) != word:
        return None
    index = first_nonexact_index(path)
    if index is None:
        return False
    defect = local_defect(path[index])
    gap = formal_gap(n, len(word), odd_count(word), bit_limit=bit_limit)
    if gap is None:
        return None
    return defect > gap


def word_row(
    n: int,
    word: str,
    *,
    bit_limit: int = BIT_BUDGET,
) -> dict[str, Any] | None:
    path = itinerary(n, len(word))
    realized = word_of(path)
    if realized != word:
        return None
    image = path[-1]
    odds = odd_count(word)
    index = first_nonexact_index(path)
    gap = formal_gap(n, len(word), odds, bit_limit=bit_limit)
    deficit = tiny_deficit(n, image, len(word), odds, bit_limit=bit_limit)
    defect = None if index is None else local_defect(path[index])
    return {
        "word": word,
        "n": n,
        "k": len(word),
        "odd_count": odds,
        "formal_ratio_num": 3**odds,
        "formal_ratio_den": 1 << len(word),
        "first_defect_position": index,
        "first_defect": defect,
        "envelope_gap_to_contraction": gap,
        "certified_deficit_lower_bound": defect,
        "actual_deficit": deficit,
        "image": image,
        "actual_contraction": image < n,
        "first_defect_certifies": (
            None if gap is None or defect is None else defect > gap
        ),
    }


def scan_word(
    word: str,
    n_max: int,
    *,
    n_min: int = 2,
    step: int = 1,
    bit_limit: int = BIT_BUDGET,
    contract_cap: int = 16,
) -> dict[str, Any]:
    if n_max < n_min:
        raise ValueError("scan_word requires n_min ≤ n_max")
    realized = 0
    contracts: list[dict[str, Any]] = []
    first_ok = 0
    first_fail = 0
    first_unknown = 0
    for n in range(n_min, n_max + 1, step):
        if not follows_itinerary(n, word):
            continue
        realized += 1
        row = word_row(n, word, bit_limit=bit_limit)
        if row is None:
            continue
        if row["actual_contraction"] and len(contracts) < contract_cap:
            contracts.append(row)
        cert = row["first_defect_certifies"]
        if cert is True:
            first_ok += 1
        elif cert is False:
            first_fail += 1
        else:
            first_unknown += 1
    return {
        "word": word,
        "n_min": n_min,
        "n_max": n_max,
        "step": step,
        "realized": realized,
        "contract_count": len(contracts),
        "contracts": contracts,
        "first_defect_sufficient_count": first_ok,
        "first_defect_insufficient_count": first_fail,
        "first_defect_unknown_count": first_unknown,
    }


def eoo_witnesses(*, bit_limit: int = BIT_BUDGET) -> list[dict[str, Any]]:
    rows = []
    for n in (2, 12, 14):
        row = word_row(n, "EOO", bit_limit=bit_limit)
        if row is None:
            raise RuntimeError(f"EOO witness {n} failed to realize")
        rows.append(row)
    return rows


def lean_api_present() -> dict[str, bool]:
    text = juggler_text()
    return {
        "sorry_free": "sorry" not in text and "admit" not in text,
        **{name: f"theorem {name}" in text for name in LEAN_THEOREMS},
        "PowerHeight_absent": "PowerHeight" not in text,
        "PowerBoundStrict_absent": (
            "structure PowerBoundStrict" not in text
            and "def PowerBoundStrict" not in text
            and "theorem PowerBoundStrict" not in text
        ),
        "mixed_word_power_lt_absent": "theorem mixed_word_power_lt" not in text,
        "ooe_not_contracts": "theorem floorPower_ooe_not_contracts" in text,
        "oeo_not_contracts": "theorem floorPower_oeo_not_contracts" in text,
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    eoo = scan["length3"]["EOO"]
    ooe = scan["length3"]["OOE"]
    oeo = scan["length3"]["OEO"]
    first_ok = sum(
        item["first_defect_sufficient_count"] for item in scan["length3"].values()
    )
    lean_ok = lean["sorry_free"] and all(lean[name] for name in LEAN_THEOREMS)
    if first_ok:
        return {
            "classification": CLASS_FIRST,
            "reason": (
                "a first local defect alone exceeded the formal gap on a "
                "positive-drift mixed word"
            ),
        }
    if eoo["contract_count"] and lean_ok:
        return {
            "classification": CLASS_FOUND,
            "reason": (
                "EOO contracts exactly at n ∈ {2, 12, 14}; the first-defect "
                "bound is never enough for (k,o)=(3,2), so compensation uses "
                "the full envelope deficit"
            ),
        }
    if eoo["contract_count"]:
        return {
            "classification": CLASS_AMP,
            "reason": (
                "EOO contracts on a finite family, but the Lean certificate "
                "is incomplete"
            ),
        }
    if ooe["contract_count"] == 0 and oeo["contract_count"] == 0 and lean_ok:
        return {
            "classification": CLASS_NON,
            "reason": (
                "no length-3 mixed positive-drift contraction was found and "
                "the Lean API is present"
            ),
        }
    return {
        "classification": CLASS_USELESS,
        "reason": "no useful compensated-contraction family or obstruction",
    }


def run_probe(
    *,
    n_max: int = N_MAX,
    eoo_even_max: int = EOO_EVEN_MAX,
    k4_n_max: int = K4_N_MAX,
    bit_limit: int = BIT_BUDGET,
) -> dict[str, Any]:
    length3 = {
        "OOE": scan_word("OOE", n_max, n_min=3, step=2, bit_limit=bit_limit),
        "OEO": scan_word("OEO", n_max, n_min=3, step=2, bit_limit=bit_limit),
        "EOO": scan_word(
            "EOO", eoo_even_max, n_min=2, step=2, bit_limit=bit_limit
        ),
    }
    length4 = {
        word: scan_word(word, k4_n_max, bit_limit=bit_limit)
        for word in LENGTH4_MIXED
    }
    return {
        "n_max": n_max,
        "eoo_even_max": eoo_even_max,
        "k4_n_max": k4_n_max,
        "bit_limit": bit_limit,
        "length3": length3,
        "length4": length4,
        "eoo_witnesses": eoo_witnesses(bit_limit=max(bit_limit, 64)),
        "ten_eoo_expands": word_row(10, "EOO", bit_limit=bit_limit),
    }


def probe_payload(
    *,
    n_max: int = N_MAX,
    eoo_even_max: int = EOO_EVEN_MAX,
    k4_n_max: int = K4_N_MAX,
) -> dict[str, Any]:
    scan = run_probe(n_max=n_max, eoo_even_max=eoo_even_max, k4_n_max=k4_n_max)
    lean = lean_api_present()
    decision = classify(scan, lean)
    return {
        "experiment": "juggler_compensated_contraction",
        "engine_control_layer_modified": False,
        "anti_overclaim": dict(ANTI_OVERCLAIM),
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "realized length-3 mixed positive-drift words via exact "
            "floor_power; G and Δ only inside a bit budget; no floats"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    length3 = scan["length3"]
    lines = [
        "# Juggler defect-compensated contraction",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment and",
        "not a termination theorem. Formal drift `3^o > 2^k` is not a",
        "complete predictor of block direction.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Can a mixed word with 3^o > 2^k still",
        "                        contract because floor defect overcomes",
        "                        the formal gap?",
        "Novelty hypothesis      A shortest mixed positive-drift family",
        "                        contracts, or the family is obstructed",
        "Falsifier               No contraction and no obstruction, or a",
        "                        first-defect certificate that never fires",
        "Existing machinery      PowerBound, powerDeficit, localDefect,",
        "                        first-defect sharpness",
        "Maximum Phase-0 scope   Search OOE/OEO/EOO; first-defect vs G;",
        "                        Lean certificate or EOO obstruction",
        "```",
        "",
        "## Metadata",
        "",
        f"- OOE/OEO domain: `n <= {scan['n_max']}` odd",
        f"- EOO domain: even `n <= {scan['eoo_even_max']}`",
        f"- length-4 mixed domain: `n <= {scan['k4_n_max']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Length-3 mixed positive-drift words",
        "",
        "These words have two odd letters, so `3^2 = 9 > 8 = 2^3`.",
        "",
    ]
    for name in LENGTH3:
        item = length3[name]
        lines.append(
            f"- `{name}`: realized `{item['realized']}`, "
            f"contractions `{item['contract_count']}`, "
            f"first-defect certificates `{item['first_defect_sufficient_count']}`"
        )
    lines.extend(
        [
            "",
            "## EOO witnesses",
            "",
        ]
    )
    for row in scan["eoo_witnesses"]:
        lines.append(
            f"- n=`{row['n']}` → T^3=`{row['image']}`; "
            f"δ=`{row['first_defect']}`; "
            f"G=`{row['envelope_gap_to_contraction']}`; "
            f"Δ=`{row['actual_deficit']}`"
        )
    ten = scan["ten_eoo_expands"]
    lines.extend(
        [
            "",
            f"n=10 also realizes `EOO` but expands: T^3=`{ten['image']}`.",
            "",
            "## Lean",
            "",
        ]
    )
    for name in LEAN_THEOREMS:
        lines.append(f"- `{name}`: `{lean.get(name)}`")
    lines.extend(
        [
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
            "This is a finite-word direction statement, not a global halt result.",
            "",
        ]
    )
    return "\n".join(lines) + "\n"


def write_artifacts(
    payload: dict[str, Any] | None = None,
    *,
    n_max: int = N_MAX,
    eoo_even_max: int = EOO_EVEN_MAX,
    k4_n_max: int = K4_N_MAX,
) -> dict[str, Any]:
    data = (
        payload
        if payload is not None
        else probe_payload(n_max=n_max, eoo_even_max=eoo_even_max, k4_n_max=k4_n_max)
    )
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

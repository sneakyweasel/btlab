"""Uniformity test for first-even superquadratic thresholds.

Not a Research Engine control-layer experiment. The ε-only family
statement is false: even towers collapse 2^{2^{k-1}} onto 1. Not a halt
theorem and not a generic lower-envelope theory.
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
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_uniform_thresholds.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_uniform_thresholds.md"

CLASS_MARGIN = "UNIFORM_MARGIN_GREEN"
CLASS_LENGTH = "UNIFORM_LENGTH_MARGIN_GREEN"
CLASS_ARTIFACT = "UNIFORM_CONSTANT_ARTIFACT"
CLASS_COUNTER = "CHANGING_SUFFIX_COUNTEREXAMPLE"
CLASS_NONE = "NO_USEFUL_UNIFORMITY"

K_MAX = 6
Q_MAX = 80
Q_MAX_HEAVY = 40

LEAN_THEOREMS = (
    "alphaMargin",
    "minimal_superquadratic_margin",
    "even_tower_to_one",
    "even_tower_odd_tail_contracts",
    "three_k_superquadratic",
    "changing_suffix_unbounded_contraction",
    "LowerPowerBound",
    "lower_growth_word",
    "eventually_no_first_even_contraction",
    "alpha_ne_two",
    "first_even_contracts_iff",
    "first_even_freeze",
)

CERTIFICATE_UNCHANGED = (
    "power_bound_compensated_contracts",
    "eventually_no_first_even_contraction",
)


def is_superquadratic(word: str) -> bool:
    return 3 ** word.count("O") > 2 ** (len(word) + 1)


def formal_alpha(word: str) -> tuple[int, int]:
    return 3 ** word.count("O"), 1 << len(word)


def q_contracts(q: int, word: str) -> bool:
    return follows_itinerary(q, word) and image_after(q, word) + 1 < (q + 1) ** 2


def q_max_of(word: str, *, q_cap: int) -> int | None:
    last = None
    for q in range(1, q_cap + 1):
        if q_contracts(q, word):
            last = q
    return last


def lower_denom(word: str) -> int:
    k = 0
    denom = 1
    for letter in word:
        if letter == "E":
            denom = denom * 4 ** (2 ** k)
        else:
            denom = denom**3 * 4 ** (2 ** k)
        k += 1
    return denom


def even_tower_odd_tail(k: int, o: int) -> str:
    return "E" * k + "O" * o


def collapse_q(k: int) -> int:
    return 2 ** (2 ** (k - 1))


def collapse_family(*, k_max: int = 5) -> list[dict[str, Any]]:
    rows = []
    for k in range(2, k_max + 1):
        o = 3 * k
        word = even_tower_odd_tail(k, o)
        q = collapse_q(k)
        output = image_after(q, word)
        num, den = formal_alpha(word)
        rows.append(
            {
                "k": k,
                "o": o,
                "word": word,
                "length": len(word),
                "odd_count": o,
                "alpha_num": num,
                "alpha_den": den,
                "q": q,
                "follows": follows_itinerary(q, word),
                "output": output,
                "contracts": output + 1 < (q + 1) ** 2,
                "superquadratic": is_superquadratic(word),
            }
        )
    return rows


def margin_scan(*, k_max: int = K_MAX, q_max: int = Q_MAX, q_max_heavy: int = Q_MAX_HEAVY) -> list[dict[str, Any]]:
    rows = []
    for r in range(1, k_max + 1):
        for letters in product("EO", repeat=r):
            word = "".join(letters)
            if not is_superquadratic(word):
                continue
            o = word.count("O")
            cap = q_max_heavy if o >= 5 or r >= 6 else q_max
            num, den = formal_alpha(word)
            rows.append(
                {
                    "word": word,
                    "length": r,
                    "odd_count": o,
                    "alpha_num": num,
                    "alpha_den": den,
                    "alpha_minus_2_num": num - 2 * den,
                    "alpha_minus_2_den": den,
                    "q_max": q_max_of(word, q_cap=cap),
                    "q_cap": cap,
                }
            )
    rows.sort(key=lambda item: (item["alpha_minus_2_num"] / item["alpha_minus_2_den"], item["length"], item["word"]))
    return rows


def denom_audit() -> list[dict[str, Any]]:
    rows = []
    for letters in product("EO", repeat=5):
        word = "".join(letters)
        if word.count("O") != 4:
            continue
        denom = lower_denom(word)
        rows.append(
            {
                "word": word,
                "D_bit_length": denom.bit_length(),
                "same_r_o": True,
            }
        )
    return rows


def epsilon_r_table(*, r_max: int = 12) -> list[dict[str, Any]]:
    rows = []
    for r in range(1, r_max + 1):
        best = None
        for o in range(r + 1):
            if 3**o > 2 ** (r + 1):
                gap = 3**o - 2 ** (r + 1)
                item = {
                    "length": r,
                    "odd_count": o,
                    "gap": gap,
                    "alpha_minus_2_num": gap,
                    "alpha_minus_2_den": 1 << r,
                    "at_least_inv_len": gap >= 1,
                }
                if best is None or gap * best["alpha_minus_2_den"] < best["gap"] * (1 << r):
                    best = item
        rows.append(best if best is not None else {"length": r, "odd_count": None})
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
        "mixed_word_power_lt_absent": "theorem mixed_word_power_lt" not in text,
        "no_uniform_first_even_threshold": "theorem uniform_first_even_threshold" not in text,
    }


def classify(family: list[dict[str, Any]], lean: dict[str, bool]) -> dict[str, Any]:
    collapse_ok = all(
        row["follows"] and row["contracts"] and row["superquadratic"] and row["output"] == 1
        for row in family
    )
    growing = family[-1]["q"] > family[0]["q"] if family else False
    lean_ok = lean["sorry_free"] and lean["changing_suffix_unbounded_contraction"]
    if collapse_ok and growing:
        return {
            "classification": CLASS_COUNTER,
            "reason": (
                "the family E^k O^{3k} at q=2^{2^{k-1}} is superquadratic, "
                "maps onto 1, and contracts for arbitrarily large q; "
                "no Q(ε) exists"
            ),
            "lean_family_theorem": lean_ok,
        }
    return {
        "classification": CLASS_NONE,
        "reason": "the even-tower collapse family was not confirmed",
        "lean_family_theorem": lean_ok,
    }


def run_probe(*, k_max: int = K_MAX, q_max: int = Q_MAX, family_k_max: int = 5) -> dict[str, Any]:
    family = collapse_family(k_max=family_k_max)
    return {
        "k_max": k_max,
        "q_max": q_max,
        "margin_scan": margin_scan(k_max=k_max, q_max=q_max),
        "denom_audit": denom_audit(),
        "epsilon_r": epsilon_r_table(),
        "collapse_family": family,
        "D_v_depends_on_order": True,
        "q_max_depends_on_order": True,
        "D_v_is_uniformity_obstruction": False,
    }


def probe_payload(*, k_max: int = K_MAX, q_max: int = Q_MAX) -> dict[str, Any]:
    scan = run_probe(k_max=k_max, q_max=q_max)
    lean = lean_api_present()
    decision = classify(scan["collapse_family"], lean)
    return {
        "experiment": "juggler_uniform_thresholds",
        "engine_control_layer_modified": False,
        "anti_overclaim": dict(ANTI_OVERCLAIM),
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "group short words by α-2; audit lowerDenom order; "
            "exact even-tower collapse family; no logs, no huge envelopes"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler uniform superquadratic thresholds",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment and",
        "not a termination theorem. A threshold depending only on the",
        "exponent margin `α_v-2` does not exist.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Does Q(ε) exist for all α_v ≥ 2+ε?",
        "Novelty hypothesis      Margin above 2 might give a family bound",
        "Falsifier               Superquadratic v_q with unbounded contracting q",
        "Existing machinery      LowerPowerBound; first_even_freeze",
        "Maximum Phase-0 scope   q_max vs ε; D_v audit; even-tower family",
        "```",
        "",
        "## Metadata",
        "",
        f"- short-word length: `k <= {scan['k_max']}`",
        f"- short-word q domain: `q <= {scan['q_max']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Collapse family `E^k O^{3k}`",
        "",
    ]
    for row in scan["collapse_family"]:
        lines.append(
            f"- k=`{row['k']}` v=`{row['word']}` α=`{row['alpha_num']}/"
            f"{row['alpha_den']}` q=`{row['q']}` T=`{row['output']}` "
            f"contracts=`{row['contracts']}`"
        )
    lines.extend(
        [
            "",
            "## Short-word `q_max` by margin",
            "",
        ]
    )
    for item in scan["margin_scan"]:
        lines.append(
            f"- `{item['word']}` ε=`{item['alpha_minus_2_num']}/"
            f"{item['alpha_minus_2_den']}` q_max=`{item['q_max']}`"
        )
    lines.extend(
        [
            "",
            "## `D_v` order audit for `(r,o)=(5,4)`",
            "",
        ]
    )
    for item in scan["denom_audit"]:
        lines.append(f"- `{item['word']}` D bit-length=`{item['D_bit_length']}`")
    lines.extend(
        [
            "",
            "## Minimal positive margin by length",
            "",
        ]
    )
    for item in scan["epsilon_r"]:
        if item.get("odd_count") is None:
            lines.append(f"- r=`{item['length']}` none")
        else:
            lines.append(
                f"- r=`{item['length']}` o=`{item['odd_count']}` "
                f"ε_r=`{item['alpha_minus_2_num']}/{item['alpha_minus_2_den']}`"
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
            f"- certificate unchanged: `{lean.get('certificate_present')}`",
            f"- `PowerHeight` absent: `{lean.get('PowerHeight_absent')}`",
            f"- no `uniform_first_even_threshold`: `{lean.get('no_uniform_first_even_threshold')}`",
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

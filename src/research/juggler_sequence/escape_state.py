"""Escape-state margin on prefix-NC non-contracting Juggler prefixes.

Not a Research Engine control-layer experiment. Not a halt theorem.
Asks whether M = formal_gap − Δ, or a small tuple, is a progress
measure on prefixes that avoid both exponent contraction and
defect-driven contraction. ResidualStep is not extended. Prefix-NC
word admissibility is not reopened.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.compensated_contraction import formal_gap
from research.juggler_sequence.envelope_defect import (
    first_nonexact_index,
    local_defect,
    tiny_deficit,
)
from research.juggler_sequence.equality_language import is_monochrome
from research.juggler_sequence.near_extremal_prefixes import (
    exponent_gap,
    prefix_noncontracting,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, itinerary, odd_count, word_of
from research.juggler_sequence.lean_paths import (
    ENVELOPE,
    RESIDUALS,
    juggler_text,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_escape_state.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_escape_state.md"
LEAN_NEW = REPO_ROOT / "formal" / "Problems" / "Engine" / "EscapeState.lean"
FLOOR_PATH = ENVELOPE
RESIDUAL_PATH = RESIDUALS
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "escape_state"

CLASS_INVARIANT = "ESCAPE_STATE_INVARIANT_GREEN"
CLASS_MARGIN = "ESCAPE_MARGIN_GREEN"
CLASS_REGIME = "ESCAPE_REGIME_GREEN"
CLASS_COUNTER = "ESCAPE_COUNTEREXAMPLE"
CLASS_COMPLEX = "ESCAPE_STATE_COMPLEX"
CLASS_INCOMPLETE = "ESCAPE_STATE_INCOMPLETE"

HARD_STARTS = (5, 9, 37, 69, 173)
N_MAX = 200
K_MAX = 8
BIT_LIMIT = 80

FLOOR_LEMMAS = (
    "power_bound_contracts",
    "power_bound_compensated_contracts",
    "power_bound_eq_iff_extremal",
    "powerDeficit",
)


def power_if_small(base: int, exp: int, *, bit_limit: int = BIT_LIMIT) -> int | None:
    if base < 0 or exp < 0:
        raise ValueError("power_if_small requires nonnegative base and exponent")
    if exp == 0:
        return 1
    if base <= 1:
        return base
    if base.bit_length() * exp > bit_limit:
        return None
    return base**exp


def image_margin(n: int, image: int, k: int, *, bit_limit: int = BIT_LIMIT) -> int | None:
    """T^k(n)^{2^k} − n^{2^k}, or None if either power exceeds the bit budget."""

    left = power_if_small(image, 1 << k, bit_limit=bit_limit)
    right = power_if_small(n, 1 << k, bit_limit=bit_limit)
    if left is None or right is None:
        return None
    return left - right


def escape_row(n: int, k: int, *, bit_limit: int = BIT_LIMIT) -> dict[str, Any]:
    if n < 1 or k < 1:
        raise ValueError("escape_row requires n >= 1 and k >= 1")
    path = itinerary(n, k)
    word = word_of(path)
    image = path[-1]
    odds = odd_count(word)
    gap = exponent_gap(k, odds)
    formal = formal_gap(n, k, odds, bit_limit=bit_limit)
    deficit = tiny_deficit(n, image, k, odds, bit_limit=bit_limit)
    margin_from_gap = None if formal is None or deficit is None else formal - deficit
    margin_from_image = image_margin(n, image, k, bit_limit=bit_limit)
    index = first_nonexact_index(path)
    first = None if index is None else local_defect(path[index])
    budget = None if formal is None or first is None else formal - first
    identity = (
        margin_from_gap is not None
        and margin_from_image is not None
        and margin_from_gap == margin_from_image
    )
    return {
        "n": n,
        "k": k,
        "word": word,
        "image": image,
        "odd_count": odds,
        "exponent_gap": gap,
        "prefix_nc": prefix_noncontracting(word),
        "monochrome": is_monochrome(word),
        "image_ge_n": image >= n,
        "actual_contraction": image < n,
        "formal_gap": formal,
        "deficit": deficit,
        "margin_from_gap": margin_from_gap,
        "margin_from_image": margin_from_image,
        "identity_holds": identity,
        "first_defect_position": index,
        "first_defect": first,
        "defect_budget": budget,
        "escape": gap <= 0 and image >= n and not is_monochrome(word),
        "margin_zero": image == n,
    }


def walk_prefixes(n: int, k_max: int = K_MAX) -> list[dict[str, Any]]:
    return [escape_row(n, k) for k in range(1, k_max + 1)]


def identity_failures(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    out = []
    for row in rows:
        if row["exponent_gap"] > 0:
            continue
        if row["margin_from_gap"] is None or row["margin_from_image"] is None:
            continue
        if row["margin_from_gap"] != row["margin_from_image"]:
            out.append({"n": row["n"], "k": row["k"], "word": row["word"]})
    return out


def monotone_failures(walks: list[list[dict[str, Any]]], key: str) -> list[dict[str, Any]]:
    fails = []
    for walk in walks:
        escape = [row for row in walk if row["escape"] and row[key] is not None]
        for prev, nxt in zip(escape, escape[1:]):
            if nxt[key] >= prev[key]:
                fails.append(
                    {
                        "n": prev["n"],
                        "k": prev["k"],
                        "next_k": nxt["k"],
                        "prev": prev[key],
                        "next": nxt[key],
                        "key": key,
                    }
                )
    return fails


def image_not_approaching(walks: list[list[dict[str, Any]]]) -> list[dict[str, Any]]:
    """Escape prefixes whose image moves farther from the start."""

    fails = []
    for walk in walks:
        escape = [row for row in walk if row["escape"]]
        for prev, nxt in zip(escape, escape[1:]):
            if nxt["image"] - nxt["n"] >= prev["image"] - prev["n"]:
                fails.append(
                    {
                        "n": prev["n"],
                        "k": prev["k"],
                        "next_k": nxt["k"],
                        "prev_overshoot": prev["image"] - prev["n"],
                        "next_overshoot": nxt["image"] - nxt["n"],
                    }
                )
    return fails


def sign_failures(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    fails = []
    for row in rows:
        margin = row["margin_from_image"]
        if margin is None:
            continue
        if (margin >= 0) != row["image_ge_n"]:
            fails.append({"n": row["n"], "k": row["k"], "margin": margin})
    return fails


def scan_window(*, n_max: int = N_MAX, k_max: int = K_MAX) -> dict[str, Any]:
    walks = [walk_prefixes(n, k_max) for n in range(2, n_max + 1)]
    rows = [row for walk in walks for row in walk]
    escape = [row for row in rows if row["escape"]]
    zeros = [row for row in rows if row["margin_zero"] and row["n"] >= 2]
    return {
        "n_max": n_max,
        "k_max": k_max,
        "prefix_count": len(rows),
        "escape_count": len(escape),
        "identity_failures": identity_failures(rows),
        "sign_failures": sign_failures(rows),
        "margin_not_decreasing": monotone_failures(walks, "margin_from_image"),
        "budget_not_decreasing": monotone_failures(walks, "defect_budget"),
        "image_not_approaching": image_not_approaching(walks),
        "margin_zero": [
            {"n": row["n"], "k": row["k"], "word": row["word"]} for row in zeros[:8]
        ],
        "longest_escape": max((row["k"] for row in escape), default=0),
        "search_horizon_is_not_L": True,
    }


def lean_api_present() -> dict[str, bool]:
    floor = juggler_text()
    residual = RESIDUAL_PATH.read_text(encoding="utf-8")
    combined = floor + residual
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        "power_bound_contracts": "theorem power_bound_contracts" in floor,
        "power_bound_compensated_contracts": (
            "theorem power_bound_compensated_contracts" in floor
        ),
        "power_bound_eq_iff_extremal": "theorem power_bound_eq_iff_extremal" in floor,
        "powerDeficit": "def powerDeficit" in floor,
        "EscapeState_absent": not LEAN_NEW.is_file(),
        "no_escape_margin_step": "escape_margin_step" not in floor
        and "escape_state_progress" not in residual,
        "ResidualStep_not_extended": "escape_state" not in residual,
        "no_global_termination_theorem": "theorem juggler_reaches_one" not in combined,
        "no_forbidden_engine": "PowerHeight" not in residual
        and "RemainderDynamics" not in residual
        and "CycleEngine" not in residual,
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["EscapeState_absent"]
        and lean["power_bound_compensated_contracts"]
        and lean["no_global_termination_theorem"]
        and lean["ResidualStep_not_extended"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if scan["identity_failures"] or scan["sign_failures"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "M identity or sign failed on G<=0 or bit-capped rows",
        }
    if scan["image_not_approaching"] or scan["margin_not_decreasing"]:
        return {
            "classification": CLASS_COMPLEX,
            "secondary": [CLASS_COUNTER],
            "reason": (
                "on G<=0, M = T^{2^k}-n^{2^k} and M>=0 iff T>=n; "
                "that is actual non-contraction, not a new progress law; "
                "escape images move farther from the start on known expanders"
            ),
        }
    return {
        "classification": CLASS_COMPLEX,
        "reason": (
            "on G<=0, M = T^{2^k}-n^{2^k} and M>=0 iff T>=n; "
            "no compact progress law survived"
        ),
    }


def run_probe() -> dict[str, Any]:
    hard = [{"n": n, "walk": walk_prefixes(n)} for n in HARD_STARTS]
    window = scan_window()
    return {
        "hard": hard,
        "window": window,
        "basin": [1],
        "residual_step_extended": False,
        "explicit_L": False,
        "word_census": False,
        "adversarial_engine": False,
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan["window"], lean)
    anti = dict(ANTI_OVERCLAIM)
    anti["search_horizon_is_L"] = False
    anti["escape_margin_is_new_progress"] = False
    anti["finite_progress_for_all"] = False
    return {
        "experiment": "juggler_escape_state",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "M = formal_gap-Δ compared with T^{2^k}-n^{2^k} on G<=0; "
            f"HARD_STARTS {HARD_STARTS}; window n<={N_MAX} k<={K_MAX}; "
            "no ResidualStep; no word-exclusion census"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    window = scan["window"]
    lines = [
        "# Juggler escape-state margin",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. An escape prefix is mixed,",
        "prefix-NC, and non-contracting. The question is whether",
        "`M = formal_gap − Δ` is a progress measure.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Does M or a small tuple progress on escape prefixes?",
        "Novelty hypothesis      escape now implies a strictly tighter escape later",
        "Falsifier               M is T^{2^k}-n^{2^k}; sign is image>=n; M grows",
        "Existing machinery      formal_gap, tiny_deficit, compensated contraction,",
        "                        prefix_noncontracting, first defect",
        "Maximum Phase-0 scope   identity; HARD_STARTS; n<=200 k<=8; no automaton",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- secondary: `{decision.get('secondary')}`",
        f"- sorry-free: `{lean['sorry_free']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Window",
        "",
        f"- prefixes: `{window['prefix_count']}`",
        f"- escape prefixes: `{window['escape_count']}`",
        f"- identity failures on G<=0: `{len(window['identity_failures'])}`",
        f"- sign failures: `{len(window['sign_failures'])}`",
        f"- M not decreasing: `{len(window['margin_not_decreasing'])}`",
        f"- first-defect budget not decreasing: `{len(window['budget_not_decreasing'])}`",
        f"- image not approaching n: `{len(window['image_not_approaching'])}`",
        f"- M=0 with n>=2: `{window['margin_zero']}`",
        f"- longest escape in window: `{window['longest_escape']}` (horizon, not L)",
        "",
        "## Hard starts",
        "",
    ]
    for item in scan["hard"]:
        lines.append(f"### n = {item['n']}")
        lines.append("")
        for row in item["walk"]:
            if not row["escape"] and row["k"] > 3:
                continue
            lines.append(
                f"- k=`{row['k']}` `{row['word']}` image=`{row['image']}` "
                f"G=`{row['exponent_gap']}` escape=`{row['escape']}` "
                f"M=`{row['margin_from_image']}` W=`{row['defect_budget']}`"
            )
        lines.append("")
    lines.extend(["## Lean", ""])
    for name in FLOOR_LEMMAS:
        lines.append(f"- `{name}`: `{lean.get(name)}`")
    lines.extend(
        [
            f"- new EscapeState file absent: `{lean.get('EscapeState_absent')}`",
            f"- ResidualStep not extended: `{lean.get('ResidualStep_not_extended')}`",
            f"- no global halt theorem: `{lean.get('no_global_termination_theorem')}`",
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
            "The future orbit is a function of the current integer.",
            "Indefinite escape is non-termination, not a new local state.",
            "A search-horizon escape prefix is not a bound L.",
            "",
        ]
    )
    return "\n".join(lines) + "\n"


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    DOC_PATH.write_text(render_markdown(data), encoding="utf-8")
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    (DATA_DIR / "summaries").mkdir(exist_ok=True)
    (DATA_DIR / "analysis").mkdir(exist_ok=True)
    (DATA_DIR / "README.md").write_text(
        "# Escape-state margin\n\n"
        "Phase-0 identity and traces for `M = formal_gap − Δ` on "
        "mixed prefix-NC non-contracting prefixes. This is evidence, "
        "not a progress theorem and not a termination theorem.\n",
        encoding="utf-8",
    )
    (DATA_DIR / "summaries" / "summary.md").write_text(
        render_markdown(data), encoding="utf-8"
    )
    (DATA_DIR / "analysis" / "window.json").write_text(
        json.dumps(data["scan"]["window"], indent=2) + "\n", encoding="utf-8"
    )
    (DATA_DIR / "analysis" / "hard.json").write_text(
        json.dumps(
            [
                {
                    "n": item["n"],
                    "escape": [
                        {
                            "k": row["k"],
                            "word": row["word"],
                            "image": row["image"],
                            "margin": row["margin_from_image"],
                            "budget": row["defect_budget"],
                        }
                        for row in item["walk"]
                        if row["escape"]
                    ],
                }
                for item in data["scan"]["hard"]
            ],
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    return data


def main() -> None:
    payload = write_artifacts()
    print(payload["decision"]["classification"])
    print(payload["decision"]["reason"])


if __name__ == "__main__":
    main()

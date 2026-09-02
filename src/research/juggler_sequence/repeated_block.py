"""Repeated O^a E^b scale budget on a hypothetical minimal non-1 orbit.

Not a Research Engine control-layer experiment. Not a frequency theorem
and not a halt theorem. Separates formally contracting blocks
(3^a < 2^{a+b}) from formally expanding ones, and records that
repetition alone is not a global obstruction.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.capture_certificates import classify_block
from research.juggler_sequence.compensated_contraction import follows_itinerary, image_after
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, cmp_pow, floor_power, word_of
from research.juggler_sequence.lean_paths import (
    ENVELOPE,
    MINIMAL,
    SCALE,
    juggler_text,
    engine_floor_text,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_repeated_block.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_repeated_block.md"
LEAN_PATH = SCALE
ODD_PATH = SCALE
REPEATED_PATH = SCALE
MIN_PATH = MINIMAL
FLOOR_PATH = ENVELOPE

CLASS_GREEN = "REPEATED_BLOCK_SCALE_GREEN"
CLASS_CONTRACT = "REPEATED_CONTRACTION_FORBIDDEN"
CLASS_EXPAND = "REPEATED_EXPANSION_SURVIVES"
CLASS_OBSTRUCTION = "REPETITION_GLOBAL_OBSTRUCTION_GREEN"
CLASS_COUNTER = "REPEATED_BLOCK_SCALE_COUNTEREXAMPLE"
CLASS_INCOMPLETE = "REPEATED_BLOCK_INCOMPLETE"

N_MAX = 80
PREFIX_CAP = 40
PAIRS = (
    (1, 1),
    (1, 2),
    (2, 1),
    (2, 2),
    (3, 1),
    (3, 2),
    (4, 1),
    (4, 2),
    (5, 2),
)
CALIBRATION = (
    (13, "OE"),
    (69, "OOEOOE"),
    (5, "OOE"),
    (17537, "OEOE"),
    (225, "OOOEOOOE"),
)

LEAN_THEOREMS = (
    "repeatedOddEven",
    "odd_even_exponents_ne",
    "contracting_gap_repeat",
    "repeated_block_power_bound",
    "repeated_odd_even_scale_barrier",
    "contracting_odd_even_block_contracts",
    "contracting_repeated_odd_even_contracts",
    "initial_contracting_block_forbidden",
    "initial_contracting_repeated_forbidden",
)

CERTIFICATE_UNCHANGED = (
    "power_bound_word",
    "power_bound_contracts",
    "power_bound_compensated_contracts",
    "even_run_scale_barrier",
    "odd_even_block_scale_barrier",
    "repeated_oe_scale_barrier",
    "first_even_freeze",
)


def pow_le(left_base: int, left_exp: int, right_base: int, right_exp: int) -> bool:
    return cmp_pow(left_base, left_exp, right_base, right_exp) <= 0


def block_word(a: int, b: int) -> str:
    return ("O" * a) + ("E" * b)


def regime_of(a: int, b: int) -> str:
    left, right = 3**a, 1 << (a + b)
    if left < right:
        return "contract"
    if left > right:
        return "expand"
    return "equal"


def envelope_holds(x0: int, a: int, b: int, r: int, xr: int) -> bool:
    return pow_le(xr, 1 << (r * (a + b)), x0, 3 ** (a * r))


def scale_holds(n: int, x0: int, a: int, b: int, r: int) -> bool:
    return pow_le(n, 1 << (r * (a + b)), x0, 3 ** (a * r))


def classify_repeat(n: int, x0: int, xr: int) -> str:
    if xr == 1:
        return "CAPTURE"
    if xr < n:
        return "DESCENT"
    if xr > x0:
        return "EXPANDING"
    return "UNRESOLVED"


def consecutive_blocks(n: int, a: int, b: int, cap: int = PREFIX_CAP) -> list[dict[str, Any]]:
    word = block_word(a, b)
    if not word:
        return []
    path = [n]
    current = n
    for _ in range(cap):
        current = floor_power(current)
        path.append(current)
    letters = word_of(tuple(path))
    rows: list[dict[str, Any]] = []
    index = 0
    width = len(word)
    while index + width <= len(letters):
        if letters[index : index + width] != word:
            index += 1
            continue
        end = index
        while end + width <= len(letters) and letters[end : end + width] == word:
            end += width
        r = (end - index) // width
        x0 = path[index]
        xr = path[end]
        stay = xr >= n
        rows.append(
            {
                "n": n,
                "a": a,
                "b": b,
                "r": r,
                "x0": x0,
                "xr": xr,
                "at_start": index == 0,
                "stay_ge_n": stay,
                "envelope_ok": envelope_holds(x0, a, b, r, xr),
                "scale_ok": (not stay) or scale_holds(n, x0, a, b, r),
                "kind": classify_repeat(n, x0, xr),
                "regime": regime_of(a, b),
            }
        )
        index = end
    return rows


def regime_table(*, a_max: int = 5, b_max: int = 5) -> list[dict[str, Any]]:
    rows = []
    for a in range(a_max + 1):
        for b in range(b_max + 1):
            if a == 0 or b == 0:
                continue
            left, right = 3**a, 1 << (a + b)
            rows.append(
                {
                    "a": a,
                    "b": b,
                    "three_pow": left,
                    "two_pow": right,
                    "regime": regime_of(a, b),
                    "near_one": abs(left / right - 1.0),
                }
            )
    rows.sort(key=lambda row: (row["regime"] != "expand", row["near_one"], row["a"], row["b"]))
    return rows


def block_census(*, n_max: int = N_MAX, cap: int = PREFIX_CAP) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    for n in range(2, n_max + 1):
        for a, b in PAIRS:
            rows.extend(consecutive_blocks(n, a, b, cap))
    env_fail = [row for row in rows if not row["envelope_ok"]]
    scale_fail = [row for row in rows if not row["scale_ok"]]
    stay = [row for row in rows if row["stay_ge_n"]]
    expand_stay = [row for row in stay if row["regime"] == "expand"]
    contract_stay = [row for row in stay if row["regime"] == "contract"]
    expand_repeat = [row for row in expand_stay if row["r"] >= 2]
    start_contract = [
        row for row in rows if row["at_start"] and row["regime"] == "contract" and row["stay_ge_n"]
    ]
    longest_expand = (
        max(expand_stay, key=lambda row: (row["r"], row["x0"])) if expand_stay else None
    )
    return {
        "n_max": n_max,
        "pairs": [list(pair) for pair in PAIRS],
        "run_count": len(rows),
        "stay_ge_n": len(stay),
        "envelope_fail": len(env_fail),
        "scale_fail": len(scale_fail),
        "expand_stay": len(expand_stay),
        "contract_stay": len(contract_stay),
        "expand_repeat_stay": len(expand_repeat),
        "start_contract_stay": len(start_contract),
        "max_r": max((row["r"] for row in rows), default=0),
        "max_r_expand_stay": max((row["r"] for row in expand_stay), default=0),
        "max_r_contract_stay": max((row["r"] for row in contract_stay), default=0),
        "longest_expand_stay": longest_expand,
        "expand_repeat_sample": expand_repeat[:4],
        "contract_stay_sample": contract_stay[:4],
    }


def calibration_rows() -> list[dict[str, Any]]:
    rows = []
    for n, word in CALIBRATION:
        if not follows_itinerary(n, word):
            rows.append({"n": n, "word": word, "follows": False})
            continue
        image = image_after(n, word)
        rows.append(
            {
                "n": n,
                "word": word,
                "follows": True,
                "image": image,
                "kind": classify_block(n, word),
                "stay_ge_n": image >= n,
                "expanded": image > n,
            }
        )
    return rows


def lean_api_present() -> dict[str, bool]:
    text = LEAN_PATH.read_text(encoding="utf-8")
    odd = ODD_PATH.read_text(encoding="utf-8")
    repeated = REPEATED_PATH.read_text(encoding="utf-8")
    minimum = MIN_PATH.read_text(encoding="utf-8")
    corpus = juggler_text()
    floor = engine_floor_text()
    combined = text + odd + repeated + minimum + corpus
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **{
            name: (f"theorem {name}" in text or f"def {name}" in text)
            for name in LEAN_THEOREMS
        },
        "certificate_present": all(
            f"theorem {name}" in combined for name in CERTIFICATE_UNCHANGED
        ),
        "PowerHeight_absent": "PowerHeight" not in combined,
        "no_lower_envelope_structure": "structure LowerEnvelope" not in combined,
        "no_global_termination_theorem": "theorem juggler_reaches_one" not in combined,
        "no_infinite_path_type": "coinductive" not in text.lower()
        and "def InfinitePath" not in text,
        "no_frequency_theorem": "theorem block_frequency" not in text
        and "theorem oe_frequency" not in text,
        "FloorPower_not_rewritten": "repeatedOddEven" not in floor,
    }


def classify(census: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    if census["envelope_fail"] > 0:
        return {
            "classification": CLASS_COUNTER,
            "reason": f"repeated-block envelope failed: {census['envelope_fail']} runs",
        }
    if census["scale_fail"] > 0:
        return {
            "classification": CLASS_COUNTER,
            "reason": "repeated scale n^{2^{r(a+b)}} <= x^{3^{a r}} failed on a stay-ge-n run",
        }
    if census["start_contract_stay"] > 0:
        return {
            "classification": CLASS_COUNTER,
            "reason": "a formally contracting block stayed at the start",
        }
    lean_ok = (
        lean["sorry_free"]
        and lean["repeated_block_power_bound"]
        and lean["repeated_odd_even_scale_barrier"]
        and lean["initial_contracting_block_forbidden"]
        and lean["odd_even_exponents_ne"]
        and lean["no_global_termination_theorem"]
        and lean["no_frequency_theorem"]
        and lean["FloorPower_not_rewritten"]
    )
    if lean_ok:
        secondary = [CLASS_CONTRACT]
        if census["expand_repeat_stay"] > 0:
            secondary.append(CLASS_EXPAND)
        return {
            "classification": CLASS_GREEN,
            "secondary": secondary,
            "reason": (
                "(O^a E^b)^r on a minimal non-1 orbit requires "
                "n^{2^{r(a+b)}} <= x^{3^{a r}}; contracting blocks cannot "
                "start at n_*; expanding repetition can stay above the start"
            ),
        }
    return {
        "classification": CLASS_INCOMPLETE,
        "reason": f"lean_ok={lean_ok}",
    }


def run_probe() -> dict[str, Any]:
    return {
        "census": block_census(),
        "regimes": regime_table(),
        "calibration": calibration_rows(),
        "basin": [1],
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan["census"], lean)
    anti = dict(ANTI_OVERCLAIM)
    anti["all_odd_orbit"] = False
    anti["oe_frequency_theorem"] = False
    anti["absolute_later_odd_run_length"] = False
    anti["repetition_global_obstruction"] = False
    anti["contracting_later_forbidden"] = False
    return {
        "experiment": "juggler_repeated_block",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "consecutive O^a E^b runs on realized prefixes; envelope "
            "xr^{2^{r(a+b)}}<=x0^{3^{ar}}; scale when exit>=n; regime split "
            "3^a ? 2^{a+b}; no frequency claim"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    census = scan["census"]
    longest = census["longest_expand_stay"]
    lines = [
        "# Juggler repeated O^a E^b blocks",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment,",
        "not a frequency theorem, and not a termination theorem. If a",
        "minimal non-1 orbit realizes `(O^a E^b)^r` from a later state `x`,",
        "then `n^{2^{r(a+b)}} ≤ x^{3^{a r}}`. Formally contracting blocks",
        "cannot start at `n_*`. Repeated expansion can stay above the start.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     (O^a E^b)^r on MinimalNonTerm => n^{2^{r(a+b)}} <= x^{3^{a r}}",
        "Novelty hypothesis      Contracting start is forbidden; expanding repetition may survive",
        "Falsifier               Envelope fail, stay-ge-n scale fail, or start-contracting stay",
        "Existing machinery      power_bound_word, power_bound_contracts, oddEvenBlock, MinimalNonTerm",
        "Maximum Phase-0 scope   Repeated envelope+barrier; start contraction; expanding census",
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
        "## Repeated-block census",
        "",
        f"- realized runs: `{census['run_count']}`",
        f"- stay >= n: `{census['stay_ge_n']}`",
        f"- envelope failures: `{census['envelope_fail']}`",
        f"- scale failures on stay-ge-n: `{census['scale_fail']}`",
        f"- expanding stay: `{census['expand_stay']}`",
        f"- contracting stay: `{census['contract_stay']}`",
        f"- expanding r>=2 stay: `{census['expand_repeat_stay']}`",
        f"- start contracting stay: `{census['start_contract_stay']}`",
        f"- max r: `{census['max_r']}`",
        f"- max expanding stay r: `{census['max_r_expand_stay']}`",
        "",
    ]
    if longest is not None:
        lines.append(
            f"- longest expanding stay: n=`{longest['n']}` x0=`{longest['x0']}` "
            f"O^{longest['a']}E^{longest['b']} r=`{longest['r']}` xr=`{longest['xr']}` "
            f"kind=`{longest['kind']}`"
        )
    lines.extend(["", "## Closest expanding regimes", ""])
    expand = [row for row in scan["regimes"] if row["regime"] == "expand"][:6]
    for row in expand:
        lines.append(
            f"- O^{row['a']}E^{row['b']}: 3^{row['a']}=`{row['three_pow']}` vs "
            f"2^{row['a']+row['b']}=`{row['two_pow']}`"
        )
    lines.extend(["", "## Calibration", ""])
    for row in scan["calibration"]:
        if not row.get("follows", True):
            lines.append(f"- n=`{row['n']}` word=`{row['word']}` follows=`False`")
            continue
        lines.append(
            f"- n=`{row['n']}` word=`{row['word']}` T=`{row['image']}` "
            f"kind=`{row['kind']}` stay=`{row['stay_ge_n']}` "
            f"expanded=`{row['expanded']}`"
        )
    lines.extend(["", "## Lean", ""])
    for name in LEAN_THEOREMS:
        lines.append(f"- `{name}`: `{lean.get(name)}`")
    lines.extend(
        [
            f"- certificate unchanged: `{lean.get('certificate_present')}`",
            f"- `PowerHeight` absent: `{lean.get('PowerHeight_absent')}`",
            f"- FloorPower not rewritten: `{lean.get('FloorPower_not_rewritten')}`",
            f"- no infinite-path type: `{lean.get('no_infinite_path_type')}`",
            f"- no frequency theorem: `{lean.get('no_frequency_theorem')}`",
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
            "Repetition alone is not a global obstruction. This is not a",
            "halt result and not a block-frequency theorem.",
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

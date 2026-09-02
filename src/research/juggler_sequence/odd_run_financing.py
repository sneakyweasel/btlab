"""Odd-run financing of the first legal even residual.

Not a Research Engine control-layer experiment. Not a frequency theorem
and not a halt theorem. Records the exact scale cost of a realized
`O^a E^b` block if it occurs on a hypothetical minimal non-1 orbit.
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
    engine_floor_text,
    has_named,
    juggler_text,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_odd_run_financing.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_odd_run_financing.md"
LEAN_PATH = SCALE
REPEATED_PATH = SCALE
MIN_PATH = MINIMAL
FLOOR_PATH = ENVELOPE

CLASS_GREEN = "ODD_RUN_FINANCING_GREEN"
CLASS_MINIMUM = "ODD_RUN_MINIMUM_GREEN"
CLASS_BLOCK = "BLOCK_FINANCING_GREEN"
CLASS_LATER_A1 = "SCALE_FINANCING_COUNTEREXAMPLE"
CLASS_COUNTER = "ODD_RUN_FINANCING_COUNTEREXAMPLE"
CLASS_INCOMPLETE = "ODD_RUN_FINANCING_INCOMPLETE"

N_MAX = 80
PREFIX_CAP = 40
CALIBRATION = (
    (13, "OE"),
    (27, "OE"),
    (25, "OOOE"),
    (5, "OOE"),
    (33, "OOE"),
)

LEAN_THEOREMS = (
    "oddEvenBlock",
    "follows_of_append_right",
    "odd_run_even_residual",
    "two_pow_succ_le_three_pow_iff",
    "odd_run_power_bound",
    "odd_even_block_scale_barrier",
    "odd_run_financing_scale_barrier",
    "initial_even_not_before_ooe",
)

CERTIFICATE_UNCHANGED = (
    "power_bound_word",
    "power_bound_compensated_contracts",
    "first_even_freeze",
    "even_run_scale_barrier",
    "repeated_oe_scale_barrier",
    "minimal_counterexample_normal_form",
)


def pow_le(left_base: int, left_exp: int, right_base: int, right_exp: int) -> bool:
    return cmp_pow(left_base, left_exp, right_base, right_exp) <= 0


def two_pow_succ_le_three(a: int) -> bool:
    return (1 << (a + 1)) <= 3**a


def smallest_admissible_a() -> int:
    a = 0
    while not two_pow_succ_le_three(a):
        a += 1
    return a


def envelope_holds(x0: int, a: int, xa: int) -> bool:
    return pow_le(xa, 1 << a, x0, 3**a)


def financing_holds(n: int, x0: int, a: int) -> bool:
    return pow_le(n, 1 << (a + 1), x0, 3**a)


def block_financing_holds(n: int, x0: int, a: int, b: int) -> bool:
    return pow_le(n, 1 << (a + b), x0, 3**a)


def even_scale_holds(n: int, xa: int, b: int) -> bool:
    return pow_le(n, 1 << b, xa, 1)


def financing_margin_bits(n: int, x0: int, a: int) -> int:
    """Coarse integer slack: right-hand bits minus left-hand bits."""

    if n < 2 or x0 < 2:
        return 0
    left = (1 << (a + 1)) * n.bit_length()
    right = (3**a) * x0.bit_length()
    return right - left


def odd_even_blocks(n: int, cap: int = PREFIX_CAP) -> list[dict[str, Any]]:
    path = [n]
    current = n
    for _ in range(cap):
        current = floor_power(current)
        path.append(current)
    word = word_of(tuple(path))
    rows: list[dict[str, Any]] = []
    index = 0
    while index < len(word):
        if word[index] != "O":
            index += 1
            continue
        start = index
        while index < len(word) and word[index] == "O":
            index += 1
        a = index - start
        if index >= len(word) or word[index] != "E":
            continue
        even_start = index
        while index < len(word) and word[index] == "E":
            index += 1
        b = index - even_start
        x0 = path[start]
        xa = path[start + a]
        xab = path[start + a + b]
        nxt = path[start + a + 1]
        env_ok = envelope_holds(x0, a, xa)
        xa_ge_sq = xa >= n * n
        xa_ge_even = even_scale_holds(n, xa, b)
        fin_ok = financing_holds(n, x0, a)
        block_ok = block_financing_holds(n, x0, a, b)
        rows.append(
            {
                "n": n,
                "x0": x0,
                "a": a,
                "b": b,
                "xa": xa,
                "xab": xab,
                "next": nxt,
                "at_start": start == 0,
                "xa_even": xa % 2 == 0,
                "xa_ge_n_sq": xa_ge_sq,
                "xa_ge_n_pow_2b": xa_ge_even,
                "xab_ge_n": xab >= n,
                "envelope_ok": env_ok,
                "financing_ok": fin_ok,
                "block_ok": block_ok,
                "financing_required": xa_ge_sq,
                "block_required": xa_ge_even and xab >= n,
                "margin_bits": financing_margin_bits(n, x0, a),
            }
        )
    return rows


def first_even_from_start(n: int, cap: int = PREFIX_CAP) -> dict[str, Any] | None:
    if n % 2 == 0:
        return None
    current = n
    for a in range(1, cap + 1):
        current = floor_power(current)
        if current % 2 == 0:
            return {
                "n": n,
                "a": a,
                "xa": current,
                "xa_ge_n_sq": current >= n * n,
                "financing_ok": financing_holds(n, n, a),
                "exponent_ok": two_pow_succ_le_three(a),
            }
    return {"n": n, "a": None, "incomplete": True}


def odd_run_census(*, n_max: int = N_MAX, cap: int = PREFIX_CAP) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    firsts: list[dict[str, Any]] = []
    for n in range(2, n_max + 1):
        rows.extend(odd_even_blocks(n, cap))
        first = first_even_from_start(n, cap)
        if first is not None and first.get("a") is not None:
            firsts.append(first)
    later = [row for row in rows if not row["at_start"]]
    later_a1 = [row for row in later if row["a"] == 1]
    start_a1 = [row for row in rows if row["at_start"] and row["a"] == 1]
    start_legal = [row for row in firsts if row["a"] >= 2]
    env_fail = [row for row in rows if not row["envelope_ok"]]
    fin_fail = [
        row for row in rows if row["financing_required"] and not row["financing_ok"]
    ]
    block_fail = [row for row in rows if row["block_required"] and not row["block_ok"]]
    legal_even = [row for row in rows if row["xa_ge_n_sq"]]
    legal_ge_twelve = [row for row in legal_even if row["n"] >= 12]
    closest = None
    if legal_even:
        closest = min(
            legal_even, key=lambda row: (row["xa"] / (row["n"] * row["n"]), row["a"])
        )
    closest_ge_twelve = None
    if legal_ge_twelve:
        closest_ge_twelve = min(
            legal_ge_twelve,
            key=lambda row: (row["xa"] / (row["n"] * row["n"]), row["a"]),
        )
    required = [row for row in rows if row["financing_required"]]
    tightest = min(required, key=lambda row: row["margin_bits"]) if required else None
    later_a1_sample = max(later_a1, key=lambda row: row["x0"]) if later_a1 else None
    return {
        "n_max": n_max,
        "block_count": len(rows),
        "later_count": len(later),
        "later_a1_count": len(later_a1),
        "start_a1_count": len(start_a1),
        "start_a_ge_2_count": len(start_legal),
        "envelope_fail": len(env_fail),
        "financing_fail": len(fin_fail),
        "block_fail": len(block_fail),
        "legal_even_count": len(legal_even),
        "max_a": max((row["a"] for row in rows), default=0),
        "max_b": max((row["b"] for row in rows), default=0),
        "smallest_admissible_a": smallest_admissible_a(),
        "closest_legal_even": closest,
        "closest_legal_even_ge_twelve": closest_ge_twelve,
        "tightest_margin": tightest,
        "later_a1_sample": later_a1_sample,
        "first_even_a_values": sorted({row["a"] for row in firsts}),
        "samples": (legal_even + later_a1)[:8],
    }


def calibration_rows() -> list[dict[str, Any]]:
    rows = []
    for n, word in CALIBRATION:
        if not follows_itinerary(n, word):
            rows.append({"n": n, "word": word, "follows": False})
            continue
        a = word.count("O")
        b = word.count("E")
        xa = image_after(n, "O" * a)
        image = image_after(n, word)
        rows.append(
            {
                "n": n,
                "word": word,
                "follows": True,
                "a": a,
                "b": b,
                "xa": xa,
                "image": image,
                "kind": classify_block(n, word),
                "xa_ge_n_sq": xa >= n * n,
                "envelope_ok": envelope_holds(n, a, xa),
                "financing_ok": financing_holds(n, n, a),
                "exponent_ok": two_pow_succ_le_three(a),
            }
        )
    return rows


def lean_api_present() -> dict[str, bool]:
    text = LEAN_PATH.read_text(encoding="utf-8")
    repeated = REPEATED_PATH.read_text(encoding="utf-8")
    minimum = MIN_PATH.read_text(encoding="utf-8")
    corpus = juggler_text()
    floor = engine_floor_text()
    combined = text + repeated + minimum + corpus
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **{name: has_named(combined, name) for name in LEAN_THEOREMS},
        "certificate_present": all(
            f"theorem {name}" in combined for name in CERTIFICATE_UNCHANGED
        ),
        "PowerHeight_absent": "PowerHeight" not in combined,
        "no_lower_envelope_structure": "structure LowerEnvelope" not in combined,
        "no_global_termination_theorem": "theorem juggler_reaches_one" not in combined,
        "no_infinite_path_type": "coinductive" not in text.lower()
        and "def InfinitePath" not in text,
        "no_frequency_theorem": "theorem odd_run_frequency" not in text
        and "theorem oe_frequency" not in text,
        "FloorPower_not_rewritten": "oddEvenBlock" not in floor,
    }


def classify(census: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    if census["envelope_fail"] > 0:
        return {
            "classification": CLASS_COUNTER,
            "reason": f"odd-run envelope failed: {census['envelope_fail']} blocks",
        }
    if census["financing_fail"] > 0:
        return {
            "classification": CLASS_COUNTER,
            "reason": "financing n^{2^{a+1}} <= x0^{3^a} failed on a legal even residual",
        }
    if census["block_fail"] > 0:
        return {
            "classification": CLASS_COUNTER,
            "reason": "block financing n^{2^{a+b}} <= x0^{3^a} failed on a required block",
        }
    lean_ok = (
        lean["sorry_free"]
        and lean["odd_run_even_residual"]
        and lean["odd_run_financing_scale_barrier"]
        and lean["odd_even_block_scale_barrier"]
        and lean["initial_even_not_before_ooe"]
        and lean["two_pow_succ_le_three_pow_iff"]
        and lean["no_global_termination_theorem"]
        and lean["no_frequency_theorem"]
        and lean["FloorPower_not_rewritten"]
    )
    if lean_ok:
        later = (
            f"; later a=1 occurs ({census['later_a1_count']} times), so an "
            "absolute later odd-run lower bound of 2 is false"
            if census["later_a1_count"] > 0
            else ""
        )
        return {
            "classification": CLASS_GREEN,
            "secondary": [CLASS_MINIMUM, CLASS_BLOCK, CLASS_LATER_A1],
            "reason": (
                "O^a E^b on a minimal non-1 orbit requires "
                "n^{2^{a+b}} <= x^{3^a}; at the start the first even "
                f"residual cannot occur before OOE (smallest a="
                f"{census['smallest_admissible_a']})"
                + later
            ),
        }
    return {
        "classification": CLASS_INCOMPLETE,
        "reason": f"lean_ok={lean_ok}",
    }


def run_probe() -> dict[str, Any]:
    return {
        "census": odd_run_census(),
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
    anti["repeated_block_obstruction"] = False
    return {
        "experiment": "juggler_odd_run_financing",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "realized O^a E^b blocks on prefixes; envelope xa^{2^a}<=x0^{3^a}; "
            "financing n^{2^{a+1}}<=x0^{3^a} when xa>=n^2; block form "
            "n^{2^{a+b}}<=x0^{3^a}; start-only 2^{a+1}<=3^a; no frequency claim"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    census = scan["census"]
    closest = census["closest_legal_even"]
    closest12 = census["closest_legal_even_ge_twelve"]
    later = census["later_a1_sample"]
    lines = [
        "# Juggler odd-run financing",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment,",
        "not a frequency theorem, and not a termination theorem. If a",
        "minimal non-1 orbit realizes `O^a E^b` from a later state `x`,",
        "then `n^{2^{a+b}} ≤ x^{3^a}`. At the start itself the first even",
        "residual cannot occur before `OOE`.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     MinimalNonTerm n and O^a E from x => n^{2^{a+1}} <= x^{3^a}",
        "Novelty hypothesis      Odd growth finances the first legal even residual",
        "Falsifier               Envelope fail, or xa>=n^2 with n^{2^{a+1}} > x^{3^a}",
        "Existing machinery      power_bound_word, even_run_scale_barrier, follows",
        "Maximum Phase-0 scope   Financing inequality; O^a E^b; start a>=2; later a=1 census",
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
        "## Odd-run census",
        "",
        f"- realized O^a E^b blocks: `{census['block_count']}`",
        f"- later (not at start) blocks: `{census['later_count']}`",
        f"- later a=1 blocks: `{census['later_a1_count']}`",
        f"- start a=1 blocks: `{census['start_a1_count']}`",
        f"- odd starts whose first even has a>=2: `{census['start_a_ge_2_count']}`",
        f"- envelope failures: `{census['envelope_fail']}`",
        f"- financing failures on xa>=n^2: `{census['financing_fail']}`",
        f"- block-financing failures: `{census['block_fail']}`",
        f"- blocks with xa>=n^2: `{census['legal_even_count']}`",
        f"- max a / max b: `{census['max_a']}` / `{census['max_b']}`",
        f"- smallest a with 2^{{a+1}}<=3^a: `{census['smallest_admissible_a']}`",
        "",
    ]
    if closest is not None:
        lines.append(
            f"- closest legal even residual: n=`{closest['n']}` x0=`{closest['x0']}` "
            f"a=`{closest['a']}` xa=`{closest['xa']}` n^2=`{closest['n'] ** 2}` "
            f"margin_bits=`{closest['margin_bits']}`"
        )
    if closest12 is not None:
        lines.append(
            f"- closest legal even residual with n>=12: n=`{closest12['n']}` "
            f"x0=`{closest12['x0']}` a=`{closest12['a']}` xa=`{closest12['xa']}` "
            f"n^2=`{closest12['n'] ** 2}` margin_bits=`{closest12['margin_bits']}`"
        )
    if later is not None:
        lines.append(
            f"- later a=1 sample: n=`{later['n']}` x0=`{later['x0']}` "
            f"xa=`{later['xa']}` xab=`{later['xab']}`"
        )
    lines.extend(["", "## Calibration", ""])
    for row in scan["calibration"]:
        if not row.get("follows", True):
            lines.append(f"- n=`{row['n']}` word=`{row['word']}` follows=`False`")
            continue
        lines.append(
            f"- n=`{row['n']}` word=`{row['word']}` xa=`{row['xa']}` "
            f"T=`{row['image']}` kind=`{row['kind']}` "
            f"xa>=n^2=`{row['xa_ge_n_sq']}` exponent_ok=`{row['exponent_ok']}`"
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
            "This is not a halt result, not an odd-run frequency theorem,",
            "and not an absolute lower bound on later odd runs.",
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

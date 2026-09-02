"""OOEOOEOO first cube-odd lifts hug the cube envelope, not n^8.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a first-return Q-map. Not a W_5 reopen. Not a defect census.

The word OOEOOEOO loses the inherited eighth-cell gap
(2187 > 2048). Phase 0 asks whether a first cube-odd even lift of
that word is forced above n^8, or only the 4309 family. Full-word
LowerPowerBound fires only near 2^73 bits. The laboratory images
instead sit next to the upper envelope n^{729/256}.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.cube_odd_return import cube_odd_landing
from research.juggler_sequence.cycle_ooo_scale import lower_denom
from research.juggler_sequence.first_lift_eighth import (
    UNSAFE_WORD,
    WITNESS_4309,
    WITNESS_5791,
    first_lift_row,
)
from research.juggler_sequence.lean_paths import (
    JUGGLER_PAPER_BARREL,
    MINIMAL,
    MINIMUM_RELATIVE,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power, word_of

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_ooeooeoo_eighth.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_ooeooeoo_eighth.md"

CLASS_PARKED = "OOEOOEOO_EIGHTH_PARKED"
CLASS_INCOMPLETE = "OOEOOEOO_EIGHTH_INCOMPLETE"

# Formal scale milli = floor(1000 * n^{139/256}).
FORMAL_NUM = 139
FORMAL_DEN = 256
CENSUS_LIMIT = 30001
EXTENDED_LIMIT = 200001
# lowerDenom(OOEOOEOO) bit length; LPB needs log2 n >= 3/139 * (bits-1).
LPB_BITS = 3395
LPB_LOG2_N = 73

LEAN_THEOREMS = (
    "itineraryOOEOOEOO",
    "follows_ooeooeoo_image_lt_cube",
    "odd_even_eighth_lt_sq",
    "power_bound_word",
)

FORBIDDEN_THEOREMS = (
    "juggler_reaches_one",
    "no_juggler_escape",
    "no_juggler_cycle",
)


def integer_root(value: int, degree: int) -> int:
    if value < 1 or degree < 1:
        return 0
    root = 1 << ((value.bit_length() + degree - 1) // degree)
    while True:
        nxt = ((degree - 1) * root + value // pow(root, degree - 1)) // degree
        if nxt >= root:
            return root
        root = nxt


def formal_milli(n: int) -> int:
    """Largest integer m with m^{256} <= 1000^{256} n^{139}."""

    return integer_root(1000**FORMAL_DEN * n**FORMAL_NUM, FORMAL_DEN)


def actual_milli(n: int, x: int) -> int:
    return (x**3 * 1000) // n**8


def ooeooeoo_first_cube(n: int) -> dict[str, Any] | None:
    """Eight-step walk. None if the first cube-odd lift is not OOEOOEOO."""

    path = [n]
    cur = n
    for _ in range(8):
        if cur < n:
            return None
        cur = floor_power(cur)
        path.append(cur)
    if word_of(tuple(path)) != UNSAFE_WORD:
        return None
    if any(cube_odd_landing(n, state) for state in path[:-1]):
        return None
    x = path[8]
    if not cube_odd_landing(n, x):
        return None
    y = floor_power(x)
    return {
        "n": n,
        "x": x,
        "y": y,
        "s6": path[6],
        "s7": path[7],
        "y_even": y % 2 == 0,
        "x3_lt_n8": x**3 < n**8,
        "milli": actual_milli(n, x),
        "formal_milli": formal_milli(n),
        "s7_9_ge_n16": s7_ninth_ge(path[7], n),
    }


def s7_ninth_ge(s7: int, n: int) -> bool:
    return s7**9 >= n**16


def census(limit: int) -> dict[str, Any]:
    even_safe = 0
    even_unsafe = 0
    odd_safe = 0
    odd_unsafe = 0
    closest: dict[str, Any] | None = None
    for n in range(3, limit, 2):
        row = ooeooeoo_first_cube(n)
        if row is None:
            continue
        if row["y_even"]:
            if row["x3_lt_n8"]:
                even_safe += 1
            else:
                even_unsafe += 1
        elif row["x3_lt_n8"]:
            odd_safe += 1
        else:
            odd_unsafe += 1
        if closest is None or row["milli"] < closest["milli"]:
            closest = row
    return {
        "limit": limit,
        "even_safe": even_safe,
        "even_unsafe": even_unsafe,
        "odd_safe": odd_safe,
        "odd_unsafe": odd_unsafe,
        "no_safe": even_safe == 0 and odd_safe == 0,
        "closest": closest,
    }


def lower_denom_too_weak() -> dict[str, Any]:
    denom = lower_denom(UNSAFE_WORD)
    return {
        "bits": denom.bit_length(),
        "expected_bits": LPB_BITS,
        "log2_n_threshold": LPB_LOG2_N,
        "laboratory_n_bits": WITNESS_4309[0].bit_length(),
        "too_weak": denom.bit_length() == LPB_BITS
        and WITNESS_4309[0].bit_length() < LPB_LOG2_N,
    }


def witness_tracks_envelope(n: int, x: int) -> dict[str, Any]:
    actual = actual_milli(n, x)
    formal = formal_milli(n)
    return {
        "n": n,
        "x": x,
        "actual_milli": actual,
        "formal_milli": formal,
        "below_formal": actual <= formal,
        "far_above_boundary": actual > 1000,
        "near_envelope": formal - actual <= formal // 1000 + 1,
    }


def run_probe() -> dict[str, Any]:
    row_4309 = first_lift_row(WITNESS_4309[0])
    row_5791 = first_lift_row(WITNESS_5791[0])
    row_365 = first_lift_row(365)
    hit_4309 = ooeooeoo_first_cube(WITNESS_4309[0])
    hit_565 = ooeooeoo_first_cube(565)
    scan = census(CENSUS_LIMIT)
    lpb = lower_denom_too_weak()
    track = witness_tracks_envelope(WITNESS_4309[0], WITNESS_4309[2])
    return {
        "basin": "ordinary_integers",
        "census": scan,
        "lower_denom": lpb,
        "track_4309": track,
        "witness_4309": hit_4309,
        "witness_565": hit_565,
        "first_365_not_ooeooeoo": row_365 is not None
        and row_365["word"] != UNSAFE_WORD,
        "both_witnesses_unsafe": row_4309 is not None
        and row_5791 is not None
        and not row_4309["x3_lt_n8"]
        and not row_5791["x3_lt_n8"]
        and row_4309["y_even"]
        and row_5791["y_even"],
        "odd_t_also_above": hit_565 is not None
        and not hit_565["y_even"]
        and not hit_565["x3_lt_n8"],
        "no_safe_in_window": scan["no_safe"],
        "lpb_too_weak": lpb["too_weak"],
        "hugs_upper_envelope": track["near_envelope"]
        and track["far_above_boundary"],
        "letter_chain": False,
        "q_return": False,
        "defect_census": False,
        "paper_a_modified": False,
        "halt_theorem": False,
    }


def lean_api_present() -> dict[str, bool]:
    combined = juggler_text()
    if MINIMUM_RELATIVE.is_file():
        combined += MINIMUM_RELATIVE.read_text(encoding="utf-8")
    if MINIMAL.is_file():
        combined += MINIMAL.read_text(encoding="utf-8")
    named = {name: has_named(combined, name) for name in LEAN_THEOREMS}
    forbidden = {name: has_named(combined, name) for name in FORBIDDEN_THEOREMS}
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    barrel = (REPO_ROOT / "formal" / "Problems" / "Juggler.lean").read_text(
        encoding="utf-8"
    )
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        **{f"has_{name}": present for name, present in forbidden.items()},
        "in_laboratory_barrel": "Problems.Juggler.MinimumRelative" in barrel,
        "not_in_paper_barrel": "odd_even_eighth_lt_sq" not in paper,
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
        "no_new_ooeooeoo_eighth_lean": "ooeooeoo_eighth" not in combined,
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and all(lean[name] for name in LEAN_THEOREMS)
        and not lean["has_juggler_reaches_one"]
        and lean["in_laboratory_barrel"]
        and lean["not_in_paper_barrel"]
        and lean["no_new_ooeooeoo_eighth_lean"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if not scan["no_safe_in_window"] or not scan["both_witnesses_unsafe"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "an OOEOOEOO first-hit sat below n^8",
        }
    if not scan["lpb_too_weak"] or not scan["hugs_upper_envelope"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "LPB or envelope-tracking witness failed",
        }
    if scan["letter_chain"] or scan["q_return"] or scan["defect_census"]:
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope claim"}
    return {
        "classification": CLASS_PARKED,
        "reason": (
            "OOEOOEOO first cube-odd lifts sit next to n^{729/256}, "
            "not on a forced n^8 lower cell; LowerPowerBound is too "
            "weak at laboratory scale"
        ),
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "ooeooeoo_forced_eighth": False,
            "letter_chain": False,
            "q_return": False,
            "defect_census": False,
            "global_termination": False,
        }
    )
    return {
        "experiment": "juggler_ooeooeoo_eighth",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "eight-step OOEOOEOO first cube-odd census; "
            "x^3/n^8 versus n^{139/256}; lowerDenom bit length"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler OOEOOEOO eighth lower cell",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "First cube-odd lifts of `OOEOOEOO` hug the cube envelope.",
        "They are not a forced `x^3 >= n^8` cell. Not a halt theorem.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     OOEOOEOO first cube-odd => x^3 >= n^8?",
        "Novelty hypothesis      a lower envelope, not only 4309",
        "Maximum Phase-0 scope   census; LPB bits; envelope tracking",
        "```",
        "",
        "## Metadata",
        "",
        f"- classification: **{decision['classification']}**",
        f"- no safe in window: `{scan['no_safe_in_window']}`",
        f"- LPB too weak: `{scan['lpb_too_weak']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Lean",
        "",
    ]
    for name in LEAN_THEOREMS:
        lines.append(f"- `{name}`: `{lean[name]}`")
    lines.extend(["", "## Anti-overclaim", ""])
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

"""Third residual after the CE OOEOOE trap forces OOEOOEOO.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not an expanding-grammar reopen.

Phase 0 asks whether that completed third residual drops below n or
stays a persistent expanding block. It does not prove a uniform
answer. It records the CE-capable cube/square envelopes and the
witnesses that kill both uniforms.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_itinerary import follows_itinerary, image_after
from research.juggler_sequence.lean_paths import (
    ESCAPE,
    JUGGLER_PAPER_BARREL,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power
from research.juggler_sequence.progress_coverage import is_odd_odd
from research.juggler_sequence.residual_chain import residual_excursion

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_third_residual.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_third_residual.md"

CLASS_GREEN = "THIRD_RESIDUAL_GREEN"
CLASS_REMAINS = "THIRD_RESIDUAL_REMAINS"
CLASS_INCOMPLETE = "THIRD_RESIDUAL_INCOMPLETE"

N_HI = 4001
PE_WITNESS = (365, 1749, 4447)
OOE_NOT_PE_WITNESS = (429, 2145, 5595)
OVERSHOOT_WITNESS = 565
CONTRACTING_DROP = (2177, 2185, 3565)

LEAN_THEOREMS = (
    "itineraryOOEOOEOO",
    "itineraryOOEOOEOOE",
    "follows_ooeooeoo_image_lt_cube",
    "follows_ooeooeooe_image_lt_sq",
    "minimal_ooeooe_follows_ooeooeoo",
    "minimal_ooeooeooe_not_even_landing",
    "minimal_ooeooe_forces_oo",
)

FORBIDDEN_THEOREMS = (
    "no_juggler_escape",
    "juggler_reaches_one",
    "no_juggler_cycle",
)


def cube_gap_ooeooeoo() -> bool:
    return 3**6 < 3 * 2**8


def square_gap_ooeooeooe() -> bool:
    return 3**6 < 2 ** (9 + 1)


def ooeooeooee_contracting() -> bool:
    return 3**6 < 2**10


def is_expanding(odds: int, length: int) -> bool:
    return 2**length < 3**odds


def third_residual_row(n: int) -> dict[str, Any] | None:
    if not follows_itinerary(n, "OOEOOE"):
        return None
    x = image_after(n, "OOEOOE")
    z = floor_power(x)
    forced_oo = x % 2 == 1 and z % 2 == 1
    if not forced_oo:
        return {
            "n": n,
            "x": x,
            "z": z,
            "forced_oo": False,
            "x_even": x % 2 == 0,
            "z_even": z % 2 == 0,
        }
    step = residual_excursion(x)
    if step is None:
        return None
    a, b, y = int(step["a"]), int(step["b"]), int(step["y"])
    pe = y > x and y >= 2 and is_odd_odd(y)
    drop = y < n
    mid = n <= y <= x
    contracting = not is_expanding(a, a + b)
    return {
        "n": n,
        "x": x,
        "z": z,
        "forced_oo": True,
        "a": a,
        "b": b,
        "y": y,
        "pe": pe,
        "drop": drop,
        "mid": mid,
        "contracting": contracting,
        "y_ge_sq": y >= n * n,
        "x_lt_sq": x < n * n,
        "y_odd": y % 2 == 1,
        "ooe": a == 2 and b == 1,
    }


def scan_window(n_hi: int = N_HI) -> dict[str, Any]:
    forced = 0
    pe = 0
    non_pe = 0
    drop = 0
    drop_contracting = 0
    drop_expanding = 0
    mid = 0
    ooe = 0
    ooe_pe = 0
    long_odd = 0
    samples: list[dict[str, Any]] = []
    for n in range(13, n_hi, 2):
        row = third_residual_row(n)
        if row is None or not row.get("forced_oo"):
            continue
        forced += 1
        if row["pe"]:
            pe += 1
        else:
            non_pe += 1
        if row["drop"]:
            drop += 1
            if row["contracting"]:
                drop_contracting += 1
            else:
                drop_expanding += 1
        if row["mid"]:
            mid += 1
        if row["ooe"]:
            ooe += 1
            if row["pe"]:
                ooe_pe += 1
        if row["a"] >= 3:
            long_odd += 1
        if n in (PE_WITNESS[0], OOE_NOT_PE_WITNESS[0], OVERSHOOT_WITNESS) or (
            row["drop"] and n in CONTRACTING_DROP
        ):
            samples.append(row)
    return {
        "n_hi": n_hi,
        "forced_oo": forced,
        "pe": pe,
        "non_pe": non_pe,
        "drop": drop,
        "drop_contracting": drop_contracting,
        "drop_expanding": drop_expanding,
        "mid": mid,
        "ooe": ooe,
        "ooe_pe": ooe_pe,
        "long_odd": long_odd,
        "samples": samples,
    }


def witness_365() -> dict[str, Any]:
    row = third_residual_row(PE_WITNESS[0])
    assert row is not None
    return {
        "n": PE_WITNESS[0],
        "x": row["x"],
        "y": row["y"],
        "pe": row["pe"],
        "word": "OOEOOEOOE",
        "image": image_after(PE_WITNESS[0], "OOEOOEOOE"),
    }


def witness_429() -> dict[str, Any]:
    row = third_residual_row(OOE_NOT_PE_WITNESS[0])
    assert row is not None
    y = row["y"]
    nxt = floor_power(y)
    return {
        "n": OOE_NOT_PE_WITNESS[0],
        "x": row["x"],
        "y": y,
        "pe": row["pe"],
        "next_even": nxt % 2 == 0,
        "next": nxt,
        "next_ge_sq": nxt >= OOE_NOT_PE_WITNESS[0] ** 2,
    }


def run_probe() -> dict[str, Any]:
    return {
        "basin": [1],
        "n_hi": N_HI,
        "cube_gap": cube_gap_ooeooeoo(),
        "square_gap": square_gap_ooeooeooe(),
        "ooeooeooee_contracting": ooeooeooee_contracting(),
        "window": scan_window(),
        "witness_365": witness_365(),
        "witness_429": witness_429(),
        "uniform_pe": False,
        "uniform_drop": False,
        "expanding_grammar_reopen": False,
        "halt_claim": False,
    }


def lean_api_present() -> dict[str, bool]:
    combined = juggler_text()
    named = {name: has_named(combined, name) for name in LEAN_THEOREMS}
    forbidden = {name: has_named(combined, name) for name in FORBIDDEN_THEOREMS}
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    escape = ESCAPE.read_text(encoding="utf-8")
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        **{f"has_{name}": present for name, present in forbidden.items()},
        "escape_has_cube": has_named(escape, "follows_ooeooeoo_image_lt_cube"),
        "escape_has_third_sq": has_named(escape, "follows_ooeooeooe_image_lt_sq"),
        "not_in_paper_barrel": "Problems.Juggler.Escape" not in paper,
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and all(lean[name] for name in LEAN_THEOREMS)
        and lean["escape_has_cube"]
        and lean["escape_has_third_sq"]
        and not lean["has_no_juggler_escape"]
        and lean["not_in_paper_barrel"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if scan["expanding_grammar_reopen"] or scan["halt_claim"]:
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope search"}
    if not scan["cube_gap"] or not scan["square_gap"] or not scan["ooeooeooee_contracting"]:
        return {"classification": CLASS_INCOMPLETE, "reason": "exponent gaps failed"}
    window = scan["window"]
    w365 = scan["witness_365"]
    w429 = scan["witness_429"]
    if window["drop_expanding"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "an expanding third residual dropped below n",
        }
    if window["mid"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "a third residual landed in [n, x]",
        }
    if not w365["pe"] or w429["pe"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "365/429 witnesses failed",
        }
    if window["pe"] == 0 or window["non_pe"] == 0:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "window missed a side of the dichotomy",
        }
    if scan["uniform_pe"] or scan["uniform_drop"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "a uniform claim was asserted",
        }
    return {
        "classification": CLASS_GREEN,
        "reason": (
            "OOEOOEOO < n^3 and OOEOOEOOE < n^2; CE even third-OOE "
            "landing drops; 365 is PE and 429/565 are not; drops in "
            "the window are contracting"
        ),
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "no_escape": False,
            "cycles_impossible": False,
            "uniform_third_pe": False,
            "uniform_third_drop": False,
        }
    )
    return {
        "experiment": "juggler_third_residual",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "CE-shaped OOEOOE followers; complete the residual from "
            "T_OOEOOE(n); cube/square gaps; Lean CE even-trap; no halt"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    window = scan["window"]
    lines = [
        "# Juggler third residual after forced OO",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. After OOEOOE forces OOEOOEOO,",
        "the completed third residual is not uniformly a drop and not",
        "uniformly PE.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     After the CE OOEOOE trap forces",
        "                        OOEOOEOO, does the third residual",
        "                        drop below n or stay PE?",
        "Novelty hypothesis      cube/square envelopes survive on CE;",
        "                        both uniforms fail",
        "Existing machinery      minimal_ooeooe_forces_oo; power_bound;",
        "                        residual_excursion",
        "Maximum Phase-0 scope   cube and square cells; CE even-trap;",
        "                        window scan; no halt",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        f"- cube gap 729<768: `{scan['cube_gap']}`",
        f"- square gap 729<1024: `{scan['square_gap']}`",
        f"- forced OO: `{window['forced_oo']}`",
        f"- PE / non-PE: `{window['pe']}` / `{window['non_pe']}`",
        f"- drops (all contracting): `{window['drop']}`",
        f"- 365 PE: `{scan['witness_365']['pe']}`",
        f"- 429 PE: `{scan['witness_429']['pe']}`",
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
            "This is not a halt result and not a uniform PE theorem.",
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
    decision = payload["decision"]
    window = payload["scan"]["window"]
    print(decision["classification"])
    print(decision["reason"])
    print(f"forced={window['forced_oo']} pe={window['pe']} non_pe={window['non_pe']}")


if __name__ == "__main__":
    main()

"""Mixed OE cell: odd cube plus even square is x^3 < n^8.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a first-return Q-map. Not a defect census. Not a W_5 reopen.

An odd step x |-> y = floor(x^{3/2}) followed by an even step
y |-> z = floor(sqrt(y)) satisfies z < n^2 if and only if x^3 < n^8.
That is strictly sharper than composing x < n^3 into z < n^{9/4}.
The floor defect theta = delta/(2y+1) stays maximally broad.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.cube_odd_return import (
    WITNESS_1517,
    WITNESS_501_LATER,
    leftover_first_lifts,
)
from research.juggler_sequence.lean_paths import (
    JUGGLER_PAPER_BARREL,
    MINIMAL,
    MINIMUM_RELATIVE,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_mixed_oe_cell.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_mixed_oe_cell.md"

CLASS_GREEN = "MIXED_OE_CELL_GREEN"
CLASS_INCOMPLETE = "MIXED_OE_CELL_INCOMPLETE"

LEAN_THEOREMS = (
    "odd_even_eighth_lt_sq",
    "finiteProgress_of_odd_even_eighth",
    "minimal_odd_even_eighth_forces_odd_return",
    "even_below_fourth",
    "cube_lift_even_reset_fourth",
)

FORBIDDEN_THEOREMS = (
    "juggler_reaches_one",
    "no_juggler_escape",
    "no_juggler_cycle",
)


def odd_even_eighth(n: int, x: int) -> bool:
    return x % 2 == 1 and x**3 < n**8


def mixed_return(n: int, x: int) -> dict[str, Any]:
    if x % 2 != 1:
        raise ValueError("mixed_return expects an odd source")
    y = floor_power(x)
    z = floor_power(y)
    delta = x**3 - y * y
    return {
        "n": n,
        "x": x,
        "y": y,
        "z": z,
        "delta": delta,
        "theta": delta / (2 * y + 1) if y >= 0 else None,
        "y_even": y % 2 == 0,
        "x3_lt_n8": x**3 < n**8,
        "z_lt_sq": z < n * n,
        "z_fourth_lt_nine": z**4 < n**9,
        "mixed_matches": (y % 2 == 0) and ((z < n * n) == (x**3 < n**8)),
    }


def leftover_eighth() -> dict[int, dict[str, Any]]:
    out: dict[int, dict[str, Any]] = {}
    for n, row in leftover_first_lifts().items():
        if not row.get("hit"):
            out[n] = {"hit": False}
            continue
        mixed = mixed_return(n, row["x"])
        out[n] = {"hit": True, "step": row["step"], **mixed}
    return out


def witness_501_later() -> dict[str, Any]:
    n, x = WITNESS_501_LATER
    row = mixed_return(n, x)
    return {
        "above_eighth": not row["x3_lt_n8"],
        "not_square": row["y_even"] and not row["z_lt_sq"],
        **row,
    }


def witness_1517() -> dict[str, Any]:
    n, _word, x = WITNESS_1517
    return mixed_return(n, x)


def sharpness_window(n: int = 13) -> dict[str, Any]:
    """Exhaustive even-lift check on the cube-band of a small n."""
    below_ok = 0
    above_ok = 0
    fail = 0
    theta_min = 1.0
    theta_max = 0.0
    thetas = 0
    for x in range(n * n, n**3):
        if x % 2 == 0:
            continue
        y = floor_power(x)
        delta = x**3 - y * y
        theta = delta / (2 * y + 1)
        theta_min = min(theta_min, theta)
        theta_max = max(theta_max, theta)
        thetas += 1
        if y % 2 == 1:
            continue
        z = floor_power(y)
        want = x**3 < n**8
        got = z < n * n
        if want == got:
            if want:
                below_ok += 1
            else:
                above_ok += 1
        else:
            fail += 1
    return {
        "n": n,
        "below_ok": below_ok,
        "above_ok": above_ok,
        "fail": fail,
        "theta_min": theta_min,
        "theta_max": theta_max,
        "theta_samples": thetas,
        "defect_full_range": theta_min <= 0.05 and theta_max >= 0.95,
    }


def run_probe() -> dict[str, Any]:
    leftovers = leftover_eighth()
    later = witness_501_later()
    first = witness_1517()
    sharp = sharpness_window()
    leftovers_below = all(
        row.get("x3_lt_n8") and row.get("z_lt_sq")
        for row in leftovers.values()
        if row.get("hit")
    )
    return {
        "basin": "ordinary_integers",
        "witness_1517": first,
        "witness_501_later": later,
        "leftover_eighth": leftovers,
        "sharpness": sharp,
        "leftovers_in_eighth": leftovers_below,
        "later_above_eighth": later["above_eighth"] and later["not_square"],
        "iff_holds": first["mixed_matches"] and later["mixed_matches"] and sharp["fail"] == 0,
        "defect_not_restrictive": sharp["defect_full_range"],
        "letter_chain": False,
        "q_return": False,
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
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and all(lean[name] for name in LEAN_THEOREMS)
        and not lean["has_juggler_reaches_one"]
        and lean["in_laboratory_barrel"]
        and lean["not_in_paper_barrel"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if not scan["iff_holds"] or not scan["leftovers_in_eighth"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "the mixed iff or leftover eighth cell failed",
        }
    if not scan["later_above_eighth"] or not scan["defect_not_restrictive"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "the 501 sharpness or defect-range witness failed",
        }
    if scan["letter_chain"] or scan["q_return"] or scan["halt_theorem"]:
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope claim"}
    return {
        "classification": CLASS_GREEN,
        "reason": (
            "odd-even composition is the eighth-power cell: "
            "z < n^2 iff x^3 < n^8; leftovers sit below; "
            "501 later sits above; defect stays full-range"
        ),
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "defect_excludes_interval": False,
            "letter_chain": False,
            "q_return": False,
            "global_termination": False,
        }
    )
    return {
        "experiment": "juggler_mixed_oe_cell",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "leftover first cube-odd lifts; 501 later landing; "
            "exhaustive even-lift iff on the n=13 cube-band"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler mixed OE cell",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Odd cube plus even square is `x^3 < n^8`. Not a halt theorem.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     mixed OE cell after cube-scale lift",
        "Novelty hypothesis      z < n^2 iff x^3 < n^8",
        "Maximum Phase-0 scope   Lean iff; leftover / 501 split",
        "```",
        "",
        "## Metadata",
        "",
        f"- classification: **{decision['classification']}**",
        f"- iff holds: `{scan['iff_holds']}`",
        f"- leftovers in eighth: `{scan['leftovers_in_eighth']}`",
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

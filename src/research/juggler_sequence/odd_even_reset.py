"""Odd-to-even reset interface: last odd, first even, post-even.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a source-descent replay, cube-crossing reopen, OddChain, Sigma
automaton, Z5, length-11, or power-cell hierarchy.

Phase 0 asks whether the quadruple (x, x_r, e, s) carries a coupled
reset identity that is not oe_block_scale, floorPower_odd_even_two_step_lt,
or EnvelopeState on O^r E.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.lean_paths import (
    JUGGLER_DIR,
    JUGGLER_PAPER_BARREL,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.odd_chain_minimality import (
    L_LAB,
    LONG_ODD_STARTS,
    extract_odd_runs,
    initial_odd_run,
    l_lab_chain,
)
from research.juggler_sequence.minimal_anchor_closure import trajectory_until_drop
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_odd_even_reset.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_odd_even_reset.md"

CLASS_CLOSED = "ODD_EVEN_RESET_CLOSED"
CLASS_PARK = "ODD_EVEN_RESET_PARK"
CLASS_GREEN = "ODD_EVEN_RESET_GREEN"
CLASS_INCOMPLETE = "ODD_EVEN_RESET_INCOMPLETE"

STARTS = (37, 69, 89, 365, 501, 1517, 6187)
CONTROLS = (365, 501, 1517, 6187)
GENERIC_HI = 201

EXISTING_LEAN = (
    "oe_block_scale",
    "oe_block_contracts",
    "floorPower_odd_even_two_step_lt",
    "floorPower_odd_sq_le_cube",
    "floorPower_even_sq_le",
    "EnvelopeState",
    "cube_lift_even_reset",
    "even_below_anchor_pow",
    "ReturnBelow",
)

FORBIDDEN_THEOREMS = (
    "juggler_reaches_one",
    "no_juggler_escape",
    "all_finiteProgress",
)

FORBIDDEN_NEW_API = (
    "OddEvenReset",
    "OddEvenResetRelation",
    "reset_defect_identity",
    "reset_source_bound",
    "reset_return_bound",
    "OddChain",
    "OddEscapeCorridor",
)

NEW_LEAN_FILES = (
    JUGGLER_DIR / "OddEvenReset.lean",
    JUGGLER_DIR / "OddEvenResetRelation.lean",
    JUGGLER_DIR / "OddChain.lean",
)


def reset_from_run(n: int, run: dict[str, Any]) -> dict[str, Any] | None:
    """Build (x, x_r, e, s) from an extract_odd_runs row."""

    e = run["even_reset"]
    if e is None:
        return None
    chain = run["chain"]
    x = chain[0]
    x_r = chain[-1]
    s = floor_power(e)
    delta = x_r**3 - e * e
    eps = e - s * s
    psi = 2 * eps * s * s + eps * eps + delta
    gap = x_r**3 - s**4
    r = len(chain)
    return {
        "n": n,
        "x": x,
        "r": r,
        "x_r": x_r,
        "e": e,
        "s": s,
        "s_odd": s % 2 == 1,
        "delta_odd": delta,
        "delta_even": eps,
        "psi": psi,
        "gap_xr3_s4": gap,
        "psi_match": gap == psi,
        "s4_le_xr3": s**4 <= x_r**3,
        "s4_lt_xr3": s**4 < x_r**3,
        "s_lt_xr": s < x_r,
        "s_lt_x": s < x,
        "s_ge_n": s >= n,
        "s4_le_x3": s**4 <= x**3,
        "t_s": floor_power(s),
        "t_s_lt_n": floor_power(s) < n,
    }


def next_odd_source(s: int, n: int, cap: int = 8) -> int | None:
    """Next AboveAnchor odd state at or after s."""

    cur = s
    for _ in range(cap + 1):
        if cur < n:
            return None
        if cur % 2 == 1:
            return cur
        cur = floor_power(cur)
    return None


def orbit_resets(n: int) -> dict[str, Any]:
    path = trajectory_until_drop(n)
    runs = extract_odd_runs(path, n)
    rows = []
    for run in runs:
        rec = reset_from_run(n, run)
        if rec is None:
            continue
        rec["x_next"] = next_odd_source(rec["s"], n)
        rows.append(rec)
    pairs = []
    for prev, cur in zip(rows, rows[1:]):
        pairs.append(
            {
                "x": prev["x"],
                "s": prev["s"],
                "x_next": prev["x_next"],
                "x2": cur["x"],
                "x2_lt_x": cur["x"] < prev["x"],
            }
        )
    triples = []
    for a, _b, c in zip(rows, rows[1:], rows[2:]):
        triples.append(
            {
                "x": a["x"],
                "x2": c["x"],
                "x2_lt_x": c["x"] < a["x"],
            }
        )
    return {
        "n": n,
        "count": len(rows),
        "resets": rows,
        "pairs": pairs,
        "triples": triples,
        "psi_ok": all(row["psi_match"] for row in rows),
        "s4_lt_ok": all(row["s4_lt_xr3"] for row in rows),
        "s_lt_xr_ok": all(row["s_lt_xr"] for row in rows),
        "s_lt_x_all": all(row["s_lt_x"] for row in rows),
        "s_lt_x_when_r1": all(row["s_lt_x"] for row in rows if row["r"] == 1),
        "s_lt_x_fails_r_ge_2": any(not row["s_lt_x"] and row["r"] >= 2 for row in rows),
        "two_episode_descent": all(item["x2_lt_x"] for item in triples) if triples else None,
    }


def generic_oe_resets(hi: int = GENERIC_HI) -> dict[str, Any]:
    """Independent odd-to-even steps, not required to be episode endpoints."""

    rows = []
    for x in range(3, hi, 2):
        e = floor_power(x)
        if e % 2 == 1:
            continue
        rec = reset_from_run(x, {"chain": [x], "even_reset": e})
        if rec is None:
            continue
        rows.append(rec)
    return {
        "hi": hi,
        "count": len(rows),
        "psi_ok": all(row["psi_match"] for row in rows),
        "s4_lt_ok": all(row["s4_lt_xr3"] for row in rows),
        "s_lt_xr_ok": all(row["s_lt_xr"] for row in rows),
        "s_lt_x_ok": all(row["s_lt_x"] for row in rows),
    }


def long_resets() -> dict[int, dict[str, Any]]:
    out: dict[int, dict[str, Any]] = {}
    for n in LONG_ODD_STARTS:
        run = initial_odd_run(n)
        rec = reset_from_run(n, run)
        if rec is not None:
            rec["x_next"] = next_odd_source(rec["s"], n)
        out[n] = rec
    lab = l_lab_chain()
    rec = reset_from_run(L_LAB, lab)
    if rec is not None:
        rec["x_next"] = next_odd_source(rec["s"], L_LAB)
        rec["t"] = lab["t"]
    out[L_LAB] = rec
    return out


def run_probe() -> dict[str, Any]:
    tables = {n: orbit_resets(n) for n in STARTS}
    generic = generic_oe_resets()
    long_rows = long_resets()
    all_rows = [row for n in STARTS for row in tables[n]["resets"]]
    triples = [item for n in STARTS for item in tables[n]["triples"]]
    two_ep_false = any(item["x2_lt_x"] is False for item in triples)
    s_lt_x_fail = any(not row["s_lt_x"] and row["r"] >= 2 for row in all_rows)
    leftover_first = {n: tables[n]["resets"][0] for n in CONTROLS if tables[n]["resets"]}
    even_s = [row for row in all_rows if not row["s_odd"]]
    first37 = tables[37]["resets"][0]
    sources37 = [row["x"] for row in tables[37]["resets"]]
    return {
        "basin": "ordinary_integers",
        "tables": {str(n): tables[n] for n in STARTS},
        "generic_oe": generic,
        "long_resets": {str(n): long_rows[n] for n in long_rows},
        "reset_count": len(all_rows),
        "psi_ok": all(tables[n]["psi_ok"] for n in STARTS) and generic["psi_ok"],
        "s4_lt_ok": all(tables[n]["s4_lt_ok"] for n in STARTS) and generic["s4_lt_ok"],
        "s_lt_xr_ok": all(tables[n]["s_lt_xr_ok"] for n in STARTS),
        "generic_s_lt_x": generic["s_lt_x_ok"],
        "s_lt_x_fails_long_run": s_lt_x_fail,
        "two_episode_descent_false": two_ep_false,
        "identity_is_generic_oe": generic["psi_ok"] and generic["s4_lt_ok"],
        "leftover_first_r_ge_2": all(row["r"] >= 2 for row in leftover_first.values()),
        "leftover_first_s_gt_x": all(not row["s_lt_x"] for row in leftover_first.values()),
        "s4_le_x3_all": all(row["s4_le_x3"] for row in all_rows),
        "even_s_second_even_always_progress": all(row["t_s_lt_n"] for row in even_s)
        if even_s
        else False,
        "first37": {
            "x": first37["x"],
            "r": first37["r"],
            "x_r": first37["x_r"],
            "e": first37["e"],
            "s": first37["s"],
            "s_odd": first37["s_odd"],
            "s_lt_x": first37["s_lt_x"],
            "psi_match": first37["psi_match"],
            "s4_lt_xr3": first37["s4_lt_xr3"],
        },
        "sources37": sources37,
        "letter_chain": False,
        "source_descent_reopen": False,
        "cube_crossing_reopen": False,
        "odd_even_reset_lean": False,
        "z5_reopen": False,
        "paper_a_modified": False,
        "halt_theorem": False,
    }


def lean_api_present() -> dict[str, bool]:
    combined = juggler_text()
    named = {name: has_named(combined, name) for name in EXISTING_LEAN}
    forbidden = {name: has_named(combined, name) for name in FORBIDDEN_THEOREMS}
    new_api = {name: has_named(combined, name) for name in FORBIDDEN_NEW_API}
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        **{f"has_{name}": present for name, present in forbidden.items()},
        **{f"has_api_{name}": present for name, present in new_api.items()},
        "new_lean_file": any(path.is_file() for path in NEW_LEAN_FILES),
        "not_in_paper_barrel": "OddEvenReset" not in paper
        and "reset_defect_identity" not in paper,
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and all(lean[name] for name in EXISTING_LEAN)
        and not lean["has_juggler_reaches_one"]
        and not lean["new_lean_file"]
        and not any(lean[f"has_api_{name}"] for name in FORBIDDEN_NEW_API)
        and lean["not_in_paper_barrel"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if (
        scan["letter_chain"]
        or scan["source_descent_reopen"]
        or scan["cube_crossing_reopen"]
        or scan["odd_even_reset_lean"]
        or scan["z5_reopen"]
        or scan["halt_theorem"]
    ):
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope claim"}
    if (
        scan["psi_ok"]
        and scan["s4_lt_ok"]
        and scan["s_lt_xr_ok"]
        and scan["generic_s_lt_x"]
        and scan["s_lt_x_fails_long_run"]
        and scan["two_episode_descent_false"]
        and scan["identity_is_generic_oe"]
    ):
        return {
            "classification": CLASS_CLOSED,
            "reason": (
                "x_r^3 - s^4 = 2 e_eps s^2 + e_eps^2 + delta is generic OE; "
                "s^4 < x_r^3 is oe_block_scale plus odd/even parity; "
                "s < x_r is floorPower_odd_even_two_step_lt; "
                "s < x fails for r>=2; two-episode descent is already false"
            ),
        }
    return {
        "classification": CLASS_PARK,
        "reason": "reset identity incomplete or not matched to existing lemmas",
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "independent_reset_identity": False,
            "source_reset_bound": False,
            "two_episode_descent": False,
            "odd_even_reset_lean": False,
            "source_descent_reopen": False,
            "z5_reopen": False,
            "global_termination": False,
        }
    )
    return {
        "experiment": "juggler_odd_even_reset",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "reset quadruples on 37/69/89/365/501/1517/6187; "
            "generic OE n<201; long starts 37/241/329; L-lab 33391"
        ),
    }


def _fmt(row: dict[str, Any] | None) -> str:
    if row is None:
        return "none"
    return (
        f"x=`{row['x']}` r=`{row['r']}` x_r=`{row['x_r']}` "
        f"e=`{row['e']}` s=`{row['s']}` s_odd=`{row['s_odd']}` "
        f"s_lt_x=`{row['s_lt_x']}`"
    )


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler odd-to-even reset interface",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Reset quadruple (x, x_r, e, s) versus generic OE floor identities.",
        "Not a halt theorem. Not a source-descent reopen.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     non-generic relation at odd-to-even reset",
        "Novelty hypothesis      (delta, eps) couples beyond EnvelopeState",
        "Maximum Phase-0 scope   named resets; generic OE; no Lean",
        "```",
        "",
        "## Metadata",
        "",
        f"- classification: **{decision['classification']}**",
        f"- resets: `{scan['reset_count']}`",
        f"- psi ok: `{scan['psi_ok']}`",
        f"- s^4 < x_r^3: `{scan['s4_lt_ok']}`",
        f"- s < x fails on long runs: `{scan['s_lt_x_fails_long_run']}`",
        f"- two-episode descent false: `{scan['two_episode_descent_false']}`",
        f"- leftover first runs have r>=2: `{scan['leftover_first_r_ge_2']}`",
        f"- leftover first s>x: `{scan['leftover_first_s_gt_x']}`",
        f"- s^4 <= x^3 on all named resets: `{scan['s4_le_x3_all']}`",
        f"- even-s second even always FiniteProgress: `{scan['even_s_second_even_always_progress']}`",
        f"- 37 sources: `{scan['sources37']}`",
        f"- 37 first reset: x=`{scan['first37']['x']}` r=`{scan['first37']['r']}` "
        f"x_r=`{scan['first37']['x_r']}` e=`{scan['first37']['e']}` "
        f"s=`{scan['first37']['s']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Named orbits",
        "",
    ]
    for n in STARTS:
        table = scan["tables"][str(n)]
        lines.append(f"- `{n}`: count=`{table['count']}`")
        for row in table["resets"]:
            lines.append(f"  - {_fmt(row)}")
    lines.extend(["", "## Long / L resets", ""])
    for key, row in scan["long_resets"].items():
        lines.append(f"- `{key}`: {_fmt(row)}")
    lines.extend(["", "## Existing Lean (unchanged)", ""])
    for name in EXISTING_LEAN:
        lines.append(f"- `{name}`: `{lean[name]}`")
    lines.extend(
        [
            f"- new Lean file: `{lean['new_lean_file']}`",
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
    print("count", payload["scan"]["reset_count"])
    first = payload["scan"]["tables"]["37"]["resets"][0]
    print("37 first", first["x"], first["r"], first["s"], first["s_lt_x"])


if __name__ == "__main__":
    main()

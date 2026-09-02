"""Non-escape spine: cycle-or-escape, and the CE OOEOOE trap.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not an escape-margin revival, not Paper B, not bunched-short, and not
a length-11 census.

Phase 0 records that every orbit eventually cycles or escapes, and
that a MinimalNonTerm start that follows OOEOOE is forced onto
another OO. Growing residual prefixes are not unbounded orbits.
"""

from __future__ import annotations

import json
from collections import Counter
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_word import follows_word, image_after
from research.juggler_sequence.lean_paths import (
    ESCAPE,
    JUGGLER_PAPER_BARREL,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.minimal_ooe_corridor import WORD, corridor_states
from research.juggler_sequence.odd_ooe_landing import first_event
from research.juggler_sequence.power_words import ANTI_OVERCLAIM, floor_power
from research.juggler_sequence.progress_coverage import is_odd_odd

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_non_escape.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_non_escape.md"

CLASS_GREEN = "NON_ESCAPE_SPINE_GREEN"
CLASS_REMAINS = "NON_ESCAPE_REMAINS"
CLASS_INCOMPLETE = "NON_ESCAPE_INCOMPLETE"

N_MIN = 12
N_HI = 801

# Finite growing residual prefix, not an unbounded orbit.
ESCAPE_PREFIX = (365, 763, 1749, 4447)

LEAN_THEOREMS = (
    "EscapesToInfinity",
    "EventuallyCycles",
    "not_escapes_iff_bounded",
    "bounded_trajectory_eventually_cycles",
    "cycles_or_escapes",
    "reachesOne_implies_eventually_cycles",
    "minimal_nonterm_cycles_or_escapes",
    "follows_ooeooe_image_lt_sq",
    "follows_ooeooeo_image_lt_sq",
    "minimal_ooeooe_not_even_landing",
    "minimal_ooeooe_forces_oo",
    "finiteProgress_of_ooeooe_even_landing",
    "no_nontrivial_cycle_no_bounded_nonterm",
)

FORBIDDEN_THEOREMS = (
    "no_juggler_escape",
    "juggler_reaches_one",
    "all_finiteProgress",
    "no_juggler_cycle",
    "no_cycle_word_length_eleven",
)


def iterate_floor(n: int, steps: int) -> int:
    current = n
    for _ in range(steps):
        current = floor_power(current)
    return current


def eventually_cycles(n: int, cap: int = 64) -> bool:
    seen: dict[int, int] = {}
    current = n
    for i in range(cap + 1):
        if current in seen:
            return seen[current] < i
        seen[current] = i
        current = floor_power(current)
    return False


def ooeooe_row(n: int) -> dict[str, Any] | None:
    states = corridor_states(n, WORD)
    if states is None:
        return None
    x = states["x6"]
    z = floor_power(x)
    drop = floor_power(x) if x % 2 == 0 else None
    even_next_drop = floor_power(z) if z % 2 == 0 else None
    return {
        "n": n,
        "odd_odd": is_odd_odd(n),
        "x": x,
        "x_even": x % 2 == 0,
        "x_below_sq": x < n * n,
        "x_ge_n": x >= n,
        "z": z,
        "z_even": z % 2 == 0,
        "z_below_sq": z < n * n,
        "even_landing_drop": drop < n if drop is not None else None,
        "even_z_drop": even_next_drop < n if even_next_drop is not None else None,
        "forced_oo": x % 2 == 1 and z % 2 == 1,
        "ce_shaped": x >= n and (x % 2 == 1) and z >= n,
    }


def scan_window(n_hi: int = N_HI) -> dict[str, Any]:
    follows = 0
    even_land = 0
    even_survive = 0
    odd_land = 0
    case_a = 0
    a_survive = 0
    case_b = 0
    x_ge_sq = 0
    z_ge_sq = 0
    firsts: Counter[str] = Counter()
    samples: list[dict[str, Any]] = []
    for n in range(13, n_hi, 2):
        row = ooeooe_row(n)
        if row is None:
            continue
        follows += 1
        if not row["x_below_sq"]:
            x_ge_sq += 1
        if row["x_even"]:
            even_land += 1
            if row["even_landing_drop"] is False:
                even_survive += 1
            firsts["even_landing_drop"] += 1
        else:
            odd_land += 1
            if not row["z_below_sq"]:
                z_ge_sq += 1
            if row["z_even"]:
                case_a += 1
                if row["even_z_drop"] is False:
                    a_survive += 1
                firsts["even_z_drop"] += 1
            else:
                case_b += 1
                firsts["forced_oo"] += 1
        if len(samples) < 8:
            samples.append(
                {
                    "n": n,
                    "x": row["x"],
                    "z": row["z"],
                    "x_even": row["x_even"],
                    "forced_oo": row["forced_oo"],
                }
            )
    return {
        "n_hi": n_hi,
        "follows": follows,
        "even_land": even_land,
        "even_survive": even_survive,
        "odd_land": odd_land,
        "case_a": case_a,
        "a_survive": a_survive,
        "case_b": case_b,
        "x_ge_sq": x_ge_sq,
        "z_ge_sq": z_ge_sq,
        "firsts": {k: v for k, v in firsts.most_common()},
        "samples": samples,
    }


def escape_prefix_row() -> dict[str, Any]:
    chain = list(ESCAPE_PREFIX)
    steps = []
    current = chain[0]
    ok = follows_word(current, WORD)
    land = image_after(current, WORD) if ok else None
    for nxt in chain[1:]:
        steps.append({"from": current, "to": nxt, "grows": nxt > current})
        current = nxt
    return {
        "chain": chain,
        "follows_ooeooe": ok,
        "landing": land,
        "landing_is_1749": land == 1749,
        "monotone": all(item["grows"] for item in steps),
        "unbounded_orbit": False,
        "steps": steps,
    }


def run_probe() -> dict[str, Any]:
    event_365 = first_event(365)
    event_89 = first_event(89)
    event_69 = corridor_states(69, WORD)
    return {
        "basin": [1],
        "n_min": N_MIN,
        "n_hi": N_HI,
        "square_cell_64_81": (1 << 7) > 3**4,
        "square_cell_128_243": (1 << 8) > 3**5,
        "window": scan_window(),
        "escape_prefix": escape_prefix_row(),
        "case_a_89": event_89,
        "case_b_365": event_365,
        "even_landing_69": event_69,
        "one_cycles": eventually_cycles(1),
        "length_eleven_census": False,
        "z5_cells": False,
        "paper_b_reopen": False,
        "escape_margin_m": False,
        "expanding_grammar": False,
        "bunched_short_reopen": False,
        "finite_coeff_stop_theorem": False,
    }


def lean_api_present() -> dict[str, bool]:
    combined = juggler_text()
    if ESCAPE.is_file():
        combined += ESCAPE.read_text(encoding="utf-8")
    named = {name: has_named(combined, name) for name in LEAN_THEOREMS}
    forbidden = {name: has_named(combined, name) for name in FORBIDDEN_THEOREMS}
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    escape_text = ESCAPE.read_text(encoding="utf-8") if ESCAPE.is_file() else ""
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        **{f"has_{name}": present for name, present in forbidden.items()},
        "in_laboratory_barrel": "Problems.Juggler.Escape" in (
            REPO_ROOT / "formal" / "Problems" / "Juggler.lean"
        ).read_text(encoding="utf-8"),
        "not_in_paper_barrel": "Escape" not in paper
        or "Problems.Juggler.Escape" not in paper,
        "no_halt_theorem": "theorem no_juggler_escape" not in escape_text,
        "no_coeff_stop_theorem": "theorem FiniteCoeffStopConjecture"
        not in escape_text,
        "FloorPower_not_rewritten": "CycleWord" not in engine_floor_text(),
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and all(lean[name] for name in LEAN_THEOREMS)
        and not lean["has_no_juggler_escape"]
        and not lean["has_juggler_reaches_one"]
        and not lean["has_no_juggler_cycle"]
        and lean["in_laboratory_barrel"]
        and lean["not_in_paper_barrel"]
        and lean["no_halt_theorem"]
        and lean["no_coeff_stop_theorem"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if (
        scan["length_eleven_census"]
        or scan["z5_cells"]
        or scan["paper_b_reopen"]
        or scan["escape_margin_m"]
        or scan["expanding_grammar"]
        or scan["bunched_short_reopen"]
        or scan["finite_coeff_stop_theorem"]
    ):
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope search"}
    window = scan["window"]
    prefix = scan["escape_prefix"]
    if window["x_ge_sq"] or window["even_survive"] or window["a_survive"]:
        return {
            "classification": CLASS_REMAINS,
            "reason": "an OOEOOE follower violated the even trap",
        }
    if not prefix["follows_ooeooe"] or not prefix["monotone"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "the 365 escape prefix failed",
        }
    if prefix["unbounded_orbit"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "a finite prefix was recorded as an unbounded orbit",
        }
    if window["follows"] == 0 or window["case_b"] == 0:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "no OOEOOE follower or no forced-OO event",
        }
    return {
        "classification": CLASS_GREEN,
        "reason": (
            "every scanned OOEOOE follower either drops on an even "
            "landing or even z, or is forced onto another OO; "
            "365->4447 is a finite escape prefix, not an unbounded orbit"
        ),
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "cycles_impossible": False,
            "no_escape": False,
            "length_eleven_census": False,
            "escape_margin_is_new_progress": False,
        }
    )
    return {
        "experiment": "juggler_non_escape",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "OOEOOE followers in an odd window; even-trap and forced-OO "
            "split; 365 residual prefix recorded as finite; Lean Escape "
            "module only; no halt theorem"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    window = scan["window"]
    prefix = scan["escape_prefix"]
    lines = [
        "# Juggler non-escape spine",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. Cycle-or-escape plus the CE",
        "OOEOOE trap. Growing residual prefixes are not unbounded",
        "orbits. Not Paper B, not escape-margin M, not bunched-short.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     MinimalNonTerm is a cycle or escape;",
        "                        OOEOOE forces another OO on a CE",
        "Novelty hypothesis      the even trap does not need image = n",
        "Existing machinery      bounded_prefix_not_nodup; wordOOEOOE;",
        "                        even_floorPower_lt_iff",
        "Maximum Phase-0 scope   Lean Escape module; OOEOOE window;",
        "                        one finite escape prefix",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        f"- square cells 64/81 and 128/243: `{scan['square_cell_64_81']}` / `{scan['square_cell_128_243']}`",
        f"- OOEOOE followers: `{window['follows']}`",
        f"- even land / survive: `{window['even_land']}` / `{window['even_survive']}`",
        f"- Case A / survive: `{window['case_a']}` / `{window['a_survive']}`",
        f"- forced OO: `{window['case_b']}`",
        f"- escape prefix: `{prefix['chain']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Attack 1 — cycle or escape",
        "",
        "A bounded orbit of length `M+2` in `[0, M]` repeats. That is",
        "`EventuallyCycles`. The negation is `EscapesToInfinity`.",
        "`ReachesOne` is the 1-cycle. On `MinimalNonTerm` a cycle",
        "stays `>= n`.",
        "",
        "## Attack 2 — OOEOOE without CycleMin return",
        "",
        "`power_bound_word` gives `x^{64} <= n^{81}`, so `x < n^2`.",
        "An even landing drops. The next odd image satisfies",
        "`z^{128} <= n^{243}`, so `z < n^2`. An even `z` drops. A CE",
        "is therefore forced onto another `OO`.",
        "",
        "## Attack 3 — finite escape prefixes",
        "",
        f"The chain `{prefix['chain']}` grows and follows `OOEOOE`.",
        "It is a finite residual prefix, not a proof of escape and",
        "not an unbounded orbit.",
        "",
    ]
    if window["samples"]:
        lines.append("## Window samples")
        lines.append("")
        for row in window["samples"]:
            lines.append(
                f"- n=`{row['n']}` x=`{row['x']}` z=`{row['z']}` "
                f"even_x=`{row['x_even']}` forced_oo=`{row['forced_oo']}`"
            )
        lines.append("")
    lines.extend(["## Lean", ""])
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
            "This is not a halt result, not a cycle exclusion, and not",
            "`FiniteCoeffStopConjecture`.",
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
    print(
        f"follows={window['follows']} even={window['even_land']} "
        f"A={window['case_a']} B={window['case_b']}"
    )


if __name__ == "__main__":
    main()

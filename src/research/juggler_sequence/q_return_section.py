"""First-return sections of residual Q-orbits.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a Q-descriptor reopen. Not first-return-below T^k(n)<n.
Not a ReturnSection Lean layer.

On leftover AboveAnchor paths, Q is already known to have no
compressed one-step law. Phase 0 asks whether any exact scale
section S_n(α) = {x : n <= x and x^A < n^B} has Poincaré returns
that are simpler than one-step Q. A section whose typical return
time is 1 is rejected: R_S is Q.
"""

from __future__ import annotations

import json
from collections import Counter
from pathlib import Path
from typing import Any

from research.juggler_sequence.block_map_q import (
    CONTROLS,
    CONTRAST,
    WINDOW_HI,
    q_blocks,
)
from research.juggler_sequence.minimal_anchor_closure import trajectory_until_drop
from research.juggler_sequence.lean_paths import (
    JUGGLER_DIR,
    JUGGLER_PAPER_BARREL,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.power_words import ANTI_OVERCLAIM

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_q_return_section.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_q_return_section.md"

CLASS_PARK = "Q_RETURN_SECTION_PARK"
CLASS_GREEN = "Q_RETURN_SECTION_GREEN"
CLASS_CLOSED = "Q_RETURN_SECTION_CLOSED"
CLASS_INCOMPLETE = "Q_RETURN_SECTION_INCOMPLETE"

# Exact membership x^A < n^B. No floats.
SECTIONS: tuple[tuple[str, int, int], ...] = (
    ("3/2", 2, 3),
    ("2", 1, 2),
    ("9/4", 4, 9),
    ("8/3", 3, 8),
    ("3", 1, 3),
)

EXISTING_LEAN = (
    "AboveAnchor",
    "oe_block_contracts",
    "ReturnBelow",
)

FORBIDDEN_THEOREMS = (
    "juggler_reaches_one",
    "no_juggler_escape",
    "all_finiteProgress",
)

FORBIDDEN_NEW_API = (
    "ReturnSection",
    "PermanentEscape",
    "ReturnOrder",
    "BlockMapQ",
)

NEW_LEAN_FILES = (
    JUGGLER_DIR / "ReturnSection.lean",
    JUGGLER_DIR / "BlockMapQ.lean",
)


def in_section(n: int, x: int, anum: int, bnum: int) -> bool:
    return x >= n and x**anum < n**bnum


def q_section_orbit(n: int) -> list[int]:
    """Starts and Q-images along q_blocks, consecutive duplicates dropped."""

    points: list[int] = []
    for row in q_blocks(n):
        if not points or points[-1] != row["x"]:
            points.append(row["x"])
        if points[-1] != row["Q"]:
            points.append(row["Q"])
    return points


def band_index(n: int, x: int) -> int:
    """Smallest section index containing x, or len(SECTIONS) if above all."""

    if x < n:
        return -1
    for idx, (_name, anum, bnum) in enumerate(SECTIONS):
        if x**anum < n**bnum:
            return idx
    return len(SECTIONS)


def first_return(
    n: int, orbit: list[int], index: int, anum: int, bnum: int
) -> dict[str, Any] | None:
    x = orbit[index]
    if not in_section(n, x, anum, bnum):
        return None
    peak = x
    saw_outside = False
    rest = orbit[index + 1 :]
    if not rest:
        return {
            "x": x,
            "tau": None,
            "R": None,
            "kind": "end",
            "peak": peak,
            "tau_is_one": False,
            "multiblock": False,
            "band_x": band_index(n, x),
            "band_R": None,
            "band_descends": False,
        }
    for step, y in enumerate(rest, start=1):
        if y < n:
            return {
                "x": x,
                "tau": None,
                "R": None,
                "kind": "drop",
                "peak": peak,
                "tau_is_one": False,
                "multiblock": False,
                "band_x": band_index(n, x),
                "band_R": -1,
                "band_descends": False,
            }
        if y > peak:
            peak = y
        if in_section(n, y, anum, bnum):
            if y < x:
                kind = "I"
            elif y == x:
                kind = "II"
            else:
                kind = "plus"
            band_x = band_index(n, x)
            band_r = band_index(n, y)
            return {
                "x": x,
                "tau": step,
                "R": y,
                "kind": kind,
                "peak": peak,
                "tau_is_one": step == 1,
                "multiblock": step >= 2,
                "band_x": band_x,
                "band_R": band_r,
                "band_descends": band_r < band_x,
            }
        saw_outside = True
    return {
        "x": x,
        "tau": None,
        "R": None,
        "kind": "III" if saw_outside else "end",
        "peak": peak,
        "tau_is_one": False,
        "multiblock": False,
        "band_x": band_index(n, x),
        "band_R": None,
        "band_descends": False,
    }


def record_lows(visits: list[int]) -> dict[str, Any]:
    if not visits:
        return {"visits": 0, "strict_descents": 0, "any_ascent": False}
    running = visits[0]
    descents = 0
    ascent = False
    for value in visits[1:]:
        if value < running:
            descents += 1
            running = value
        elif value > running:
            ascent = True
    return {
        "visits": len(visits),
        "strict_descents": descents,
        "any_ascent": ascent,
        "first": visits[0],
        "last_min": running,
    }


def section_row(n: int, name: str, anum: int, bnum: int) -> dict[str, Any]:
    orbit = q_section_orbit(n)
    returns = []
    for idx, x in enumerate(orbit):
        if x < n:
            break
        row = first_return(n, orbit, idx, anum, bnum)
        if row is not None:
            returns.append(row)
    defined = [row for row in returns if row["tau"] is not None]
    tau1 = sum(1 for row in defined if row["tau_is_one"])
    multi = sum(1 for row in defined if row["multiblock"])
    kinds = Counter(row["kind"] for row in returns)
    visits = [x for x in orbit if in_section(n, x, anum, bnum)]
    if trajectory_until_drop(n)[-1] < n:
        for row in returns:
            if row["kind"] == "III":
                row["kind"] = "exit_then_drop"
        kinds = Counter(row["kind"] for row in returns)
    typical_one = len(defined) > 0 and tau1 == len(defined)
    rejected = typical_one or multi == 0
    return {
        "n": n,
        "section": name,
        "A": anum,
        "B": bnum,
        "orbit": orbit,
        "n_in_s": len(visits),
        "n_defined": len(defined),
        "n_tau1": tau1,
        "n_multiblock": multi,
        "kinds": dict(kinds),
        "returns": [
            {
                "x": row["x"],
                "tau": row["tau"],
                "R": row["R"],
                "kind": row["kind"],
                "peak": row["peak"],
                "band_descends": row["band_descends"],
            }
            for row in returns
        ],
        "record_low": record_lows(visits),
        "typical_tau_one": typical_one,
        "rejected": rejected,
        "has_type_II": kinds.get("II", 0) > 0,
        "has_type_III": kinds.get("III", 0) > 0,
        "has_type_I": kinds.get("I", 0) > 0,
        "has_plus": kinds.get("plus", 0) > 0,
    }


def leftover_tables() -> dict[str, dict[str, dict[str, Any]]]:
    out: dict[str, dict[str, dict[str, Any]]] = {}
    for name, anum, bnum in SECTIONS:
        out[name] = {}
        for n in CONTROLS:
            out[name][str(n)] = section_row(n, name, anum, bnum)
    return out


def section_verdict(tables: dict[str, dict[str, dict[str, Any]]]) -> dict[str, Any]:
    verdicts: dict[str, Any] = {}
    surviving: list[str] = []
    for name, _anum, _bnum in SECTIONS:
        rows = tables[name]
        multi = sum(row["n_multiblock"] for row in rows.values())
        defined = sum(row["n_defined"] for row in rows.values())
        tau1 = sum(row["n_tau1"] for row in rows.values())
        type_iii = sum(row["kinds"].get("III", 0) for row in rows.values())
        type_ii = sum(row["kinds"].get("II", 0) for row in rows.values())
        type_i = sum(row["kinds"].get("I", 0) for row in rows.values())
        plus = sum(row["kinds"].get("plus", 0) for row in rows.values())
        rejected = all(row["rejected"] for row in rows.values())
        if not rejected and multi > 0:
            surviving.append(name)
        verdicts[name] = {
            "defined": defined,
            "tau1": tau1,
            "multiblock": multi,
            "type_I": type_i,
            "type_II": type_ii,
            "type_III": type_iii,
            "plus": plus,
            "rejected": rejected,
        }
    return {"by_section": verdicts, "surviving": surviving}


def window_scan(n_hi: int = WINDOW_HI) -> dict[str, Any]:
    """Modest odd window: leftover-specific or generic?"""

    counts = {
        name: {"defined": 0, "tau1": 0, "multiblock": 0, "type_I": 0, "plus": 0}
        for name, _a, _b in SECTIONS
    }
    for n in range(3, n_hi, 2):
        orbit = q_section_orbit(n)
        if len(orbit) < 2:
            continue
        for name, anum, bnum in SECTIONS:
            for idx, x in enumerate(orbit):
                if x < n:
                    break
                row = first_return(n, orbit, idx, anum, bnum)
                if row is None or row["tau"] is None:
                    continue
                bucket = counts[name]
                bucket["defined"] += 1
                if row["tau_is_one"]:
                    bucket["tau1"] += 1
                if row["multiblock"]:
                    bucket["multiblock"] += 1
                if row["kind"] == "I":
                    bucket["type_I"] += 1
                elif row["kind"] == "plus":
                    bucket["plus"] += 1
    return counts


def contrast_tables() -> dict[str, dict[str, dict[str, Any]]]:
    out: dict[str, dict[str, dict[str, Any]]] = {}
    for name, anum, bnum in SECTIONS:
        out[name] = {}
        for n in CONTRAST:
            out[name][str(n)] = section_row(n, name, anum, bnum)
    return out


def run_probe() -> dict[str, Any]:
    leftovers = leftover_tables()
    verdict = section_verdict(leftovers)
    window = window_scan()
    contrast = contrast_tables()
    surviving = verdict["surviving"]
    # Structural split among survivors: Type I only, or mixed I/plus.
    mixed_on_survivor = False
    type_i_only = True
    for name in surviving:
        rowset = leftovers[name]
        plus = sum(row["kinds"].get("plus", 0) for row in rowset.values())
        typ_i = sum(row["kinds"].get("I", 0) for row in rowset.values())
        if plus > 0 and typ_i > 0:
            mixed_on_survivor = True
        if plus > 0:
            type_i_only = False
    record_low_fails = any(
        leftovers["3/2"][str(n)]["record_low"]["any_ascent"]
        or leftovers["2"][str(n)]["record_low"]["any_ascent"]
        for n in CONTROLS
        if leftovers["3/2"][str(n)]["record_low"]["visits"] > 1
    )
    return {
        "basin": "ordinary_integers",
        "leftovers": leftovers,
        "contrast": contrast,
        "verdict": verdict,
        "window": window,
        "all_sections_rejected": len(surviving) == 0,
        "surviving": surviving,
        "mixed_on_survivor": mixed_on_survivor,
        "type_i_only_on_survivor": type_i_only and len(surviving) > 0,
        "record_low_fails": record_low_fails,
        "has_type_II": any(
            leftovers[name][str(n)]["has_type_II"]
            for name, _a, _b in SECTIONS
            for n in CONTROLS
        ),
        "letter_chain": False,
        "q_descriptor_reopen": False,
        "return_section_lean": False,
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
        "not_in_paper_barrel": "ReturnSection" not in paper
        and "q_return_section" not in paper,
        "FloorPower_not_rewritten": "CycleWord" not in engine_floor_text(),
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
    if scan["letter_chain"] or scan["q_descriptor_reopen"] or scan["halt_theorem"]:
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope claim"}
    if scan["all_sections_rejected"]:
        return {
            "classification": CLASS_CLOSED,
            "reason": (
                "every candidate S_n(α) has typical leftover return "
                "time 1, so R_S is Q"
            ),
        }
    if scan["has_type_II"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "an exact section fixed point appeared; hand to CycleCore",
        }
    if scan["type_i_only_on_survivor"] and not scan["mixed_on_survivor"]:
        return {
            "classification": CLASS_GREEN,
            "reason": (
                "a surviving section has only Type I multi-block returns"
            ),
        }
    return {
        "classification": CLASS_PARK,
        "reason": (
            "some sections have multi-block leftover returns, but the "
            "return relation is mixed Type I and ascent and is not a "
            "shared well-founded order"
        ),
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "section_return_descent": False,
            "q_descriptor_reopen": False,
            "return_section_lean": False,
            "letter_chain": False,
            "global_termination": False,
        }
    )
    return {
        "experiment": "juggler_q_return_section",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "q_blocks landing skeleton; exact x^A < n^B sections "
            "3/2, 2, 9/4, 8/3, 3; leftover Poincaré returns; "
            "odd n<2001 window"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    verdict = scan["verdict"]["by_section"]
    lines = [
        "# Juggler Q first-return section",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Poincaré returns of residual Q-orbits to exact scale sections.",
        "Not a halt theorem. Not a Q-descriptor reopen.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     scale section with simpler Q returns",
        "Novelty hypothesis      exit-and-reenter is well-founded",
        "Maximum Phase-0 scope   leftovers; five exact α; no Lean",
        "```",
        "",
        "## Metadata",
        "",
        f"- classification: **{decision['classification']}**",
        f"- surviving sections: `{scan['surviving']}`",
        f"- all rejected: `{scan['all_sections_rejected']}`",
        f"- mixed on survivor: `{scan['mixed_on_survivor']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Section verdicts",
        "",
    ]
    for name, row in verdict.items():
        lines.append(
            f"- `{name}`: defined=`{row['defined']}` tau1=`{row['tau1']}` "
            f"multi=`{row['multiblock']}` I=`{row['type_I']}` "
            f"+`={row['plus']}` III=`{row['type_III']}` "
            f"rejected=`{row['rejected']}`"
        )
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
    print("surviving", payload["scan"]["surviving"])
    print(payload["scan"]["verdict"]["by_section"])


if __name__ == "__main__":
    main()

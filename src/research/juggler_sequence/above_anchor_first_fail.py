"""First shared AboveAnchor kill on leftover odd-landing corridors.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a two-sided-gap reopen, not a first-lift-eighth reopen, not a
PE-walk census, not Z5, and not a length-11 assembler.

Phase 0 asks which odd-landing corridor first fails a named shared
AboveAnchor obstruction that is not the tautological last
even-below-square step. Paper A is unchanged.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.cube_odd_return import cube_odd_landing
from research.juggler_sequence.first_internal_oo import isolated_oe_exponent_ok
from research.juggler_sequence.lean_paths import (
    JUGGLER_DIR,
    JUGGLER_PAPER_BARREL,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.minimal_anchor_closure import (
    corridor_rank,
    trajectory_until_drop,
    word_of_path,
)
from research.juggler_sequence.power_words import ANTI_OVERCLAIM, floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_above_anchor_first_fail.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_above_anchor_first_fail.md"

CLASS_CLOSED = "FIRST_ANCHOR_FAIL_CLOSED"
CLASS_PARK = "FIRST_ANCHOR_FAIL_PARK"
CLASS_GREEN = "FIRST_ANCHOR_FAIL_GREEN"
CLASS_INCOMPLETE = "FIRST_ANCHOR_FAIL_INCOMPLETE"

STARTS = (37, 69, 89, 365, 501, 1517, 6187)
CONTROLS = (365, 501, 1517, 6187)
CONTRAST = (69, 89)
LAB = 37
WINDOW_HI = 201

# Pinned first strong kills. Tautological-only rows have None.
PINNED = {
    37: {"tag": "cube_even_even", "i": 13, "x": 5854},
    69: {"tag": "eighth_oee", "i": 4, "x": 1265},
    89: None,
    365: {"tag": "eighth_oee", "i": 12, "x": 12707},
    501: {"tag": "eighth_oee", "i": 20, "x": 12707},
    1517: {"tag": "cube_odd_even_below_square", "i": 13, "x": 43916043},
    6187: None,
}

STRONG = (
    "isolated_scale_gap",
    "oe_start",
    "eighth_oee",
    "cube_even_even",
    "cube_odd_even_below_square",
    "two_even_below_fourth_not_cube",
    "envelope_on_above_anchor",
)

EXISTING_LEAN = (
    "AboveAnchor",
    "aboveAnchor_not_envelope_drop",
    "aboveAnchor_not_odd_even",
    "aboveAnchor_isolated_two",
    "even_below_square_drop",
    "two_even_below_fourth",
    "finiteProgress_of_cube_even_even",
    "finiteProgress_of_cube_odd_even_below_square",
    "finiteProgress_of_odd_even_eighth",
    "finiteProgress_of_even_power_bound_square",
    "finiteProgress_of_ooe_oe",
    "odd_even_eighth_lt_sq",
    "CubeOddLanding",
)

FORBIDDEN_THEOREMS = (
    "juggler_reaches_one",
    "no_juggler_escape",
    "all_finiteProgress",
)

FORBIDDEN_NEW_API = (
    "FirstAnchorFail",
    "SharedObstruction",
    "OddLandingKill",
    "AboveAnchorFail",
)

NEW_LEAN_FILES = (
    JUGGLER_DIR / "FirstAnchorFail.lean",
    JUGGLER_DIR / "SharedObstruction.lean",
    JUGGLER_DIR / "OddLandingKill.lean",
)


def band(n: int, x: int) -> str:
    if x < n:
        return "below"
    if x < n * n:
        return "square"
    if x < n**3:
        return "cube"
    if x < n**4:
        return "fourth"
    if x < n**5:
        return "fifth"
    return f"r{corridor_rank(x, n)}"


def leading_isolated(word: str) -> tuple[int, int, str] | None:
    """Leading O^a E (OE)^r, or None if the word is not isolated-shaped."""

    if not word or word[0] != "O":
        return None
    i = 0
    while i < len(word) and word[i] == "O":
        i += 1
    a = i
    if a < 1 or i >= len(word) or word[i] != "E":
        return None
    i += 1
    r = 0
    while i + 1 < len(word) and word[i] == "O" and word[i + 1] == "E":
        r += 1
        i += 2
    prefix = "O" * a + "E" + "OE" * r
    return a, r, prefix


def tags_at(
    n: int,
    path: tuple[int, ...],
    i: int,
    word: str,
    drop: int,
) -> list[str]:
    """Named cells at path[i] that use already-realized later letters."""

    x = path[i]
    tags: list[str] = []
    n2, n3, n4, n8 = n * n, n**3, n**4, n**8
    if i >= 1:
        prefix = word[:i]
        odd = prefix.count("O")
        if 3**odd < 2**i and path[i] >= n:
            tags.append("envelope_on_above_anchor")
        if 3**odd < 2 * (2**i) and x % 2 == 0 and x >= n:
            tags.append("k2_envelope_even")
    if i + 1 > drop:
        return tags
    nxt = path[i + 1]
    if x % 2 == 0 and x < n2:
        tags.append("even_below_square")
    if x % 2 == 0 and n2 <= x < n3 and nxt % 2 == 0:
        tags.append("cube_even_even")
    if x % 2 == 0 and n3 <= x < n4 and nxt % 2 == 0:
        tags.append("two_even_below_fourth_not_cube")
    if cube_odd_landing(n, x) and nxt % 2 == 0 and i + 2 <= drop:
        z = path[i + 2]
        if z % 2 == 0 and z < n2:
            tags.append("cube_odd_even_below_square")
    if x % 2 == 1 and nxt % 2 == 0 and x**3 < n8 and i + 2 <= drop:
        z = path[i + 2]
        if z % 2 == 0 and n <= z < n2:
            tags.append("eighth_oee")
        if z < n and nxt < n2:
            tags.append("square_odd_even_drop")
    return tags


def classify_orbit(n: int) -> dict[str, Any]:
    path = trajectory_until_drop(n)
    word = word_of_path(path)
    drop = len(path) - 1
    iso = leading_isolated(word)
    iso_gap = bool(iso and iso[0] >= 2 and not isolated_oe_exponent_ok(iso[0], iso[1]))
    events: list[dict[str, Any]] = []
    first_strong: dict[str, Any] | None = None
    if word.startswith("OE"):
        first_strong = {"i": 0, "tag": "oe_start", "band": band(n, path[0]), "x": path[0]}
    if iso_gap and first_strong is None:
        first_strong = {
            "i": 0,
            "tag": "isolated_scale_gap",
            "band": band(n, path[0]),
            "x": path[0],
            "a": iso[0],
            "r": iso[1],
        }
    for i in range(drop):
        tags = tags_at(n, path, i, word, drop)
        x = path[i]
        if tags:
            events.append(
                {
                    "i": i,
                    "band": band(n, x),
                    "parity": "E" if x % 2 == 0 else "O",
                    "x": x,
                    "tags": tags,
                }
            )
        if first_strong is None:
            strong = [tag for tag in tags if tag in STRONG]
            if strong:
                first_strong = {
                    "i": i,
                    "tag": strong[0],
                    "band": band(n, x),
                    "x": x,
                    "tags": strong,
                }
    last = path[drop - 1]
    return {
        "n": n,
        "drop": drop,
        "word": word,
        "iso": None if iso is None else {"a": iso[0], "r": iso[1], "prefix": iso[2]},
        "iso_gap": iso_gap,
        "first_strong": first_strong,
        "tautological_only": first_strong is None,
        "drop_from": {
            "band": band(n, last),
            "x": last,
            "parity": "E" if last % 2 == 0 else "O",
        },
        "events": events,
    }


def _matches_pin(row: dict[str, Any]) -> bool:
    pin = PINNED[row["n"]]
    strong = row["first_strong"]
    if pin is None:
        return strong is None
    return (
        strong is not None
        and strong["tag"] == pin["tag"]
        and strong["i"] == pin["i"]
        and strong["x"] == pin["x"]
    )


def run_probe() -> dict[str, Any]:
    tables = {n: classify_orbit(n) for n in STARTS}
    leftover_strong = {
        n: tables[n]["first_strong"]["tag"] if tables[n]["first_strong"] else None
        for n in CONTROLS
    }
    contrast_strong = {
        n: tables[n]["first_strong"]["tag"] if tables[n]["first_strong"] else None
        for n in CONTRAST
    }
    pins_ok = all(_matches_pin(tables[n]) for n in STARTS)
    envelope_leak = any(
        ev["tags"] and "envelope_on_above_anchor" in ev["tags"]
        for row in tables.values()
        for ev in row["events"]
    )
    hist: dict[str, int] = {}
    taut_window: list[int] = []
    isolated_window = 0
    window_count = 0
    for n in range(3, WINDOW_HI, 2):
        if floor_power(n) % 2 == 0:
            continue
        try:
            row = classify_orbit(n)
        except ValueError:
            continue
        window_count += 1
        tag = None if row["first_strong"] is None else row["first_strong"]["tag"]
        key = "none" if tag is None else tag
        hist[key] = hist.get(key, 0) + 1
        if tag is None:
            taut_window.append(n)
        if tag == "isolated_scale_gap":
            isolated_window += 1
    unknown = [key for key in hist if key not in STRONG and key != "none"]
    return {
        "basin": "ordinary_integers",
        "tables": {str(n): tables[n] for n in STARTS},
        "leftover_strong": {str(n): leftover_strong[n] for n in CONTROLS},
        "contrast_strong": {str(n): contrast_strong[n] for n in CONTRAST},
        "lab_strong": None
        if tables[LAB]["first_strong"] is None
        else tables[LAB]["first_strong"]["tag"],
        "pins_ok": pins_ok,
        "envelope_leak": envelope_leak,
        "leftover_has_new_cell": any(
            leftover_strong[n] not in (None, *STRONG) for n in CONTROLS
        ),
        "tautological_leftover": leftover_strong[6187] is None,
        "tautological_contrast": contrast_strong[89] is None,
        "named_leftover_kills": leftover_strong[365] == "eighth_oee"
        and leftover_strong[501] == "eighth_oee"
        and leftover_strong[1517] == "cube_odd_even_below_square",
        "window_hi": WINDOW_HI,
        "window_count": window_count,
        "window_hist": hist,
        "window_tautological": taut_window,
        "window_isolated": isolated_window,
        "window_unknown": unknown,
        "no_unknown_window_tag": unknown == [],
        "letter_chain": False,
        "eighth_reopen": False,
        "sigma_automaton": False,
        "first_fail_lean": False,
        "paper_a_modified": False,
        "halt_theorem": False,
        "gap_reopen": False,
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
        "not_in_paper_barrel": "FirstAnchorFail" not in paper
        and "SharedObstruction" not in paper
        and "OddLandingKill" not in paper,
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
    if (
        scan["letter_chain"]
        or scan["eighth_reopen"]
        or scan["sigma_automaton"]
        or scan["first_fail_lean"]
        or scan["halt_theorem"]
        or scan["gap_reopen"]
    ):
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope claim"}
    if scan["leftover_has_new_cell"] or scan["window_unknown"]:
        return {
            "classification": CLASS_GREEN,
            "reason": "a first kill is outside the named shared catalog",
        }
    if scan["envelope_leak"]:
        return {
            "classification": CLASS_GREEN,
            "reason": "envelope gap fired while the state was still AboveAnchor",
        }
    if (
        scan["pins_ok"]
        and scan["named_leftover_kills"]
        and scan["tautological_leftover"]
        and scan["tautological_contrast"]
        and scan["no_unknown_window_tag"]
        and not scan["envelope_leak"]
    ):
        return {
            "classification": CLASS_CLOSED,
            "reason": (
                "non-tautological first kills are eighth_oee, cube_even_even, "
                "or cube_odd_even_below_square; 6187 and 89 fail only the "
                "last even-below-square step after a square-odd OE"
            ),
        }
    return {
        "classification": CLASS_PARK,
        "reason": "named-start pins or window catalog did not match",
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "new_shared_obstruction": False,
            "tautological_square_is_new_cell": False,
            "first_fail_lean": False,
            "eighth_reopen": False,
            "sigma_automaton": False,
            "global_termination": False,
        }
    )
    return {
        "experiment": "juggler_above_anchor_first_fail",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "first named shared AboveAnchor kill on "
            "37/69/89/365/501/1517/6187; odd window < 201; "
            "tautological last even-below-square excluded"
        ),
    }


def _fmt_strong(row: dict[str, Any]) -> str:
    strong = row["first_strong"]
    if strong is None:
        return "tautological_only"
    extra = f" tags=`{strong['tags']}`" if "tags" in strong else ""
    return (
        f"tag=`{strong['tag']}` i=`{strong['i']}` "
        f"band=`{strong['band']}` x=`{strong['x']}`{extra}"
    )


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler first shared AboveAnchor failure",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "First named shared `AboveAnchor` kill on leftover odd-landing",
        "corridors. The last even-below-square step is excluded.",
        "Not a halt theorem.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     which leftover corridor first fails",
        "                        a named shared AboveAnchor cell",
        "Novelty hypothesis      a missed shared kill, or a new cell",
        "Maximum Phase-0 scope   named starts; odd window < 201;",
        "                        no Lean; no Sigma",
        "```",
        "",
        "## Metadata",
        "",
        f"- classification: **{decision['classification']}**",
        f"- pins ok: `{scan['pins_ok']}`",
        f"- leftover strong: `{scan['leftover_strong']}`",
        f"- contrast strong: `{scan['contrast_strong']}`",
        f"- lab strong: `{scan['lab_strong']}`",
        f"- window tautological: `{scan['window_tautological']}`",
        f"- window hist: `{scan['window_hist']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Named starts",
        "",
    ]
    for n in STARTS:
        row = scan["tables"][str(n)]
        lines.append(
            f"- `{n}`: word=`{row['word']}` drop=`{row['drop']}` "
            f"{_fmt_strong(row)}"
        )
        for ev in row["events"]:
            lines.append(
                f"  - i=`{ev['i']}` {ev['band']} {ev['parity']} "
                f"x=`{ev['x']}` tags=`{ev['tags']}`"
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
    scan = payload["scan"]
    print("leftover", scan["leftover_strong"])
    print("contrast", scan["contrast_strong"])
    print("window", scan["window_hist"], "taut", scan["window_tautological"])


if __name__ == "__main__":
    main()

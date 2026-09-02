"""First leftover cube-odd lift is not forced into x^3 < n^8.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a first-return Q-map. Not a W_5 reopen. Not a new exponent chain.

The mixed OE cell says that an odd x with even T(x) satisfies
T^2(x) < n^2 iff x^3 < n^8. Named leftovers 365, 501, 1517, 6187
sit on the safe side at their first cube-odd landing. That is not
an AboveAnchor first-lift theorem: n=4309 follows OOEOOEOO to a
genuine first cube-odd state with even T(x) and x^3 >= n^8.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.cube_odd_return import (
    LEFTOVER_STARTS,
    WITNESS_501_LATER,
    cube_odd_landing,
    first_odd_cube_on_anchor,
)
from research.juggler_sequence.lean_paths import (
    JUGGLER_PAPER_BARREL,
    MINIMAL,
    MINIMUM_RELATIVE,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.mixed_oe_cell import mixed_return
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power, itinerary, word_of

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_first_lift_eighth.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_first_lift_eighth.md"

CLASS_REFUTED = "FIRST_LIFT_EIGHTH_REFUTED"
CLASS_INCOMPLETE = "FIRST_LIFT_EIGHTH_INCOMPLETE"

UNSAFE_WORD = "OOEOOEOO"
# Smallest odd n whose first cube-odd landing has even T and x^3 >= n^8.
WITNESS_4309 = (4309, UNSAFE_WORD, 22357213525)
# Long AboveAnchor leftover (first drop at step 42) on the same word.
WITNESS_5791 = (5791, UNSAFE_WORD, 51875574891)

LEAN_THEOREMS = (
    "AboveAnchor",
    "odd_even_eighth_lt_sq",
    "finiteProgress_of_odd_even_eighth",
    "power_bound_word",
)

FORBIDDEN_THEOREMS = (
    "juggler_reaches_one",
    "no_juggler_escape",
    "no_juggler_cycle",
)


def envelope_gap(length: int, odd_count: int) -> int:
    """3^{o+1} - 8 * 2^k. Negative iff the word envelope forces x^3 < n^8."""

    return 3 ** (odd_count + 1) - 8 * (2**length)


def envelope_implies_eighth(length: int, odd_count: int) -> bool:
    return envelope_gap(length, odd_count) < 0


def first_lift_row(n: int, max_steps: int = 80) -> dict[str, Any] | None:
    hit = first_odd_cube_on_anchor(n, max_steps)
    if hit is None:
        return None
    step, x = hit
    path = itinerary(n, step)
    word = word_of(path)
    mixed = mixed_return(n, x)
    odd_c = word.count("O")
    length = len(word)
    return {
        "n": n,
        "step": step,
        "word": word,
        "odd_count": odd_c,
        "length": length,
        "x": x,
        "y": mixed["y"],
        "z": mixed["z"],
        "x3_minus_n8": x**3 - n**8,
        "z_minus_n2": mixed["z"] - n * n,
        "y_even": mixed["y_even"],
        "z_even": mixed["z"] % 2 == 0,
        "x3_lt_n8": mixed["x3_lt_n8"],
        "z_lt_sq": mixed["z_lt_sq"],
        "in_cell": cube_odd_landing(n, x),
        "envelope_gap": envelope_gap(length, odd_c),
        "envelope_implies_eighth": envelope_implies_eighth(length, odd_c),
        "pred_even": path[-2] % 2 == 0 if step else None,
    }


def leftover_first_eighth() -> dict[int, dict[str, Any]]:
    out: dict[int, dict[str, Any]] = {}
    for n in LEFTOVER_STARTS:
        row = first_lift_row(n)
        out[n] = {"hit": row is not None, **(row or {})}
    return out


def witness_4309() -> dict[str, Any]:
    n, word, x = WITNESS_4309
    row = first_lift_row(n)
    if row is None:
        raise ValueError("4309 has no first cube-odd landing")
    return {
        "is_first_lift": row["step"] == 8 and row["x"] == x,
        "word_is_unsafe_class": row["word"] == word,
        "refutes_first_eighth": row["y_even"] and not row["x3_lt_n8"],
        **row,
    }


def witness_5791() -> dict[str, Any]:
    n, word, x = WITNESS_5791
    row = first_lift_row(n)
    if row is None:
        raise ValueError("5791 has no first cube-odd landing")
    cur = n
    drop_at = None
    for step in range(1, 80):
        cur = floor_power(cur)
        if cur < n:
            drop_at = step
            break
    return {
        "is_first_lift": row["x"] == x,
        "word_is_unsafe_class": row["word"] == word,
        "refutes_first_eighth": row["y_even"] and not row["x3_lt_n8"],
        "drop_at": drop_at,
        "long_above_anchor": drop_at is not None and drop_at > 30,
        **row,
    }


def witness_501_later() -> dict[str, Any]:
    n, x = WITNESS_501_LATER
    first = first_lift_row(n)
    mixed = mixed_return(n, x)
    return {
        "n": n,
        "x": x,
        "is_first_lift": first is not None and first["x"] == x,
        "x3_lt_n8": mixed["x3_lt_n8"],
        "y_even": mixed["y_even"],
        "z_lt_sq": mixed["z_lt_sq"],
        "first_x": None if first is None else first["x"],
        "first_x3_lt_n8": None if first is None else first["x3_lt_n8"],
    }


def boundary_perfect_power(m: int) -> dict[str, Any]:
    """Integer solutions of x^3 = n^8 are n = m^3, x = m^8."""

    n = m**3
    x = m**8
    y = floor_power(x)
    return {
        "m": m,
        "n": n,
        "x": x,
        "equal": x**3 == n**8,
        "x_odd": x % 2 == 1,
        "in_cube_band": n * n <= x < n**3,
        "y": y,
        "y_even": y % 2 == 0,
        "y_is_m12": y == m**12,
    }


def smaller_unsafe_first_even(limit: int = WITNESS_4309[0]) -> list[int]:
    """Odd anchors below `limit` with an unsafe first even-lift."""

    found: list[int] = []
    for n in range(3, limit, 2):
        row = first_lift_row(n)
        if row is None:
            continue
        if row["y_even"] and not row["x3_lt_n8"]:
            found.append(n)
    return found


def run_probe() -> dict[str, Any]:
    leftovers = leftover_first_eighth()
    unsafe = witness_4309()
    long_unsafe = witness_5791()
    later = witness_501_later()
    leftovers_safe = all(
        row.get("hit")
        and row.get("y_even")
        and row.get("x3_lt_n8")
        and row.get("envelope_implies_eighth")
        for row in leftovers.values()
    )
    leftover_itineraries = {n: leftovers[n].get("word") for n in LEFTOVER_STARTS}
    leftover_z_odd = {
        n: leftovers[n].get("hit") and not leftovers[n].get("z_even")
        for n in LEFTOVER_STARTS
    }
    bounds = [boundary_perfect_power(m) for m in (3, 5, 7)]
    boundary_even_T = any(row["x_odd"] and row["y_even"] for row in bounds)
    return {
        "basin": "ordinary_integers",
        "leftover_first_eighth": leftovers,
        "leftover_itineraries": leftover_itineraries,
        "witness_4309": unsafe,
        "witness_5791": long_unsafe,
        "witness_501_later": later,
        "boundary": bounds,
        "leftovers_safe_and_enveloped": leftovers_safe,
        "falsifier_a": unsafe["refutes_first_eighth"] and unsafe["is_first_lift"],
        "long_leftover_also_unsafe": long_unsafe["refutes_first_eighth"]
        and long_unsafe["long_above_anchor"],
        "first_is_not_later": later["is_first_lift"] is False
        and later["first_x3_lt_n8"] is True
        and later["x3_lt_n8"] is False,
        "unsafe_word": UNSAFE_WORD,
        "unsafe_envelope_gap": envelope_gap(len(UNSAFE_WORD), UNSAFE_WORD.count("O")),
        "ooeoo_implies_eighth": envelope_implies_eighth(5, 4),
        "ooeooeoo_implies_eighth": envelope_implies_eighth(8, 6),
        "leftover_t2_often_odd": leftover_z_odd[365]
        and leftover_z_odd[501]
        and leftover_z_odd[6187],
        "boundary_excludes_even_T": not boundary_even_T
        and all(row["equal"] and row["y_is_m12"] for row in bounds),
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
        "no_new_first_lift_lean": "first_lift_eighth" not in combined
        and "leftover_first_eighth" not in combined,
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and all(lean[name] for name in LEAN_THEOREMS)
        and not lean["has_juggler_reaches_one"]
        and lean["in_laboratory_barrel"]
        and lean["not_in_paper_barrel"]
        and lean["no_new_first_lift_lean"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if not scan["falsifier_a"] or not scan["leftovers_safe_and_enveloped"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "the 4309 falsifier or leftover envelope split failed",
        }
    if not scan["first_is_not_later"] or scan["ooeooeoo_implies_eighth"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "later/first split or OOEOOEOO envelope gap failed",
        }
    if scan["letter_chain"] or scan["q_return"] or scan["halt_theorem"]:
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope claim"}
    return {
        "classification": CLASS_REFUTED,
        "reason": (
            "AboveAnchor first cube-odd even lift does not force "
            "x^3 < n^8: n=4309 follows OOEOOEOO; named leftovers "
            "sit below only because their first-lift words keep "
            "3^{o+1} < 8*2^{|w|}"
        ),
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "first_lift_always_eighth": False,
            "letter_chain": False,
            "q_return": False,
            "global_termination": False,
        }
    )
    return {
        "experiment": "juggler_first_lift_eighth",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "first cube-odd landing on leftover-generated AboveAnchor "
            "prefixes; EnvelopeState gap 3^{o+1} vs 8*2^{|w|}; "
            "4309 / 5791 as first-lift falsifiers; 501 later as "
            "non-first complementary landing"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler first-lift eighth cell",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "First leftover cube-odd even lifts are not forced into `x^3 < n^8`.",
        "Not a halt theorem.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     leftover first cube-odd => x^3 < n^8?",
        "Novelty hypothesis      inherited PE envelope ratio <= 8/3",
        "Maximum Phase-0 scope   leftover first hits; OOEOOEOO census",
        "```",
        "",
        "## Metadata",
        "",
        f"- classification: **{decision['classification']}**",
        f"- Falsifier A: `{scan['falsifier_a']}`",
        f"- leftovers enveloped: `{scan['leftovers_safe_and_enveloped']}`",
        f"- unsafe word: `{scan['unsafe_word']}`",
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

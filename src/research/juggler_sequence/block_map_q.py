"""Maximal odd-run block map Q on residual AboveAnchor landings.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a run-length automaton, not a PE-scalar reopen, not a residue
modulus search, not Z5, and not a length-11 assembler.

Convention. For odd x, a(x) is the number of consecutive odd
states starting at x (including x). Then T^{a(x)}(x) is even and

    Q(x) = T^{a(x)+1}(x)

is the landing after that even step. The terminal even state is
interior to the block; Q may be odd or even. Domain D_n is the
sequence of odd landings >= n on the AboveAnchor trajectory of n.

Paper A is unchanged.
"""

from __future__ import annotations

import json
from collections import Counter, defaultdict
from fractions import Fraction
from pathlib import Path
from typing import Any

from research.juggler_sequence.lean_paths import (
    FIRST_INTERNAL_OO,
    JUGGLER_DIR,
    JUGGLER_PAPER_BARREL,
    MINIMUM_RELATIVE,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.minimal_anchor_closure import trajectory_until_drop
from research.juggler_sequence.odd_run_itinerary import prefix_lambda
from research.juggler_sequence.parity_persist import odd_run_len
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_block_map_q.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_block_map_q.md"

CLASS_PARK = "BLOCK_MAP_Q_PARK"
CLASS_CYCLE = "BLOCK_MAP_Q_CYCLE"
CLASS_INCOMPLETE = "BLOCK_MAP_Q_INCOMPLETE"

CONTROLS = (365, 501, 1517, 6187)
CONTRAST = (69, 89)
WINDOW_HI = 2001
COLLISION_INDEX = 3

EXISTING_LEAN = (
    "oe_block_contracts",
    "isolatedOddSurvival_bound",
    "finiteProgress_of_ooe_oe",
    "AboveAnchor",
)

FORBIDDEN_THEOREMS = (
    "juggler_reaches_one",
    "no_juggler_escape",
    "all_finiteProgress",
)

FORBIDDEN_NEW_API = (
    "BlockMapQ",
    "QOrbit",
    "BlockPotential",
)

NEW_LEAN_FILES = (
    JUGGLER_DIR / "BlockMapQ.lean",
    JUGGLER_DIR / "QOrbit.lean",
)

INTRINSIC_KEYS = ("x", "a", "Q", "prev", "first_def", "rem", "Q_minus_x")


def a_of(x: int, cap: int = 40) -> int:
    """Maximal odd-run length at odd x, including x."""
    if x < 1 or x % 2 == 0:
        raise ValueError("a(x) is defined on odd positive integers")
    return odd_run_len(x, cap=cap)


def block_map(x: int) -> int:
    """Q(x) = T^{a(x)+1}(x): landing after the closing even step."""
    cur = x
    for _ in range(a_of(x) + 1):
        cur = floor_power(cur)
    return cur


def first_odd_defect(x: int) -> int:
    image = floor_power(x)
    return x * x * x - image * image


def even_remainder(x: int) -> int:
    cur = x
    for _ in range(a_of(x)):
        cur = floor_power(cur)
    landing = floor_power(cur)
    return cur - landing * landing


def block_mu(odds: int) -> Fraction:
    return Fraction(3**odds, 2 ** (odds + 1))


def q_blocks(n: int) -> list[dict[str, Any]]:
    """Odd block endpoints on the AboveAnchor path of n until drop.

    Each row starts at an odd state x >= n. The interior even state
    T^{a(x)}(x) is not a row. If Q(x) is even, the next odd landing
    (if still >= n) is a later row; prev keeps the last odd start.
    """
    path = trajectory_until_drop(n)
    rows: list[dict[str, Any]] = []
    idx = 0
    prev: int | None = None
    while idx < len(path) - 1:
        start = path[idx]
        if start < n:
            break
        if start % 2 == 0:
            idx += 1
            continue
        odd_end = idx
        while odd_end < len(path) and path[odd_end] % 2 == 1:
            odd_end += 1
        if odd_end >= len(path) or odd_end + 1 >= len(path):
            break
        ax = odd_end - idx
        even = path[odd_end]
        qx = path[odd_end + 1]
        rows.append(
            {
                "n": n,
                "x": start,
                "a": ax,
                "Q": qx,
                "even": even,
                "prev": prev,
                "expands": qx > start,
                "contracts": qx < start,
                "below_n": qx < n,
                "q_ge_n": qx >= n,
                "first_def": start * start * start - path[idx + 1] * path[idx + 1],
                "rem": even - qx * qx,
                "Q_minus_x": qx - start,
            }
        )
        if qx < n:
            break
        prev = start
        idx = odd_end + 1
    return rows


def _public_row(row: dict[str, Any]) -> dict[str, Any]:
    return {
        "x": row["x"],
        "a": row["a"],
        "Q": row["Q"],
        "prev": row["prev"],
        "expands": row["expands"],
        "contracts": row["contracts"],
        "below_n": row["below_n"],
        "first_def": row["first_def"],
        "rem": row["rem"],
        "Q_minus_x": row["Q_minus_x"],
    }


def leftover_orbits() -> dict[str, list[dict[str, Any]]]:
    return {str(n): [_public_row(row) for row in q_blocks(n)] for n in CONTROLS}


def contrast_orbits() -> dict[str, list[dict[str, Any]]]:
    return {str(n): [_public_row(row) for row in q_blocks(n)] for n in CONTRAST}


def collision_state() -> dict[str, Any]:
    left = q_blocks(365)
    right = q_blocks(1517)
    third_left = left[COLLISION_INDEX]
    third_right = right[COLLISION_INDEX]
    shared = {
        key: third_left[key] == third_right[key] for key in INTRINSIC_KEYS
    }
    return {
        "index": COLLISION_INDEX,
        "365": _public_row(third_left),
        "1517": _public_row(third_right),
        "prefix_runs": [2, 2, 2],
        "prefix_lambda": str(prefix_lambda([2, 2, 2])),
        "intrinsic_equal": shared,
        "any_intrinsic_shared": any(shared.values()),
        "next_a": {"365": third_left["a"], "1517": third_right["a"]},
        "minimal_predictor": "the integer landing Q^3(n)",
    }


def window_scan(n_hi: int = WINDOW_HI) -> dict[str, Any]:
    repeated_on_orbit = 0
    a1_expands = 0
    a_ge2_contracts = 0
    expand_then_q2_lt_x = 0
    expand_then_q2_gt_q = 0
    contract_stay_then_q2_below = 0
    contract_stay_then_q2_stay = 0
    next_from_a_sign: dict[tuple[int, int], set[int]] = defaultdict(set)
    next_from_pair_a: dict[tuple[int, int], set[int]] = defaultdict(set)
    def_to_a: dict[int, set[int]] = defaultdict(set)
    rem_to_next_a: dict[int, set[int]] = defaultdict(set)
    prefix_next: Counter[int] = Counter()
    n_with_blocks = 0
    total_blocks = 0
    for n in range(3, n_hi, 2):
        rows = q_blocks(n)
        if not rows:
            continue
        n_with_blocks += 1
        total_blocks += len(rows)
        starts = [row["x"] for row in rows]
        if len(starts) != len(set(starts)):
            repeated_on_orbit += 1
        for idx, row in enumerate(rows):
            def_to_a[row["first_def"]].add(row["a"])
            if row["a"] == 1 and row["expands"]:
                a1_expands += 1
            if row["a"] >= 2 and row["contracts"]:
                a_ge2_contracts += 1
            if idx + 1 >= len(rows):
                continue
            nxt = rows[idx + 1]
            sign = 1 if row["expands"] else (-1 if row["contracts"] else 0)
            next_from_a_sign[(row["a"], sign)].add(nxt["a"])
            rem_to_next_a[row["rem"]].add(nxt["a"])
            if idx >= 1:
                next_from_pair_a[(rows[idx - 1]["a"], row["a"])].add(nxt["a"])
            if row["expands"]:
                q2 = nxt["Q"]
                if q2 < row["x"]:
                    expand_then_q2_lt_x += 1
                if q2 > row["Q"]:
                    expand_then_q2_gt_q += 1
            if row["contracts"] and row["q_ge_n"]:
                if nxt["Q"] < n:
                    contract_stay_then_q2_below += 1
                else:
                    contract_stay_then_q2_stay += 1
        if len(rows) >= 4 and [row["a"] for row in rows[:3]] == [2, 2, 2]:
            prefix_next[rows[3]["a"]] += 1
    return {
        "n_hi": n_hi,
        "n_with_blocks": n_with_blocks,
        "total_blocks": total_blocks,
        "repeated_endpoints_on_orbit": repeated_on_orbit,
        "a1_expands": a1_expands,
        "a_ge2_contracts": a_ge2_contracts,
        "expand_then_q2_lt_x": expand_then_q2_lt_x,
        "expand_then_q2_gt_q": expand_then_q2_gt_q,
        "contract_stay_then_q2_below": contract_stay_then_q2_below,
        "contract_stay_then_q2_stay": contract_stay_then_q2_stay,
        "a_sign_ambiguous": sum(
            1 for values in next_from_a_sign.values() if len(values) > 1
        ),
        "pair_a_ambiguous": sum(
            1 for values in next_from_pair_a.values() if len(values) > 1
        ),
        "first_def_ambiguous_a": sum(
            1 for values in def_to_a.values() if len(values) > 1
        ),
        "rem_ambiguous_next_a": sum(
            1 for values in rem_to_next_a.values() if len(values) > 1
        ),
        "next_from_2_expand": sorted(next_from_a_sign[(2, 1)]),
        "next_from_pair_22": sorted(next_from_pair_a[(2, 2)]),
        "prefix_222_next": {str(key): val for key, val in sorted(prefix_next.items())},
        "prefix_222_branching": len(prefix_next) >= 2,
    }


def leftover_summary(orbits: dict[str, list[dict[str, Any]]]) -> dict[str, Any]:
    starts = {
        name: [row["x"] for row in rows] for name, rows in orbits.items()
    }
    return {
        "365_starts": starts["365"],
        "1517_starts": starts["1517"],
        "501_starts": starts["501"],
        "6187_starts": starts["6187"],
        "365_runs": [row["a"] for row in orbits["365"]],
        "1517_runs": [row["a"] for row in orbits["1517"]],
        "no_repeated_endpoint": all(
            len(vals) == len(set(vals)) for vals in starts.values()
        ),
        "q3_365": orbits["365"][COLLISION_INDEX]["x"],
        "q3_1517": orbits["1517"][COLLISION_INDEX]["x"],
        "contract_then_expand_1517": (
            orbits["1517"][3]["Q"] == 2493
            and orbits["1517"][3]["Q"] >= 1517
            and orbits["1517"][4]["Q"] > orbits["1517"][4]["x"]
        ),
        "mu_one_contracts": block_mu(1) < 1,
        "mu_two_expands": block_mu(2) > 1,
    }


def lean_api_present() -> dict[str, bool]:
    combined = juggler_text()
    if MINIMUM_RELATIVE.is_file():
        combined += MINIMUM_RELATIVE.read_text(encoding="utf-8")
    if FIRST_INTERNAL_OO.is_file():
        combined += FIRST_INTERNAL_OO.read_text(encoding="utf-8")
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    named = {name: has_named(combined, name) for name in EXISTING_LEAN}
    new_api = {name: has_named(combined, name) for name in FORBIDDEN_NEW_API}
    forbidden = {name: has_named(combined, name) for name in FORBIDDEN_THEOREMS}
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        **{f"has_{name}": present for name, present in new_api.items()},
        **{f"has_{name}": present for name, present in forbidden.items()},
        "new_lean_file": any(path.is_file() for path in NEW_LEAN_FILES),
        "paper_a_has_new_api": any(name in paper for name in FORBIDDEN_NEW_API),
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
    }


def run_probe() -> dict[str, Any]:
    orbits = leftover_orbits()
    return {
        "basin": "ordinary_integers",
        "controls": orbits,
        "contrasts": contrast_orbits(),
        "collision": collision_state(),
        "window": window_scan(),
        "summary": leftover_summary(orbits),
        "paper_a_modified": False,
        "halt_theorem": False,
        "residue_automaton": False,
        "run_length_graph": False,
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and all(lean[name] for name in EXISTING_LEAN)
        and not lean["new_lean_file"]
        and not lean["paper_a_has_new_api"]
        and not lean["has_juggler_reaches_one"]
        and not lean["has_BlockMapQ"]
        and lean["FloorPower_not_rewritten"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if (
        scan["paper_a_modified"]
        or scan["halt_theorem"]
        or scan["residue_automaton"]
        or scan["run_length_graph"]
    ):
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope claim"}
    window = scan["window"]
    if window["repeated_endpoints_on_orbit"] > 0:
        return {
            "classification": CLASS_CYCLE,
            "reason": "an exact block endpoint repeated on one orbit",
        }
    if window["a1_expands"] > 0:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "a=1 expanded, contradicting oe_block_contracts",
        }
    summary = scan["summary"]
    collision = scan["collision"]
    if summary["q3_365"] != 4447 or summary["q3_1517"] != 33811:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "Q^3 collision landings moved",
        }
    if collision["any_intrinsic_shared"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "365/1517 shared an intrinsic Q^3 coordinate",
        }
    if collision["next_a"]["365"] == collision["next_a"]["1517"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "365/1517 no longer split after Q^3",
        }
    if not summary["contract_then_expand_1517"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "1517 contraction-then-expansion failed",
        }
    if not summary["no_repeated_endpoint"]:
        return {
            "classification": CLASS_CYCLE,
            "reason": "a leftover Q-orbit repeated an endpoint",
        }
    if (
        window["contract_stay_then_q2_stay"] == 0
        or window["expand_then_q2_gt_q"] == 0
        or not window["prefix_222_branching"]
        or window["a_sign_ambiguous"] == 0
        or window["pair_a_ambiguous"] == 0
        or window["first_def_ambiguous_a"] == 0
        or window["rem_ambiguous_next_a"] == 0
        or 1 not in window["next_from_2_expand"]
        or 2 not in window["next_from_2_expand"]
    ):
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "a compressed descriptor accidentally looked predictive",
        }
    return {
        "classification": CLASS_PARK,
        "reason": (
            "Q on D_n is no more predictive than the raw landing: "
            "after (2,2,2) the states 4447 and 33811 share no intrinsic "
            "coordinate, (a,sign) and (prev a,a) do not determine the "
            "next run, first-odd defect and even remainder collide, "
            "Q>x need not force Q^2 descent, and Q<x with Q>=n need "
            "not force Q^2 below the anchor; no exact endpoint repeats"
        ),
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "block_transition_theorem": False,
            "finite_q_descriptor": False,
            "two_block_return_law": False,
            "run_length_graph": False,
            "residue_automaton": False,
            "global_termination": False,
        }
    )
    return {
        "experiment": "juggler_block_map_q",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "define Q = T^{a(x)+1} on leftover D_n; compare Q^3(365) "
            "with Q^3(1517); search repeated endpoints and compressed "
            "descriptors on odd n<2001"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    summary = scan["summary"]
    window = scan["window"]
    collision = scan["collision"]
    lines = [
        "# Juggler maximal odd-run block map Q",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment,",
        "not a run-length automaton, not a residue search, and not a",
        "halt theorem. The leftover is the arithmetic map Q on odd",
        "AboveAnchor landings.",
        "",
        "## Convention",
        "",
        "For odd `x`, `a(x)` counts consecutive odd states starting at",
        "`x`. Then `T^{a(x)}(x)` is even and `Q(x)=T^{a(x)+1}(x)` is",
        "the post-even landing. The even state is interior. `Q(x)` may",
        "be even. Domain `D_n` is odd landings `>= n` on the path of `n`.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     smallest exact state that gives Q a",
        "                        transition law on residual D_n",
        "Novelty hypothesis      (x,Q(x)) or a two-block relation",
        "                        predicts the next run",
        "Falsifier               every finite descriptor fails; the",
        "                        integer landing is the only predictor",
        "Existing machinery      a(x), pe_blocks, leftover controls,",
        "                        oe_block_contracts, isolated OE",
        "Maximum Phase-0 scope   leftovers + odd n<2001; no automaton",
        "```",
        "",
        "## Metadata",
        "",
        f"- classification: **{decision['classification']}**",
        f"- Q^3(365): `{collision['365']['x']}` a=`{collision['365']['a']}`",
        f"- Q^3(1517): `{collision['1517']['x']}` a=`{collision['1517']['a']}`",
        f"- intrinsic shared: `{collision['any_intrinsic_shared']}`",
        f"- repeated endpoints: `{window['repeated_endpoints_on_orbit']}`",
        f"- (2,+) next a: `{window['next_from_2_expand']}`",
        f"- 222 next: `{window['prefix_222_next']}`",
        f"- contract then Q^2 stays: `{window['contract_stay_then_q2_stay']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Leftover Q-orbits",
        "",
        f"- 365 starts: `{summary['365_starts']}` runs=`{summary['365_runs']}`",
        f"- 1517 starts: `{summary['1517_starts']}` runs=`{summary['1517_runs']}`",
        f"- 501 starts: `{summary['501_starts']}`",
        f"- 6187 starts: `{summary['6187_starts']}`",
        "",
        "## Existing Lean (unchanged)",
        "",
    ]
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
            "This is not a halt result and not a Q-frequency theorem.",
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

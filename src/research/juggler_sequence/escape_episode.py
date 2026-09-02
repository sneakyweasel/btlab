"""Escape-episode descent on leftover AboveAnchor corridors.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a PredClosure reopen, not a terminal-cell census, not Z5, and
not a length-11 assembler.

Phase 0 partitions leftover laboratories into escape episodes under
three candidate boundaries and asks whether a completed episode
lowers a well-founded quantity or exactly recurs. Smaller-bad
descent and short Pred_{E,OE,OOE,OOOE} were already REFUTED in
minimal_anchor_closure and are not re-tested. Paper A is unchanged.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.lean_paths import (
    COLLAPSE,
    DRIFT,
    FIRST_PASSAGE,
    JUGGLER_DIR,
    JUGGLER_PAPER_BARREL,
    MINIMUM_RELATIVE,
    PROGRESS,
    RESIDUALS,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.minimal_anchor_closure import (
    corridor_rank,
    trajectory_until_drop,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_escape_episode.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_escape_episode.md"

CLASS_PARK = "ESCAPE_EPISODE_PARK"
CLASS_INCOMPLETE = "ESCAPE_EPISODE_INCOMPLETE"

CONTROLS = (365, 501, 1517, 6187)
CONTRAST = (69, 89)

EXISTING_LEAN = (
    "AboveAnchor",
    "ReturnBelow",
    "HasFiniteStop",
    "FiniteProgress",
    "even_below_anchor_pow",
    "finiteProgress_of_aboveAnchor_returnBelow",
    "cycles_or_escapes",
    "trajectoryExponentGap",
    "collapse_on_pow_two",
)

FORBIDDEN_NEW_API = (
    "EscapeEpisode",
    "EpisodeRank",
    "RecordMinimum",
    "escape_dichotomy",
    "episode_finite_progress",
    "escape_implies_smaller_bad",
)

FORBIDDEN_THEOREMS = (
    "juggler_reaches_one",
    "no_juggler_escape",
    "all_finiteProgress",
    "no_juggler_cycle",
)

NEW_LEAN_FILES = (
    JUGGLER_DIR / "EscapeEpisode.lean",
    JUGGLER_DIR / "EpisodeDescent.lean",
)


def word_of_segment(path: tuple[int, ...]) -> str:
    return "".join("O" if item % 2 else "E" for item in path[:-1])


def even_reset_cuts(path: tuple[int, ...], n: int) -> list[int]:
    """Landing index after an even state whose image has strictly smaller rank."""
    cuts: list[int] = []
    for idx in range(len(path) - 1):
        nxt = path[idx + 1]
        if path[idx] % 2 == 0 and corridor_rank(nxt, n) < corridor_rank(path[idx], n):
            cuts.append(idx + 1)
    return cuts


def rank_return_cuts(path: tuple[int, ...], n: int) -> list[int]:
    """Landing index of any strict corridor-rank drop."""
    cuts: list[int] = []
    for idx in range(len(path) - 1):
        if corridor_rank(path[idx + 1], n) < corridor_rank(path[idx], n):
            cuts.append(idx + 1)
    return cuts


def first_below_anchor_cuts(path: tuple[int, ...], n: int) -> list[int]:
    """First (and only) index with T^k(n) < n."""
    for idx in range(1, len(path)):
        if path[idx] < n:
            return [idx]
    return []


def episode_from(
    path: tuple[int, ...], n: int, start: int, end: int
) -> dict[str, Any]:
    if end <= start:
        raise ValueError("episode requires a positive length")
    segment = path[start : end + 1]
    ranks = [corridor_rank(state, n) for state in segment]
    reset_state = path[end - 1]
    return {
        "start_index": start,
        "end_index": end,
        "start": path[start],
        "landing": path[end],
        "max_state": max(segment),
        "episode_min": min(segment),
        "reset_state": reset_state,
        "reset_even": reset_state % 2 == 0,
        "rank_before": ranks[0],
        "rank_after": ranks[-1],
        "peak_rank": max(ranks),
        "rank_after_lt_before": ranks[-1] < ranks[0],
        "landing_lt_start": path[end] < path[start],
        "landing_lt_anchor": path[end] < n,
        "above_anchor": all(state >= n for state in segment),
        "word": word_of_segment(segment),
        "signature": [path[start], reset_state],
    }


def episodes_from_cuts(
    path: tuple[int, ...], n: int, cuts: list[int]
) -> list[dict[str, Any]]:
    start = 0
    rows: list[dict[str, Any]] = []
    for end in cuts:
        if end <= start:
            continue
        rows.append(episode_from(path, n, start, end))
        start = end
    return rows


def successive_pairs(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    pairs: list[dict[str, Any]] = []
    for prev, nxt in zip(rows, rows[1:]):
        pairs.append(
            {
                "from_start": prev["start"],
                "to_start": nxt["start"],
                "rank_after_descends": nxt["rank_after"] < prev["rank_after"],
                "landing_descends": nxt["landing"] < prev["landing"],
                "episode_min_descends": nxt["episode_min"] < prev["episode_min"],
                "same_signature": prev["signature"] == nxt["signature"],
            }
        )
    return pairs


def partition_row(n: int, name: str, cuts: list[int], path: tuple[int, ...]) -> dict[str, Any]:
    rows = episodes_from_cuts(path, n, cuts)
    above = [row for row in rows if row["above_anchor"]]
    rank2 = [row for row in above if row["rank_before"] == 2]
    high_even = [row for row in above if row["rank_before"] >= 3]
    landings = [row["landing"] for row in rank2]
    signatures = [tuple(row["signature"]) for row in rows]
    return {
        "definition": name,
        "episode_count": len(rows),
        "above_anchor_count": len(above),
        "rank2_count": len(rank2),
        "episodes": rows,
        "rank2_landings": landings,
        "high_even_starts": [row["start"] for row in high_even],
        "high_even_landings": [row["landing"] for row in high_even],
        "landings_strictly_decreasing": (
            len(landings) >= 2
            and all(landings[idx] > landings[idx + 1] for idx in range(len(landings) - 1))
        ),
        "landings_strictly_increasing": (
            len(landings) >= 2
            and all(landings[idx] < landings[idx + 1] for idx in range(len(landings) - 1))
        ),
        "any_rank2_return_drop": any(row["rank_after_lt_before"] for row in rank2),
        "high_even_chain_drops": all(row["rank_after_lt_before"] for row in high_even)
        if high_even
        else True,
        "any_exact_recurrence": len(signatures) != len(set(signatures)),
        "successive": successive_pairs(rank2),
        "peak_ranks": [row["peak_rank"] for row in rank2],
    }


def global_record_mins(path: tuple[int, ...]) -> list[int]:
    running = path[0]
    out = [running]
    for state in path[1:]:
        running = min(running, state)
        out.append(running)
    return out


def control_row(n: int) -> dict[str, Any]:
    path = trajectory_until_drop(n)
    even_cuts = even_reset_cuts(path, n)
    rank_cuts = rank_return_cuts(path, n)
    below_cuts = first_below_anchor_cuts(path, n)
    records = global_record_mins(path)
    frozen = all(value == n for value in records[:-1])
    even_part = partition_row(n, "even_reset", even_cuts, path)
    return {
        "n": n,
        "path": list(path),
        "drop": path[-1],
        "drop_index": len(path) - 1,
        "max_state": max(path),
        "max_rank": max(corridor_rank(state, n) for state in path),
        "global_record_min_frozen": frozen,
        "rank_return_equals_even_reset": even_cuts == rank_cuts,
        "even_reset": even_part,
        "rank_return": partition_row(n, "rank_return", rank_cuts, path),
        "first_below_anchor": partition_row(n, "first_below_anchor", below_cuts, path),
    }


def machinery_reframe() -> dict[str, str]:
    """Existing non-cycle names versus the episode cut."""
    return {
        "AboveAnchor": "every finite prefix of a leftover laboratory stays >= n",
        "ReturnBelow": "first later word with image < n; the terminal drop only",
        "HasFiniteStop": "the same terminal drop; FirstPassage does not cut mid-corridor",
        "even_below_anchor_pow": "an even high state drops its own rank; the return stays rank 2",
        "FiniteProgress": "emitted only by the terminal drop on these laboratories",
        "trajectoryExponentGap": "Drift is an word-exponent predicate, not an episode rank",
        "collapse_on_pow_two": "Collapse is an even-tower identity, not a PE landing law",
        "cycles_or_escapes": "bounded recurrence is already a cycle; leftover prefixes are not recurrent",
    }


def leftover_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    by_n = {int(row["n"]): row for row in rows}
    aa_counts = {
        n: by_n[n]["even_reset"]["rank2_count"] for n in CONTROLS
    }
    increasing = {
        n: by_n[n]["even_reset"]["landings_strictly_increasing"] for n in CONTROLS
    }
    decreasing = any(
        by_n[n]["even_reset"]["landings_strictly_decreasing"] for n in CONTROLS
    )
    rank_drop = any(
        by_n[n]["even_reset"]["any_rank2_return_drop"] for n in CONTROLS
    )
    high_even_ok = all(
        by_n[n]["even_reset"]["high_even_chain_drops"] for n in CONTROLS
    )
    recurrence = any(
        by_n[n]["even_reset"]["any_exact_recurrence"] for n in CONTROLS
    )
    frozen = all(by_n[n]["global_record_min_frozen"] for n in CONTROLS)
    cuts_agree = all(by_n[n]["rank_return_equals_even_reset"] for n in CONTROLS)
    below_is_drop = all(
        by_n[n]["first_below_anchor"]["episode_count"] == 1
        and by_n[n]["first_below_anchor"]["episodes"][0]["landing"] == by_n[n]["drop"]
        for n in CONTROLS
    )
    osc_1517 = by_n[1517]["even_reset"]["rank2_landings"]
    return {
        "rank2_episode_counts": aa_counts,
        "landings_365": by_n[365]["even_reset"]["rank2_landings"],
        "landings_1517": osc_1517,
        "landings_increasing": increasing,
        "any_landing_descent_law": decreasing,
        "any_rank2_return_drop": rank_drop,
        "high_even_chain_drops": high_even_ok,
        "any_exact_recurrence": recurrence,
        "global_record_min_frozen": frozen,
        "rank_return_equals_even_reset": cuts_agree,
        "first_below_is_terminal_drop": below_is_drop,
        "1517_oscillates": osc_1517[:4] == [3789, 10613, 33811, 2493],
        "365_pe_climb": by_n[365]["even_reset"]["rank2_landings"][:4]
        == [763, 1749, 4447, 12707],
    }


def contrast_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    by_n = {int(row["n"]): row for row in rows}
    return {
        "69_landings": by_n[69]["even_reset"]["rank2_landings"],
        "89_landings": by_n[89]["even_reset"]["rank2_landings"],
        "same_rank2_return": all(
            not by_n[n]["even_reset"]["any_rank2_return_drop"]
            and by_n[n]["rank_return_equals_even_reset"]
            and by_n[n]["global_record_min_frozen"]
            for n in CONTRAST
        ),
        "generic_not_leftover_only": True,
    }


def lean_api_present() -> dict[str, bool]:
    combined = juggler_text()
    extra = (MINIMUM_RELATIVE, RESIDUALS, FIRST_PASSAGE, PROGRESS, DRIFT, COLLAPSE)
    for path in extra:
        if path.is_file():
            combined += path.read_text(encoding="utf-8")
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    named = {name: has_named(combined, name) for name in EXISTING_LEAN}
    new_api = {name: has_named(combined, name) for name in FORBIDDEN_NEW_API}
    forbidden = {name: has_named(combined, name) for name in FORBIDDEN_THEOREMS}
    paper_new = {name: name in paper for name in FORBIDDEN_NEW_API}
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        **{f"has_{name}": present for name, present in new_api.items()},
        **{f"has_{name}": present for name, present in forbidden.items()},
        "new_lean_file": any(path.is_file() for path in NEW_LEAN_FILES),
        "paper_a_has_new_api": any(paper_new.values()),
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
    }


def run_probe() -> dict[str, Any]:
    leftover = [control_row(n) for n in CONTROLS]
    contrast = [control_row(n) for n in CONTRAST]
    return {
        "basin": "ordinary_integers",
        "controls": leftover,
        "contrast": contrast,
        "summary": leftover_summary(leftover),
        "contrast_summary": contrast_summary(contrast),
        "machinery": machinery_reframe(),
        "paper_a_modified": False,
        "halt_theorem": False,
        "predclosure_reopened": False,
        "smaller_bad_retested": False,
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and all(lean[name] for name in EXISTING_LEAN)
        and not lean["new_lean_file"]
        and not lean["paper_a_has_new_api"]
        and not lean["has_juggler_reaches_one"]
        and not lean["has_no_juggler_escape"]
        and not lean["has_EscapeEpisode"]
        and not lean["has_escape_dichotomy"]
        and lean["FloorPower_not_rewritten"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if scan["paper_a_modified"] or scan["halt_theorem"] or scan["predclosure_reopened"]:
        return {"classification": CLASS_INCOMPLETE, "reason": "out-of-scope claim"}
    if scan["smaller_bad_retested"]:
        return {"classification": CLASS_INCOMPLETE, "reason": "re-tested a REFUTED claim"}
    summary = scan["summary"]
    contrast = scan["contrast_summary"]
    if summary["any_exact_recurrence"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "Falsifier D: an exact episode signature recurred",
        }
    if (
        summary["any_landing_descent_law"]
        or summary["any_rank2_return_drop"]
        or not summary["high_even_chain_drops"]
        or not summary["global_record_min_frozen"]
        or not summary["first_below_is_terminal_drop"]
        or not summary["rank_return_equals_even_reset"]
        or not summary["365_pe_climb"]
        or not summary["1517_oscillates"]
    ):
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "an unexpected rank-2 descent or unfrozen record min appeared",
        }
    if not contrast["same_rank2_return"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "the 69/89 contrast is not the same rank-2 return",
        }
    if summary["rank2_episode_counts"][365] < 2:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "365 did not produce multiple AboveAnchor episodes",
        }
    return {
        "classification": CLASS_PARK,
        "reason": (
            "even-reset and rank-return coincide and return to rank 2; "
            "PE landings climb or oscillate; global record min is frozen "
            "at n; first-below-anchor is the existing terminal drop; "
            "no exact episode recurrence; 69/89 show the same pattern"
        ),
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "episode_descent_dichotomy": False,
            "record_min_implies_recurrence": False,
            "even_reset_lowers_return_rank": False,
            "smaller_bad_descent": False,
            "predclosure_reopened": False,
            "global_termination": False,
        }
    )
    return {
        "experiment": "juggler_escape_episode",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "leftover 365/501/1517/6187 and contrast 69/89: even-reset, "
            "rank-return, and first-below-anchor partitions; return rank, "
            "episode landings, frozen global min, exact (start, reset) "
            "recurrence; no new Lean"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    summary = scan["summary"]
    contrast = scan["contrast_summary"]
    lines = [
        "# Juggler escape-episode descent",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment,",
        "not a PredClosure reopen, and not a halt theorem. Leftover",
        "AboveAnchor prefixes are partitioned into escape episodes.",
        "Smaller-bad descent is not re-tested.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     leftover completed escape episode",
        "                        lowers a well-founded quantity or",
        "                        exactly recurs",
        "Novelty hypothesis      episode first-passage / record min,",
        "                        not whole-path rank or first-overshoot Pred",
        "Falsifier               landings climb or oscillate; L frozen;",
        "                        no recurrence; rank-return = even-reset",
        "Existing machinery      AboveAnchor; ReturnBelow; HasFiniteStop;",
        "                        even_below_anchor_pow; FiniteProgress",
        "Maximum Phase-0 scope   365, 501, 1517, 6187; 69/89 contrast;",
        "                        three episode cuts; no new Lean",
        "```",
        "",
        "## Metadata",
        "",
        f"- classification: **{decision['classification']}**",
        f"- 365 PE climb: `{summary['landings_365']}`",
        f"- 1517 landings: `{summary['landings_1517']}`",
        f"- rank-2 return drop: `{summary['any_rank2_return_drop']}`",
        f"- landing descent law: `{summary['any_landing_descent_law']}`",
        f"- exact recurrence: `{summary['any_exact_recurrence']}`",
        f"- global L frozen: `{summary['global_record_min_frozen']}`",
        f"- first-below is drop: `{summary['first_below_is_terminal_drop']}`",
        f"- rank-return = even-reset: `{summary['rank_return_equals_even_reset']}`",
        f"- 69 landings: `{contrast['69_landings']}`",
        f"- 89 landings: `{contrast['89_landings']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Controls",
        "",
    ]
    for row in scan["controls"]:
        even = row["even_reset"]
        lines.append(
            f"- n=`{row['n']}` drop=`{row['drop']}` max_rank=`{row['max_rank']}` "
            f"rank2 episodes=`{even['rank2_count']}` "
            f"landings=`{even['rank2_landings']}` "
            f"peaks=`{even['peak_ranks']}` "
            f"L_frozen=`{row['global_record_min_frozen']}`"
        )
    lines.extend(
        [
            "",
            "## Existing machinery",
            "",
        ]
    )
    for name, gloss in scan["machinery"].items():
        lines.append(f"- `{name}`: {gloss}")
    lines.extend(
        [
            "",
            "## Existing Lean (unchanged)",
            "",
        ]
    )
    for name in EXISTING_LEAN:
        lines.append(f"- `{name}`: `{lean[name]}`")
    lines.extend(
        [
            f"- new Lean file: `{lean['new_lean_file']}`",
            f"- Paper A has new API: `{lean['paper_a_has_new_api']}`",
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
            "This is not a halt result and not a PredClosure reopen.",
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

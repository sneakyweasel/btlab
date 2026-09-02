"""Later ReturnBelow after a first-E overshoot with even y.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a two-excursion retry, not a Paper B engine, and not a K3 attack.

After e<=3 the first even always overshoots on MinimalNonTerm /
CycleMin. Halt on the leftover is ReturnBelow from y>n. The easy
even-y words a=2,3 are Paper B contractors. Novelty is only a>=4:
O^a EE is expanding and sits in the OOOO* tree.
"""

from __future__ import annotations

import json
from collections import Counter
from pathlib import Path
from typing import Any

from research.juggler_sequence.lean_paths import (
    EVEN_COUNT_THREE,
    JUGGLER_PAPER_BARREL,
    PROGRESS,
    RESIDUALS,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.odd_odd_frontier import (
    even_run_end,
    first_even_residual,
    post_even_kind,
    residual_cell,
)
from research.juggler_sequence.post_overshoot import excursion
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, itinerary, word_of
from research.juggler_sequence.progress_coverage import is_odd_odd

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_overshoot_return.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_overshoot_return.md"

CLASS_GREEN = "EVEN_Y_LATER_CONTRACTOR_GREEN"
CLASS_SCATTER = "EVEN_Y_RETURN_SUFFIX_SCATTER"
CLASS_REPARAM = "EVEN_Y_PAPER_B_REPARAMETERIZATION"
CLASS_INCOMPLETE = "OVERSHOOT_RETURN_INCOMPLETE"

N_MAX = 10_000
N_PIN = 80
FIRST_EVEN_CAP = 24
RETURN_CAP = 400

PAPER_B_ENGINES = frozenset(
    {
        "OOEE",
        "OOOEE",
        "OOEOE",
        "OOEOOEE",
        "OOOEOEE",
        "OOEOOEOE",
        "OOEOOOEE",
        "OOOEOEOE",
        "OOOEOOEE",
    }
)

LEAN_THEOREMS = (
    "minimal_first_even_overshoots",
    "cycleMin_first_even_overshoots",
    "no_cycle_itinerary_even_count_le_three",
    "ReturnBelow",
    "finiteProgress_of_returnBelow",
    "minimal_first_even_dichotomy",
)

CERTIFICATE_UNCHANGED = (
    "FiniteProgress",
    "reachesOne_of_all_finiteProgress",
    "ReachesOne",
    "DescentCertificate",
)


def first_return_below(n: int, cap: int = RETURN_CAP) -> dict[str, Any] | None:
    path = itinerary(n, cap)
    for step in range(1, len(path)):
        if path[step] < n:
            prefix = path[: step + 1]
            return {
                "step": step,
                "value": path[step],
                "word": word_of(prefix),
            }
    return None


def suffix_after_oa_ee(word: str, a: int) -> str | None:
    prefix = "O" * a + "EE"
    if not word.startswith(prefix):
        return None
    return word[len(prefix) :]


def overshoot_row(n: int, cap: int = FIRST_EVEN_CAP) -> dict[str, Any] | None:
    if not is_odd_odd(n):
        return None
    fe = first_even_residual(n, cap)
    if fe is None:
        return None
    a, z, e = fe["a"], fe["z"], fe["e"]
    if e <= n:
        return None
    b, y_star = even_run_end(z)
    y_even = e % 2 == 0
    first_lt = y_star < n
    second_lt = None
    second_y = None
    if not first_lt and y_star > 1:
        second = excursion(y_star, cap)
        if second is not None:
            second_y = second["y"]
            second_lt = second["y"] < n
    ret = first_return_below(n)
    suffix = None
    if ret is not None and y_even:
        suffix = suffix_after_oa_ee(ret["word"], a)
    return {
        "n": n,
        "a": a,
        "z": z,
        "e": e,
        "b": b,
        "y_star": y_star,
        "cell": residual_cell(n, z),
        "y_even": y_even,
        "first_kind": post_even_kind(n, y_star),
        "first_exc_lt": first_lt,
        "second_y": second_y,
        "second_exc_lt": second_lt,
        "return": ret,
        "suffix": suffix,
    }


def _bucket(row: dict[str, Any]) -> str:
    if row["y_even"] and row["a"] in (2, 3):
        return "easy_even_y"
    if row["y_even"] and row["a"] >= 4:
        return "hard_even_y"
    return "odd_y"


def _hard_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    first_lt = [row for row in rows if row["first_exc_lt"]]
    first_stay = [row for row in rows if not row["first_exc_lt"]]
    second_ok = [row for row in first_stay if row["second_exc_lt"]]
    second_fail = [row for row in first_stay if row["second_exc_lt"] is False]
    missing_return = [row["n"] for row in rows if row["return"] is None]
    suffixes = Counter(row["suffix"] for row in rows if row["suffix"] is not None)
    by_a: dict[int, set[str | None]] = {}
    lengths: list[int] = []
    for row in rows:
        by_a.setdefault(row["a"], set()).add(row["suffix"])
        if row["return"] is not None:
            lengths.append(row["return"]["step"])
    family_by_a = bool(rows) and all(len(vals) == 1 for vals in by_a.values())
    even_only = bool(suffixes) and all(
        suffix is not None and set(suffix) <= {"E"} for suffix in suffixes
    )
    paper_b = any(
        ("O" * row["a"] + "EE" + (row["suffix"] or "")) in PAPER_B_ENGINES
        for row in rows
        if row["return"] is not None
    )
    n0 = max((row["n"] for row in first_lt), default=None)
    first_stay_min = min((row["n"] for row in first_stay), default=None)
    return {
        "count": len(rows),
        "first_exc_lt_count": len(first_lt),
        "first_exc_stay_count": len(first_stay),
        "first_exc_all_lt": bool(rows) and not first_stay,
        "first_exc_n0": n0,
        "first_exc_stay_min": first_stay_min,
        "first_exc_stay_ns": [row["n"] for row in first_stay[:12]],
        "second_exc_ok_count": len(second_ok),
        "second_exc_fail_count": len(second_fail),
        "second_exc_all_lt": bool(first_stay) and not second_fail,
        "second_exc_fail_ns": [row["n"] for row in second_fail[:12]],
        "missing_return": missing_return[:12],
        "missing_return_count": len(missing_return),
        "suffix_counts": dict(suffixes.most_common()),
        "suffix_count": len(suffixes),
        "family_by_a": family_by_a,
        "suffixes_even_only": even_only,
        "suffixes_are_paper_b": paper_b,
        "return_len_min": min(lengths) if lengths else None,
        "return_len_max": max(lengths) if lengths else None,
        "a_values": sorted({row["a"] for row in rows}),
        "samples": [
            {
                "n": row["n"],
                "a": row["a"],
                "e": row["e"],
                "b": row["b"],
                "y_star": row["y_star"],
                "first_kind": row["first_kind"],
                "second_exc_lt": row["second_exc_lt"],
                "return": row["return"],
                "suffix": row["suffix"],
            }
            for row in rows[:8]
        ],
    }


def overshoot_return_census(
    *, n_max: int = N_MAX, cap: int = FIRST_EVEN_CAP
) -> dict[str, Any]:
    buckets: dict[str, list[dict[str, Any]]] = {
        "easy_even_y": [],
        "hard_even_y": [],
        "odd_y": [],
    }
    for n in range(3, n_max + 1, 2):
        row = overshoot_row(n, cap)
        if row is None:
            continue
        buckets[_bucket(row)].append(row)
    easy = buckets["easy_even_y"]
    hard = buckets["hard_even_y"]
    odd = buckets["odd_y"]
    return {
        "n_max": n_max,
        "overshoot_count": sum(len(v) for v in buckets.values()),
        "easy_even_y_count": len(easy),
        "hard_even_y_count": len(hard),
        "odd_y_count": len(odd),
        "easy_first_exc_all_lt": bool(easy) and all(row["first_exc_lt"] for row in easy),
        "easy_a_values": sorted({row["a"] for row in easy}),
        "odd_y_two_excursion_stay": [
            row["n"]
            for row in odd
            if not row["first_exc_lt"] and row["second_exc_lt"] is False
        ][:20],
        "hard": _hard_summary(hard),
    }


def lean_api_present() -> dict[str, bool]:
    even = EVEN_COUNT_THREE.read_text(encoding="utf-8")
    residuals = RESIDUALS.read_text(encoding="utf-8")
    progress = PROGRESS.read_text(encoding="utf-8")
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    corpus = juggler_text()
    floor = engine_floor_text()
    combined = even + residuals + progress + corpus + floor
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **{name: has_named(combined, name) for name in LEAN_THEOREMS},
        "certificate_present": all(has_named(combined, name) for name in CERTIFICATE_UNCHANGED),
        "paper_a_has_no_overshoot_return": "minimal_first_even_overshoots" not in paper,
        "no_global_termination_theorem": "theorem juggler_reaches_one" not in combined,
        "no_return_below_universal": "theorem overshoot_return_below" not in combined,
        "no_two_excursion_progress": "theorem odd_odd_two_excursion_progress"
        not in combined,
        "PowerHeight_absent": "PowerHeight" not in combined,
        "FloorPower_not_rewritten": "ReturnBelow" not in floor
        and "minimal_first_even_overshoots" not in floor,
        "Progress_unchanged": "minimal_first_even_overshoots" not in progress,
    }


def classify(census: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["minimal_first_even_overshoots"]
        and lean["cycleMin_first_even_overshoots"]
        and lean["ReturnBelow"]
        and lean["no_global_termination_theorem"]
        and lean["no_return_below_universal"]
        and lean["paper_a_has_no_overshoot_return"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    hard = census["hard"]
    if hard["count"] == 0:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "no a>=4 even-y overshoots in the window",
        }
    if hard["suffixes_are_paper_b"]:
        return {
            "classification": CLASS_REPARAM,
            "reason": (
                "a>=4 even-y return words are already-certified "
                "non-OOOO Paper B engines"
            ),
        }
    later_uniform = (
        (not hard["first_exc_all_lt"])
        and hard["missing_return_count"] == 0
        and (
            hard["second_exc_all_lt"]
            or hard["suffix_count"] == 1
            or hard["family_by_a"]
        )
        and not hard["suffixes_even_only"]
    )
    if later_uniform:
        return {
            "classification": CLASS_GREEN,
            "reason": (
                "a>=4 even-y overshoots share a later ReturnBelow "
                "comparison that is not a Paper B engine and not the "
                "expanding first excursion"
            ),
        }
    if (
        hard["missing_return_count"] == 0
        and hard["suffix_count"] > 1
        and not hard["family_by_a"]
        and not hard["second_exc_all_lt"]
    ):
        return {
            "classification": CLASS_SCATTER,
            "reason": (
                f"a>=4 even-y first-excursion descent dies "
                f"(N0={hard['first_exc_n0']}); second excursion is not "
                f"uniform; {hard['suffix_count']} ReturnBelow suffixes "
                f"scatter with lengths "
                f"{hard['return_len_min']}..{hard['return_len_max']}"
            ),
        }
    return {
        "classification": CLASS_REPARAM,
        "reason": (
            "no later uniform contractor: first-excursion descent is "
            f"the whole story through N0={hard['first_exc_n0']}, or "
            "the only pattern is more trailing evens of O^a EE"
        ),
    }


def run_probe(*, n_max: int = N_MAX) -> dict[str, Any]:
    return {
        "census": overshoot_return_census(n_max=n_max),
        "pin": overshoot_return_census(n_max=N_PIN),
        "basin": [1],
    }


def probe_payload(*, n_max: int = N_MAX) -> dict[str, Any]:
    scan = run_probe(n_max=n_max)
    lean = lean_api_present()
    decision = classify(scan["census"], lean)
    anti = dict(ANTI_OVERCLAIM)
    anti["finite_progress_for_all"] = False
    anti["return_below_universal"] = False
    anti["cycle_impossible"] = False
    anti["density_one_claimed"] = False
    anti["two_excursion_always_returns"] = False
    return {
        "experiment": "juggler_overshoot_return",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "odd-odd first-E overshoots; split even y by a=2,3 vs a>=4; "
            "first excursion, next excursion, then ReturnBelow suffix "
            "after O^a EE; no K3, no Paper B engine hunt, no halt theorem"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    census = scan["census"]
    pin = scan["pin"]
    hard = census["hard"]
    lines = [
        "# Juggler later ReturnBelow after even-y overshoot",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. After e<=3 the first even",
        "always overshoots on a minimal non-terminator. Halt on that",
        "leftover is ReturnBelow from y>n. Novelty is only a>=4",
        "even-y; a=2,3 replay Paper B.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Does every first-E overshoot with even y",
        "                        admit a uniform later word from y that",
        "                        lands below the original n?",
        "Novelty hypothesis      After e<=3 the first even always overshoots;",
        "                        the even-y class then has one later",
        "                        contractor, giving FiniteProgress on that class",
        "Falsifier               a>=4 return words scatter, or only Paper B engines,",
        "                        or an even-y stay like 37 / 77",
        "Existing machinery      Progress spine; ReturnBelow; e<=3; Paper B; K3 parked",
        "Maximum Phase-0 scope   Lean overshoot corollary; even-y census, novelty at a>=4",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Window",
        "",
        f"- n_max: `{census['n_max']}`",
        f"- overshoots: `{census['overshoot_count']}`",
        f"- easy even-y a=2,3: `{census['easy_even_y_count']}`",
        f"- hard even-y a>=4: `{census['hard_even_y_count']}`",
        f"- odd y: `{census['odd_y_count']}`",
        f"- easy first-excursion all descend: `{census['easy_first_exc_all_lt']}`",
        f"- odd-y two-excursion stays (count only): `{census['odd_y_two_excursion_stay']}`",
        "",
        f"Pin n<=`{pin['n_max']}`: easy `{pin['easy_even_y_count']}`, "
        f"hard `{pin['hard_even_y_count']}`, odd `{pin['odd_y_count']}`.",
        "",
        "## Hard class a>=4 even y",
        "",
        f"- count: `{hard['count']}`",
        f"- first excursion < n: `{hard['first_exc_lt_count']}`",
        f"- first excursion stay: `{hard['first_exc_stay_count']}`",
        f"- first-excursion N0: `{hard['first_exc_n0']}`",
        f"- first stay min n: `{hard['first_exc_stay_min']}`",
        f"- first stay samples: `{hard['first_exc_stay_ns']}`",
        f"- second excursion all < n on stays: `{hard['second_exc_all_lt']}`",
        f"- second excursion failures: `{hard['second_exc_fail_ns']}`",
        f"- missing ReturnBelow: `{hard['missing_return']}`",
        f"- suffix counts: `{hard['suffix_counts']}`",
        f"- family by a: `{hard['family_by_a']}`",
        f"- suffixes even-only: `{hard['suffixes_even_only']}`",
        f"- suffixes Paper B: `{hard['suffixes_are_paper_b']}`",
        f"- return length: `{hard['return_len_min']}`..`{hard['return_len_max']}`",
        f"- a values: `{hard['a_values']}`",
        "",
        "## Hard samples",
        "",
    ]
    for row in hard["samples"]:
        lines.append(
            f"- n=`{row['n']}` a=`{row['a']}` e=`{row['e']}` b=`{row['b']}` "
            f"y*=`{row['y_star']}` first=`{row['first_kind']}` "
            f"second_lt=`{row['second_exc_lt']}` "
            f"return=`{row['return']}` suffix=`{row['suffix']}`"
        )
    lines.extend(["", "## Lean", ""])
    for name in LEAN_THEOREMS:
        lines.append(f"- `{name}`: `{lean.get(name)}`")
    lines.extend(
        [
            f"- certificate unchanged: `{lean.get('certificate_present')}`",
            f"- Paper A has no overshoot-return: `{lean.get('paper_a_has_no_overshoot_return')}`",
            f"- `PowerHeight` absent: `{lean.get('PowerHeight_absent')}`",
            f"- FloorPower not rewritten: `{lean.get('FloorPower_not_rewritten')}`",
            f"- Progress unchanged: `{lean.get('Progress_unchanged')}`",
            f"- no universal return-below: `{lean.get('no_return_below_universal')}`",
            f"- no two-excursion progress: `{lean.get('no_two_excursion_progress')}`",
            f"- no global halt theorem: `{lean.get('no_global_termination_theorem')}`",
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
            "This is not a halt result. A cycle of length >=11 is one",
            "FiniteProgress failure. Odd-y overshoot and K3 stay closed.",
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
    hard = payload["scan"]["census"]["hard"]
    print(f"hard={hard['count']} suffixes={hard['suffix_counts']}")
    print(
        f"first_lt={hard['first_exc_lt_count']} stay={hard['first_exc_stay_count']} "
        f"second_all={hard['second_exc_all_lt']}"
    )


if __name__ == "__main__":
    main()

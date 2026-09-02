"""Residual progress from uncertified Juggler collapse states.

Not a Research Engine control-layer experiment. Studies the residual
state y after an uncertified collapse n→y, independently of how y was
reached. Not a halt theorem and not a new infinite-path type.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Callable

from research.juggler_sequence.no_progress_paths import (
    PREFIX_CAP,
    classify_collapse_row,
    collapse_census,
    even_collapses,
    realized_prefix,
)
from research.juggler_sequence.lean_paths import juggler_text
from research.juggler_sequence.power_itineraries import (
    ANTI_OVERCLAIM,
    LEAN_PATH,
    floor_power,
    odd_count,
    word_of,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_residual_progress.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_residual_progress.md"

CLASS_GREEN = "RESIDUAL_PROGRESS_GREEN"
CLASS_ESCAPE = "RESIDUAL_ESCAPE_FOUND"
CLASS_CORE = "SMALL_RESIDUAL_CORE_FOUND"
CLASS_INCOMPLETE = "RESIDUAL_PROGRESS_INCOMPLETE"

CALIBRATION = (11, 9317, 2233)
ANNOTATED_STARTS = (9, 37)
M_LEAN = 12
EVEN_SQ = 144
HORIZON_CAP = 40
SLOW_EXAMPLE = 193
SLOW_CAP = 80
N_MAX = 80

LEAN_THEOREMS = (
    "three_reachesOne",
    "five_reachesOne",
    "seven_reachesOne",
    "nine_reachesOne",
    "ten_reachesOne",
    "eleven_reachesOne",
    "reachesOne_of_lt_twelve",
    "image_lt_twelve_reachesOne",
    "non_reachesOne_ge_twelve",
    "even_lt_sq_twelve_reachesOne",
    "image_pos",
    "reachesOne_of_image",
    "minimal_avoids_reachesOne_image",
)

CERTIFICATE_UNCHANGED = (
    "power_bound_compensated_contracts",
    "first_even_freeze",
    "eventually_no_first_even_contraction",
    "changing_suffix_unbounded_contraction",
    "two_reachesOne",
    "minimal_avoids_progress",
)


def certified_reaches_one(y: int) -> bool:
    if y < 1:
        return False
    if y < M_LEAN:
        return True
    return y % 2 == 0 and y < EVEN_SQ


def iterate_path(y: int, steps: int) -> list[int]:
    if y < 1 or steps < 0:
        raise ValueError("iterate_path requires y >= 1 and steps >= 0")
    path = [y]
    current = y
    for _ in range(steps):
        current = floor_power(current)
        path.append(current)
    return path


def first_index(path: list[int], pred: Callable[[int, int], bool]) -> int | None:
    for index, state in enumerate(path):
        if index == 0:
            continue
        if pred(index, state):
            return index
    return None


def descends_within(y: int, limit: int) -> bool:
    path = iterate_path(y, limit)
    return first_index(path, lambda _r, state: state < y) is not None


def reaches_one_within(y: int, limit: int) -> bool:
    path = iterate_path(y, limit)
    return first_index(path, lambda _r, state: certified_reaches_one(state)) is not None


def progress_within(y: int, limit: int) -> bool:
    return descends_within(y, limit) or reaches_one_within(y, limit)


def global_descent_within(y: int, start: int, limit: int) -> bool:
    path = iterate_path(y, limit)
    return first_index(path, lambda _r, state: state < start) is not None


def largest_even_stats(path: list[int]) -> dict[str, Any]:
    runs = even_collapses(path)
    if not runs:
        return {
            "largest_even_run": 0,
            "largest_collapse_x": None,
            "largest_collapse_y": None,
        }
    longest = max(runs, key=lambda row: row["r"])
    biggest = max(runs, key=lambda row: (row["x"], row["y"]))
    return {
        "largest_even_run": longest["r"],
        "largest_collapse_x": biggest["x"],
        "largest_collapse_y": biggest["y"],
    }


def residual_record(y: int, *, cap: int = HORIZON_CAP, start: int | None = None) -> dict[str, Any]:
    path = iterate_path(y, cap)
    word = word_of(tuple(path))
    local_i = first_index(path, lambda _r, state: state < y)
    cert_i = first_index(path, lambda _r, state: certified_reaches_one(state))
    capture_i = first_index(path, lambda _r, state: state == 1)
    global_i = None
    if start is not None:
        global_i = first_index(path, lambda _r, state: state < start)
    if capture_i is not None and (local_i is None or capture_i <= local_i) and (
        cert_i is None or capture_i <= cert_i
    ):
        kind = "CAPTURE"
        horizon = capture_i
    elif cert_i is not None and (local_i is None or cert_i <= local_i):
        kind = "REACHES_ONE"
        horizon = cert_i
    elif local_i is not None:
        kind = "LOCAL_DESCENT"
        horizon = local_i
    else:
        kind = "UNRESOLVED"
        horizon = None
    first_cert = None
    if cert_i is not None:
        first_cert = path[cert_i]
    stats = largest_even_stats(path if horizon is None else path[: horizon + 1])
    return {
        "start": y,
        "origin_n": start,
        "initial_parity": "O" if y % 2 else "E",
        "first_progress_type": kind,
        "progress_horizon": horizon,
        "progress_image": None if horizon is None else path[horizon],
        "min_visited": min(path if horizon is None else path[: horizon + 1]),
        "max_visited": max(path if horizon is None else path[: horizon + 1]),
        "max_visited_bits": (max(path if horizon is None else path[: horizon + 1])).bit_length(),
        "first_reaches_one_state": first_cert,
        "renewal_horizon": global_i,
        "renewal_image": None if global_i is None else path[global_i],
        "word": word if horizon is None else word[:horizon],
        "itinerary_length": len(word if horizon is None else word[:horizon]),
        "odd_count": odd_count(word if horizon is None else word[:horizon]),
        **stats,
        "progress_within": kind != "UNRESOLVED",
    }


def small_interval_scan(*, m: int = M_LEAN) -> dict[str, Any]:
    missing = [y for y in range(1, m) if not progress_within(y, HORIZON_CAP)]
    steps = {}
    for y in range(1, m):
        rec = residual_record(y, cap=HORIZON_CAP)
        steps[str(y)] = rec["progress_horizon"]
    return {
        "m": m,
        "all_progress": missing == [],
        "missing": missing,
        "horizons": steps,
        "max_horizon": max(steps.values()) if steps else 0,
    }


def even_square_scan(*, limit: int = EVEN_SQ) -> dict[str, Any]:
    missing = [
        y
        for y in range(2, limit, 2)
        if not certified_reaches_one(y) or not progress_within(y, 1)
    ]
    return {"limit": limit, "missing": missing, "all_even_progress": missing == []}


def calibration_records() -> list[dict[str, Any]]:
    origins = {11: 9, 9317: 37, 2233: 37}
    return [residual_record(y, start=origins.get(y)) for y in CALIBRATION]


def uncertified_pairs(*, n_max: int = N_MAX, cap: int = PREFIX_CAP) -> list[dict[str, Any]]:
    pairs: list[dict[str, Any]] = []
    seen: set[int] = set()
    for n in range(2, n_max + 1):
        record = realized_prefix(n, cap)
        for run in even_collapses(record["path"]):
            row = classify_collapse_row(n, run, record["word"])
            if row["uncertified_ge_n"] and row["y"] not in seen:
                seen.add(row["y"])
                pairs.append(row)
    pairs.sort(key=lambda row: (row["y"], row["n"]))
    return pairs


def uncertified_residual_records(*, n_max: int = N_MAX) -> dict[str, Any]:
    pairs = uncertified_pairs(n_max=n_max)
    rows = [residual_record(item["y"], start=item["n"]) for item in pairs]
    unresolved = [row for row in rows if not row["progress_within"]]
    outside_r = [row["start"] for row in rows if not certified_reaches_one(row["start"])]
    minimized = collapse_census(n_max=n_max)["minimized_uncertified_ge_n"]
    return {
        "records": rows[:8],
        "unresolved": unresolved,
        "outside_certified_r": outside_r,
        "outside_count": len(outside_r),
        "all_progress": unresolved == [],
        "minimized_uncertified": minimized,
    }


def renewal_scan(*, n_max: int = N_MAX) -> dict[str, Any]:
    failures = []
    pairs = uncertified_pairs(n_max=n_max)
    for item in pairs:
        if not global_descent_within(item["y"], item["n"], HORIZON_CAP):
            failures.append({"n": item["n"], "y": item["y"]})
    return {
        "checked": len(pairs),
        "failures": failures,
        "no_counterexample": failures == [],
    }


def slow_local_descent() -> dict[str, Any]:
    rec = residual_record(SLOW_EXAMPLE, cap=SLOW_CAP)
    return {
        "y": SLOW_EXAMPLE,
        "progress_horizon": rec["progress_horizon"],
        "first_progress_type": rec["first_progress_type"],
        "progress_image": rec["progress_image"],
        "max_visited_bits": rec["max_visited_bits"],
        "uniform_L_on_all_N": False,
    }


def lean_api_present() -> dict[str, bool]:
    text = juggler_text()
    return {
        "sorry_free": "sorry" not in text and "admit" not in text,
        **{
            name: (f"theorem {name}" in text or f"def {name}" in text)
            for name in LEAN_THEOREMS
        },
        "certificate_present": all(f"theorem {name}" in text for name in CERTIFICATE_UNCHANGED),
        "PowerHeight_absent": "PowerHeight" not in text,
        "no_lower_envelope_structure": "structure LowerEnvelope" not in text,
        "no_global_termination_theorem": "theorem juggler_reaches_one" not in text,
        "no_no_progress_prefix_type": "def no_progress_prefix" not in text
        and "structure NoProgressPrefix" not in text
        and "def ResidualState" not in text,
    }


def classify(
    small: dict[str, Any],
    evens: dict[str, Any],
    calibration: list[dict[str, Any]],
    uncertified: dict[str, Any],
    renewal: dict[str, Any],
    lean: dict[str, bool],
) -> dict[str, Any]:
    escape = [
        row
        for row in calibration + uncertified["unresolved"]
        if not row["progress_within"]
    ]
    if escape:
        return {
            "classification": CLASS_ESCAPE,
            "reason": f"a residual evaded ProgressWithin: {escape[:2]}",
        }
    lean_ok = (
        lean["sorry_free"]
        and lean["reachesOne_of_lt_twelve"]
        and lean["image_lt_twelve_reachesOne"]
        and lean["even_lt_sq_twelve_reachesOne"]
        and lean["eleven_reachesOne"]
        and lean["no_global_termination_theorem"]
        and lean["no_no_progress_prefix_type"]
    )
    cal_ok = all(row["progress_within"] for row in calibration)
    if (
        lean_ok
        and small["all_progress"]
        and evens["all_even_progress"]
        and cal_ok
        and uncertified["all_progress"]
        and renewal["no_counterexample"]
    ):
        return {
            "classification": CLASS_GREEN,
            "reason": (
                "R={1,...,11} is ReachesOne; even residuals below 144 "
                "are ReachesOne by one even step; known uncertified collapse "
                "residuals locally descend from y; 9→11 is now ReachesOne-implied"
            ),
        }
    if small["all_progress"] and not lean_ok:
        return {
            "classification": CLASS_CORE,
            "reason": "small residuals progress computationally, Lean interval missing",
        }
    return {
        "classification": CLASS_INCOMPLETE,
        "reason": (
            f"lean_ok={lean_ok} small={small['all_progress']} "
            f"evens={evens['all_even_progress']} cal_ok={cal_ok}"
        ),
    }


def run_probe() -> dict[str, Any]:
    small = small_interval_scan()
    evens = even_square_scan()
    calibration = calibration_records()
    uncertified = uncertified_residual_records()
    renewal = renewal_scan()
    slow = slow_local_descent()
    return {
        "small_interval": small,
        "even_square": evens,
        "calibration": calibration,
        "uncertified": uncertified,
        "renewal": renewal,
        "slow_local_descent": slow,
        "certified_r": {"lt": M_LEAN, "even_lt": EVEN_SQ},
        "basin": [1],
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(
        scan["small_interval"],
        scan["even_square"],
        scan["calibration"],
        scan["uncertified"],
        scan["renewal"],
        lean,
    )
    return {
        "experiment": "juggler_residual_progress",
        "engine_control_layer_modified": False,
        "anti_overclaim": dict(ANTI_OVERCLAIM),
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "ProgressWithin/DescendsWithin/ReachesOneWithin from residual y; "
            "calibration 11 and 9317; small-M interval; even<144; renewal "
            "T^r(y)<n counterexample search; no logs, no halt claim"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler residual progress",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment and",
        "not a termination theorem. After an uncertified collapse `n→y`,",
        "progress is measured from the residual `y` itself.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Useful R with ProgressWithin; residuals from known collapses",
        "Novelty hypothesis      All y<12 are ReachesOne; even y<144 follow",
        "Falsifier               Some y<12 fails, or a calibration residual escapes",
        "Existing machinery      ReachesOne closure, floorPower_pos, collapse census",
        "Maximum Phase-0 scope   Census plus Lean interval <12 and even <144",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- certified R: `y<{scan['certified_r']['lt']}` and even `y<{scan['certified_r']['even_lt']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- sorry-free: `{lean['sorry_free']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Calibration residuals",
        "",
    ]
    for row in scan["calibration"]:
        lines.append(
            f"- y=`{row['start']}` from n=`{row['origin_n']}` kind=`{row['first_progress_type']}` "
            f"horizon=`{row['progress_horizon']}` image=`{row['progress_image']}` "
            f"renewal=`{row['renewal_horizon']}`→`{row['renewal_image']}`"
        )
    small = scan["small_interval"]
    evens = scan["even_square"]
    slow = scan["slow_local_descent"]
    lines.extend(
        [
            "",
            "## Small interval and even square",
            "",
            f"- all `1≤y<{small['m']}` have ProgressWithin: `{small['all_progress']}` "
            f"(max horizon `{small['max_horizon']}`)",
            f"- all even `2≤y<{evens['limit']}` have ProgressWithin in one step: "
            f"`{evens['all_even_progress']}`",
            f"- uncertified residuals outside R: `{scan['uncertified']['outside_count']}`",
            f"- renewal counterexamples `T^r(y)<n`: `{len(scan['renewal']['failures'])}`",
            "",
            "## Uniform horizon",
            "",
            f"- y=`{slow['y']}` first progress=`{slow['first_progress_type']}` "
            f"horizon=`{slow['progress_horizon']}` image=`{slow['progress_image']}` "
            f"max bits=`{slow['max_visited_bits']}`",
            "- No uniform `L` works for every positive integer. The useful `R` is the",
            "  certified initial segment, not all of `ℕ`.",
            "",
            "## Lean",
            "",
        ]
    )
    for name in LEAN_THEOREMS:
        lines.append(f"- `{name}`: `{lean.get(name)}`")
    lines.extend(
        [
            f"- certificate unchanged: `{lean.get('certificate_present')}`",
            f"- `PowerHeight` absent: `{lean.get('PowerHeight_absent')}`",
            f"- no residual-path datatype: `{lean.get('no_no_progress_prefix_type')}`",
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
            "This is not a halt result.",
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

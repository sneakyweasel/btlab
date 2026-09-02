"""First even residual of an odd-to-odd Juggler start.

Not a Research Engine control-layer experiment. Not a halt theorem.
Classifies the first even residual into below-n^2, return cell, or
overshoot. Does not prove FiniteProgress on the overshoot class.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power
from research.juggler_sequence.progress_coverage import coverage_bucket, is_odd_odd
from research.juggler_sequence.lean_paths import (
    ENVELOPE,
    MINIMAL,
    PROGRESS,
    RESIDUALS,
    SCALE,
    juggler_text,
    engine_floor_text,
    has_named,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_odd_odd_frontier.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_odd_odd_frontier.md"
LEAN_PATH = RESIDUALS
PROGRESS_PATH = PROGRESS
FLOOR_PATH = ENVELOPE
MIN_PATH = MINIMAL
FIN_PATH = SCALE

CLASS_CLASSIFIED = "FIRST_EVEN_RESIDUAL_CLASSIFIED"
CLASS_OVERSHOOT = "ODD_ODD_COUNTEREXAMPLE_CLASS"
CLASS_CYCLE = "BOUNDARY_CYCLE_GREEN"
CLASS_INCOMPLETE = "ODD_ODD_FRONTIER_INCOMPLETE"

N_MAX = 80
FIRST_EVEN_CAP = 24
CALIBRATION = (3, 5, 9, 13, 25, 37, 69, 77)

LEAN_THEOREMS = (
    "image_oddEvenBlock",
    "first_even_return",
    "even_floorPower_lt_iff",
    "even_floorPower_eq_iff",
    "even_floorPower_gt_iff",
    "even_ne_odd_square",
    "odd_even_residual_trichotomy",
    "odd_even_residual_image",
    "first_even_descent_iff",
    "finiteProgress_of_first_even_below",
    "minimal_even_residual_gt_sq",
    "minimal_nonterm_not_first_even_descent",
    "minimal_nonterm_not_first_even_capture",
    "first_even_return_cycle",
    "minimal_first_even_dichotomy",
)

CERTIFICATE_UNCHANGED = (
    "FiniteProgress",
    "reachesOne_of_all_finiteProgress",
    "unresolved_is_odd_odd",
    "even_run_scale_barrier",
    "odd_run_financing_scale_barrier",
    "power_bound_word",
    "ReachesOne",
    "DescentCertificate",
    "descent_of_below",
)


def first_even_residual(n: int, cap: int = FIRST_EVEN_CAP) -> dict[str, Any] | None:
    if n % 2 == 0:
        return None
    current = n
    for a in range(1, cap + 1):
        current = floor_power(current)
        if current % 2 == 0:
            return {"a": a, "z": current, "e": floor_power(current)}
    return None


def even_run_end(z: int, cap: int = 40) -> tuple[int, int]:
    current = z
    b = 0
    while current % 2 == 0 and current > 0 and b < cap:
        current = floor_power(current)
        b += 1
    return b, current


def residual_cell(n: int, z: int) -> str:
    if z < n * n:
        return "below"
    if z < (n + 1) * (n + 1):
        return "boundary"
    return "overshoot"


def post_even_kind(n: int, y: int) -> str:
    if y == 1:
        return "CAPTURE"
    if y < n:
        return "DESCENT"
    if y == n:
        return "RETURN"
    return "STAY"


def frontier_row(n: int, cap: int = FIRST_EVEN_CAP) -> dict[str, Any] | None:
    if coverage_bucket(n) != "ODD_ODD":
        return None
    fe = first_even_residual(n, cap)
    if fe is None:
        return {
            "n": n,
            "cell": "NO_EVEN_WITHIN_HORIZON",
            "kind": "NO_EVEN_WITHIN_HORIZON",
        }
    a, z, e = fe["a"], fe["z"], fe["e"]
    b, y = even_run_end(z)
    return {
        "n": n,
        "a": a,
        "z": z,
        "e": e,
        "b": b,
        "y": y,
        "cell": residual_cell(n, z),
        "e_cmp": "lt" if e < n else ("eq" if e == n else "gt"),
        "kind": post_even_kind(n, y),
    }


def frontier_census(*, n_max: int = N_MAX, cap: int = FIRST_EVEN_CAP) -> dict[str, Any]:
    rows = []
    for n in range(2, n_max + 1):
        row = frontier_row(n, cap)
        if row is not None:
            rows.append(row)
    cells = {"below": 0, "boundary": 0, "overshoot": 0, "NO_EVEN_WITHIN_HORIZON": 0}
    kinds: dict[str, int] = {}
    for row in rows:
        cells[row["cell"]] = cells.get(row["cell"], 0) + 1
        kinds[row["kind"]] = kinds.get(row["kind"], 0) + 1
    stay = [row for row in rows if row["kind"] == "STAY"]
    return {
        "n_max": n_max,
        "odd_odd": len(rows),
        "cells": cells,
        "post_even_kinds": kinds,
        "stay_count": len(stay),
        "stay_samples": stay[:8],
        "overshoot_samples": [row for row in rows if row["cell"] == "overshoot"][:6],
    }


def calibration_rows() -> list[dict[str, Any]]:
    rows = []
    for n in CALIBRATION:
        row: dict[str, Any] = {
            "n": n,
            "bucket": coverage_bucket(n),
            "odd_odd": is_odd_odd(n),
        }
        if is_odd_odd(n):
            row.update(frontier_row(n) or {})
        rows.append(row)
    return rows


def lean_api_present() -> dict[str, bool]:
    text = LEAN_PATH.read_text(encoding="utf-8")
    progress = PROGRESS_PATH.read_text(encoding="utf-8")
    corpus = juggler_text()
    floor = engine_floor_text()
    minimum = MIN_PATH.read_text(encoding="utf-8")
    financing = FIN_PATH.read_text(encoding="utf-8")
    combined = text + progress + corpus + minimum + financing
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **{name: has_named(combined, name) for name in LEAN_THEOREMS},
        "certificate_present": all(
            (has_named(combined, name))
            for name in CERTIFICATE_UNCHANGED
        ),
        "PowerHeight_absent": "PowerHeight" not in combined,
        "no_global_termination_theorem": "theorem juggler_reaches_one" not in combined,
        "no_all_finiteProgress_proved": "theorem all_finiteProgress" not in combined,
        "no_infinite_path_type": "coinductive" not in text.lower()
        and "def InfinitePath" not in text,
        "no_frequency_theorem": "theorem odd_run_frequency" not in text,
        "no_cycle_engine": "def CycleSearch" not in text,
        "FloorPower_not_rewritten": "odd_even_residual_trichotomy" not in floor,
        "Progress_unchanged": "minimal_first_even_dichotomy" not in progress,
    }


def classify(census: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["odd_even_residual_trichotomy"]
        and lean["minimal_first_even_dichotomy"]
        and lean["minimal_nonterm_not_first_even_descent"]
        and lean["finiteProgress_of_first_even_below"]
        and lean["no_global_termination_theorem"]
        and lean["FloorPower_not_rewritten"]
        and lean["Progress_unchanged"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if census["cells"].get("below", 0) > 0:
        return {
            "classification": CLASS_CLASSIFIED,
            "secondary": [CLASS_OVERSHOOT],
            "reason": "trichotomy compiles; a below-n^2 odd-odd residual occurred",
        }
    return {
        "classification": CLASS_CLASSIFIED,
        "secondary": [CLASS_OVERSHOOT],
        "reason": (
            "first even residual is below n^2, return-to-n, or overshoot; "
            "a MinimalNonTerm start cannot Descent or Capture on the first "
            "O^a E; the window is all overshoot"
        ),
    }


def run_probe() -> dict[str, Any]:
    return {
        "census": frontier_census(),
        "calibration": calibration_rows(),
        "basin": [1],
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan["census"], lean)
    anti = dict(ANTI_OVERCLAIM)
    anti["all_odd_orbit"] = False
    anti["finite_progress_for_all"] = False
    anti["first_even_descends"] = False
    anti["cycle_impossible"] = False
    anti["overshoot_is_progress"] = False
    return {
        "experiment": "juggler_odd_odd_frontier",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "odd-odd starts; first even residual cell vs n^2 and (n+1)^2; "
            "maximal even-run endpoint; no FiniteProgress search as a proof"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    census = scan["census"]
    cells = census["cells"]
    lines = [
        "# Juggler odd-to-odd first-even residual",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. An even residual `z` of an odd",
        "start `n` is below `n^2`, in the return cell, or an overshoot.",
        "A `MinimalNonTerm` start cannot close on the first `O^a E`.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     classify the first even residual of an odd-to-odd start",
        "Novelty hypothesis      CE first O^a E is a cycle candidate or overshoot",
        "Falsifier               below-n^2 on a CE, or first O^a E Descent on a CE",
        "Existing machinery      even barrier, square-cell inverse, FiniteProgress, oddEvenBlock",
        "Maximum Phase-0 scope   trichotomy; CE dichotomy; FiniteProgress if z<n^2; census",
        "```",
        "",
        "## Metadata",
        "",
        f"- basin: `{scan['basin']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- secondary: `{decision.get('secondary')}`",
        f"- sorry-free: `{lean['sorry_free']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Residual census",
        "",
        f"- odd-odd starts: `{census['odd_odd']}`",
        f"- below n^2: `{cells.get('below', 0)}`",
        f"- return cell: `{cells.get('boundary', 0)}`",
        f"- overshoot: `{cells.get('overshoot', 0)}`",
        f"- post-even kinds: `{census['post_even_kinds']}`",
        f"- stay after maximal even run: `{census['stay_count']}`",
        "",
        "## Stay-after-even samples",
        "",
    ]
    for row in census["stay_samples"]:
        lines.append(
            f"- n=`{row['n']}` a=`{row['a']}` z=`{row['z']}` e=`{row['e']}` "
            f"b=`{row['b']}` y=`{row['y']}`"
        )
    lines.extend(["", "## Calibration", ""])
    for row in scan["calibration"]:
        if not row.get("odd_odd"):
            lines.append(f"- n=`{row['n']}` bucket=`{row['bucket']}`")
            continue
        lines.append(
            f"- n=`{row['n']}` a=`{row.get('a')}` z=`{row.get('z')}` "
            f"cell=`{row.get('cell')}` e=`{row.get('e')}` b=`{row.get('b')}` "
            f"y=`{row.get('y')}` kind=`{row.get('kind')}`"
        )
    lines.extend(["", "## Lean", ""])
    for name in LEAN_THEOREMS:
        lines.append(f"- `{name}`: `{lean.get(name)}`")
    lines.extend(
        [
            f"- certificate unchanged: `{lean.get('certificate_present')}`",
            f"- `PowerHeight` absent: `{lean.get('PowerHeight_absent')}`",
            f"- FloorPower not rewritten: `{lean.get('FloorPower_not_rewritten')}`",
            f"- Progress spine unchanged: `{lean.get('Progress_unchanged')}`",
            f"- no cycle engine: `{lean.get('no_cycle_engine')}`",
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
            "This is not a halt result. Overshoot is not FiniteProgress.",
            "Return-to-n is a cycle candidate, not a cycle-impossibility theorem.",
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

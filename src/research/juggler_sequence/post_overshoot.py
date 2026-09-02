"""Post-overshoot residual of an odd-to-odd Juggler start.

Not a Research Engine control-layer experiment. Not a halt theorem.
Classifies the first state after a first-even overshoot and records
that two excursions do not always return below the original start.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.odd_odd_frontier import (
    even_run_end,
    first_even_residual,
    frontier_row,
    post_even_kind,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power, itinerary
from research.juggler_sequence.progress_coverage import is_odd_odd
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
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_post_overshoot.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_post_overshoot.md"
LEAN_PATH = RESIDUALS
PROGRESS_PATH = PROGRESS
FLOOR_PATH = ENVELOPE
MIN_PATH = MINIMAL
FIN_PATH = SCALE

CLASS_PERSISTENT = "PERSISTENT_OVERSHOOT_COUNTEREXAMPLE"
CLASS_RETURN = "RETURN_BELOW_START_GREEN"
CLASS_TWO = "TWO_EXCURSION_GREEN"
CLASS_PROGRESS = "POST_OVERSHOOT_PROGRESS_GREEN"
CLASS_INCOMPLETE = "POST_OVERSHOOT_INCOMPLETE"

N_MAX = 80
FIRST_EVEN_CAP = 24
ORIGIN_CAP = 80
HARD_PROBES = (9, 37, 49, 69, 77)

LEAN_THEOREMS = (
    "post_even_overshoot",
    "overshoot_residual_gt_start",
    "post_overshoot_parity",
    "ReturnBelow",
    "finiteProgress_of_returnBelow",
    "finiteProgress_of_oddEven_lt",
    "minimal_nonterm_no_returnBelow",
    "minimal_post_even_even_y_ge_sq",
    "minimal_post_even_even_overshoots",
    "minimal_post_even_even_z_ge_fourth",
    "minimal_first_even_dichotomy",
    "even_floorPower_gt_iff",
)

CERTIFICATE_UNCHANGED = (
    "FiniteProgress",
    "ReachesOne",
    "DescentCertificate",
    "descent_of_below",
    "even_run_scale_barrier",
    "odd_run_financing_scale_barrier",
    "power_bound_word",
)


def excursion(start: int, cap: int = FIRST_EVEN_CAP) -> dict[str, Any] | None:
    if start <= 1:
        return None
    if start % 2 == 0:
        z = start
        a = 0
    else:
        fe = first_even_residual(start, cap)
        if fe is None:
            return None
        a, z = fe["a"], fe["z"]
    e = floor_power(z)
    b, y = even_run_end(z)
    return {"a": a, "z": z, "e": e, "b": b, "y": y}


def origin_scale_probe(n: int, cap: int = ORIGIN_CAP) -> dict[str, Any]:
    path = list(itinerary(n, cap))
    first_below = None
    first_eq = None
    first_one = None
    for step, value in enumerate(path):
        if step == 0:
            continue
        if first_below is None and value < n:
            first_below = {"step": step, "value": value}
        if first_eq is None and value == n:
            first_eq = {"step": step, "value": value}
        if first_one is None and value == 1:
            first_one = {"step": step, "value": value}
            path = path[: step + 1]
            break
    return {
        "n": n,
        "first_below": first_below,
        "first_eq": first_eq,
        "first_one": first_one,
        "min_state": min(path),
        "max_state": max(path),
        "horizon": len(path) - 1,
    }


def hard_shape(n: int) -> dict[str, Any]:
    first = excursion(n)
    if first is None:
        return {"n": n, "missing": True}
    second = excursion(first["y"]) if first["y"] > 1 else None
    origin = origin_scale_probe(n)
    return {
        "n": n,
        "first": first,
        "second": second,
        "y1_parity": "even" if first["e"] % 2 == 0 else "odd",
        "first_kind": post_even_kind(n, first["y"]),
        "second_kind": (
            None if second is None else post_even_kind(n, second["y"])
        ),
        "origin": origin,
    }


def post_overshoot_census(*, n_max: int = N_MAX, cap: int = FIRST_EVEN_CAP) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    e_parity = {"even": 0, "odd": 0}
    first_kinds: dict[str, int] = {}
    second_kinds: dict[str, int] = {}
    two_excursion_stay: list[int] = []
    for n in range(2, n_max + 1):
        if not is_odd_odd(n):
            continue
        row = frontier_row(n, cap)
        if row is None or row.get("cell") == "NO_EVEN_WITHIN_HORIZON":
            continue
        e = row["e"]
        parity = "even" if e % 2 == 0 else "odd"
        e_parity[parity] += 1
        kind = row["kind"]
        first_kinds[kind] = first_kinds.get(kind, 0) + 1
        record: dict[str, Any] = {
            "n": n,
            "a": row["a"],
            "z": row["z"],
            "e": e,
            "b": row["b"],
            "y": row["y"],
            "cell": row["cell"],
            "e_parity": parity,
            "first_kind": kind,
        }
        if kind == "STAY":
            second = excursion(row["y"], cap)
            if second is not None:
                kind2 = post_even_kind(n, second["y"])
                record["second"] = {**second, "kind": kind2}
                second_kinds[kind2] = second_kinds.get(kind2, 0) + 1
                if kind2 == "STAY":
                    two_excursion_stay.append(n)
        rows.append(record)
    return {
        "n_max": n_max,
        "odd_odd_overshoot": len(rows),
        "e_parity": e_parity,
        "first_kinds": first_kinds,
        "second_kinds": second_kinds,
        "two_excursion_stay": two_excursion_stay,
        "stay_after_first": [row["n"] for row in rows if row["first_kind"] == "STAY"],
        "rows": rows,
    }


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
        **{
            name: (f"theorem {name}" in text or f"def {name}" in text)
            for name in LEAN_THEOREMS
        },
        "certificate_present": all(
            (has_named(combined, name))
            for name in CERTIFICATE_UNCHANGED
        ),
        "ReturnBelow_distinct": "def ReturnBelow" in text
        and "inductive DescentCertificate" in corpus
        and "inductive DescentCertificate" in corpus
        and "def ReachesOne" in corpus,
        "PowerHeight_absent": "PowerHeight" not in combined,
        "no_global_termination_theorem": "theorem juggler_reaches_one" not in combined,
        "no_return_below_universal": "theorem overshoot_return_below" not in text,
        "no_two_excursion_progress": "theorem odd_odd_two_excursion_progress"
        not in text,
        "no_infinite_path_type": "coinductive" not in text.lower()
        and "def InfinitePath" not in text,
        "no_frequency_theorem": "theorem odd_run_frequency" not in text,
        "no_cycle_engine": "def CycleSearch" not in text,
        "FloorPower_not_rewritten": "ReturnBelow" not in floor
        and "post_even_overshoot" not in floor,
        "Progress_unchanged": "ReturnBelow" not in progress
        and "post_even_overshoot" not in progress,
    }


def classify(census: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and lean["post_even_overshoot"]
        and lean["overshoot_residual_gt_start"]
        and lean["ReturnBelow"]
        and lean["finiteProgress_of_returnBelow"]
        and lean["minimal_nonterm_no_returnBelow"]
        and lean["minimal_post_even_even_z_ge_fourth"]
        and lean["no_global_termination_theorem"]
        and lean["no_return_below_universal"]
        and lean["no_two_excursion_progress"]
        and lean["FloorPower_not_rewritten"]
        and lean["Progress_unchanged"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    stay = census.get("two_excursion_stay") or []
    if stay:
        return {
            "classification": CLASS_PERSISTENT,
            "secondary": [],
            "reason": (
                "first post-overshoot state is classified even or odd; even y "
                "on a CE forces n^4 ≤ z; ReturnBelow is FiniteProgress when it "
                f"fires; two excursions do not always return below n ({stay})"
            ),
        }
    return {
        "classification": CLASS_TWO,
        "secondary": [],
        "reason": "window has no two-excursion stay; do not promote a general law",
    }


def run_probe() -> dict[str, Any]:
    return {
        "census": post_overshoot_census(),
        "hard": [hard_shape(n) for n in HARD_PROBES],
        "basin": [1],
    }


def probe_payload() -> dict[str, Any]:
    scan = run_probe()
    lean = lean_api_present()
    decision = classify(scan["census"], lean)
    anti = dict(ANTI_OVERCLAIM)
    anti["all_odd_orbit"] = False
    anti["finite_progress_for_all"] = False
    anti["overshoot_is_progress"] = False
    anti["return_below_universal"] = False
    anti["two_excursion_always_returns"] = False
    anti["cycle_impossible"] = False
    return {
        "experiment": "juggler_post_overshoot",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "odd-odd overshoots; first post-even parity; first O^a E^b kind; "
            "second excursion from stay-odd y; origin-scale first below / "
            "equal / ReachesOne; no universal return-below theorem"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    census = scan["census"]
    lines = [
        "# Juggler post-overshoot residual",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. After a first-even overshoot the",
        "residual `y = T(z)` exceeds `n` and may be even or odd. Return",
        "below the original start is a finite-prefix certificate, not a",
        "proved law.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     classify post-overshoot y=T(z)>n and leftover certificates",
        "Novelty hypothesis      even y on a CE forces n^4 ≤ z; two excursions need not return",
        "Falsifier               even y on a CE with y < n^2; or a universal two-excursion return",
        "Existing machinery      even_floorPower_gt_iff, even barrier, FiniteProgress, follows_append",
        "Maximum Phase-0 scope   y>n; parity split; CE even-y scale; ReturnBelow; two-excursion census",
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
        "## Post-overshoot census",
        "",
        f"- odd-odd overshoots: `{census['odd_odd_overshoot']}`",
        f"- first post-even parity: `{census['e_parity']}`",
        f"- first O^a E^b kinds: `{census['first_kinds']}`",
        f"- stay after first excursion: `{census['stay_after_first']}`",
        f"- second-excursion kinds from stay: `{census['second_kinds']}`",
        f"- two-excursion stay: `{census['two_excursion_stay']}`",
        "",
        "## Hard probes",
        "",
    ]
    for row in scan["hard"]:
        first = row["first"]
        second = row.get("second")
        origin = row["origin"]
        lines.append(
            f"- n=`{row['n']}` z1=`{first['z']}` y1=`{first['y']}` "
            f"parity=`{row['y1_parity']}` first=`{row['first_kind']}` "
            f"second=`{row['second_kind']}` "
            f"z2=`{None if second is None else second['z']}` "
            f"y2=`{None if second is None else second['y']}` "
            f"below=`{origin['first_below']}` one=`{origin['first_one']}` "
            f"min=`{origin['min_state']}` max=`{origin['max_state']}`"
        )
    lines.extend(["", "## Lean", ""])
    for name in LEAN_THEOREMS:
        lines.append(f"- `{name}`: `{lean.get(name)}`")
    lines.extend(
        [
            f"- certificate unchanged: `{lean.get('certificate_present')}`",
            f"- ReturnBelow distinct: `{lean.get('ReturnBelow_distinct')}`",
            f"- `PowerHeight` absent: `{lean.get('PowerHeight_absent')}`",
            f"- FloorPower not rewritten: `{lean.get('FloorPower_not_rewritten')}`",
            f"- Progress spine unchanged: `{lean.get('Progress_unchanged')}`",
            f"- no universal return-below: `{lean.get('no_return_below_universal')}`",
            f"- no two-excursion progress theorem: `{lean.get('no_two_excursion_progress')}`",
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
            "Two excursions are not a general return-below theorem.",
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

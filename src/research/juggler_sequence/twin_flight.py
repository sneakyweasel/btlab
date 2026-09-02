"""Twin-flight of nearby same-parity Juggler starts.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a reopen of high_merge / minimal-anchor closure, not a leftover
word census, not a 10^9 stopping-time census, and not Paper A.
Coalescence is not evidence of termination.

Phase 0 treats a same-parity pair (n, n+2) as one object: synchronized
relative gap, merge time, common tail / phase shift, and high-water
isolation. First-step closeness is the setup, not a shadow. The sink
{1, 2} is excluded from common-tail detection.
"""

from __future__ import annotations

import json
import subprocess
from collections import Counter
from functools import lru_cache
from pathlib import Path
from typing import Any

from research.juggler_sequence.lean_paths import (
    JUGGLER_DIR,
    JUGGLER_PAPER_BARREL,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_twin_flight.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_twin_flight.md"
DOSSIER_PATH = REPO_ROOT / "docs" / "problems" / "juggler_twin_flight.md"
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "twin_flight"

CLASS_CLOSED = "TWIN_FLIGHT_CLOSED"
CLASS_GREEN = "TWIN_FLIGHT_GREEN"
CLASS_PARK = "TWIN_FLIGHT_PARK"
CLASS_INCOMPLETE = "TWIN_FLIGHT_INCOMPLETE"

HARD_LABS = (37, 69, 89, 365, 501, 1517, 6187, 329, 33391)
RECORD_EXTRAS = (193, 425, 557, 761, 1181, 1721, 1773, 2183, 3889)
ALL_LABS = HARD_LABS + RECORD_EXTRAS
WINDOW_HALF = 10
CONTROL_N_MAX = 2000
STEP_CAP = 400
BIT_CAP = 4096
SHADOW_EPS = 0.05
SHADOW_MIN_STEPS = 8
DELTA_KS = (1, 2, 4, 8)
COMMON_MIN = 3
ISOLATION_CUT = 0.1
RATE_LIFT = 2.0
RATE_GAP = 0.15
CONTACT_FLOOR = 0.10
WORD_PREFIX = 32
JSON_INT_BITS = 256
CALIBRATION_STATE = 763

CLASS_EXACT = "exact_merge"
CLASS_SHIFT = "shifted_flight"
CLASS_SHADOW = "long_shadow"
CLASS_SEPARATE = "separate"
CLASS_CAP_SHADOW = "capped_shadow"
CLASS_CAP_SEPARATE = "capped_separate"
CONTACT_CLASSES = frozenset({CLASS_EXACT, CLASS_SHIFT})
SHADOW_CLASSES = frozenset({CLASS_SHADOW, CLASS_CAP_SHADOW})
PAIR_CLASSES = (
    CLASS_EXACT,
    CLASS_SHIFT,
    CLASS_SHADOW,
    CLASS_SEPARATE,
    CLASS_CAP_SHADOW,
    CLASS_CAP_SEPARATE,
)

EXISTING_LEAN = (
    "floorPower",
    "AboveAnchor",
)

FORBIDDEN_THEOREMS = (
    "juggler_reaches_one",
    "no_juggler_escape",
    "all_finiteProgress",
)

FORBIDDEN_NEW_API = (
    "TwinFlight",
    "TwinOrbit",
    "CommonTail",
    "ShadowPair",
)

NEW_LEAN_FILES = (
    JUGGLER_DIR / "TwinFlight.lean",
    JUGGLER_DIR / "TwinOrbit.lean",
    JUGGLER_DIR / "CommonTail.lean",
    JUGGLER_DIR / "ShadowPair.lean",
)


def git_commit() -> str:
    try:
        return subprocess.check_output(
            ["git", "rev-parse", "HEAD"],
            cwd=REPO_ROOT,
            text=True,
            stderr=subprocess.DEVNULL,
        ).strip()
    except (OSError, subprocess.CalledProcessError):
        return "unknown"


def compact_int(value: int | None, *, bits: int = JSON_INT_BITS) -> int | dict[str, Any] | None:
    if value is None:
        return None
    if value.bit_length() <= bits:
        return value
    return {"bits": value.bit_length(), "hex_head": hex(value)[:18]}


def window_starts(n: int, *, half: int = WINDOW_HALF) -> tuple[int, ...]:
    if n % 2 == 0:
        raise ValueError("window_starts requires an odd start")
    out: list[int] = []
    for offset in range(-half, half + 1, 2):
        start = n + offset
        if start >= 3 and start % 2 == 1:
            out.append(start)
    return tuple(out)


def first_step_delta(n: int) -> dict[str, Any]:
    if n < 1 or n % 2 == 0:
        raise ValueError("first_step_delta requires an odd positive integer")
    left = floor_power(n)
    right = floor_power(n + 2)
    top = max(left, right)
    delta = abs(right - left) / top if top else 0.0
    return {
        "n": n,
        "T_n": left,
        "T_n_plus_2": right,
        "d_1": abs(right - left),
        "delta_1": delta,
        "approx_3_over_n": 3.0 / n,
    }


def _bit_would_exceed(current: int, bit_cap: int) -> bool:
    if current % 2 == 1:
        return current.bit_length() * 3 > bit_cap
    return current.bit_length() > bit_cap


@lru_cache(maxsize=None)
def _walk_cached(n: int, step_cap: int, bit_cap: int) -> tuple[tuple[int, ...], int, str, int | None, str]:
    if n < 1:
        raise ValueError("walk_trajectory requires a positive integer")
    states = [n]
    seen = {n}
    current = n
    peak = n
    letters: list[str] = []
    for step in range(1, step_cap + 1):
        if _bit_would_exceed(current, bit_cap):
            return tuple(states), peak, "BIT_CAP", None, "".join(letters)
        nxt = floor_power(current)
        letters.append("O" if current % 2 else "E")
        states.append(nxt)
        if nxt > peak:
            peak = nxt
        if nxt == 1:
            return tuple(states), peak, "HIT_ONE", step, "".join(letters)
        if nxt in seen:
            return tuple(states), peak, "CYCLE", None, "".join(letters)
        seen.add(nxt)
        current = nxt
    return tuple(states), peak, "STEP_CAP", None, "".join(letters)


def walk_trajectory(
    n: int,
    *,
    step_cap: int = STEP_CAP,
    bit_cap: int = BIT_CAP,
) -> dict[str, Any]:
    states, peak, status, tau, word = _walk_cached(n, step_cap, bit_cap)
    return {
        "n": n,
        "states": states,
        "H": peak,
        "H_bits": peak.bit_length(),
        "status": status,
        "tau": tau,
        "word": word,
        "steps": len(states) - 1,
        "step_cap": step_cap,
        "bit_cap": bit_cap,
    }


def _orbit_summary(row: dict[str, Any]) -> dict[str, Any]:
    return {
        "n": row["n"],
        "steps": row["steps"],
        "H": compact_int(row["H"]),
        "H_bits": row["H_bits"],
        "status": row["status"],
        "tau": row["tau"],
        "word": row["word"][:WORD_PREFIX],
    }


def _delta(a: int, b: int) -> float:
    top = max(a, b)
    if top <= 0:
        return 0.0
    return abs(a - b) / top


def _first_indices(states: tuple[int, ...], *, common_min: int) -> dict[int, int]:
    out: dict[int, int] = {}
    for idx, state in enumerate(states):
        if state >= common_min and state not in out:
            out[state] = idx
    return out


def _first_common(
    left: tuple[int, ...],
    right: tuple[int, ...],
    *,
    common_min: int,
) -> dict[str, Any] | None:
    index_left = _first_indices(left, common_min=common_min)
    best: tuple[int, int, int, int, int] | None = None
    for j, state in enumerate(right):
        if state < common_min:
            continue
        i = index_left.get(state)
        if i is None:
            continue
        cand = (i + j, abs(i - j), i, j, state)
        if best is None or cand < best:
            best = cand
    if best is None:
        return None
    _cost, _spread, i, j, state = best
    return {"state": state, "i": i, "j": j, "r": j - i}


def compare_pair(
    left: dict[str, Any],
    right: dict[str, Any],
    *,
    common_min: int = COMMON_MIN,
    shadow_eps: float = SHADOW_EPS,
    shadow_min_steps: int = SHADOW_MIN_STEPS,
) -> dict[str, Any]:
    a = left["states"]
    b = right["states"]
    synced = min(len(a), len(b)) - 1
    deltas: dict[int, float] = {}
    max_delta = 0.0
    max_sep = 0
    tau_merge: int | None = None
    even_reset = False
    for k in range(1, synced + 1):
        d_k = abs(a[k] - b[k])
        delta_k = _delta(a[k], b[k])
        if d_k > max_sep:
            max_sep = d_k
        if delta_k > max_delta:
            max_delta = delta_k
        if k in DELTA_KS:
            deltas[k] = delta_k
        if tau_merge is None and a[k] == b[k] and a[k] >= common_min:
            tau_merge = k
            even_reset = a[k - 1] % 2 == 0 and b[k - 1] % 2 == 0
    common = _first_common(a, b, common_min=common_min)
    capped = left["status"] in {"STEP_CAP", "BIT_CAP"} or right["status"] in {
        "STEP_CAP",
        "BIT_CAP",
    }
    if tau_merge is not None:
        klass = CLASS_EXACT
    elif common is not None and common["r"] != 0:
        klass = CLASS_SHIFT
    elif capped and max_delta <= shadow_eps:
        klass = CLASS_CAP_SHADOW
    elif capped:
        klass = CLASS_CAP_SEPARATE
    elif synced >= shadow_min_steps and max_delta <= shadow_eps:
        klass = CLASS_SHADOW
    else:
        klass = CLASS_SEPARATE
    return {
        "a": left["n"],
        "b": right["n"],
        "class": klass,
        "tau_merge": tau_merge,
        "even_reset": even_reset,
        "max_delta": max_delta,
        "max_sep": compact_int(max_sep),
        "synced": synced,
        "delta_at": {str(k): deltas[k] for k in DELTA_KS if k in deltas},
        "common": None
        if common is None
        else {
            "state": compact_int(common["state"]),
            "i": common["i"],
            "j": common["j"],
            "r": common["r"],
        },
        "capped": capped,
        "status_a": left["status"],
        "status_b": right["status"],
    }


def _class_counts(rows: list[dict[str, Any]]) -> dict[str, int]:
    tallies = Counter(row["class"] for row in rows)
    return {name: int(tallies.get(name, 0)) for name in PAIR_CLASSES}


def _rate(counts: dict[str, int], names: frozenset[str], total: int) -> float:
    if total <= 0:
        return 0.0
    return sum(counts[name] for name in names) / total


def _elevated(hard: float, ctrl: float) -> bool:
    if hard < CONTACT_FLOOR:
        return False
    return hard >= RATE_LIFT * max(ctrl, 0.02) or hard - ctrl >= RATE_GAP


def isolation_row(
    n: int,
    orbits: dict[int, dict[str, Any]],
    *,
    isolation_cut: float = ISOLATION_CUT,
) -> dict[str, Any]:
    centre = orbits[n]
    peak = centre["H"]
    left_n = n - 2
    right_n = n + 2
    left = orbits.get(left_n)
    right = orbits.get(right_n)
    r_minus = (left["H"] / peak) if left is not None and peak else None
    r_plus = (right["H"] / peak) if right is not None and peak else None
    cmp_left = compare_pair(left, centre) if left is not None else None
    cmp_right = compare_pair(centre, right) if right is not None else None
    shares = any(
        row is not None and row["class"] in CONTACT_CLASSES
        for row in (cmp_left, cmp_right)
    )
    isolated = (
        r_minus is not None
        and r_plus is not None
        and r_minus < isolation_cut
        and r_plus < isolation_cut
        and not shares
    )
    return {
        "n": n,
        "H_bits": centre["H_bits"],
        "R_minus": r_minus,
        "R_plus": r_plus,
        "neighbor_left": None if cmp_left is None else cmp_left["class"],
        "neighbor_right": None if cmp_right is None else cmp_right["class"],
        "shares_neighbor": shares,
        "isolated": isolated,
        "status": centre["status"],
        "tau": centre["tau"],
        "word": centre["word"][:WORD_PREFIX],
    }


def window_matrix(
    n: int,
    *,
    step_cap: int = STEP_CAP,
    bit_cap: int = BIT_CAP,
    starts: tuple[int, ...] | None = None,
) -> dict[str, Any]:
    members = starts if starts is not None else window_starts(n)
    orbits = {
        start: walk_trajectory(start, step_cap=step_cap, bit_cap=bit_cap) for start in members
    }
    pairs: list[dict[str, Any]] = []
    adjacent: list[dict[str, Any]] = []
    ordered = list(members)
    for i, a in enumerate(ordered):
        for b in ordered[i + 1 :]:
            row = compare_pair(orbits[a], orbits[b])
            pairs.append(row)
            if b - a == 2:
                adjacent.append(row)
    return {
        "n": n,
        "starts": list(members),
        "orbits": {str(start): _orbit_summary(orbits[start]) for start in members},
        "pairs": pairs,
        "adjacent": adjacent,
        "adjacent_counts": _class_counts(adjacent),
        "pair_counts": _class_counts(pairs),
        "isolation": isolation_row(n, orbits) if n in orbits else None,
    }


def control_pairs(
    *,
    n_max: int = CONTROL_N_MAX,
    step_cap: int = STEP_CAP,
    bit_cap: int = BIT_CAP,
) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    for n in range(3, n_max + 1, 2):
        left = walk_trajectory(n, step_cap=step_cap, bit_cap=bit_cap)
        right = walk_trajectory(n + 2, step_cap=step_cap, bit_cap=bit_cap)
        rows.append(compare_pair(left, right))
    counts = _class_counts(rows)
    total = len(rows)
    return {
        "n_max": n_max,
        "pairs": total,
        "counts": counts,
        "contact_rate": _rate(counts, CONTACT_CLASSES, total),
        "shadow_rate": _rate(counts, SHADOW_CLASSES, total),
        "separate_rate": counts[CLASS_SEPARATE] / total if total else 0.0,
        "capped": counts[CLASS_CAP_SHADOW] + counts[CLASS_CAP_SEPARATE],
        "even_reset": sum(1 for row in rows if row["even_reset"]),
        "examples": {
            name: next((row for row in rows if row["class"] == name), None)
            for name in PAIR_CLASSES
        },
    }


def cross_lab(
    labs: tuple[int, ...] = HARD_LABS,
    *,
    step_cap: int = STEP_CAP,
    bit_cap: int = BIT_CAP,
) -> dict[str, Any]:
    orbits = {n: walk_trajectory(n, step_cap=step_cap, bit_cap=bit_cap) for n in labs}
    rows: list[dict[str, Any]] = []
    for i, a in enumerate(labs):
        for b in labs[i + 1 :]:
            rows.append(compare_pair(orbits[a], orbits[b]))
    hits = [row for row in rows if row["class"] in CONTACT_CLASSES]
    calibration = next(
        (
            row
            for row in rows
            if {row["a"], row["b"]} == {365, 501}
        ),
        None,
    )
    recovered = False
    if calibration is not None and calibration["common"] is not None:
        state = calibration["common"]["state"]
        recovered = state == CALIBRATION_STATE or (
            isinstance(state, dict) and False
        )
        if isinstance(state, int):
            recovered = state == CALIBRATION_STATE
    return {
        "labs": list(labs),
        "pairs": len(rows),
        "hits": hits,
        "hit_count": len(hits),
        "calibration": calibration,
        "calibration_365_501_at_763": recovered,
    }


def _adjacent_from_windows(windows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for window in windows:
        rows.extend(window["adjacent"])
    return rows


def run_probe(
    *,
    labs: tuple[int, ...] = ALL_LABS,
    hard_labs: tuple[int, ...] = HARD_LABS,
    n_max: int = CONTROL_N_MAX,
    step_cap: int = STEP_CAP,
    bit_cap: int = BIT_CAP,
) -> dict[str, Any]:
    windows = [
        window_matrix(n, step_cap=step_cap, bit_cap=bit_cap) for n in labs
    ]
    hard_windows = [window for window in windows if window["n"] in hard_labs]
    adjacent = _adjacent_from_windows(hard_windows)
    adjacent_counts = _class_counts(adjacent)
    adjacent_total = len(adjacent)
    control = control_pairs(n_max=n_max, step_cap=step_cap, bit_cap=bit_cap)
    cross = cross_lab(hard_labs, step_cap=step_cap, bit_cap=bit_cap)
    isolations = [window["isolation"] for window in hard_windows if window["isolation"]]
    isolated = [row["n"] for row in isolations if row["isolated"]]
    step37 = first_step_delta(37)
    hard_contact = _rate(adjacent_counts, CONTACT_CLASSES, adjacent_total)
    hard_shadow = _rate(adjacent_counts, SHADOW_CLASSES, adjacent_total)
    return {
        "labs": list(labs),
        "hard_labs": list(hard_labs),
        "window_half": WINDOW_HALF,
        "n_max": n_max,
        "step_cap": step_cap,
        "bit_cap": bit_cap,
        "shadow_eps": SHADOW_EPS,
        "common_min": COMMON_MIN,
        "isolation_cut": ISOLATION_CUT,
        "windows": windows,
        "hard_adjacent": {
            "pairs": adjacent_total,
            "counts": adjacent_counts,
            "contact_rate": hard_contact,
            "shadow_rate": hard_shadow,
            "separate_rate": (
                adjacent_counts[CLASS_SEPARATE] / adjacent_total if adjacent_total else 0.0
            ),
            "even_reset": sum(1 for row in adjacent if row["even_reset"]),
        },
        "control": control,
        "cross_lab": {
            "pairs": cross["pairs"],
            "hit_count": cross["hit_count"],
            "hits": cross["hits"],
            "calibration": cross["calibration"],
            "calibration_365_501_at_763": cross["calibration_365_501_at_763"],
        },
        "isolations": isolations,
        "isolated_labs": isolated,
        "isolated_count": len(isolated),
        "first_step_37": step37,
        "first_step_ok": 0.02 <= step37["delta_1"] <= 0.2,
        "contact_elevated": _elevated(hard_contact, control["contact_rate"]),
        "shadow_elevated": _elevated(hard_shadow, control["shadow_rate"]),
        "rates_close": (
            abs(hard_contact - control["contact_rate"]) < 0.10
            and abs(hard_shadow - control["shadow_rate"]) < 0.10
        ),
        "git_commit": git_commit(),
    }


def lean_api_present() -> dict[str, Any]:
    text = juggler_text()
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    engine = engine_floor_text()
    out: dict[str, Any] = {
        "sorry_free": "sorry" not in text and "sorry" not in paper,
        "new_lean_file": any(path.is_file() for path in NEW_LEAN_FILES),
        "not_in_paper_barrel": all(name not in paper for name in FORBIDDEN_NEW_API),
        "engine_floor_clean": all(name not in engine for name in FORBIDDEN_NEW_API),
    }
    for name in EXISTING_LEAN:
        out[name] = has_named(text, name)
    for name in FORBIDDEN_THEOREMS:
        out[f"has_{name}"] = has_named(text, name) or has_named(paper, name)
    for name in FORBIDDEN_NEW_API:
        out[f"has_api_{name}"] = has_named(text, name) or has_named(paper, name)
    return out


def classify(scan: dict[str, Any], lean: dict[str, Any]) -> dict[str, Any]:
    if (
        not lean["sorry_free"]
        or lean["new_lean_file"]
        or any(lean[f"has_{name}"] for name in FORBIDDEN_THEOREMS)
        or any(lean[f"has_api_{name}"] for name in FORBIDDEN_NEW_API)
        or not scan["cross_lab"]["calibration_365_501_at_763"]
        or not scan["first_step_ok"]
    ):
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": (
                "calibration, first-step scale, or Lean boundary failed; "
                "NOT_OBSERVED_WITHIN_BOUND is not a substitute"
            ),
        }
    hard = scan["hard_adjacent"]
    ctrl = scan["control"]
    isolated = scan["isolated_count"]
    labs = len(scan["hard_labs"])
    if scan["contact_elevated"] or scan["shadow_elevated"]:
        return {
            "classification": CLASS_GREEN,
            "reason": (
                "hard-window adjacent pairs merge, phase-shift, or shadow "
                f"above the n<={ctrl['n_max']} control "
                f"(contact {hard['contact_rate']:.3f} vs {ctrl['contact_rate']:.3f}; "
                f"shadow {hard['shadow_rate']:.3f} vs {ctrl['shadow_rate']:.3f})"
            ),
        }
    if isolated == labs and hard["contact_rate"] <= ctrl["contact_rate"] + 0.05:
        return {
            "classification": CLASS_CLOSED,
            "reason": (
                "named hard starts are height-isolated from both odd "
                "neighbors and do not share a state >2 with them; the "
                "family hypothesis is REFUTED at this window"
            ),
        }
    if scan["rates_close"]:
        kind = (
            "generic coalescence"
            if ctrl["contact_rate"] >= CONTACT_FLOOR
            else "generic decorrelation"
        )
        return {
            "classification": CLASS_CLOSED,
            "reason": (
                f"hard-window adjacent pairs match the control ({kind}: "
                f"contact {hard['contact_rate']:.3f} vs {ctrl['contact_rate']:.3f}; "
                f"shadow {hard['shadow_rate']:.3f} vs {ctrl['shadow_rate']:.3f})"
            ),
        }
    return {
        "classification": CLASS_PARK,
        "reason": (
            "hard-window rates differ from the control but not enough to "
            "promote a pair law, and isolation is incomplete"
        ),
    }


def probe_payload(
    *,
    labs: tuple[int, ...] = ALL_LABS,
    hard_labs: tuple[int, ...] = HARD_LABS,
    n_max: int = CONTROL_N_MAX,
    step_cap: int = STEP_CAP,
    bit_cap: int = BIT_CAP,
) -> dict[str, Any]:
    scan = run_probe(
        labs=labs,
        hard_labs=hard_labs,
        n_max=n_max,
        step_cap=step_cap,
        bit_cap=bit_cap,
    )
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "coalescence_is_not_termination": False,
            "pair_census_is_theorem": False,
            "high_merge_reopen": False,
            "ten_to_nine_census": False,
            "twin_flight_lean": False,
            "global_termination": False,
        }
    )
    return {
        "experiment": "juggler_twin_flight",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "same-parity windows n±10 on HARD_LABS and record extras; "
            f"odd (n,n+2) control n<={n_max}; cross-lab tails; "
            f"common state >{COMMON_MIN - 1}; sink {{1,2}} excluded; "
            f"step_cap={step_cap} bit_cap={bit_cap}"
        ),
    }


def _fmt_pair(row: dict[str, Any]) -> str:
    common = row["common"]
    common_s = "none" if common is None else (
        f"state=`{common['state']}` i=`{common['i']}` j=`{common['j']}` "
        f"r=`{common['r']}`"
    )
    return (
        f"`{row['a']}`/`{row['b']}`: class=`{row['class']}` "
        f"tau_merge=`{row['tau_merge']}` even_reset=`{row['even_reset']}` "
        f"max_delta=`{row['max_delta']:.4f}` common={common_s}"
    )


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    hard = scan["hard_adjacent"]
    ctrl = scan["control"]
    lines = [
        "# Juggler twin-flight of nearby same-parity starts",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Same-parity pair object $(n,n+2)$: synchronized relative gap,",
        "merge time, common tail / phase shift, and high-water isolation.",
        "First-step closeness is the setup, not a shadow. The sink",
        "`{1, 2}` is excluded from common-tail detection.",
        "Not a halt theorem. A pair census is not a theorem.",
        "Absence is NOT_OBSERVED_WITHIN_BOUND.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     nearby same-parity merge / shadow / isolate",
        "Novelty hypothesis      hard flights are local families",
        "Maximum Phase-0 scope   HARD_LABS ±10; n<=2000 control; no Lean",
        "```",
        "",
        "## Metadata",
        "",
        f"- classification: **{decision['classification']}**",
        f"- labs: `{scan['labs']}`",
        f"- control n_max: `{ctrl['n_max']}` pairs: `{ctrl['pairs']}`",
        f"- hard adjacent pairs: `{hard['pairs']}`",
        f"- hard contact/shadow/separate: `{hard['contact_rate']:.4f}` / "
        f"`{hard['shadow_rate']:.4f}` / `{hard['separate_rate']:.4f}`",
        f"- control contact/shadow/separate: `{ctrl['contact_rate']:.4f}` / "
        f"`{ctrl['shadow_rate']:.4f}` / `{ctrl['separate_rate']:.4f}`",
        f"- contact elevated: `{scan['contact_elevated']}` "
        f"shadow elevated: `{scan['shadow_elevated']}`",
        f"- isolated labs: `{scan['isolated_labs']}` "
        f"count: `{scan['isolated_count']}`",
        f"- 365/501 at 763: `{scan['cross_lab']['calibration_365_501_at_763']}`",
        f"- first-step 37 delta_1: `{scan['first_step_37']['delta_1']:.4f}` "
        f"approx 3/n: `{scan['first_step_37']['approx_3_over_n']:.4f}`",
        "",
        decision["reason"] + ".",
        "",
        "## Hard-window adjacent pairs",
        "",
        f"- counts: `{hard['counts']}`",
        f"- even-reset merges: `{hard['even_reset']}`",
        "",
    ]
    for window in scan["windows"]:
        if window["n"] not in scan["hard_labs"]:
            continue
        iso = window["isolation"]
        lines.append(
            f"- lab `{window['n']}`: adjacent `{window['adjacent_counts']}` "
            f"R-=`{iso['R_minus']}` R+=`{iso['R_plus']}` "
            f"isolated=`{iso['isolated']}` "
            f"neighbors=`{iso['neighbor_left']}`/`{iso['neighbor_right']}`"
        )
        for row in window["adjacent"]:
            if window["n"] in (row["a"], row["b"]):
                lines.append(f"  - {_fmt_pair(row)}")
    lines.extend(
        [
            "",
            "## Record-extra adjacent counts",
            "",
        ]
    )
    for window in scan["windows"]:
        if window["n"] in scan["hard_labs"]:
            continue
        iso = window["isolation"]
        lines.append(
            f"- `{window['n']}`: adjacent `{window['adjacent_counts']}` "
            f"isolated=`{iso['isolated']}` "
            f"R-=`{iso['R_minus']}` R+=`{iso['R_plus']}`"
        )
    lines.extend(
        [
            "",
            "## Control",
            "",
            f"- counts: `{ctrl['counts']}`",
            f"- even-reset merges: `{ctrl['even_reset']}`",
            f"- capped pairs: `{ctrl['capped']}`",
            "",
            "## Cross-lab tails among HARD_LABS",
            "",
            f"- hits: `{scan['cross_lab']['hit_count']}` of "
            f"`{scan['cross_lab']['pairs']}`",
            "",
        ]
    )
    for row in scan["cross_lab"]["hits"]:
        lines.append(f"- {_fmt_pair(row)}")
    if not scan["cross_lab"]["hits"]:
        lines.append("- none besides the excluded sink")
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


def _jsonable(payload: dict[str, Any]) -> dict[str, Any]:
    return json.loads(json.dumps(payload))


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(_jsonable(data), indent=2) + "\n", encoding="utf-8")
    DOC_PATH.write_text(render_markdown(data), encoding="utf-8")
    summary = {
        "classification": data["decision"]["classification"],
        "reason": data["decision"]["reason"],
        "hard_adjacent": data["scan"]["hard_adjacent"],
        "control": {
            "n_max": data["scan"]["control"]["n_max"],
            "pairs": data["scan"]["control"]["pairs"],
            "counts": data["scan"]["control"]["counts"],
            "contact_rate": data["scan"]["control"]["contact_rate"],
            "shadow_rate": data["scan"]["control"]["shadow_rate"],
            "separate_rate": data["scan"]["control"]["separate_rate"],
        },
        "isolated_labs": data["scan"]["isolated_labs"],
        "contact_elevated": data["scan"]["contact_elevated"],
        "shadow_elevated": data["scan"]["shadow_elevated"],
        "calibration_365_501_at_763": data["scan"]["cross_lab"][
            "calibration_365_501_at_763"
        ],
    }
    (DATA_DIR / "summary.json").write_text(
        json.dumps(summary, indent=2) + "\n", encoding="utf-8"
    )
    return data


def main() -> None:
    payload = write_artifacts()
    print(payload["decision"]["classification"])
    print(payload["decision"]["reason"])
    hard = payload["scan"]["hard_adjacent"]
    ctrl = payload["scan"]["control"]
    print("hard", hard["counts"], "contact", hard["contact_rate"])
    print("ctrl", ctrl["counts"], "contact", ctrl["contact_rate"])
    print("isolated", payload["scan"]["isolated_labs"])


if __name__ == "__main__":
    main()

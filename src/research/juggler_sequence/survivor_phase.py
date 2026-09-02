"""Rounding-phase distribution of long AboveAnchor survivors.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a reopen of excursion transfer, mixed-OE defect cuts,
cumulative floor loss, word language, or prefix cylinders.
Not a new atlas language tag and not FloorPhase.lean.

Phase 0 streams u_O / u_E on AboveAnchor prefixes, bins by
survival depth S(n), and compares long survivors to ordinary
survivors and scale-matched generic integers.
Absence is NOT_OBSERVED_WITHIN_BOUND. A histogram is not a theorem.
"""

from __future__ import annotations

import json
import math
import random
import subprocess
from math import isqrt
from pathlib import Path
from typing import Any

from research.juggler_sequence.atlas.schema import CLAIM_NOT_OBSERVED
from research.juggler_sequence.lean_paths import (
    JUGGLER_DIR,
    JUGGLER_PAPER_BARREL,
    engine_floor_text,
    has_named,
    juggler_text,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_survivor_phase.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_survivor_phase.md"
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "survivor_phase"

CLASS_CLOSED = "SURVIVOR_PHASE_CLOSED"
CLASS_PARK = "SURVIVOR_PHASE_PARK"
CLASS_GREEN = "SURVIVOR_PHASE_GREEN"
CLASS_INCOMPLETE = "SURVIVOR_PHASE_INCOMPLETE"

SCIENCE_N_MAX = 20_000_000
SCIENCE_STEP_CAP = 80
SCIENCE_BIT_CAP = 1024
TEST_N_MAX = 400
TEST_STEP_CAP = 80
TEST_BIT_CAP = 256
HARD_LABS = (37, 69, 89, 365, 501, 1517, 6187, 329, 33391)
LAB_STEP_CAP = 400
LAB_BIT_CAP = 4096
U_BINS = 20
JOINT_BINS = 8
EDGE = 0.05
SMALL_D = 2
GENERIC_D_CUT = 0.08
HOLD_D_CUT = 0.08
S_ORDINARY = 3
S_LONG = 9
CTRL_PER_BIN = 8000
CTRL_SCALE_MAX = 12

EXISTING_LEAN = (
    "localDefectOdd",
    "localDefectEven",
    "localDefectOdd_lt_succ",
    "AboveAnchor",
    "EnvelopeState",
)

FORBIDDEN_THEOREMS = (
    "juggler_reaches_one",
    "no_juggler_escape",
    "all_finiteProgress",
)

FORBIDDEN_NEW_API = (
    "FloorPhase",
    "RoundingPhase",
    "SurvivalPhase",
    "PhaseDrift",
)

NEW_LEAN_FILES = (
    JUGGLER_DIR / "FloorPhase.lean",
    JUGGLER_DIR / "RoundingPhase.lean",
    JUGGLER_DIR / "SurvivalPhase.lean",
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


def floor_phase(x: int) -> tuple[int, int, float, bool]:
    """Return (y, defect, u, is_odd). u is descriptive in [0, 1)."""

    if x < 1:
        raise ValueError("floor_phase requires a positive integer")
    odd = x % 2 == 1
    if odd:
        cube = x * x * x
        y = isqrt(cube)
        defect = cube - y * y
    else:
        y = isqrt(x)
        defect = x - y * y
    width = 2 * y + 1
    u = defect / width if width else 0.0
    return y, defect, u, odd


def u_bin(u: float, bins: int) -> int:
    idx = int(u * bins)
    if idx < 0:
        return 0
    if idx >= bins:
        return bins - 1
    return idx


def s_bin(depth: int) -> int:
    if depth <= S_ORDINARY:
        return 0
    if depth < S_LONG:
        return 1
    return 2


def _empty_hist() -> dict[str, Any]:
    return {
        "odd": [0] * U_BINS,
        "even": [0] * U_BINS,
        "odd_n": 0,
        "even_n": 0,
        "edge_lo": 0,
        "edge_hi": 0,
        "edge_n": 0,
        "joint": [0] * (JOINT_BINS * JOINT_BINS),
        "joint_n": 0,
        "oe_joint": [0] * (JOINT_BINS * JOINT_BINS),
        "oe_n": 0,
        "small_d": 0,
        "small_n": 0,
    }


def _add_u(hist: dict[str, Any], u: float, odd: bool, defect: int, y: int) -> None:
    idx = u_bin(u, U_BINS)
    if odd:
        hist["odd"][idx] += 1
        hist["odd_n"] += 1
        if y >= 10:
            hist["small_n"] += 1
            if defect <= SMALL_D:
                hist["small_d"] += 1
    else:
        hist["even"][idx] += 1
        hist["even_n"] += 1
    hist["edge_n"] += 1
    if u < EDGE:
        hist["edge_lo"] += 1
    if u >= 1.0 - EDGE:
        hist["edge_hi"] += 1


def _add_joint(hist: dict[str, Any], key: str, nkey: str, u0: float, u1: float) -> None:
    i = u_bin(u0, JOINT_BINS)
    j = u_bin(u1, JOINT_BINS)
    hist[key][i * JOINT_BINS + j] += 1
    hist[nkey] += 1


def _probs(counts: list[int], total: int) -> list[float]:
    if total <= 0:
        return [0.0] * len(counts)
    return [c / total for c in counts]


def _cdf(probs: list[float]) -> list[float]:
    out = []
    run = 0.0
    for p in probs:
        run += p
        out.append(run)
    return out


def _d_cdf(left: list[float], right: list[float]) -> float:
    return max(abs(a - b) for a, b in zip(left, right, strict=True)) if left else 0.0


def _d_hist(a: dict[str, Any], b: dict[str, Any], which: str) -> float:
    nkey = "odd_n" if which == "odd" else "even_n"
    pa = _cdf(_probs(a[which], a[nkey]))
    pb = _cdf(_probs(b[which], b[nkey]))
    if a[nkey] < 20 or b[nkey] < 20:
        return 0.0
    return _d_cdf(pa, pb)


def _indep_d(hist: dict[str, Any]) -> float:
    total = hist["joint_n"]
    if total < 40:
        return 0.0
    joint = hist["joint"]
    row = [0] * JOINT_BINS
    col = [0] * JOINT_BINS
    for i in range(JOINT_BINS):
        for j in range(JOINT_BINS):
            c = joint[i * JOINT_BINS + j]
            row[i] += c
            col[j] += c
    worst = 0.0
    for i in range(JOINT_BINS):
        for j in range(JOINT_BINS):
            pred = (row[i] / total) * (col[j] / total)
            obs = joint[i * JOINT_BINS + j] / total
            worst = max(worst, abs(obs - pred))
    return worst


def _edge_rate(hist: dict[str, Any]) -> float:
    n = hist["edge_n"]
    if n < 20:
        return 0.0
    return (hist["edge_lo"] + hist["edge_hi"]) / n


def _small_rate(hist: dict[str, Any]) -> float:
    n = hist["small_n"]
    if n < 20:
        return 0.0
    return hist["small_d"] / n


def walk_phases(
    n: int,
    *,
    step_cap: int = TEST_STEP_CAP,
    bit_cap: int = TEST_BIT_CAP,
) -> dict[str, Any]:
    if n < 2:
        raise ValueError("walk_phases requires n >= 2")
    x = n
    steps = 0
    status = "RETURNED"
    trace: list[tuple[float, bool, int, int, int]] = []
    while steps < step_cap:
        if x < n:
            break
        if x.bit_length() > bit_cap:
            status = "BIT_CAP"
            break
        y, defect, u, odd = floor_phase(x)
        scale = int(math.log10(x)) if x >= 10 else 0
        trace.append((u, odd, defect, y, scale))
        x = y
        steps += 1
    else:
        if x >= n:
            status = "HORIZON"
    return {"n": n, "status": status, "S": len(trace), "trace": trace}


def _flush_trace(
    hist: dict[str, Any], trace: list[tuple[float, bool, int, int, int]]
) -> None:
    prev_u: float | None = None
    prev_odd: bool | None = None
    prev_kept = False
    for u, odd, defect, y, scale in trace:
        keep = scale <= CTRL_SCALE_MAX
        if keep:
            _add_u(hist, u, odd, defect, y)
            if prev_kept and prev_u is not None:
                _add_joint(hist, "joint", "joint_n", prev_u, u)
                if prev_odd and not odd:
                    _add_joint(hist, "oe_joint", "oe_n", prev_u, u)
        prev_u = u
        prev_odd = odd
        prev_kept = keep


def _generic_controls(scale_need: dict[int, int], rng: random.Random) -> dict[str, Any]:
    hist = _empty_hist()
    for k, need in scale_need.items():
        if k < 1 or k > CTRL_SCALE_MAX:
            continue
        lo = 10**k
        hi = 10 ** (k + 1)
        take = min(CTRL_PER_BIN, max(need, 200))
        for _ in range(take):
            x = rng.randrange(lo | 1, hi, 2)
            y, defect, u, _odd = floor_phase(x)
            _add_u(hist, u, True, defect, y)
        for _ in range(take // 2):
            x = rng.randrange(lo + (lo % 2), hi, 2)
            if x < 2:
                continue
            y, defect, u, _odd = floor_phase(x)
            _add_u(hist, u, False, defect, y)
    return hist


def run_probe(
    *,
    n_max: int = TEST_N_MAX,
    hold_split: int | None = None,
    step_cap: int = TEST_STEP_CAP,
    bit_cap: int = TEST_BIT_CAP,
    seed: int = 0,
) -> dict[str, Any]:
    if hold_split is None:
        hold_split = n_max // 2
    rng = random.Random(seed)
    groups = {
        "ordinary": _empty_hist(),
        "mid": _empty_hist(),
        "long": _empty_hist(),
        "train_long": _empty_hist(),
        "hold_long": _empty_hist(),
    }
    starts = 0
    bit_cap_n = 0
    horizon_n = 0
    s_counts = [0, 0, 0]
    scale_need: dict[int, int] = {}
    s_max = 0

    def consume(n: int, walked: dict[str, Any], *, scored: bool) -> None:
        nonlocal starts, bit_cap_n, horizon_n, s_max
        starts += 1
        if walked["status"] == "BIT_CAP":
            bit_cap_n += 1
            return
        if walked["status"] == "HORIZON":
            horizon_n += 1
        depth = walked["S"]
        s_max = max(s_max, depth)
        kind = s_bin(depth)
        s_counts[kind] += 1
        name = ("ordinary", "mid", "long")[kind]
        _flush_trace(groups[name], walked["trace"])
        if scored and kind == 2:
            dest = "train_long" if n <= hold_split else "hold_long"
            _flush_trace(groups[dest], walked["trace"])
        for u, odd, _d, y, scale in walked["trace"]:
            if odd and 1 <= scale <= CTRL_SCALE_MAX:
                scale_need[scale] = scale_need.get(scale, 0) + 1

    for n in range(3, n_max + 1, 2):
        consume(
            n,
            walk_phases(n, step_cap=step_cap, bit_cap=bit_cap),
            scored=True,
        )
    lab_detail = []
    for n in HARD_LABS:
        walked = walk_phases(n, step_cap=LAB_STEP_CAP, bit_cap=LAB_BIT_CAP)
        if n > n_max:
            consume(n, walked, scored=False)
        phases = []
        min_u = 1.0
        max_u = 0.0
        min_d = None
        for u, odd, defect, y, _scale in walked["trace"][:40]:
            phases.append(
                {
                    "u": round(u, 6),
                    "odd": odd,
                    "d": defect if defect < 10**12 else None,
                    "y_bits": y.bit_length(),
                }
            )
            min_u = min(min_u, u)
            max_u = max(max_u, u)
            if odd and (min_d is None or defect < min_d):
                min_d = defect
        lab_detail.append(
            {
                "n": n,
                "status": walked["status"],
                "S": walked["S"],
                "min_u": min_u if walked["trace"] else None,
                "max_u": max_u if walked["trace"] else None,
                "min_d_odd": min_d,
                "phases": phases[:24],
            }
        )

    control = _generic_controls(scale_need, rng)
    ordinary = groups["ordinary"]
    long_h = groups["long"]
    mid_h = groups["mid"]
    d_long_ctrl_odd = _d_hist(long_h, control, "odd")
    d_long_ctrl_even = _d_hist(long_h, control, "even")
    d_long_ord_odd = _d_hist(long_h, ordinary, "odd")
    d_long_ord_even = _d_hist(long_h, ordinary, "even")
    d_mid_ord_odd = _d_hist(mid_h, ordinary, "odd")
    d_train_hold = _d_hist(groups["train_long"], groups["hold_long"], "odd")
    d_train_ctrl = _d_hist(groups["train_long"], control, "odd")
    d_hold_ctrl = _d_hist(groups["hold_long"], control, "odd")
    indep_long = _indep_d(long_h)
    indep_ord = _indep_d(ordinary)
    edge_long = _edge_rate(long_h)
    edge_ord = _edge_rate(ordinary)
    edge_ctrl = _edge_rate(control)
    small_long = _small_rate(long_h)
    small_ord = _small_rate(ordinary)
    small_ctrl = _small_rate(control)
    max_d = max(
        d_long_ctrl_odd,
        d_long_ctrl_even,
        d_long_ord_odd,
        d_long_ord_even,
    )
    hold_stable_generic = (
        d_train_ctrl < HOLD_D_CUT and d_hold_ctrl < HOLD_D_CUT
    )
    hold_stable_exception = (
        d_train_ctrl >= GENERIC_D_CUT
        and d_hold_ctrl >= GENERIC_D_CUT
        and d_train_hold < HOLD_D_CUT
    )
    u37 = floor_phase(37)[2]
    u225 = floor_phase(225)[2]
    fills_unit = True
    if long_h["odd_n"] >= 100:
        occupied = sum(1 for c in long_h["odd"] if c > 0)
        fills_unit = occupied >= U_BINS - 2

    return {
        "n_max": n_max,
        "hold_split": hold_split,
        "step_cap": step_cap,
        "bit_cap": bit_cap,
        "starts": starts,
        "bit_cap_n": bit_cap_n,
        "horizon_n": horizon_n,
        "s_max": s_max,
        "s_counts": {
            "ordinary": s_counts[0],
            "mid": s_counts[1],
            "long": s_counts[2],
        },
        "counts": {
            name: {"odd": groups[name]["odd_n"], "even": groups[name]["even_n"]}
            for name in ("ordinary", "mid", "long")
        },
        "control_n": {"odd": control["odd_n"], "even": control["even_n"]},
        "D": {
            "long_vs_ctrl_odd": d_long_ctrl_odd,
            "long_vs_ctrl_even": d_long_ctrl_even,
            "long_vs_ordinary_odd": d_long_ord_odd,
            "long_vs_ordinary_even": d_long_ord_even,
            "mid_vs_ordinary_odd": d_mid_ord_odd,
            "train_vs_hold_long": d_train_hold,
            "train_vs_ctrl": d_train_ctrl,
            "hold_vs_ctrl": d_hold_ctrl,
            "max": max_d,
        },
        "indep_d": {"long": indep_long, "ordinary": indep_ord},
        "edge": {"long": edge_long, "ordinary": edge_ord, "control": edge_ctrl},
        "small_d_rate": {
            "long": small_long,
            "ordinary": small_ord,
            "control": small_ctrl,
        },
        "long_odd_hist": _probs(long_h["odd"], long_h["odd_n"]),
        "ordinary_odd_hist": _probs(ordinary["odd"], ordinary["odd_n"]),
        "control_odd_hist": _probs(control["odd"], control["odd_n"]),
        "fills_unit_interval": fills_unit,
        "hold_stable_generic": hold_stable_generic,
        "hold_stable_exception": hold_stable_exception,
        "u_37": u37,
        "u_225": u225,
        "labs": lab_detail,
        "git": git_commit(),
        "letter_chain": False,
        "itinerary_language_reopen": False,
        "excursion_reopen": False,
        "defect_cut_reopen": False,
        "halt_theorem": False,
        "floor_phase_lean": False,
        "claim": CLAIM_NOT_OBSERVED,
    }


def lean_api_present() -> dict[str, bool]:
    combined = juggler_text()
    named = {name: has_named(combined, name) for name in EXISTING_LEAN}
    forbidden = {name: has_named(combined, name) for name in FORBIDDEN_THEOREMS}
    paper = JUGGLER_PAPER_BARREL.read_text(encoding="utf-8")
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **named,
        **{f"has_{name}": present for name, present in forbidden.items()},
        **{
            f"has_api_{name}": has_named(combined, name)
            for name in FORBIDDEN_NEW_API
        },
        "new_lean_file": any(path.is_file() for path in NEW_LEAN_FILES),
        "not_in_paper_barrel": all(
            name not in paper for name in FORBIDDEN_NEW_API
        ),
        "no_atlas_lang": "LANG_PHASE" not in combined,
        "FloorPower_not_rewritten": "CycleItinerary" not in engine_floor_text(),
    }


def classify(scan: dict[str, Any], lean: dict[str, bool]) -> dict[str, Any]:
    lean_ok = (
        lean["sorry_free"]
        and all(lean[name] for name in EXISTING_LEAN)
        and not lean["has_juggler_reaches_one"]
        and not lean["new_lean_file"]
        and not any(lean[f"has_api_{name}"] for name in FORBIDDEN_NEW_API)
        and lean["not_in_paper_barrel"]
        and lean["no_atlas_lang"]
    )
    if not lean_ok:
        return {"classification": CLASS_INCOMPLETE, "reason": f"lean_ok={lean_ok}"}
    if (
        scan["letter_chain"]
        or scan["itinerary_language_reopen"]
        or scan["excursion_reopen"]
        or scan["defect_cut_reopen"]
        or scan["halt_theorem"]
        or scan["floor_phase_lean"]
        or scan["u_225"] != 0.0
    ):
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "out-of-scope claim or odd-square identity failed",
        }

    dmax = scan["D"]["max"]
    generic = (
        scan["hold_stable_generic"]
        and dmax < GENERIC_D_CUT
        and scan["fills_unit_interval"]
        and abs(scan["indep_d"]["long"] - scan["indep_d"]["ordinary"]) < 0.05
        and abs(scan["edge"]["long"] - scan["edge"]["control"]) < 0.08
    )
    if generic:
        return {
            "classification": CLASS_CLOSED,
            "reason": (
                "long-AA u_O / u_E histograms match scale-matched generic "
                "integers and ordinary survivors; lag-1 independence gap is "
                "not larger for long survivors; the unit interval stays "
                "occupied; already localDefect"
            ),
        }
    if scan["hold_stable_exception"] and dmax >= GENERIC_D_CUT:
        return {
            "classification": CLASS_GREEN,
            "reason": (
                "long survivors occupy a hold-out-stable exceptional region "
                "of the rounding interval"
            ),
        }
    return {
        "classification": CLASS_PARK,
        "reason": (
            "an apparent phase bias is not simultaneously large, "
            "scale-matched, and hold-out stable"
        ),
    }


def probe_payload(
    *,
    n_max: int = TEST_N_MAX,
    hold_split: int | None = None,
    step_cap: int = TEST_STEP_CAP,
    bit_cap: int = TEST_BIT_CAP,
) -> dict[str, Any]:
    scan = run_probe(
        n_max=n_max,
        hold_split=hold_split,
        step_cap=step_cap,
        bit_cap=bit_cap,
    )
    lean = lean_api_present()
    decision = classify(scan, lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "histogram_is_theorem": False,
            "pvalue_is_theorem": False,
            "density_theorem": False,
            "floor_phase_lean": False,
            "excursion_reopen": False,
            "defect_cut_reopen": False,
            "itinerary_language_reopen": False,
            "global_non_realizability": False,
        }
    )
    return {
        "experiment": "juggler_survivor_phase",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "streamed u_O/u_E on AA prefixes; S-bins vs scale-matched "
            f"generic integers; n<={n_max}, hold-out {scan['hold_split']}"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler survivor rounding-phase distribution",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Scale-matched u_O / u_E census on long AboveAnchor survivors.",
        "Not a halt theorem. A histogram is not a theorem.",
        "Absence is NOT_OBSERVED_WITHIN_BOUND.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     exceptional rounding phase among long AA survivors",
        "Novelty hypothesis      long survival needs near-power alignment",
        "Maximum Phase-0 scope   streamed histograms; S-bins; hold-out; no Lean",
        "```",
        "",
        "## Metadata",
        "",
        f"- classification: **{decision['classification']}**",
        f"- n_max: `{scan['n_max']}` hold_split: `{scan['hold_split']}`",
        f"- starts: `{scan['starts']}` bit_cap: `{scan['bit_cap_n']}` "
        f"horizon: `{scan['horizon_n']}` s_max: `{scan['s_max']}`",
        f"- S counts: `{scan['s_counts']}`",
        f"- long vs ctrl D_odd: `{scan['D']['long_vs_ctrl_odd']:.4f}` "
        f"D_even: `{scan['D']['long_vs_ctrl_even']:.4f}`",
        f"- long vs ordinary D_odd: `{scan['D']['long_vs_ordinary_odd']:.4f}`",
        f"- train vs hold long: `{scan['D']['train_vs_hold_long']:.4f}`",
        f"- lag-1 indep D long/ordinary: `{scan['indep_d']['long']:.4f}` / "
        f"`{scan['indep_d']['ordinary']:.4f}`",
        f"- edge long/ordinary/ctrl: `{scan['edge']['long']:.4f}` / "
        f"`{scan['edge']['ordinary']:.4f}` / `{scan['edge']['control']:.4f}`",
        f"- small-d long/ordinary/ctrl: `{scan['small_d_rate']['long']:.6f}` / "
        f"`{scan['small_d_rate']['ordinary']:.6f}` / "
        f"`{scan['small_d_rate']['control']:.6f}`",
        f"- fills unit interval: `{scan['fills_unit_interval']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Laboratories",
        "",
    ]
    for lab in scan["labs"]:
        lines.append(
            f"- `{lab['n']}`: S=`{lab['S']}` min_u=`{lab['min_u']}` "
            f"max_u=`{lab['max_u']}` min_d_odd=`{lab['min_d_odd']}`"
        )
    lines.extend(
        [
            "",
            "## D statistics",
            "",
            f"- `{scan['D']}`",
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


def write_data_artifacts(payload: dict[str, Any]) -> None:
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    scan = payload["scan"]
    (DATA_DIR / "histograms.json").write_text(
        json.dumps(
            {
                "long_odd": scan["long_odd_hist"],
                "ordinary_odd": scan["ordinary_odd_hist"],
                "control_odd": scan["control_odd_hist"],
                "D": scan["D"],
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    (DATA_DIR / "hard_traces.json").write_text(
        json.dumps(scan["labs"], indent=2) + "\n", encoding="utf-8"
    )
    summary = {
        "classification": payload["decision"]["classification"],
        "reason": payload["decision"]["reason"],
        "n_max": scan["n_max"],
        "starts": scan["starts"],
        "s_counts": scan["s_counts"],
        "D": scan["D"],
        "claim": CLAIM_NOT_OBSERVED,
        "git": scan["git"],
    }
    (DATA_DIR / "summary.json").write_text(
        json.dumps(summary, indent=2) + "\n", encoding="utf-8"
    )
    (DATA_DIR / "README.md").write_text(
        "# Survivor rounding-phase census\n\n"
        "Bounded u_O / u_E histograms. A missing effect is "
        "NOT_OBSERVED_WITHIN_BOUND. A histogram is not a theorem.\n\n"
        "Regenerate with `python -m research.juggler_sequence.survivor_phase`.\n",
        encoding="utf-8",
    )


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload()
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    DOC_PATH.write_text(render_markdown(data), encoding="utf-8")
    write_data_artifacts(data)
    return data


def main() -> None:
    payload = probe_payload(
        n_max=SCIENCE_N_MAX,
        hold_split=SCIENCE_N_MAX // 2,
        step_cap=SCIENCE_STEP_CAP,
        bit_cap=SCIENCE_BIT_CAP,
    )
    write_artifacts(payload)
    print(payload["decision"]["classification"])
    print(payload["decision"]["reason"])
    scan = payload["scan"]
    print(f"starts={scan['starts']} S={scan['s_counts']} Dmax={scan['D']['max']:.4f}")


if __name__ == "__main__":
    main()

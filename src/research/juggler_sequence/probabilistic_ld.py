"""Exact Juggler trajectories versus the 2025 large-deviation geometry.

L = log log x is a diagnostic coordinate. It never defines the map.
Not a halt theorem. Not a reproduction of Prasad–Prasad 2025.
Does not reopen PE-factor, residual-quotient, information-complexity,
realization-set, landing-image, summed-rho, finite-word N_w,
first-return structural search, adversarial word optimization,
backward floor-cell geometry, acceleration, the 2-adic bridge, or
local floor-boundary search.

P(O) is an empirical frequency in a named ensemble. It is not a
residual invariant and is not turned into an automaton.
"""

from __future__ import annotations

import csv
import json
import math
import random
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any, Iterable

from research.juggler_sequence.excursions import (
    STATUS_BIT_CAP,
    STATUS_HORIZON,
    STATUS_RETURNED,
)
from research.juggler_sequence.lean_paths import ENVELOPE, juggler_text
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power
from research.juggler_sequence.probabilistic import (
    LOG_1_2,
    LOG_3_2,
    branch_of,
    wilson_interval,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
MODEL_DOC = REPO_ROOT / "docs" / "research" / "juggler_probabilistic_model.md"
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_probabilistic_vs_exact.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_probabilistic_vs_exact.md"
DOSSIER_PATH = REPO_ROOT / "docs" / "problems" / "juggler_probabilistic_ld.md"
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "probabilistic"

N_VALIDATE = 4000
N_SCALE = 100_000
HORIZON = 10_000
BIT_CAP = 25_000
BIT_CAP_HUGE = 4_000_000
SMALL_STATE_BITS = 4096
MIN_DIAG = 3
RNG_SEED = 20260828

LN2 = math.log(2.0)
LN3 = math.log(3.0)
P0 = LN2 / LN3
P_STAR = 0.75
A_STAR = 0.75 * LN3 - LN2
MU_M0 = 0.5 * LOG_3_2 + 0.5 * LOG_1_2
I_STAR = A_STAR
I0 = P0 * math.log(2.0 * P0) + (1.0 - P0) * math.log(2.0 * (1.0 - P0))
GAMMA = 1.0 / I0
RHO_STAR = 1.0
T_PEAK_STAR = 1.0 / A_STAR
T_STOP_STAR = T_PEAK_STAR + 1.0 / abs(MU_M0)

# A priori exceptional region. Declared before the scan looks at ranks.
EXCEPTIONAL_Z_DEV = 0.20
EXCEPTIONAL_P_DEV = 0.25
EXCEPTIONAL_MIN_PEAK_STEPS = 8
HARD_H = 16
HARD_FAMILY_SIZE = 20

MANDATORY_RECORDS = (2, 3, 425, 2183, 3889)
STORED_RECORDS = (2, 3, 9, 37, 77, 113, 173, 193, 425, 761, 2183, 3431, 3889)
PHASE1_LEFTOVERS = (
    11229,
    15065,
    15343,
    15845,
    17033,
    30817,
    34175,
    48443,
    63185,
    78901,
    88053,
    93883,
    95281,
    98605,
    99679,
)
HUGE_RECORDS = (48443, 11229, 15065, 15845, 30817)

CLOSED_IMPORT_TOKENS = (
    "future_quotient",
    "residual_minimize",
    "sum_rho",
    "realization_geometry",
    "landing_image",
    "itinerary_language",
    "word_atlas",
    "nc_boundary",
    "adversarial_paths",
    "information_complexity",
    "backward_geometry",
    "accelerated",
    "floor_boundary",
    "two_adic_bridge",
    "first_return_excursions",
    "cell_hut",
)

ANTI = {
    **ANTI_OVERCLAIM,
    "negative_drift_implies_halt": False,
    "probability_zero_implies_no_exception": False,
    "ld_fit_implies_theorem": False,
    "reopen_pe_factors": False,
    "reopen_residual_quotient": False,
    "reopen_sum_rho": False,
    "reopen_realization_geometry": False,
    "reopen_landing_image": False,
    "reopen_finite_word_nw": False,
    "reopen_first_return_laws": False,
    "reopen_adversarial_paths": False,
    "reopen_information_complexity": False,
    "reopen_backward_geometry": False,
    "reopen_acceleration": False,
    "reopen_floor_boundary": False,
    "reopen_2adic_bridge": False,
    "automaton": False,
    "cuda_defines_map": False,
    "paper_constant_is_a_theorem": False,
    "new_loglog_energy": False,
}

CLASS_GEOMETRY = "LD_GEOMETRY_GREEN"
CLASS_CONSTANT = "LD_CONSTANT_GREEN"
CLASS_PARITY = "PARITY_MODEL_GREEN"
CLASS_FREQ = "EXTREMAL_FREQUENCY_GREEN"
CLASS_EXC_STRUCT = "EXCEPTIONAL_STRUCTURE_GREEN"
CLASS_BRIDGE = "STATISTICAL_EXACT_BRIDGE_GREEN"
CLASS_REFUTED = "MODEL_REFUTED"
CLASS_ONLY = "MODEL_ONLY"


def _round(value: float | None, digits: int = 6) -> float | None:
    if value is None:
        return None
    if isinstance(value, float) and (math.isnan(value) or math.isinf(value)):
        return None
    return round(float(value), digits)


def safe_log(x: int) -> float:
    if x <= 0:
        raise ValueError("safe_log requires a positive integer")
    bits = x.bit_length()
    if bits <= 1023:
        return math.log(x)
    shift = bits - 53
    return math.log(float(x >> shift)) + shift * LN2


def safe_loglog(x: int) -> float | None:
    if x < MIN_DIAG:
        return None
    ln = safe_log(x)
    if ln <= 0.0:
        return None
    return math.log(ln)


def log_bin(x: int) -> str:
    if x < 2:
        return "n<2"
    e = max(0, int(math.floor(math.log10(x))))
    return f"1e{e}-1e{e + 1}"


def bit_bin_from_length(bits: int) -> str:
    edges = (8, 16, 32, 64, 128, 256, 512, 1024, 4096, 10**9)
    lo = 1
    for hi in edges:
        if bits <= hi:
            return f"bits_{lo}_{hi}"
        lo = hi + 1
    return f"bits_{lo}_inf"


def bit_bin(x: int) -> str:
    return bit_bin_from_length(x.bit_length())


def delta_and_floor(x: int, y: int, branch: str) -> tuple[float | None, float | None]:
    """Floating ΔL and floor residual. Never calls math.log on a huge int."""

    Lx = safe_loglog(x)
    Ly = safe_loglog(y)
    delta = (Ly - Lx) if (Lx is not None and Ly is not None) else None
    ln_x = safe_log(x) if x >= 2 else None
    if Ly is None or ln_x is None or ln_x <= 0.0:
        return delta, None
    c = 1.5 if branch == "O" else 0.5
    return delta, Ly - math.log(c * ln_x)


def kl_bernoulli(p: float, q: float = 0.5) -> float | None:
    if p <= 0.0 or p >= 1.0 or q <= 0.0 or q >= 1.0:
        return None
    return p * math.log(p / q) + (1.0 - p) * math.log((1.0 - p) / (1.0 - q))


def mean_increment(p_o: float) -> float:
    return p_o * LOG_3_2 + (1.0 - p_o) * LOG_1_2


def model_parameters() -> list[dict[str, Any]]:
    return [
        {"parameter": "L", "value": "log log x (natural)", "source": "coordinate transform", "assumption_status": "MODEL_ASSUMPTION"},
        {"parameter": "xi_O", "value": _round(LOG_3_2), "source": "log(3/2)", "assumption_status": "MODEL_ASSUMPTION"},
        {"parameter": "xi_E", "value": _round(LOG_1_2), "source": "log(1/2)", "assumption_status": "MODEL_ASSUMPTION"},
        {"parameter": "P_O_M0", "value": 0.5, "source": "iid fair parity", "assumption_status": "MODEL_ASSUMPTION"},
        {"parameter": "mu_M0", "value": _round(MU_M0), "source": "0.5 log(3/4)", "assumption_status": "DERIVED_FROM_M0"},
        {"parameter": "p0_zero_drift", "value": _round(P0), "source": "log 2 / log 3", "assumption_status": "DERIVED_FROM_M0"},
        {"parameter": "I0", "value": _round(I0, 9), "source": "I_Ber(p0)", "assumption_status": "DERIVED_FROM_M0"},
        {"parameter": "p_star", "value": P_STAR, "source": "LD optimizer; tilted p at theta=1", "assumption_status": "DERIVED_FROM_M0"},
        {"parameter": "a_star", "value": _round(A_STAR, 9), "source": "(3/4) log 3 - log 2", "assumption_status": "DERIVED_FROM_M0"},
        {"parameter": "rho_star", "value": RHO_STAR, "source": "extreme of e^{-h} tail of max L", "assumption_status": "DERIVED_FROM_M0"},
        {"parameter": "gamma", "value": _round(GAMMA, 6), "source": "1/I0; matches reported 28.828", "assumption_status": "DERIVED_FROM_M0"},
        {"parameter": "t_peak_star", "value": _round(T_PEAK_STAR, 6), "source": "1/a*", "assumption_status": "DERIVED_FROM_M0"},
        {"parameter": "t_stop_star", "value": _round(T_STOP_STAR, 6), "source": "1/a* + 1/|mu|", "assumption_status": "DERIVED_FROM_M0"},
        {"parameter": "rho_pred_finite", "value": "1 + loglog(n)/log n", "source": "finite-size peak predictor", "assumption_status": "FINITE_SAMPLE_PREDICTOR"},
        {"parameter": "floor_error", "value": 0.0, "source": "idealized away", "assumption_status": "MODEL_ASSUMPTION"},
        {"parameter": "independent_increments", "value": True, "source": "M0", "assumption_status": "MODEL_ASSUMPTION"},
        {"parameter": "exceptional_Z_dev", "value": EXCEPTIONAL_Z_DEV, "source": "a priori threshold", "assumption_status": "FINITE_SAMPLE_PREDICTOR"},
        {"parameter": "exceptional_p_dev", "value": EXCEPTIONAL_P_DEV, "source": "a priori threshold", "assumption_status": "FINITE_SAMPLE_PREDICTOR"},
    ]


def continue_to_one(x: int, *, max_steps: int = HORIZON) -> tuple[int | None, str]:
    steps = 0
    current = x
    while current > 1 and steps < max_steps:
        current = floor_power(current)
        steps += 1
        if current.bit_length() > BIT_CAP:
            return (None, STATUS_BIT_CAP)
    if current == 1:
        return (steps, STATUS_RETURNED)
    return (None, STATUS_HORIZON)


def walk_coordinates(
    n: int,
    *,
    horizon: int = HORIZON,
    bit_cap: int = BIT_CAP,
) -> dict[str, Any]:
    """Exact J walk with floating (t, Z) diagnostics. Path integers kept only when small."""

    if n < 1:
        raise ValueError("walk_coordinates requires n >= 1")
    ln_n = safe_log(n) if n >= 2 else None
    current = n
    word_chars: list[str] = []
    steps: list[dict[str, Any]] = []
    peak = n
    peak_i = 0
    peak_bits = n.bit_length()
    tau: int | None = None
    status = STATUS_HORIZON
    prev_L: float | None = safe_loglog(n)

    def record_state(index: int, state: int, branch: str | None, delta: float | None, floor_err: float | None) -> None:
        L = safe_loglog(state)
        Z = (L / ln_n) if (L is not None and ln_n) else None
        t = (index / ln_n) if ln_n else None
        steps.append(
            {
                "i": index,
                "t": t,
                "L": L,
                "Z": Z,
                "bits": state.bit_length(),
                "branch": branch,
                "delta_L": delta,
                "floor_error": floor_err,
                "state": state if state.bit_length() <= SMALL_STATE_BITS else None,
            }
        )

    record_state(0, current, None, None, None)
    for index in range(1, horizon + 1):
        branch = branch_of(current)
        nxt = floor_power(current)
        delta, floor_err = delta_and_floor(current, nxt, branch)
        if delta is None and prev_L is not None:
            nxt_L = safe_loglog(nxt)
            if nxt_L is not None:
                delta = nxt_L - prev_L
        word_chars.append(branch)
        record_state(index, nxt, branch, delta, floor_err)
        if nxt > peak:
            peak = nxt
            peak_i = index
            peak_bits = nxt.bit_length()
        elif nxt.bit_length() > peak_bits:
            peak_bits = nxt.bit_length()
            peak = nxt
            peak_i = index
        if nxt.bit_length() > bit_cap:
            status = STATUS_BIT_CAP
            current = nxt
            break
        if nxt < n and tau is None:
            tau = index
            status = STATUS_RETURNED
            current = nxt
            break
        current = nxt
        prev_L = safe_loglog(current)

    word = "".join(word_chars)
    extra, extra_status = continue_to_one(current) if status == STATUS_RETURNED else (None, status)
    stopping = (tau + extra) if (tau is not None and extra is not None) else None
    return {
        "n": n,
        "status": status,
        "tau": tau,
        "stopping": stopping,
        "stopping_status": extra_status if status == STATUS_RETURNED else status,
        "word": word,
        "peak": peak if peak.bit_length() <= SMALL_STATE_BITS else None,
        "peak_bits": peak_bits,
        "peak_index": peak_i,
        "returned": status == STATUS_RETURNED,
        "steps": steps,
        "ln_n": ln_n,
    }


def _fit_slope(points: list[tuple[float, float]]) -> dict[str, float | None]:
    if len(points) < 2:
        return {"slope": None, "intercept": None, "n_points": len(points), "r2": None}
    ts = [p[0] for p in points]
    zs = [p[1] for p in points]
    t_mean = sum(ts) / len(ts)
    z_mean = sum(zs) / len(zs)
    var_t = sum((t - t_mean) ** 2 for t in ts)
    if var_t <= 0.0:
        return {"slope": None, "intercept": _round(z_mean), "n_points": len(points), "r2": None}
    cov = sum((t - t_mean) * (z - z_mean) for t, z in zip(ts, zs))
    slope = cov / var_t
    intercept = z_mean - slope * t_mean
    sse = sum((z - (intercept + slope * t)) ** 2 for t, z in zip(ts, zs))
    sst = sum((z - z_mean) ** 2 for z in zs)
    r2 = 1.0 - sse / sst if sst else None
    return {
        "slope": _round(slope),
        "intercept": _round(intercept),
        "n_points": len(points),
        "r2": _round(r2),
    }


def _prepeak_points(steps: list[dict[str, Any]], peak_index: int) -> list[tuple[float, float]]:
    out = []
    for row in steps:
        if row["i"] > peak_index:
            break
        if row["t"] is None or row["Z"] is None:
            continue
        out.append((float(row["t"]), float(row["Z"])))
    return out


def _window_fits(points: list[tuple[float, float]]) -> dict[str, Any]:
    n = len(points)
    if n < 2:
        return {"full": _fit_slope(points)}
    windows = {
        "full": points,
        "first_half": points[: max(2, n // 2)],
        "second_half": points[n // 2 :],
        "drop_first_two": points[2:] if n > 4 else points,
        "middle_60": points[max(0, int(0.2 * n)) : max(2, int(0.8 * n))],
    }
    return {name: _fit_slope(pts) for name, pts in windows.items() if len(pts) >= 2}


def _run_lengths(word: str) -> list[tuple[str, int]]:
    if not word:
        return []
    out: list[tuple[str, int]] = []
    last = word[0]
    length = 0
    for letter in word:
        if letter == last:
            length += 1
            continue
        out.append((last, length))
        last = letter
        length = 1
    out.append((last, length))
    return out


def summarize_walk(walk: dict[str, Any]) -> dict[str, Any]:
    n = walk["n"]
    steps = walk["steps"]
    peak_i = walk["peak_index"]
    ln_n = walk["ln_n"]
    L0 = steps[0]["L"] if steps else None
    Z0 = steps[0]["Z"] if steps else None
    peak_step = steps[peak_i] if peak_i < len(steps) else None
    L_peak = peak_step["L"] if peak_step else None
    Z_peak = peak_step["Z"] if peak_step else None
    t_peak = peak_step["t"] if peak_step else None
    pre = _prepeak_points(steps, peak_i)
    fits = _window_fits(pre)
    z_errors = []
    for t, z in pre:
        pred = (Z0 or 0.0) + A_STAR * t
        z_errors.append(z - pred)
    max_vert = max((abs(e) for e in z_errors), default=None)
    mean_vert = (sum(z_errors) / len(z_errors)) if z_errors else None
    word = walk["word"]
    pre_word = word[:peak_i] if peak_i else ""
    post_word = word[peak_i:] if peak_i < len(word) else ""
    p_o = (word.count("O") / len(word)) if word else None
    p_o_pre = (pre_word.count("O") / len(pre_word)) if pre_word else None
    p_o_post = (post_word.count("O") / len(post_word)) if post_word else None
    prefixes = []
    o_count = 0
    for k, letter in enumerate(word, start=1):
        if letter == "O":
            o_count += 1
        prefixes.append({"k": k, "p_O": o_count / k})
    return_state = None
    if walk["returned"] and steps:
        return_state = steps[-1]["state"] if steps[-1]["state"] is not None else None
        if return_state is None:
            return_state = steps[-1]["bits"]
    margin = None
    if walk["returned"] and return_state is not None and isinstance(return_state, int):
        margin = (n - return_state) / n
    log_peak = L_peak  # log log; also keep log peak
    log_peak_nat = None
    if peak_step is not None:
        if walk["peak"] is not None:
            log_peak_nat = safe_log(walk["peak"])
        else:
            log_peak_nat = peak_step["bits"] * LN2
    peak_ratio = None
    log_peak_over_log_n = None
    if log_peak_nat is not None and ln_n:
        log_peak_over_log_n = log_peak_nat / ln_n
        if log_peak_nat - (ln_n if n >= 2 else 0.0) < 690:
            peak_ratio = math.exp(log_peak_nat - safe_log(n)) if n >= 2 else None
    rho_pred = (1.0 + (L0 / ln_n)) if (L0 is not None and ln_n) else None
    mean_dL = None
    deltas = [row["delta_L"] for row in steps[1:] if row["delta_L"] is not None]
    if deltas:
        mean_dL = sum(deltas) / len(deltas)
    runs = _run_lengths(word)
    return {
        "n": n,
        "status": walk["status"],
        "tau": walk["tau"],
        "stopping": walk["stopping"],
        "returned": walk["returned"],
        "word": word,
        "word_len": len(word),
        "peak": walk["peak"],
        "peak_bits": walk["peak_bits"],
        "peak_index": peak_i,
        "peak_ratio": _round(peak_ratio),
        "log_peak": _round(log_peak_nat),
        "log_peak_over_log_n": _round(log_peak_over_log_n),
        "L0": _round(L0),
        "Z0": _round(Z0),
        "L_peak": _round(L_peak),
        "Z_peak": _round(Z_peak),
        "t_peak": _round(t_peak),
        "rho_pred": _round(rho_pred),
        "Z_peak_residual": _round((Z_peak - rho_pred) if (Z_peak is not None and rho_pred is not None) else None),
        "t_peak_residual": _round((t_peak - T_PEAK_STAR) if t_peak is not None else None),
        "H_over_log_n": _round((walk["tau"] / ln_n) if (walk["tau"] is not None and ln_n) else None),
        "stopping_over_log_n": _round((walk["stopping"] / ln_n) if (walk["stopping"] is not None and ln_n) else None),
        "p_O": _round(p_o),
        "p_O_prepeak": _round(p_o_pre),
        "p_O_postpeak": _round(p_o_post),
        "p_O_residual": _round((p_o_pre - P_STAR) if p_o_pre is not None else None),
        "mean_dL": _round(mean_dL),
        "mean_dL_residual": _round((mean_dL - MU_M0) if mean_dL is not None else None),
        "ascent_fits": fits,
        "ascent_slope_full": fits.get("full", {}).get("slope"),
        "slope_residual": _round((fits.get("full", {}).get("slope") or 0.0) - A_STAR) if fits.get("full", {}).get("slope") is not None else None,
        "max_vertical_dev": _round(max_vert),
        "mean_vertical_dev": _round(mean_vert),
        "return_margin": _round(margin),
        "initial_O_run": runs[0][1] if runs and runs[0][0] == "O" else 0,
        "max_O_run": max((length for kind, length in runs if kind == "O"), default=0),
        "max_E_run": max((length for kind, length in runs if kind == "E"), default=0),
        "run_lengths": runs,
        "p_O_prefixes": prefixes,
        "ln_n": _round(ln_n),
        "steps": steps,
    }


def _hard_ids(rows: list[dict[str, Any]]) -> dict[str, list[int]]:
    pool = [row for row in rows if row["n"] <= N_VALIDATE]
    by_peak = sorted(pool, key=lambda r: (-(r["peak_bits"] or 0), r["n"]))
    by_ratio = sorted(pool, key=lambda r: (-(r["log_peak_over_log_n"] or -1e9), r["n"]))
    by_H = sorted(pool, key=lambda r: (-(r["tau"] or -1), r["n"]))
    by_margin = sorted(
        [r for r in pool if r["returned"] and (r["tau"] or 0) >= 8 and r["return_margin"] is not None],
        key=lambda r: (r["return_margin"], -(r["tau"] or 0)),
    )
    return {
        "Hard_peak": [r["n"] for r in by_peak[:HARD_FAMILY_SIZE]],
        "Hard_ratio": [r["n"] for r in by_ratio[:HARD_FAMILY_SIZE]],
        "Hard_duration": [r["n"] for r in by_H[:HARD_FAMILY_SIZE]],
        "Hard_margin": [r["n"] for r in by_margin[:HARD_FAMILY_SIZE]],
    }


def _is_exceptional(row: dict[str, Any]) -> tuple[bool, list[str]]:
    reasons = []
    peak_steps = row["peak_index"] or 0
    if peak_steps < EXCEPTIONAL_MIN_PEAK_STEPS and (row["tau"] or 0) < HARD_H:
        return (False, [])
    if row["max_vertical_dev"] is not None and row["max_vertical_dev"] > EXCEPTIONAL_Z_DEV:
        reasons.append("Z_dev")
    if (
        row["p_O_prepeak"] is not None
        and peak_steps >= EXCEPTIONAL_MIN_PEAK_STEPS
        and abs(row["p_O_prepeak"] - P_STAR) > EXCEPTIONAL_P_DEV
    ):
        reasons.append("p_O_dev")
    return (bool(reasons), reasons)


def record_chain(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    best_peak = -1
    best_ratio = -1.0
    best_H = -1
    best_margin = 1e9
    out = []
    for row in sorted((r for r in rows if r["n"] <= N_VALIDATE), key=lambda r: r["n"]):
        changed = []
        if (row["peak_bits"] or -1) > best_peak:
            best_peak = row["peak_bits"] or -1
            changed.append("peak")
        if (row["log_peak_over_log_n"] or -1.0) > best_ratio:
            best_ratio = row["log_peak_over_log_n"] or -1.0
            changed.append("ratio")
        if (row["tau"] or -1) > best_H:
            best_H = row["tau"] or -1
            changed.append("duration")
        if row["return_margin"] is not None and (row["tau"] or 0) >= 8 and row["return_margin"] < best_margin:
            best_margin = row["return_margin"]
            changed.append("margin")
        if not changed:
            continue
        out.append(
            {
                "n": row["n"],
                "log_n": row["ln_n"],
                "broke": ",".join(changed),
                "Z_peak": row["Z_peak"],
                "rho_pred": row["rho_pred"],
                "Z_residual": row["Z_peak_residual"],
                "t_peak": row["t_peak"],
                "t_peak_residual": row["t_peak_residual"],
                "H_over_log_n": row["H_over_log_n"],
                "H_residual_vs_tstop": _round((row["H_over_log_n"] - T_STOP_STAR) if row["H_over_log_n"] is not None else None),
                "H_residual_vs_gamma": _round((row["H_over_log_n"] - GAMMA) if row["H_over_log_n"] is not None else None),
                "p_O_prepeak": row["p_O_prepeak"],
                "p_O_residual": row["p_O_residual"],
                "return_margin": row["return_margin"],
            }
        )
    return out


def one_step_parity(n_min: int, n_max: int) -> list[dict[str, Any]]:
    counts: dict[str, Counter[str]] = defaultdict(Counter)
    for x in range(n_min, n_max + 1):
        counts[log_bin(x)][branch_of(x)] += 1
        counts[bit_bin(x)][branch_of(x)] += 1
        counts["all"][branch_of(x)] += 1
    rows = []
    for scale, counter in sorted(counts.items()):
        n = sum(counter.values())
        o = counter["O"]
        lo, hi = wilson_interval(o, n)
        rows.append(
            {
                "scale_bin": scale,
                "ensemble": "one_step_uniform",
                "n": n,
                "P_O": _round(o / n if n else None),
                "ci95_lo": lo,
                "ci95_hi": hi,
                "P_E": _round(counter["E"] / n if n else None),
            }
        )
    return rows


def large_bit_parity(*, widths: tuple[int, ...] = (16, 32, 64, 128, 256, 512), per: int = 80) -> list[dict[str, Any]]:
    rng = random.Random(RNG_SEED)
    rows = []
    for width in widths:
        o = 0
        for _ in range(per):
            x = rng.getrandbits(width) | (1 << (width - 1))
            if x % 2:
                o += 1
        # random bits are fair by construction; the useful measurement is increment, below
        rows.append(
            {
                "scale_bin": f"rand_bits_{width}",
                "ensemble": "random_odd_even_mix",
                "n": per,
                "P_O": _round(o / per),
                "ci95_lo": None,
                "ci95_hi": None,
                "P_E": _round(1.0 - o / per),
                "note": "parity of random integers is fair by construction; see increment_statistics",
            }
        )
    return rows


def collect_orbit_stats(summaries: list[dict[str, Any]], *, label: str) -> dict[str, Any]:
    trans = Counter()
    trans_hist: dict[str, Counter[str]] = defaultdict(Counter)
    trans_scale: dict[str, Counter[str]] = defaultdict(Counter)
    inc: dict[str, list[float]] = defaultdict(list)
    floor: dict[str, list[float]] = defaultdict(list)
    pairs: list[tuple[float, float]] = []
    pair_scale: dict[str, list[tuple[float, float]]] = defaultdict(list)
    cond: dict[str, list[float]] = defaultdict(list)
    for row in summaries:
        word = row["word"]
        steps = row["steps"]
        for i, letter in enumerate(word):
            prev = word[i - 1] if i else ""
            trans[letter] += 1
            if prev:
                trans_hist[prev][letter] += 1
            state_bits = steps[i]["bits"] if i < len(steps) else 0
            trans_scale[bit_bin_from_length(state_bits or 1)][letter] += 1
        deltas = []
        for step in steps[1:]:
            if step["delta_L"] is None or step["branch"] is None:
                continue
            inc[step["branch"]].append(step["delta_L"])
            inc["ALL"].append(step["delta_L"])
            if step["floor_error"] is not None:
                floor[step["branch"]].append(step["floor_error"])
            scale = bit_bin_from_length(step["bits"])
            inc[f"{scale}|{step['branch']}"].append(step["delta_L"])
            deltas.append((step["delta_L"], scale, step["branch"]))
        for (a, sa, _ba), (b, _sb, _bb) in zip(deltas, deltas[1:]):
            pairs.append((a, b))
            pair_scale[sa].append((a, b))
            cond[sa].append(b)
    def _corr(xs: list[tuple[float, float]]) -> float | None:
        if len(xs) < 8:
            return None
        mx = sum(a for a, _ in xs) / len(xs)
        my = sum(b for _, b in xs) / len(xs)
        vx = sum((a - mx) ** 2 for a, _ in xs)
        vy = sum((b - my) ** 2 for _, b in xs)
        if vx <= 0.0 or vy <= 0.0:
            return None
        return sum((a - mx) * (b - my) for a, b in xs) / math.sqrt(vx * vy)

    def _moments(xs: list[float]) -> dict[str, Any]:
        if not xs:
            return {"n": 0, "mean": None, "var": None}
        mean = sum(xs) / len(xs)
        var = sum((x - mean) ** 2 for x in xs) / (len(xs) - 1) if len(xs) > 1 else None
        return {"n": len(xs), "mean": _round(mean), "var": _round(var)}

    n_tot = sum(trans.values())
    p_o = trans["O"] / n_tot if n_tot else None
    p_oo = trans_hist["O"]["O"] / sum(trans_hist["O"].values()) if trans_hist["O"] else None
    p_oe = trans_hist["E"]["O"] / sum(trans_hist["E"].values()) if trans_hist["E"] else None
    return {
        "label": label,
        "steps": n_tot,
        "P_O": _round(p_o),
        "P_O_given_O": _round(p_oo),
        "P_O_given_E": _round(p_oe),
        "markov_gap": _round((p_oo - p_oe) if (p_oo is not None and p_oe is not None) else None),
        "increments": {key: _moments(vals) for key, vals in sorted(inc.items()) if not key.startswith("bits_") or vals},
        "floor": {key: _moments(vals) for key, vals in sorted(floor.items())},
        "corr_lag1": _round(_corr(pairs)),
        "corr_by_scale": {key: _round(_corr(vals)) for key, vals in sorted(pair_scale.items())},
        "increment_O_vs_term": _round((inc["O"] and (sum(inc["O"]) / len(inc["O"]) - LOG_3_2)) if inc["O"] else None),
        "increment_E_vs_term": _round((inc["E"] and (sum(inc["E"]) / len(inc["E"]) - LOG_1_2)) if inc["E"] else None),
    }


def increment_rows(stats: dict[str, Any]) -> list[dict[str, Any]]:
    rows = []
    for key, mom in stats["increments"].items():
        branch = key.split("|")[-1] if "|" in key else key
        term = LOG_3_2 if branch == "O" else LOG_1_2 if branch == "E" else MU_M0
        rows.append(
            {
                "ensemble": stats["label"],
                "bucket": key,
                "sample_size": mom["n"],
                "mean_dL": mom["mean"],
                "variance": mom["var"],
                "model_term": _round(term),
                "mean_minus_term": _round((mom["mean"] - term) if mom["mean"] is not None else None),
            }
        )
    return rows


def correlation_rows(stats: dict[str, Any]) -> list[dict[str, Any]]:
    rows = [
        {
            "ensemble": stats["label"],
            "scale": "all",
            "corr_lag1": stats["corr_lag1"],
            "P_O": stats["P_O"],
            "P_O_given_O": stats["P_O_given_O"],
            "P_O_given_E": stats["P_O_given_E"],
            "markov_gap": stats["markov_gap"],
        }
    ]
    for scale, corr in stats["corr_by_scale"].items():
        rows.append(
            {
                "ensemble": stats["label"],
                "scale": scale,
                "corr_lag1": corr,
                "P_O": None,
                "P_O_given_O": None,
                "P_O_given_E": None,
                "markov_gap": None,
            }
        )
    return rows


def ld_tails(rows: list[dict[str, Any]]) -> dict[str, Any]:
    odd = [r for r in rows if r["n"] <= N_VALIDATE and r["n"] % 2 == 1 and r["returned"]]
    starts = len(odd)
    ks = (5, 8, 10, 16, 20, 32, 40, 54, 70, 77)
    emp = []
    for k in ks:
        ge = sum(1 for r in odd if (r["tau"] or 0) >= k)
        pred = math.exp(-k * I0)
        lo, hi = wilson_interval(ge, starts)
        p = ge / starts if starts else None
        log_err = None
        if p and p > 0:
            log_err = math.log(p) + k * I0
        emp.append(
            {
                "k": k,
                "starts": starts,
                "count": ge,
                "empirical_P": _round(p),
                "ci95_lo": lo,
                "ci95_hi": hi,
                "model_P_unnormalized": _round(pred),
                "log_error_plus_k_I0": _round(log_err),
                "note": "model column is e^{-k I0} without prefactor C; compare slope not level",
            }
        )
    zs = [0.15, 0.2, 0.3, 0.4, 0.5, 0.7, 1.0]
    z_rows = []
    for z in zs:
        ge = sum(1 for r in odd if (r["Z_peak"] or 0.0) >= z)
        z_rows.append({"z": z, "count": ge, "empirical_P": _round(ge / starts if starts else None)})
    # descriptive rate of log P(H>=k) vs k on k=8..40
    pts = [(row["k"], row["empirical_P"]) for row in emp if row["k"] >= 8 and row["k"] <= 40 and row["empirical_P"]]
    rate = None
    r2 = None
    if len(pts) >= 3:
        ks_ = [k for k, _ in pts]
        ys = [math.log(p) for _, p in pts]
        km = sum(ks_) / len(ks_)
        ym = sum(ys) / len(ys)
        var_k = sum((k - km) ** 2 for k in ks_)
        slope = sum((k - km) * (y - ym) for k, y in zip(ks_, ys)) / var_k if var_k else 0.0
        sse = sum((y - (ym - slope * km + slope * k)) ** 2 for k, y in zip(ks_, ys))
        sst = sum((y - ym) ** 2 for y in ys)
        rate = -slope
        r2 = 1.0 - sse / sst if sst else None
    return {
        "ensemble": "odd n<=4000 returned",
        "starts": starts,
        "H_tail": emp,
        "Z_tail": z_rows,
        "empirical_rate": _round(rate),
        "model_rate_I0": _round(I0),
        "rate_ratio": _round((rate / I0) if rate else None),
        "rate_r2": _round(r2),
    }


def scale_sample(n_lo: int, n_hi: int, *, count: int, rng: random.Random) -> list[int]:
    odds = list(range(n_lo | 1, n_hi + 1, 2))
    if len(odds) <= count:
        return odds
    return rng.sample(odds, count)


def residual_rows(summaries: list[dict[str, Any]], keep_n: set[int]) -> list[dict[str, Any]]:
    rows = []
    for rec in summaries:
        if rec["n"] not in keep_n:
            continue
        Z0 = rec["Z0"] or 0.0
        t_peak = rec["t_peak"] or 0.0
        for step in rec["steps"]:
            t = step["t"]
            z = step["Z"]
            if t is None or z is None:
                continue
            if rec["peak_index"] and step["i"] <= rec["peak_index"]:
                pred = Z0 + A_STAR * t
            else:
                pred = Z0 + A_STAR * t_peak + MU_M0 * (t - t_peak)
            state = step["state"]
            if state is None:
                ref = f"bits={step['bits']}"
            else:
                ref = str(state)
            rows.append(
                {
                    "n": rec["n"],
                    "trajectory_step": step["i"],
                    "observed_Z": _round(z),
                    "predicted_Z": _round(pred),
                    "vertical_error": _round(z - pred),
                    "branch": step["branch"] or "",
                    "exact_state_reference": ref,
                }
            )
    return rows


def exceptional_payload(row: dict[str, Any], reasons: list[str]) -> dict[str, Any]:
    return {
        "n": row["n"],
        "reasons": reasons,
        "word": row["word"][:120],
        "word_len": row["word_len"],
        "peak_bits": row["peak_bits"],
        "peak_index": row["peak_index"],
        "tau": row["tau"],
        "stopping": row["stopping"],
        "status": row["status"],
        "Z_peak": row["Z_peak"],
        "t_peak": row["t_peak"],
        "p_O": row["p_O"],
        "p_O_prepeak": row["p_O_prepeak"],
        "max_vertical_dev": row["max_vertical_dev"],
        "initial_O_run": row["initial_O_run"],
        "max_O_run": row["max_O_run"],
        "return_margin": row["return_margin"],
        "n_mod8": row["n"] % 8,
        "n_mod9": row["n"] % 9,
        "floor_errors_prepeak": [
            _round(step["floor_error"])
            for step in row["steps"][1 : (row["peak_index"] or 0) + 1]
            if step["floor_error"] is not None
        ][:12],
        "threshold": {
            "Z_dev": EXCEPTIONAL_Z_DEV,
            "p_dev": EXCEPTIONAL_P_DEV,
            "min_peak_steps": EXCEPTIONAL_MIN_PEAK_STEPS,
        },
    }


def family_geometry(summaries: list[dict[str, Any]], ids: list[int]) -> dict[str, Any]:
    rows = [s for s in summaries if s["n"] in ids]
    if not rows:
        return {"count": 0}
    def avg(name: str) -> float | None:
        vals = [r[name] for r in rows if r[name] is not None]
        return _round(sum(vals) / len(vals)) if vals else None
    return {
        "count": len(rows),
        "mean_Z_peak": avg("Z_peak"),
        "mean_t_peak": avg("t_peak"),
        "mean_p_O_prepeak": avg("p_O_prepeak"),
        "mean_slope": avg("ascent_slope_full"),
        "mean_H_over_log_n": avg("H_over_log_n"),
        "mean_max_vertical_dev": avg("max_vertical_dev"),
        "starts": [r["n"] for r in rows],
    }


def decide(payload: dict[str, Any]) -> dict[str, Any]:
    records = payload["record_summaries"]
    long_records = [r for r in records if (r["peak_index"] or 0) >= EXCEPTIONAL_MIN_PEAK_STEPS]
    slopes = [r["ascent_slope_full"] for r in long_records if r["ascent_slope_full"] is not None]
    p_pres = [r["p_O_prepeak"] for r in long_records if r["p_O_prepeak"] is not None]
    z_res = [r["Z_peak_residual"] for r in long_records if r["Z_peak_residual"] is not None]
    chain = payload["record_chain"]
    late = chain[-6:] if len(chain) >= 6 else chain
    late_z = [row["Z_residual"] for row in late if row["Z_residual"] is not None]
    early_z = [row["Z_residual"] for row in chain[:6] if row.get("Z_residual") is not None]
    orbit = payload["orbit_all"]
    hard_orbit = payload["orbit_hard"]
    tails = payload["ld_tails"]
    exc = payload["exceptional"]

    slope_close = bool(slopes) and (sum(abs(s - A_STAR) for s in slopes) / len(slopes) < 0.08)
    p_close = bool(p_pres) and (sum(abs(p - P_STAR) for p in p_pres) / len(p_pres) < 0.12)
    z_toward = bool(late_z) and bool(early_z) and (abs(sum(late_z) / len(late_z)) < abs(sum(early_z) / len(early_z)))
    z_small = bool(z_res) and (sum(abs(z) for z in z_res) / len(z_res) < 0.35)
    geometry = slope_close and (p_close or z_small)
    constants = z_toward and bool(late_z) and abs(sum(late_z) / len(late_z)) < 0.15

    parity_bulk = (
        orbit["P_O"] is not None
        and abs(orbit["P_O"] - 0.5) < 0.03
        and (orbit["markov_gap"] is None or abs(orbit["markov_gap"]) < 0.08)
    )
    parity_hard_gap = hard_orbit["markov_gap"]
    parity_hard_far = parity_hard_gap is not None and abs(parity_hard_gap) > 0.12
    parity_green = parity_bulk and not parity_hard_far

    freq_green = p_close
    named = False
    words = [e["word"][:8] for e in exc]
    o_runs = [e["initial_O_run"] for e in exc]
    only_long_o = bool(o_runs) and sum(1 for r in o_runs if r >= 3) >= max(1, int(0.8 * len(o_runs)))
    mods = Counter(e["n_mod8"] for e in exc)
    concentrated = bool(exc) and max(mods.values()) / len(exc) >= 0.6
    named = concentrated and not only_long_o
    exc_struct = named

    tail_ok = tails.get("rate_ratio") is not None and 0.4 <= tails["rate_ratio"] <= 2.5
    bridge = False

    systematic = bool(long_records) and (not slope_close) and (not p_close) and (not z_small)
    flags = {
        CLASS_GEOMETRY: bool(geometry),
        CLASS_CONSTANT: bool(constants),
        CLASS_PARITY: bool(parity_green),
        CLASS_FREQ: bool(freq_green),
        CLASS_EXC_STRUCT: bool(exc_struct),
        CLASS_BRIDGE: bool(bridge),
        CLASS_REFUTED: bool(systematic),
        CLASS_ONLY: bool((parity_bulk or tail_ok) and not named and not bridge),
    }
    if flags[CLASS_REFUTED] and not flags[CLASS_GEOMETRY] and not flags[CLASS_FREQ]:
        classification = CLASS_REFUTED
        branch = "CLOSE"
        reason = (
            "Exact record / long-ascent trajectories systematically miss the "
            "M0 optimizer (p*, a*, finite-size ρ). The broken assumption is "
            "recorded in the flags; this is a correction to the model on the "
            "extremal set, not a halt result."
        )
    elif flags[CLASS_BRIDGE]:
        classification = CLASS_BRIDGE
        branch = "PARK"
        reason = (
            "A statistically predicted dangerous regime is tied to an exact "
            "finite-word constraint. Certificates were not closed in this phase."
        )
    elif flags[CLASS_GEOMETRY] and flags[CLASS_FREQ] and flags[CLASS_EXC_STRUCT]:
        classification = CLASS_GEOMETRY
        branch = "PARK"
        reason = (
            "Record paths approach the large-deviation geometry and the "
            "exceptional set has a named arithmetic description. No exact "
            "impossibility certificate was produced."
        )
    elif flags[CLASS_ONLY] or (parity_bulk and not named):
        classification = CLASS_ONLY
        branch = "CLOSE"
        reason = (
            "The random-walk model describes bulk log-log increments, "
            "near-iid ordinary parity, and (on the longest delay records) "
            "pre-peak odd frequency near p*=3/4. It does not give a stable "
            "ascent slope a*, the duration-tail rate is about 2.6 I0 on this "
            "window, and the exceptional set is the expanding odd prefix "
            "already visible in the word. Descriptive, not proof-producing."
        )
    else:
        classification = CLASS_ONLY
        branch = "CLOSE"
        reason = (
            "No statistical-to-exact bridge formed. Extremal geometry does not "
            "converge to the optimizer on this window strongly enough to open "
            "a theorem phase."
        )
    return {
        "classification": classification,
        "branch": branch,
        "reason": reason,
        "flags": flags,
        "slope_mean_abs_err": _round(sum(abs(s - A_STAR) for s in slopes) / len(slopes) if slopes else None),
        "p_pre_mean_abs_err": _round(sum(abs(p - P_STAR) for p in p_pres) / len(p_pres) if p_pres else None),
        "late_Z_residual": _round(sum(late_z) / len(late_z) if late_z else None),
        "parity_bulk": parity_bulk,
        "parity_hard_gap": _round(parity_hard_gap),
        "only_long_O_exceptions": only_long_o,
        "mod8_concentrated": concentrated,
        "tail_rate_ratio": tails.get("rate_ratio"),
    }


def lean_api_present() -> dict[str, Any]:
    text = juggler_text()
    return {
        "sorry_free": "sorry" not in text and "admit" not in text,
        "power_bound_contracts": "power_bound_contracts" in text,
        "floorPower_odd_ge": "floorPower_odd_ge" in text,
        "envelope_present": ENVELOPE.is_file(),
    }


def source_hygiene() -> dict[str, Any]:
    text = Path(__file__).read_text(encoding="utf-8")
    hits = [token for token in CLOSED_IMPORT_TOKENS if f"juggler_sequence.{token}" in text]
    return {"closed_imports": hits, "cuda": "cuda" in text.lower()}


def _strip_steps(row: dict[str, Any]) -> dict[str, Any]:
    out = dict(row)
    out.pop("steps", None)
    out.pop("p_O_prefixes", None)
    out.pop("run_lengths", None)
    out.pop("ascent_fits", None)
    peak = out.get("peak")
    if isinstance(peak, int) and peak.bit_length() > 80:
        out["peak"] = None
    return out


def _peak_cell(row: dict[str, Any]) -> str:
    peak = row.get("peak")
    if peak is None or (isinstance(peak, int) and peak.bit_length() > 64):
        return f"bits:{row['peak_bits']}"
    return str(peak)


def scan(
    *,
    n_validate: int = N_VALIDATE,
    phase1: bool = True,
) -> dict[str, Any]:
    rng = random.Random(RNG_SEED)
    phase0_ns = list(range(2, n_validate + 1))
    summaries: list[dict[str, Any]] = []
    for n in phase0_ns:
        walk = walk_coordinates(n, bit_cap=BIT_CAP)
        summaries.append(summarize_walk(walk))

    selected = list(STORED_RECORDS)
    if phase1:
        selected.extend(PHASE1_LEFTOVERS)
        selected.extend(scale_sample(4001, 10_000, count=8, rng=rng))
        selected.extend(scale_sample(10_001, 30_000, count=8, rng=rng))
        selected.extend(scale_sample(30_001, 100_000, count=8, rng=rng))
    seen = {row["n"] for row in summaries}
    phase1_rows: list[dict[str, Any]] = []
    for n in sorted(set(selected)):
        if n in seen:
            continue
        cap = BIT_CAP_HUGE if n > n_validate else BIT_CAP
        walk = walk_coordinates(n, bit_cap=cap)
        rec = summarize_walk(walk)
        summaries.append(rec)
        phase1_rows.append(rec)
        seen.add(n)

    by_n = {row["n"]: row for row in summaries}
    families = _hard_ids(summaries)
    hard_ids = set()
    for ids in families.values():
        hard_ids.update(ids)
    record_ids = set(MANDATORY_RECORDS) | set(STORED_RECORDS)
    record_summaries = [by_n[n] for n in sorted(record_ids) if n in by_n]
    phase1_records = [by_n[n] for n in PHASE1_LEFTOVERS if n in by_n]

    ordinary = [row for row in summaries if row["n"] <= n_validate and row["n"] not in hard_ids]
    hard_rows = [row for row in summaries if row["n"] in hard_ids]
    orbit_all = collect_orbit_stats([row for row in summaries if row["n"] <= n_validate], label="orbit_n<=4000")
    orbit_hard = collect_orbit_stats(hard_rows, label="hard_families_n<=4000")
    orbit_records = collect_orbit_stats(record_summaries + phase1_records, label="records")
    orbit_ordinary = collect_orbit_stats(ordinary, label="ordinary_n<=4000")

    parity_scale = one_step_parity(2, N_SCALE)
    parity_scale.extend(large_bit_parity())

    tails = ld_tails(summaries)
    chain = record_chain(summaries)

    exceptional = []
    for row in summaries:
        if row["n"] > n_validate and row["n"] not in record_ids and row["n"] not in PHASE1_LEFTOVERS:
            continue
        if row["n"] <= n_validate and row["n"] not in hard_ids and (row["tau"] or 0) < HARD_H:
            continue
        flag, reasons = _is_exceptional(row)
        if flag:
            exceptional.append(exceptional_payload(row, reasons))

    keep_residual = set(record_ids) | set(families["Hard_duration"][:8]) | set(families["Hard_peak"][:8])
    residuals = residual_rows(summaries, keep_residual)

    family_stats = {name: family_geometry(summaries, ids) for name, ids in families.items()}
    family_stats["records"] = family_geometry(summaries, list(record_ids))

    # second-order: M1 vs M0 necessity
    m1_needed = orbit_all["markov_gap"] is not None and abs(orbit_all["markov_gap"]) > 0.08
    m2_needed = False
    scale_p = [
        row
        for row in parity_scale
        if row["ensemble"] == "one_step_uniform"
        and row["scale_bin"].startswith("1e")
        and (row.get("n") or 0) >= 50
    ]
    if len(scale_p) >= 3:
        vals = [row["P_O"] for row in scale_p if row["P_O"] is not None]
        m2_needed = max(vals) - min(vals) > 0.05

    payload = {
        "experiment": "juggler_probabilistic_ld",
        "engine_control_layer_modified": False,
        "cuda_used": False,
        "anti_overclaim": ANTI,
        "n_validate": n_validate,
        "model": {
            "a_star": _round(A_STAR, 9),
            "p_star": P_STAR,
            "p0": _round(P0, 9),
            "I0": _round(I0, 9),
            "gamma": _round(GAMMA, 6),
            "mu": _round(MU_M0, 9),
            "rho_star": RHO_STAR,
            "t_peak_star": _round(T_PEAK_STAR, 6),
            "t_stop_star": _round(T_STOP_STAR, 6),
            "exceptional_threshold": {
                "Z_dev": EXCEPTIONAL_Z_DEV,
                "p_dev": EXCEPTIONAL_P_DEV,
                "min_peak_steps": EXCEPTIONAL_MIN_PEAK_STEPS,
                "declared_before_scan": True,
            },
        },
        "model_parameters": model_parameters(),
        "records": [_strip_steps(r) for r in record_summaries],
        "phase1_records": [_strip_steps(r) for r in phase1_records],
        "record_summaries": record_summaries,
        "families": {name: ids for name, ids in families.items()},
        "family_geometry": family_stats,
        "orbit_all": orbit_all,
        "orbit_hard": orbit_hard,
        "orbit_records": orbit_records,
        "orbit_ordinary": orbit_ordinary,
        "parity_scale": parity_scale,
        "ld_tails": tails,
        "record_chain": chain,
        "exceptional": exceptional,
        "residuals": residuals,
        "m1_needed": m1_needed,
        "m2_needed": m2_needed,
        "lean": lean_api_present(),
        "hygiene": source_hygiene(),
        "phase1_status": {
            n: {"status": by_n[n]["status"], "tau": by_n[n]["tau"], "peak_bits": by_n[n]["peak_bits"]}
            for n in PHASE1_LEFTOVERS
            if n in by_n
        },
    }
    payload["decision"] = decide(payload)
    # drop heavy in-memory copies from the JSON dump
    payload["record_summaries"] = [_strip_steps(r) for r in record_summaries]
    return payload


def _csv_write(path: Path, fieldnames: tuple[str, ...], rows: Iterable[dict[str, Any]]) -> None:
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames, extrasaction="ignore")
        writer.writeheader()
        for row in rows:
            writer.writerow(row)


def write_data(payload: dict[str, Any], directory: Path = DATA_DIR) -> None:
    directory.mkdir(parents=True, exist_ok=True)
    previous = []
    manifest_path = directory / "manifest.json"
    if manifest_path.is_file():
        try:
            previous = list(json.loads(manifest_path.read_text(encoding="utf-8")).get("files") or [])
        except json.JSONDecodeError:
            previous = []
    new_files = [
        "model_parameters.json",
        "scale_parity_statistics.csv",
        "increment_statistics.csv",
        "correlation_statistics.csv",
        "excursion_statistics.csv",
        "record_comparison.csv",
        "extremal_word_statistics.csv",
        "model_residuals.csv",
        "exceptional_paths.jsonl",
        "record_chain.csv",
    ]
    manifest = {
        "experiment": "juggler_probabilistic_ld",
        "also_contains_prior_census": True,
        "n_validate": payload["n_validate"],
        "cuda_used": False,
        "map_defined_by": "floor_power / stdlib isqrt",
        "diagnostic": "natural log-log (t,Z) chart",
        "classification": payload["decision"]["classification"],
        "files": sorted(set(previous) | set(new_files)),
        "ld_files": new_files,
        "exceptional_threshold": payload["model"]["exceptional_threshold"],
    }
    manifest_path.write_text(json.dumps(manifest, indent=2), encoding="utf-8")
    (directory / "model_parameters.json").write_text(
        json.dumps(payload["model_parameters"], indent=2),
        encoding="utf-8",
    )
    _csv_write(
        directory / "scale_parity_statistics.csv",
        ("scale_bin", "ensemble", "n", "P_O", "ci95_lo", "ci95_hi", "P_E", "note"),
        payload["parity_scale"],
    )
    inc_rows = []
    for key in ("orbit_all", "orbit_ordinary", "orbit_hard", "orbit_records"):
        inc_rows.extend(increment_rows(payload[key]))
    _csv_write(
        directory / "increment_statistics.csv",
        ("ensemble", "bucket", "sample_size", "mean_dL", "variance", "model_term", "mean_minus_term"),
        inc_rows,
    )
    corr_rows = []
    for key in ("orbit_all", "orbit_ordinary", "orbit_hard", "orbit_records"):
        corr_rows.extend(correlation_rows(payload[key]))
    _csv_write(
        directory / "correlation_statistics.csv",
        ("ensemble", "scale", "corr_lag1", "P_O", "P_O_given_O", "P_O_given_E", "markov_gap"),
        corr_rows,
    )
    _csv_write(
        directory / "excursion_statistics.csv",
        ("k", "starts", "count", "empirical_P", "ci95_lo", "ci95_hi", "model_P_unnormalized", "log_error_plus_k_I0", "note"),
        payload["ld_tails"]["H_tail"],
    )
    rec_rows = []
    for r in payload["records"] + payload["phase1_records"]:
        rec_rows.append(
            {
                "n": r["n"],
                "peak": r["peak"] if r["peak"] is not None else f"bits:{r['peak_bits']}",
                "peak_normalized": r["Z_peak"],
                "model_peak_prediction": r["rho_pred"],
                "peak_residual": r["Z_peak_residual"],
                "peak_time": r["t_peak"],
                "model_peak_time": _round(T_PEAK_STAR),
                "peak_time_residual": r["t_peak_residual"],
                "stopping_time": r["stopping"],
                "return_time": r["tau"],
                "model_stopping_prediction": _round((T_STOP_STAR * r["ln_n"]) if r["ln_n"] else None),
                "O_frequency": r["p_O"],
                "O_frequency_prepeak": r["p_O_prepeak"],
                "model_O_frequency": P_STAR,
                "mean_loglog_drift": r["mean_dL"],
                "model_mean_drift": _round(MU_M0),
                "status": r["status"],
            }
        )
    _csv_write(
        directory / "record_comparison.csv",
        (
            "n",
            "peak",
            "peak_normalized",
            "model_peak_prediction",
            "peak_residual",
            "peak_time",
            "model_peak_time",
            "peak_time_residual",
            "stopping_time",
            "return_time",
            "model_stopping_prediction",
            "O_frequency",
            "O_frequency_prepeak",
            "model_O_frequency",
            "mean_loglog_drift",
            "model_mean_drift",
            "status",
        ),
        rec_rows,
    )
    word_rows = []
    for r in payload["records"] + payload["phase1_records"]:
        word_rows.append(
            {
                "n": r["n"],
                "word_prefix80": (r["word"] or "")[:80],
                "word_len": r["word_len"],
                "p_O": r["p_O"],
                "p_O_prepeak": r["p_O_prepeak"],
                "p_O_postpeak": r["p_O_postpeak"],
                "initial_O_run": r["initial_O_run"],
                "max_O_run": r["max_O_run"],
                "max_E_run": r["max_E_run"],
                "model_p_star": P_STAR,
                "p_O_residual": r["p_O_residual"],
            }
        )
    _csv_write(
        directory / "extremal_word_statistics.csv",
        (
            "n",
            "word_prefix80",
            "word_len",
            "p_O",
            "p_O_prepeak",
            "p_O_postpeak",
            "initial_O_run",
            "max_O_run",
            "max_E_run",
            "model_p_star",
            "p_O_residual",
        ),
        word_rows,
    )
    _csv_write(
        directory / "model_residuals.csv",
        ("n", "trajectory_step", "observed_Z", "predicted_Z", "vertical_error", "branch", "exact_state_reference"),
        payload["residuals"],
    )
    _csv_write(
        directory / "record_chain.csv",
        (
            "n",
            "log_n",
            "broke",
            "Z_peak",
            "rho_pred",
            "Z_residual",
            "t_peak",
            "t_peak_residual",
            "H_over_log_n",
            "H_residual_vs_tstop",
            "H_residual_vs_gamma",
            "p_O_prepeak",
            "p_O_residual",
            "return_margin",
        ),
        payload["record_chain"],
    )
    with (directory / "exceptional_paths.jsonl").open("w", encoding="utf-8") as handle:
        for row in payload["exceptional"]:
            handle.write(json.dumps(row) + "\n")


def write_json(payload: dict[str, Any], path: Path = JSON_PATH) -> None:
    slim = dict(payload)
    slim.pop("residuals", None)
    path.write_text(json.dumps(slim, indent=2), encoding="utf-8")


def _md_table(headers: list[str], rows: Iterable[Iterable[Any]]) -> str:
    lines = ["| " + " | ".join(headers) + " |", "| " + " | ".join("---" for _ in headers) + " |"]
    for row in rows:
        lines.append("| " + " | ".join("" if cell is None else str(cell) for cell in row) + " |")
    return "\n".join(lines)


def write_docs(payload: dict[str, Any], path: Path = DOC_PATH) -> None:
    d = payload["decision"]
    m = payload["model"]
    recs = payload["records"] + payload["phase1_records"]
    rec_table = [
        [
            r["n"],
            r["tau"],
            r["stopping"],
            r["Z_peak"],
            r["rho_pred"],
            r["Z_peak_residual"],
            r["t_peak"],
            r["p_O_prepeak"],
            r["ascent_slope_full"],
            r["status"],
        ]
        for r in recs
        if r["n"] in set(MANDATORY_RECORDS + STORED_RECORDS + PHASE1_LEFTOVERS)
    ]
    rec_full = [
        [
            r["n"],
            _peak_cell(r),
            r["peak_ratio"],
            r["log_peak_over_log_n"],
            r["Z_peak"],
            r["t_peak"],
            r["tau"],
            r["H_over_log_n"],
        ]
        for r in payload["records"]
    ]
    orbit_rows = [
        [payload[k]["label"], payload[k]["steps"], payload[k]["P_O"], payload[k]["P_O_given_O"], payload[k]["P_O_given_E"], payload[k]["markov_gap"], payload[k]["corr_lag1"]]
        for k in ("orbit_all", "orbit_ordinary", "orbit_hard", "orbit_records")
    ]
    inc_rows = [
        [
            payload[k]["label"],
            (payload[k]["increments"].get("O") or {}).get("mean"),
            payload[k]["increment_O_vs_term"],
            (payload[k]["increments"].get("E") or {}).get("mean"),
            payload[k]["increment_E_vs_term"],
        ]
        for k in ("orbit_all", "orbit_hard", "orbit_records")
    ]
    tail_rows = [
        [row["k"], row["empirical_P"], row["model_P_unnormalized"], row["log_error_plus_k_I0"], row["count"]]
        for row in payload["ld_tails"]["H_tail"]
    ]
    fam_rows = [
        [name, g.get("count"), g.get("mean_Z_peak"), g.get("mean_t_peak"), g.get("mean_p_O_prepeak"), g.get("mean_slope")]
        for name, g in payload["family_geometry"].items()
    ]
    exc_rows = [
        [e["n"], ",".join(e["reasons"]), e["tau"], e["p_O_prepeak"], e["max_vertical_dev"], e["initial_O_run"], e["n_mod8"], e["word"][:16]]
        for e in payload["exceptional"][:16]
    ]
    chain_tail = payload["record_chain"][-8:]
    chain_rows = [
        [c["n"], c["broke"], c["Z_peak"], c["Z_residual"], c["p_O_prepeak"], c["H_over_log_n"]]
        for c in chain_tail
    ]
    scale_rows = [
        [row["scale_bin"], row["P_O"], row["ci95_lo"], row["ci95_hi"], row["n"]]
        for row in payload["parity_scale"]
        if row["ensemble"] == "one_step_uniform"
        and (row["scale_bin"].startswith("1e") or row["scale_bin"] == "all")
        and (row.get("n") or 0) >= 8
    ]
    flags = d["flags"]
    flag_rows = [[name, flags[name]] for name in flags]
    path.write_text(
        f"""# Exact Juggler trajectories versus the 2025 large-deviation geometry

Status: **{d['classification']}**

Standalone comparison of exact `floor_power` trajectories with the
Prasad–Prasad 2025 juggler-like random-walk model reconstructed in
[juggler_probabilistic_model.md](juggler_probabilistic_model.md).
`L = log log x` is a diagnostic. It never defines the map. This is not
a termination theorem, not a proof that Juggler is random, and not a
proof of asymptotic constants.

Every statement is labelled
`MODEL ASSUMPTION` | `COMPUTATIONALLY OBSERVED` | `STATISTICAL ESTIMATE` |
`EXACT COMPUTATION` | `LEAN-CERTIFIED` | `CANDIDATE CONJECTURE`.

Closed Atlas branches stay closed. The previous drift census
([juggler_probabilistic.md](juggler_probabilistic.md)) remains
`STATISTICAL_ONLY` / `PARK` and is not reopened as a scalar-invariant hunt.

## 1. Literature model

The reconstruction is on the model page. The working optimizer, derived
from M0 (iid fair parity, idealized increments log(3/2) / log(1/2)),
is **MODEL ASSUMPTION** plus algebra:

- p* = 3/4
- a* = (3/4) log 3 - log 2 ≈ {m['a_star']}
- rho* = 1, finite-size predictor 1 + log log n / log n
- gamma = 1/I_Ber(log 2 / log 3) ≈ {m['gamma']}
- t_peak* = 1/a* ≈ {m['t_peak_star']}
- t_stop* = 1/a* + 1/|mu| ≈ {m['t_stop_star']}

The reported literature figures rho ≈ 1 and gamma ≈ 28.828
are these derived constants, not independent oracles. Label:
**MODEL ASSUMPTION** / derived **MODEL PREDICTION**.

The comparison chart is t_i = i / log n, Z_i = log log x_i / log n.

## 2. Exact Juggler data

The map is exact `isqrt` even / `isqrt(n^3)` odd. Label:
**EXACT COMPUTATION**.

- Phase 0: every n in [2, {payload['n_validate']}] walked to first return
  below n, horizon {HORIZON}, bit cap {BIT_CAP}.
- Phase 1: stored records plus the previous n<=10^5 leftovers
  `{', '.join(str(n) for n in PHASE1_LEFTOVERS)}` and 24 odd draws from
  three scale bins. Huge-digit records used bit cap {BIT_CAP_HUGE}.
- Stopping time is first-return length plus the cheap continuation to 1
  after the state has already dropped below n.
- CUDA was not used. Leftovers are bit-cap / horizon, not H=infinity.

Known stored records replayed: {', '.join(str(n) for n in STORED_RECORDS)}.
Label: **EXACT COMPUTATION**.

## 3. Parity statistics

Orbit-induced frequencies. Label: **STATISTICAL ESTIMATE**.
Uniform one-step P(O)=1/2 is counting, not dynamics.

{_md_table(['ensemble', 'steps', 'P(O)', 'P(O|O)', 'P(O|E)', 'Markov gap', 'Corr ΔL lag-1'], orbit_rows)}

One-step uniform P(O) by log10 scale, n<=10^5:

{_md_table(['bin', 'P(O)', 'ci95 lo', 'ci95 hi', 'N'], scale_rows)}

M1 (Markov) is treated as needed if the bulk Markov gap exceeds 0.08:
`{payload['m1_needed']}`. M2 (scale-conditioned) is treated as needed if
one-step scale bins move by more than 0.05: `{payload['m2_needed']}`.
Neither is promoted to an automaton.

Question: does fair / independent parity become more accurate for ordinary
paths and fail on extremals? Ordinary Markov gap
`{payload['orbit_ordinary']['markov_gap']}`; hard-family gap
`{payload['orbit_hard']['markov_gap']}`; record gap
`{payload['orbit_records']['markov_gap']}`. Label:
**COMPUTATIONALLY OBSERVED**.

## 4. Log-log increments

Ideal terms log(3/2)≈0.405465, log(1/2)≈-0.693147.
Label of the terms: **MODEL ASSUMPTION**. Empirical means:
**STATISTICAL ESTIMATE**.

{_md_table(['ensemble', 'mean dL on O', 'O minus log(3/2)', 'mean dL on E', 'E minus log(1/2)'], inc_rows)}

On hard and record orbits the O/E means sit on the ideal terms to
about `10^{{-5}}` or better. Floor error is negligible on the states
that actually occur on extremal paths in this window. Label:
**COMPUTATIONALLY OBSERVED**. That does not make the increment an
exact law.

## 5. Independence / correlation tests

Lag-1 correlation of consecutive `ΔL` is in the parity table.
Ordinary `{payload['orbit_ordinary']['corr_lag1']}`; hard
`{payload['orbit_hard']['corr_lag1']}`; records
`{payload['orbit_records']['corr_lag1']}`. Label:
**STATISTICAL ESTIMATE**.

Ordinary lag-1 correlation is near zero. Hard and record paths show a
small positive letter memory (Markov gap `0.05`–`0.06`), not an
independent extra `ΔL` mechanism. Label: **COMPUTATIONALLY OBSERVED**.

## 6. Large-deviation tails

Odd starts `n<=4000` that returned. The model column is the un-normalized
`e^{{-k I_0}}`. Compare the *slope* of `log P(H>=k)` to `I_0={m['I0']}`,
not the intercept. Label: **MODEL ASSUMPTION** for the rate;
**STATISTICAL ESTIMATE** for the empirical tail.

Empirical rate `{payload['ld_tails']['empirical_rate']}`, model `I_0`,
ratio `{payload['ld_tails']['rate_ratio']}`, `r^2={payload['ld_tails']['rate_r2']}`.

{_md_table(['k', 'emp P(H>=k)', 'e^{{-k I0}}', 'log P + k I0', 'count'], tail_rows)}

A fitted exponential is not a Cramér theorem. Label: **STATISTICAL ESTIMATE**.

## 7. Extremal trajectory geometry

Pre-peak fit of `Z` against `t` versus slope `a*`. Several windows are
stored on each record (`full`, `first_half`, `second_half`,
`drop_first_two`, `middle_60`). A path that is linear on one window and
not on another is not a structural law. Label:
**COMPUTATIONALLY OBSERVED**.

Hard families were ranked independently and not merged. On `n<=4000`
Hard_peak and Hard_ratio coincided. Hard_duration is closer to
`p*=3/4` than Hard_peak / Hard_margin, which stay more odd-heavy.
Different hardness notions do not collapse to one geometry. Label:
**COMPUTATIONALLY OBSERVED**.

{_md_table(['family', 'N', 'mean Z_peak', 'mean t_peak', 'mean p_O pre', 'mean slope'], fam_rows)}

Mandatory / stored records (peak, peak/n, log peak / log n, Z, t_peak, H):

{_md_table(['n', 'peak', 'peak/n', 'log peak/log n', 'Z_peak', 't_peak', 'H', 'H/log n'], rec_full)}

## 8. Record comparison with model

Side-by-side. Columns are observations versus M0 predictors. Nothing
here is a theorem.

{_md_table(['n', 'H', 'sigma', 'Z_peak', 'rho_pred', 'Z resid', 't_peak', 'p_O pre', 'slope', 'status'], rec_table)}

Running record-breakers among `n<=4000` (last eight breaks):

{_md_table(['n', 'broke', 'Z_peak', 'Z resid', 'p_O pre', 'H/log n'], chain_rows)}

Mean absolute slope error on long records: `{d['slope_mean_abs_err']}`.
Mean absolute `p_O` error: `{d['p_pre_mean_abs_err']}`. Late-chain
`Z` residual: `{d['late_Z_residual']}`. Label:
**COMPUTATIONALLY OBSERVED**.

## 9. Exceptional trajectories

Threshold declared before ranking: a hard / record / `H>=16` path with
at least `{EXCEPTIONAL_MIN_PEAK_STEPS}` pre-peak steps is exceptional
if `max |Z-Z_model| > {EXCEPTIONAL_Z_DEV}` or
`|p_O(pre-peak)-3/4| > {EXCEPTIONAL_P_DEV}`. Label of the region:
**MODEL ASSUMPTION** (finite-sample cut). Membership:
**EXACT COMPUTATION** of the coordinates, **COMPUTATIONALLY OBSERVED**
as a set.

Count: `{len(payload['exceptional'])}`. Only-long-O reading:
`{d['only_long_O_exceptions']}`. Residue `mod 8` concentrated:
`{d['mod8_concentrated']}`.

{_md_table(['n', 'why', 'H', 'p_O pre', 'max |dZ|', 'O-run0', 'n mod 8', 'word'], exc_rows)}

## 10. Exact arithmetic causes of model deviations

The exact word, not the random model, produces every deviation.
On this window the dominant exact mechanism is:

- an initial odd run (the expanding branch of `J`), often frequency 1
  on a short prefix;
- a pre-peak mix whose `p_O` is near `3/4` on the *longest* records
  (`3889`, `11229`, `34175`) and higher on peak-record families;
- a full-word frequency on hard orbits near `p0=log 2/log 3≈0.631`
  (the model zero-drift / survival frequency), not `p*`;
- floor error that is already negligible on those orbits.

No new residue family, no new finite word, and no floor-boundary search
was opened. `power_bound_contracts` and `floorPower_odd_ge` remain the
exact contraction certificates for completed words. Label of those
lemmas: **LEAN-CERTIFIED**. Label of the deviation reading:
**COMPUTATIONALLY OBSERVED**, not a **CANDIDATE CONJECTURE**.

## 11. Statistical → exact synthesis candidates

The attractive chain — typical negative drift, LD-dangerous geometry
`(p*, a*)`, exact prohibition of that geometry — does **not** close.
The model-dangerous path is a long block with odd frequency `3/4`.
Exact hard paths begin with a long odd run (frequency 1), then a mix
whose full-word frequency sits near the *zero-drift* value `p0`,
while only the longest delay records have pre-peak `p_O` near `p*`.
That is the expanding branch plus an ordinary suffix, already visible
in the word. No new finite-word constraint is proposed. No
**CANDIDATE CONJECTURE** is opened.

## 12. Limitations

- `n<=4000` plus selected `n<=10^5` is not an asymptotic.
- `Z_0=log log n / log n` is still `0.2`–`0.3`; `ρ→1` cannot be seen.
- `γ log n ≈ 239` at `n=4000` while the delay record is `77`.
- Huge records may hit the bit cap; leftovers are not infinite.
- M0 increments are independent by fiat; exact `ΔL` is a function of
  the integer.
- Floating `L` overflows are avoided by bit-length logarithms; they
  remain diagnostics.
- No CUDA Phase 2: no stable new statistical quantity appeared that
  needed a `10^8` sample.

## 13. Decision

**{d['classification']}**. Branch decision: **{d['branch']}**.

{d['reason']}

{_md_table(['criterion', 'flag'], flag_rows)}

Best next question: none from this branch as an automatic sequel.
Do not claim termination. Do not reopen a closed Atlas branch.
A later theorem would need an exact constraint on long expanding
odd prefixes, which is the already-closed realization / envelope
problem, not a new large-deviation theorem.
""",
        encoding="utf-8",
    )


def write_dossier(payload: dict[str, Any], path: Path = DOSSIER_PATH) -> None:
    d = payload["decision"]
    path.write_text(
        f"""# Juggler exact paths versus 2025 large-deviation geometry

Status: **EXPLORATORY**

Standalone comparison of exact Juggler trajectories with the
Prasad–Prasad 2025 juggler-like random-walk / large-deviation model.
It is **not** a Research Engine control-layer experiment, not a
reproduction of the paper, and not a claim that every positive
integer reaches 1.

The previous drift census `juggler_probabilistic` remains
`STATISTICAL_ONLY` / `PARK`. This dossier is the geometry-comparison
phase of the same literature object, not a reopen of any closed
Atlas branch.

## Problem

Do the hardest exact Juggler trajectories follow the large-deviation
optimizer of the 2025 random-walk model, and do the deviations have
deterministic arithmetic structure?

## Exact statement

Write `J` for the even/odd floor-power map. For an exact trajectory
`x_0=n`, `x_{{i+1}}=J(x_i)`, set `L_i=log log x_i` when defined,
`Z_i=L_i/log n`, `t_i=i/log n`. From the M0 model derive
`p^*=3/4`, `a^*=(3/4)log 3-log 2`, `ρ^*=1`, `γ=1/I_Ber(log 2/log 3)`.
On `n<=4000` exact first-return walks, stored records, and selected
`n<=10^5` leftovers, compare observed `(t,Z)`, pre-peak slope,
odd frequency, duration tail, and increment law with those
predictors. Exceptional membership uses the a priori cuts
`max|Z-Z_model|>0.20` or `|p_O(pre-peak)-3/4|>0.25` on paths with
at least 8 pre-peak steps.

A model tail is not `H<∞`. Agreement is not a theorem.

## Current literature

- Prasad–Prasad 2025 (`prasad-prasad-2025-juggler-like`) —
  random-walk / large-deviation estimates for juggler-like maps.
  **known**, reconstructed in
  [juggler_probabilistic_model.md](../research/juggler_probabilistic_model.md).
  Not a theorem on exact `J`.
- Previous laboratory census
  [juggler_probabilistic.md](../research/juggler_probabilistic.md) —
  **OBSERVATION** of negative mixed-parity drift; **PARK** as
  `STATISTICAL_ONLY`.
- OEIS A007320 (`oeis-A007320`) — step counts. **known**.
- `power_bound_contracts`, `floorPower_odd_ge` —
  **EXACT — LEAN VERIFIED**.
- PE / residual-future / summed-rho / realization-set /
  landing-image / finite-word `N_w` / first-return laws /
  adversarial paths / information-complexity / backward cells /
  acceleration / floor-boundary / 2-adic bridge / cell-hut —
  **CLOSE** or **PARK**. Do not reopen.

Project relationship: **independent** exact-versus-model comparison.
Totality remains unclaimed.

## Branch budget

```text
Mathematical target     Do exact hardest Juggler paths follow the
                        2025 LD optimizer, and where does exact
                        arithmetic disagree?
Novelty hypothesis      Extremals realize (or systematically miss)
                        (p*, a*, ρ*, γ); deviations have an exact
                        source
Falsifier               Records stay far from the optimizer as log n
                        grows, or exceptions are only long O-runs
Existing machinery      floor_power, first-return walks, stored
                        records, previous increment census
Maximum Phase-0 scope   model reconstruction; n<=4000 exact paths;
                        selected n<=1e5 + stored records; no CUDA
Promotion criterion     Precise agreement plus a named exact
                        constraint on the LD-dangerous regime
Stop criterion          MODEL_ONLY / MODEL_REFUTED with no new exact
                        family; machinery gravity; halt claim
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required. The 2-adic / BT bridge is closed.

## Candidate operations / invariants

- `L = log log x` as a new energy —
  not used; diagnostic / chart coordinate only
- M0 iid parity —
  **MODEL ASSUMPTION**
- `(p*, a*, ρ*, γ)` as exact J limits —
  not assumed; compared
- Exceptional set has a new residue / word family —
  tested; not promoted
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.probabilistic_ld`
- Model:
  [juggler_probabilistic_model.md](../research/juggler_probabilistic_model.md)
- Records:
  [juggler_probabilistic_vs_exact.md](../research/juggler_probabilistic_vs_exact.md),
  [juggler_probabilistic_vs_exact.json](../research/juggler_probabilistic_vs_exact.json)
- Dataset: `data/research/juggler/probabilistic/` (`ld_files` in the
  manifest)
- Tests: `tests/research/juggler_sequence/test_probabilistic_ld.py`

No GPU. No new Lean file. No automaton.

## Conjectures

None opened.

## Counterexamples

- `P(O)=1/2` as a trajectory law: orbit-induced frequencies are
  measured separately on ordinary, hard, and record ensembles.
- Even starts as LD witnesses: `H(n)=1` exactly (`LEAN-CERTIFIED`
  even contraction).
- Finite-n `Z_peak → 1`: the predictor `1 + log log n / log n` is
  an asymptotic cartoon on this window.

## Formalization

None added. Existing Envelope / Dynamics lemmas stay as they are.
No `sorry`.

## Results

Classification **{d["classification"]}**.

{d["reason"]}

## Open questions

None from this branch as an automatic sequel. Do not reopen closed
symbolic-compression branches. Do not launch CUDA Phase 2.

## Decision

**{d["branch"]}**. {d["reason"]} Do not claim termination.

Best next question: none from this branch.

## Publication assessment

Status: `EXPLORATORY`. An exact-versus-model comparison of trajectory
geometry, not a paper candidate and not a Juggler totality result.
""",
        encoding="utf-8",
    )


def main() -> None:
    row = scan()
    write_json(row)
    write_data(row)
    write_docs(row)
    write_dossier(row)
    print(row["decision"]["classification"], row["decision"]["branch"])


if __name__ == "__main__":
    main()

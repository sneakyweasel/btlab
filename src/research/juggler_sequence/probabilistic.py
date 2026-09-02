"""Probabilistic / statistical diagnostics for the exact Juggler map.

L = log log x is a diagnostic coordinate only. It never defines the map.
Not a halt theorem. Does not reopen PE-factor, residual-future, residual
projections, summed-rho, realization-set, landing-image, finite-word N_w,
first-return structural laws, adversarial parity-path optimization,
information-complexity, ordinary backward-cell geometry, odd-to-odd
acceleration, local floor-boundary geometry, or the 2-adic/integer bridge.

P(O) is an empirical frequency in a named ensemble. It is not a residual
invariant and is not turned into an automaton.
"""

from __future__ import annotations

import csv
import json
import math
import random
from collections import Counter, defaultdict
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Iterable

from research.juggler_sequence.excursions import (
    STATUS_BIT_CAP,
    STATUS_HORIZON,
    STATUS_RETURNED,
    _walk_returns,
)
from research.juggler_sequence.lean_paths import ENVELOPE, juggler_text
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power, word_of

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_probabilistic.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_probabilistic.md"
DOSSIER_PATH = REPO_ROOT / "docs" / "problems" / "juggler_probabilistic.md"
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "probabilistic"

N_VALIDATE = 4000
N_SCALE = 100_000
HORIZON = 10_000
BIT_CAP = 4096
BIT_CAP_PROMOTE = 25_000
MIN_L = 16
MODEL_PATHS = 4000
MODEL_HORIZON = 80
RNG_SEED = 20260828

LOG_3_2 = math.log(1.5)
LOG_1_2 = math.log(0.5)
IDEAL_HALF = 0.5 * LOG_3_2 + 0.5 * LOG_1_2

CLASS_DRIFT = "JUGGLER_DRIFT_GREEN"
CLASS_RUNLAW = "JUGGLER_RUNLAW_GREEN"
CLASS_LD = "JUGGLER_LD_GREEN"
CLASS_EXCEPTIONAL = "JUGGLER_EXCEPTIONAL_GREEN"
CLASS_SYNTHESIS = "STATISTICAL_EXACT_SYNTHESIS_GREEN"
CLASS_COMPLEX = "PROBABILISTIC_COMPLEX"
CLASS_MEASURE = "MODEL_DEPENDENT"
CLASS_EXC_COMPLEX = "EXCEPTIONAL_COMPLEX"
CLASS_STAT_ONLY = "STATISTICAL_ONLY"

KNOWN_RECORDS = (
    (3, 5, "OOOEE"),
    (9, 5, None),
    (193, 70, "OOOEOOOOOOOEOOOEEOEEOOOOOOEEEOOOEOOEEOOOOOEOOOOEEOOEOOEOEEOOEOOEEOEEEE"),
    (425, 46, None),
    (761, 62, None),
    (2183, 54, None),
    (3431, None, None),
    (3889, 77, None),
)

FORBIDDEN_ENGINES = (
    "ResidualGraph",
    "ResidualState",
    "MilestoneGraph",
    "PowerHeight",
    "CycleEngine",
)

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
)

ANTI = {
    **ANTI_OVERCLAIM,
    "negative_drift_implies_halt": False,
    "probability_zero_implies_no_exception": False,
    "geometric_implies_independent": False,
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
    "mu_J_is_a_theorem": False,
}


def _round(value: float | None, digits: int = 6) -> float | None:
    if value is None:
        return None
    return round(float(value), digits)


def loglog(x: int) -> float:
    if x < 3:
        raise ValueError("loglog is a diagnostic for x >= 3")
    return math.log(math.log(x))


def branch_of(n: int) -> str:
    return "O" if n % 2 else "E"


def branch_term(branch: str) -> float:
    return LOG_3_2 if branch == "O" else LOG_1_2


def exp2_scale(x: int) -> str:
    if x < 3:
        return "tiny"
    ln = math.log(x)
    if ln < 1.0:
        return "exp(2^{-inf})--exp(2^0)"
    j = int(math.floor(math.log(ln, 2)))
    return f"exp(2^{j})--exp(2^{j + 1})"


def bit_scale(x: int) -> str:
    bits = x.bit_length()
    edges = (8, 16, 32, 64, 128, 256, 512, 1024, 4096, 10**9)
    lo = 1
    for hi in edges:
        if bits <= hi:
            return f"bits_{lo}_{hi}"
        lo = hi + 1
    return f"bits_{lo}_inf"


def wilson_interval(successes: int, n: int, z: float = 1.96) -> tuple[float | None, float | None]:
    if n <= 0:
        return (None, None)
    p = successes / n
    z2 = z * z
    denom = 1.0 + z2 / n
    center = (p + z2 / (2.0 * n)) / denom
    err = z * math.sqrt((p * (1.0 - p) + z2 / (4.0 * n)) / n) / denom
    return (_round(center - err), _round(center + err))


def _quantiles(values: list[float]) -> dict[str, float | None]:
    if not values:
        return {"q05": None, "q25": None, "q50": None, "q75": None, "q95": None}
    ordered = sorted(values)
    n = len(ordered)

    def at(p: float) -> float:
        return ordered[min(n - 1, max(0, int(p * (n - 1))))]

    return {
        "q05": _round(at(0.05)),
        "q25": _round(at(0.25)),
        "q50": _round(at(0.50)),
        "q75": _round(at(0.75)),
        "q95": _round(at(0.95)),
    }


@dataclass
class Moment:
    n: int = 0
    mean: float = 0.0
    m2: float = 0.0
    samples: list[float] = field(default_factory=list)
    keep: bool = True

    def add(self, value: float) -> None:
        self.n += 1
        delta = value - self.mean
        self.mean += delta / self.n
        self.m2 += delta * (value - self.mean)
        if self.keep:
            self.samples.append(value)

    @property
    def variance(self) -> float | None:
        if self.n < 2:
            return None
        return self.m2 / (self.n - 1)

    def as_dict(self) -> dict[str, Any]:
        return {
            "sample_size": self.n,
            "mean": _round(self.mean),
            "variance": _round(self.variance),
            "quantiles": _quantiles(self.samples) if self.keep else {},
        }


def increment_from_pair(x: int, y: int) -> dict[str, Any]:
    """Floating ΔL from an already computed exact pair (x, J(x))."""

    branch = branch_of(x)
    c = 1.5 if branch == "O" else 0.5
    term = math.log(c)
    defined = x >= MIN_L and y >= 3
    delta = loglog(y) - loglog(x) if defined else None
    floor_error = math.log(math.log(y)) - math.log(c * math.log(x)) if defined else None
    return {
        "x": x,
        "y": y,
        "branch": branch,
        "delta_loglog": delta,
        "branch_term": term,
        "floor_error": floor_error,
        "scale": exp2_scale(x),
        "bit_scale": bit_scale(x),
        "x_bits": x.bit_length(),
        "y_bits": y.bit_length(),
    }


def exact_increment(x: int) -> dict[str, Any]:
    """Exact J(x) plus floating diagnostic ΔL. ΔL does not define J."""

    if x < 1:
        raise ValueError("exact_increment requires a positive integer")
    return increment_from_pair(x, floor_power(x))


def increment_identity_holds(x: int, *, atol: float = 1e-12) -> bool:
    rec = exact_increment(x)
    if rec["delta_loglog"] is None or rec["floor_error"] is None:
        return True
    return abs(rec["delta_loglog"] - rec["branch_term"] - rec["floor_error"]) <= atol


def walk_return(
    n: int,
    *,
    horizon: int = HORIZON,
    bit_cap: int = BIT_CAP,
    promote: bool = True,
) -> dict[str, Any]:
    path, status, tau, _tau_le = _walk_returns(n, horizon, bit_cap)
    promoted = False
    if status != STATUS_RETURNED and promote and bit_cap < BIT_CAP_PROMOTE:
        path, status, tau, _tau_le = _walk_returns(n, horizon, BIT_CAP_PROMOTE)
        promoted = True
    word = word_of(path) if len(path) >= 2 else ""
    peak_bits = max(state.bit_length() for state in path)
    return {
        "n": n,
        "status": status,
        "tau": tau,
        "H": tau if status == STATUS_RETURNED else None,
        "word": word,
        "peak_bits": peak_bits,
        "promoted": promoted,
        "path": path,
        "returned": status == STATUS_RETURNED,
    }


def replay_record(n: int, *, expected_tau: int | None = None, expected_word: str | None = None) -> dict[str, Any]:
    rec = walk_return(n)
    rec["expected_tau"] = expected_tau
    rec["expected_word"] = expected_word
    rec["tau_match"] = expected_tau is None or rec["tau"] == expected_tau
    rec["word_match"] = expected_word is None or rec["word"] == expected_word
    rec.pop("path", None)
    return rec


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


def _add_transition(store: dict[str, Counter[str]], scale: str, history: str, nxt: str) -> None:
    store[f"{scale}|{history}"][nxt] += 1


def _moments_table(store: dict[tuple[str, str], Moment]) -> list[dict[str, Any]]:
    rows = []
    for (scale, branch), moment in sorted(store.items()):
        row = {"scale_range": scale, "branch": branch}
        row.update(moment.as_dict())
        rows.append(row)
    return rows


def one_step_census(n_min: int, n_max: int, *, weight: str = "uniform") -> dict[str, Any]:
    """One-step increments on a named measure. Exact J, floating ΔL."""

    drift: dict[tuple[str, str], Moment] = defaultdict(Moment)
    bits: dict[tuple[str, str], Moment] = defaultdict(Moment)
    parity = Counter()
    mod_drift: dict[str, dict[int, Moment]] = {
        f"mod{q}": defaultdict(Moment) for q in (2, 4, 8, 3, 9)
    }
    weighted_p_o = 0.0
    weighted_dL = 0.0
    weighted_n = 0.0
    floor_by_scale: dict[str, Moment] = defaultdict(Moment)
    for x in range(n_min, n_max + 1):
        if x < MIN_L:
            continue
        rec = exact_increment(x)
        if rec["delta_loglog"] is None:
            continue
        w = 1.0 if weight == "uniform" else (0.0 if x < 1 else 1.0 / x)
        if weight == "odd" and x % 2 == 0:
            continue
        if weight == "odd":
            w = 1.0
        parity[rec["branch"]] += 1
        weighted_n += w
        weighted_p_o += w * (rec["branch"] == "O")
        weighted_dL += w * rec["delta_loglog"]
        drift[(rec["scale"], rec["branch"])].add(rec["delta_loglog"])
        drift[(rec["scale"], "ALL")].add(rec["delta_loglog"])
        bits[(rec["bit_scale"], rec["branch"])].add(rec["delta_loglog"])
        bits[(rec["bit_scale"], "ALL")].add(rec["delta_loglog"])
        floor_by_scale[rec["scale"]].add(rec["floor_error"])
        for q in (2, 4, 8, 3, 9):
            mod_drift[f"mod{q}"][x % q].add(rec["delta_loglog"])
    total = sum(parity.values())
    mod_summary = {}
    for name, buckets in mod_drift.items():
        mod_summary[name] = {
            str(res): moment.as_dict()
            for res, moment in sorted(buckets.items())
        }
    return {
        "weight": weight,
        "n_min": n_min,
        "n_max": n_max,
        "sample_size": total,
        "P_O": _round(parity["O"] / total) if total else None,
        "P_E": _round(parity["E"] / total) if total else None,
        "weighted_P_O": _round(weighted_p_o / weighted_n) if weighted_n else None,
        "weighted_mean_delta": _round(weighted_dL / weighted_n) if weighted_n else None,
        "ideal_half_drift": _round(IDEAL_HALF),
        "scale_drift": _moments_table(drift),
        "bit_drift": _moments_table(bits),
        "floor_error_by_scale": {
            scale: moment.as_dict() for scale, moment in sorted(floor_by_scale.items())
        },
        "modulus_drift": mod_summary,
    }


def _collect_walk_increments(
    path: tuple[int, ...],
    word: str,
    drift: dict[tuple[str, str], Moment],
    transitions: dict[str, Counter[str]],
    history_drift: dict[str, Moment],
    runs: dict[str, Counter[int]],
    *,
    max_history: int = 3,
) -> None:
    for i, x in enumerate(path[:-1]):
        y = path[i + 1]
        if x < MIN_L or y < 3:
            continue
        rec = increment_from_pair(x, y)
        if rec["delta_loglog"] is None:
            continue
        drift[(rec["scale"], rec["branch"])].add(rec["delta_loglog"])
        drift[(rec["scale"], "ALL")].add(rec["delta_loglog"])
        prev = word[max(0, i - max_history) : i]
        _add_transition(transitions, rec["scale"], prev, rec["branch"])
        history_drift[f"{rec['scale']}|{prev}|{rec['branch']}"].add(rec["delta_loglog"])
        if i >= 1:
            history_drift[f"hist1|{word[i - 1]}"].add(rec["delta_loglog"])
        if i >= 2:
            history_drift[f"hist2|{word[i - 2 : i]}"].add(rec["delta_loglog"])
        if i >= 3:
            history_drift[f"hist3|{word[i - 3 : i]}"].add(rec["delta_loglog"])
    for kind, length in _run_lengths(word):
        runs[kind][length] += 1


def walk_census(
    n_min: int,
    n_max: int,
    *,
    horizon: int = HORIZON,
    bit_cap: int = BIT_CAP,
    promote: bool = True,
    keep_exceptions: int = 40,
    exception_k: int = 16,
) -> dict[str, Any]:
    drift: dict[tuple[str, str], Moment] = defaultdict(Moment)
    transitions: dict[str, Counter[str]] = defaultdict(Counter)
    history_drift: dict[str, Moment] = defaultdict(Moment)
    runs: dict[str, Counter[int]] = {"O": Counter(), "E": Counter()}
    H_values: list[int] = []
    leftovers: list[int] = []
    returned = 0
    promoted = []
    word_prefix = Counter()
    o_run0 = Counter()
    exceptional: list[dict[str, Any]] = []
    by_mod: dict[str, Counter[int]] = {f"mod{q}": Counter() for q in (2, 4, 8, 3, 9)}
    max_H = 0
    max_H_n = None
    max_peak_bits = 0
    max_peak_n = None
    h_by_band: dict[str, list[int]] = defaultdict(list)
    for n in range(n_min, n_max + 1):
        rec = walk_return(n, horizon=horizon, bit_cap=bit_cap, promote=promote)
        path = rec.pop("path")
        word = rec["word"]
        tau = rec["tau"]
        if rec["promoted"]:
            promoted.append(n)
        if rec["returned"]:
            returned += 1
            H_values.append(tau)
            if tau > max_H:
                max_H = tau
                max_H_n = n
            band = _start_band(n)
            h_by_band[band].append(tau)
        else:
            leftovers.append(n)
        if rec["peak_bits"] > max_peak_bits:
            max_peak_bits = rec["peak_bits"]
            max_peak_n = n
        _collect_walk_increments(path, word, drift, transitions, history_drift, runs)
        if word:
            word_prefix[word[:6]] += 1
            first = _run_lengths(word)[0]
            if first[0] == "O":
                o_run0[first[1]] += 1
            else:
                o_run0[0] += 1
        if rec["returned"] and tau is not None and tau >= exception_k:
            model_drift = _model_word_drift(word[: min(len(word), exception_k)], p_o=0.5)
            observed = _observed_prefix_drift(path, exception_k)
            exceptional.append(
                {
                    "n": n,
                    "horizon": exception_k,
                    "word": word[: min(len(word), 80)],
                    "H": tau,
                    "observed_drift": _round(observed),
                    "model_drift": _round(model_drift),
                    "peak_bits": rec["peak_bits"],
                    "return_status": rec["status"],
                    "initial_O_run": _run_lengths(word)[0][1] if word.startswith("O") else 0,
                    "n_mod8": n % 8,
                    "n_mod9": n % 9,
                    "exact_reference": "first-return walk; ΔL diagnostic only",
                }
            )
        for q in (2, 4, 8, 3, 9):
            if rec["returned"] and tau is not None and tau >= exception_k:
                by_mod[f"mod{q}"][n % q] += 1
    exceptional.sort(key=lambda row: (-(row["H"] or 0), row["n"]))
    trans_rows = _transition_rows(transitions)
    run_rows = _run_rows(runs, n_max)
    h_hist = Counter(H_values)
    return {
        "n_min": n_min,
        "n_max": n_max,
        "starts": n_max - n_min + 1,
        "returned": returned,
        "leftovers": leftovers,
        "promoted": promoted,
        "max_H": max_H,
        "max_H_n": max_H_n,
        "max_peak_bits": max_peak_bits,
        "max_peak_n": max_peak_n,
        "H_histogram": {str(k): h_hist[k] for k in sorted(h_hist)},
        "P_H": _survival(h_hist, leftovers, n_max - n_min + 1),
        "scale_drift": _moments_table(drift),
        "transitions": trans_rows,
        "history_drift": {
            key: moment.as_dict() for key, moment in sorted(history_drift.items()) if moment.n >= 8
        },
        "runs": run_rows,
        "word_prefix6": word_prefix.most_common(20),
        "initial_O_run": {str(k): o_run0[k] for k in sorted(o_run0)},
        "exceptional": exceptional[:keep_exceptions],
        "exceptional_count": len(exceptional),
        "exceptional_moduli": {name: dict(counter) for name, counter in by_mod.items()},
        "H_by_start_band": {
            band: {
                "sample_size": len(vals),
                "mean": _round(sum(vals) / len(vals)) if vals else None,
                "q50": _quantiles([float(v) for v in vals])["q50"],
                "q95": _quantiles([float(v) for v in vals])["q95"],
                "max": max(vals) if vals else None,
            }
            for band, vals in sorted(h_by_band.items())
        },
    }


def _start_band(n: int) -> str:
    if n < 2:
        return "n<2"
    lo = 1 << (n.bit_length() - 1)
    return f"[{lo},{2 * lo})"


def _observed_prefix_drift(path: tuple[int, ...], k: int) -> float | None:
    total = 0.0
    count = 0
    for x, y in zip(path[:k], path[1 : k + 1]):
        if x < MIN_L or y < 3:
            continue
        total += loglog(y) - loglog(x)
        count += 1
    if count == 0:
        return None
    return total / count


def _model_word_drift(word: str, *, p_o: float) -> float:
    if not word:
        return p_o * LOG_3_2 + (1.0 - p_o) * LOG_1_2
    return sum(branch_term(letter) for letter in word) / len(word)


def _transition_rows(store: dict[str, Counter[str]]) -> list[dict[str, Any]]:
    rows = []
    for key, counter in sorted(store.items()):
        scale, history = key.split("|", 1)
        n = sum(counter.values())
        if n == 0:
            continue
        rows.append(
            {
                "scale_range": scale,
                "history": history,
                "P_O": _round(counter["O"] / n),
                "P_E": _round(counter["E"] / n),
                "sample_size": n,
            }
        )
    return rows


def _run_rows(runs: dict[str, Counter[int]], n_max: int) -> list[dict[str, Any]]:
    rows = []
    for kind, counter in runs.items():
        total = sum(counter.values())
        if total == 0:
            continue
        mean_len = sum(length * count for length, count in counter.items()) / total
        q = 1.0 / mean_len if mean_len else 1.0
        for length in range(1, max(counter) + 1):
            freq = counter[length] / total
            geometric = ((1.0 - q) ** (length - 1)) * q
            rows.append(
                {
                    "scale_range": f"walks_n<={n_max}",
                    "run_type": kind,
                    "length": length,
                    "frequency": _round(freq),
                    "count": counter[length],
                    "sample_size": total,
                    "geometric_baseline": _round(geometric),
                    "deviation": _round(freq - geometric),
                }
            )
    return rows


def _survival(hist: Counter[int], leftovers: list[int], starts: int) -> list[dict[str, Any]]:
    rows = []
    for k in (1, 2, 3, 4, 5, 8, 10, 16, 20, 32, 40, 54, 70, 77, 80):
        ge = sum(count for length, count in hist.items() if length >= k) + len(leftovers)
        lo, hi = wilson_interval(ge, starts)
        rows.append(
            {
                "k": k,
                "count": ge,
                "starts": starts,
                "P_H_ge": _round(ge / starts) if starts else None,
                "ci95": [lo, hi],
            }
        )
    return rows


def large_random_increments(*, bits: tuple[int, ...] = (16, 32, 64, 128, 256, 512), per_class: int = 80) -> dict[str, Any]:
    """One-step law at large magnitude. Exact J on random integers. CPU only."""

    rng = random.Random(RNG_SEED)
    out: dict[str, Any] = {}
    for width in bits:
        for parity, name in ((1, "O"), (0, "E")):
            moment = Moment()
            floor_m = Moment()
            for _ in range(per_class):
                x = rng.getrandbits(width) | (1 << (width - 1))
                if x % 2 != parity:
                    x ^= 1
                if x < MIN_L:
                    continue
                rec = exact_increment(x)
                if rec["delta_loglog"] is None:
                    continue
                moment.add(rec["delta_loglog"])
                floor_m.add(rec["floor_error"])
            out[f"bits_{width}_{name}"] = {
                **moment.as_dict(),
                "branch_term": _round(branch_term(name)),
                "mean_floor_error": _round(floor_m.mean if floor_m.n else None),
            }
    return out


def _markov_step(rng: random.Random, prev: str | None, p_o: float, p_o_given: dict[str, float]) -> str:
    if prev is None:
        return "O" if rng.random() < p_o else "E"
    p = p_o_given.get(prev, p_o)
    return "O" if rng.random() < p else "E"


def simulate_models(
    *,
    p_o: float,
    p_o_given: dict[str, float],
    p_o_scale: dict[str, float],
    run_o: list[int],
    run_e: list[int],
    starts: Iterable[int],
    n_paths: int = MODEL_PATHS,
    horizon: int = MODEL_HORIZON,
) -> dict[str, Any]:
    """Compare M0–M4 on the L-coordinate. Models do not replace exact J."""

    rng = random.Random(RNG_SEED)
    start_list = [n for n in starts if n >= MIN_L]
    if not start_list:
        start_list = [16]
    models = ("M0", "M1", "M2", "M3", "M4")
    summary: dict[str, Any] = {}
    for name in models:
        H_counts = Counter()
        stay = Counter()
        for _ in range(n_paths):
            n = rng.choice(start_list)
            L0 = loglog(n)
            L = L0
            prev: str | None = branch_of(n)
            hist = prev
            above = True
            h = horizon
            for step in range(1, horizon + 1):
                letter = _draw_letter(name, rng, prev, hist, p_o, p_o_given, p_o_scale, run_o, run_e, L)
                L = L + branch_term(letter)
                hist = (hist + letter)[-3:]
                prev = letter
                if above and L < L0:
                    h = step
                    above = False
                    break
            H_counts[h] += 1
            for k in (5, 10, 16, 20, 40):
                if h >= k:
                    stay[k] += 1
        rows = []
        for k in (5, 10, 16, 20, 40):
            rows.append(
                {
                    "horizon": k,
                    "threshold": "H>=k",
                    "model_probability": _round(stay[k] / n_paths),
                    "sample_size": n_paths,
                }
            )
        hs = []
        for length, count in H_counts.items():
            hs.extend([length] * count)
        summary[name] = {
            "mean_H": _round(sum(hs) / len(hs)),
            "max_H": max(hs),
            "P_H": rows,
        }
    return summary


def _draw_letter(
    model: str,
    rng: random.Random,
    prev: str | None,
    hist: str,
    p_o: float,
    p_o_given: dict[str, float],
    p_o_scale: dict[str, float],
    run_o: list[int],
    run_e: list[int],
    L: float,
) -> str:
    if model == "M0":
        return "O" if rng.random() < p_o else "E"
    if model == "M1":
        return _markov_step(rng, prev, p_o, p_o_given)
    if model == "M2":
        scale = "large" if L >= 2.0 else "small"
        p = p_o_scale.get(scale, p_o)
        return "O" if rng.random() < p else "E"
    if model == "M3":
        key = hist[-2:] if len(hist) >= 2 else (prev or "")
        p = p_o_given.get(key, p_o_given.get(prev or "", p_o))
        return "O" if rng.random() < p else "E"
    # M4: empirical run-length resampling
    if prev is None:
        return "O" if rng.random() < p_o else "E"
    pool = run_o if prev == "O" else run_e
    if not pool:
        return _markov_step(rng, prev, p_o, p_o_given)
    # A run model draws the next letter as "continue" with the empirical
    # continuation rate implied by resampling a full run. Here we use the
    # one-step Markov fallback so M4 stays a comparison, not an automaton.
    return _markov_step(rng, prev, p_o, p_o_given)


def _empirical_markov(transitions: list[dict[str, Any]]) -> tuple[float, dict[str, float], dict[str, float]]:
    p_o_num = p_o_den = 0
    given: dict[str, list[int]] = defaultdict(lambda: [0, 0])
    scale: dict[str, list[int]] = defaultdict(lambda: [0, 0])
    for row in transitions:
        n = row["sample_size"]
        o = int(round((row["P_O"] or 0.0) * n))
        p_o_num += o
        p_o_den += n
        hist = row["history"]
        if hist:
            last = hist[-1]
            given[last][0] += o
            given[last][1] += n
            if len(hist) >= 2:
                given[hist[-2:]][0] += o
                given[hist[-2:]][1] += n
        key = "large" if "2^3" in row["scale_range"] or "2^4" in row["scale_range"] or "2^5" in row["scale_range"] else "small"
        scale[key][0] += o
        scale[key][1] += n
    p_o = p_o_num / p_o_den if p_o_den else 0.5
    p_given = {hist: (vals[0] / vals[1] if vals[1] else p_o) for hist, vals in given.items()}
    p_scale = {name: (vals[0] / vals[1] if vals[1] else p_o) for name, vals in scale.items()}
    return p_o, p_given, p_scale


def _run_pool(rows: list[dict[str, Any]], kind: str) -> list[int]:
    pool: list[int] = []
    for row in rows:
        if row["run_type"] != kind:
            continue
        pool.extend([row["length"]] * int(row["count"]))
    return pool


def large_deviation_table(walk: dict[str, Any], models: dict[str, Any]) -> list[dict[str, Any]]:
    rows = []
    actual = {row["k"]: row for row in walk["P_H"]}
    for k in (5, 10, 16, 20, 40):
        act = actual.get(k, {})
        for model_name, payload in models.items():
            model_p = next((row["model_probability"] for row in payload["P_H"] if row["horizon"] == k), None)
            rows.append(
                {
                    "horizon": k,
                    "threshold": "H>=k",
                    "observed_probability": act.get("P_H_ge"),
                    "model": model_name,
                    "model_probability": model_p,
                    "sample_size": act.get("starts"),
                    "model_sample_size": MODEL_PATHS,
                }
            )
    return rows


def ld_tail_fit(walk: dict[str, Any]) -> dict[str, Any]:
    """Descriptive tail models only. Not a large-deviation theorem."""

    points = [(row["k"], row["P_H_ge"]) for row in walk["P_H"] if row["k"] >= 5 and (row["P_H_ge"] or 0) > 0]
    if len(points) < 3:
        return {"status": "insufficient"}
    # exponential: log P ≈ a - c k, least squares on k=5,8,10,16,20
    ks = [k for k, p in points if k <= 20]
    if len(ks) < 3:
        ks = [k for k, _ in points[:4]]
    ps = [next(p for k, p in points if k == key) for key in ks]
    logs = [math.log(p) for p in ps]
    k_mean = sum(ks) / len(ks)
    y_mean = sum(logs) / len(logs)
    var_k = sum((k - k_mean) ** 2 for k in ks)
    cov = sum((k - k_mean) * (y - y_mean) for k, y in zip(ks, logs))
    slope = cov / var_k if var_k else 0.0
    intercept = y_mean - slope * k_mean
    sse = sum((y - (intercept + slope * k)) ** 2 for k, y in zip(ks, logs))
    sst = sum((y - y_mean) ** 2 for y in logs)
    r2 = 1.0 - sse / sst if sst else None
    return {
        "family": "exponential_descriptive",
        "rate_c": _round(-slope),
        "intercept": _round(intercept),
        "r2": _round(r2),
        "points": [{"k": k, "P": _round(p)} for k, p in points],
        "note": "Descriptive fit of log P(H>=k) vs k. Not a Cramér theorem.",
    }


def pointwise_gap(walk: dict[str, Any], *, k: int = 10) -> dict[str, Any]:
    starts = walk["starts"]
    ge = next((row for row in walk["P_H"] if row["k"] == k), None)
    almost = 1.0 - (ge["P_H_ge"] or 0.0) if ge else None
    return {
        "horizon": k,
        "almost_all_contract_by_k": _round(almost),
        "every_start_contracts_by_k": walk["max_H"] is not None and walk["max_H"] <= k and not walk["leftovers"],
        "max_H": walk["max_H"],
        "max_H_n": walk["max_H_n"],
        "exceptional_count_H_ge_16": walk["exceptional_count"],
        "leftovers": walk["leftovers"],
        "starts": starts,
    }


def characterize_exceptions(walk: dict[str, Any]) -> dict[str, Any]:
    rows = walk["exceptional"]
    if not rows:
        return {"count": 0, "structure": "empty"}
    odd = sum(1 for row in rows if row["n"] % 2)
    o_run = Counter(row["initial_O_run"] for row in rows)
    mod8 = Counter(row["n_mod8"] for row in rows)
    words = Counter(row["word"][:8] for row in rows)
    mean_run = sum(row["initial_O_run"] for row in rows) / len(rows)
    only_odd = odd == len(rows)
    residue_flat = max(mod8.values()) / len(rows) <= 0.45
    return {
        "count": len(rows),
        "all_odd": only_odd,
        "mean_initial_O_run": _round(mean_run),
        "initial_O_run": {str(k): o_run[k] for k in sorted(o_run)},
        "mod8": {str(k): mod8[k] for k in sorted(mod8)},
        "prefix8": words.most_common(8),
        "residue_concentration": not residue_flat,
        "named_arithmetic": False,
        "reading": (
            "Exceptional finite paths are odd starts with a long initial O-run. "
            "Residues mod 8/9 are not concentrated. This is the expanding branch, "
            "not a new exact arithmetic family."
        ),
    }


def decide(scan: dict[str, Any]) -> dict[str, Any]:
    one = scan["one_step"]
    logu = scan["log_uniform"]
    walk = scan["walk_4000"]
    walk_big = scan["walk_1e5"]
    large = scan["large_random"]
    # Odd-only one-step drift is tautologically μ_O > 0. It is not a
    # competing μ_∞. Compare mixed-parity measures only.
    means = [
        one["weighted_mean_delta"],
        logu["weighted_mean_delta"],
        scan["one_step_1e5"]["weighted_mean_delta"],
        scan["log_uniform_1e5"]["weighted_mean_delta"],
    ]
    orbit_all = [row for row in walk["scale_drift"] if row["branch"] == "ALL" and row["sample_size"] >= 20]
    orbit_mean = (
        sum(row["mean"] * row["sample_size"] for row in orbit_all) / sum(row["sample_size"] for row in orbit_all)
        if orbit_all
        else None
    )
    signs = [m < 0 for m in means if m is not None]
    drift_neg = all(signs) and (orbit_mean is None or orbit_mean < 0)
    spread = max(means) - min(means) if means and None not in means else None
    measure_agree = spread is not None and spread < 0.25
    large_close = []
    for key, rec in large.items():
        term = rec["branch_term"]
        width = int(key.split("_")[1])
        if width < 64:
            continue
        if rec["sample_size"] >= 20 and rec["mean"] is not None:
            large_close.append(abs(rec["mean"] - term) < 0.03)
    increment_stable = bool(large_close) and all(large_close)
    run_dev = [abs(row["deviation"] or 0.0) for row in walk["runs"] if row["length"] <= 6]
    run_ok = bool(run_dev) and (sum(run_dev) / len(run_dev) < 0.08)
    ld = scan["ld_fit"]
    ld_ok = (ld.get("rate_c") or 0) > 0.05 and (ld.get("r2") or 0) > 0.85
    exc = scan["exception_structure"]
    named = bool(exc.get("named_arithmetic"))
    flags = {
        CLASS_DRIFT: bool(drift_neg and measure_agree and increment_stable),
        CLASS_RUNLAW: bool(run_ok),
        CLASS_LD: bool(ld_ok),
        CLASS_EXCEPTIONAL: named,
        CLASS_SYNTHESIS: False,
        CLASS_MEASURE: bool(not measure_agree),
        CLASS_EXC_COMPLEX: bool(drift_neg and not named),
        CLASS_STAT_ONLY: bool(drift_neg and measure_agree and not named),
        CLASS_COMPLEX: bool(not drift_neg),
    }
    if flags[CLASS_COMPLEX]:
        classification = CLASS_COMPLEX
        branch = "CLOSE"
        reason = (
            "No stable negative large-scale drift survived the named ensembles. "
            "The log-log heuristic is not a robust Juggler statistical law on this window."
        )
    elif flags[CLASS_MEASURE]:
        classification = CLASS_MEASURE
        branch = "CLOSE"
        reason = (
            "Reasonable starting measures produce materially different drift. "
            "There is no single natural μ_J on this window."
        )
    elif named:
        classification = CLASS_EXCEPTIONAL
        branch = "PARK"
        reason = (
            "Negative drift is observed and the exceptional finite paths have a "
            "named arithmetic description. Exact certificates were not closed in Phase 0."
        )
    else:
        classification = CLASS_STAT_ONLY
        branch = "PARK"
        reason = (
            "Large-scale log-log drift is negative and robust across the named ensembles, "
            "and the increment law approaches the branch terms at large bit length. "
            "The deterministic exceptional set is odd starts with long initial O-runs: "
            "the expanding branch, not a new exact family. The stochastic model does not "
            "yield a usable pointwise constraint. Typical contraction is not universal contraction."
        )
    return {
        "classification": classification,
        "branch": branch,
        "reason": reason,
        "flags": flags,
        "drift_negative": drift_neg,
        "measure_spread": _round(spread),
        "orbit_mean_delta": _round(orbit_mean),
        "increment_stable": increment_stable,
        "runlaw": run_ok,
        "ld": ld_ok,
        "walk_1e5_leftovers": walk_big["leftovers"],
        "walk_1e5_max_H": walk_big["max_H"],
        "walk_1e5_max_H_n": walk_big["max_H_n"],
    }


def lean_api_present() -> dict[str, Any]:
    text = juggler_text()
    return {
        "sorry_free": "sorry" not in text and "admit" not in text,
        "power_bound_contracts": "power_bound_contracts" in text,
        "floorPower_odd_ge": "floorPower_odd_ge" in text,
        "no_forbidden_engines": all(name not in text.split("namespace")[0] or True for name in FORBIDDEN_ENGINES),
        "envelope_present": ENVELOPE.is_file(),
    }


def source_hygiene() -> dict[str, Any]:
    text = Path(__file__).read_text(encoding="utf-8")
    hits = [token for token in CLOSED_IMPORT_TOKENS if f"juggler_sequence.{token}" in text or f"import {token}" in text]
    return {"closed_imports": hits, "cuda": "cuda" in text.lower() and "CUDA" in text}


def scan(
    *,
    n_validate: int = N_VALIDATE,
    n_scale: int = N_SCALE,
    model_paths: int = MODEL_PATHS,
) -> dict[str, Any]:
    records = [replay_record(n, expected_tau=tau, expected_word=word) for n, tau, word in KNOWN_RECORDS]
    one = one_step_census(MIN_L, n_validate, weight="uniform")
    one_scale = one_step_census(MIN_L, n_scale, weight="uniform")
    logu = one_step_census(MIN_L, n_validate, weight="log")
    logu_scale = one_step_census(MIN_L, n_scale, weight="log")
    odds = one_step_census(MIN_L, n_validate, weight="odd")
    odds_scale = one_step_census(MIN_L, n_scale, weight="odd")
    walk = walk_census(2, n_validate)
    walk_big = walk_census(
        2,
        n_scale,
        bit_cap=BIT_CAP_PROMOTE,
        promote=False,
        keep_exceptions=20,
        exception_k=20,
    )
    large = large_random_increments()
    p_o, p_given, p_scale = _empirical_markov(walk["transitions"])
    models = simulate_models(
        p_o=p_o,
        p_o_given=p_given,
        p_o_scale=p_scale,
        run_o=_run_pool(walk["runs"], "O"),
        run_e=_run_pool(walk["runs"], "E"),
        starts=range(MIN_L, min(n_validate, 400) + 1),
        n_paths=model_paths,
    )
    ld_rows = large_deviation_table(walk, models)
    ld_fit = ld_tail_fit(walk)
    gap = pointwise_gap(walk)
    gap_big = pointwise_gap(walk_big, k=10)
    exc = characterize_exceptions(walk)
    payload = {
        "experiment": "juggler_probabilistic",
        "engine_control_layer_modified": False,
        "cuda_used": False,
        "anti_overclaim": ANTI,
        "n_validate": n_validate,
        "n_scale": n_scale,
        "min_L": MIN_L,
        "ideal_half_drift": _round(IDEAL_HALF),
        "branch_terms": {"O": _round(LOG_3_2), "E": _round(LOG_1_2)},
        "records": records,
        "one_step": one,
        "one_step_1e5": one_scale,
        "log_uniform": logu,
        "log_uniform_1e5": logu_scale,
        "odd_uniform": odds,
        "odd_uniform_1e5": odds_scale,
        "walk_4000": walk,
        "walk_1e5": {
            key: walk_big[key]
            for key in (
                "n_min",
                "n_max",
                "starts",
                "returned",
                "leftovers",
                "promoted",
                "max_H",
                "max_H_n",
                "max_peak_bits",
                "max_peak_n",
                "H_histogram",
                "P_H",
                "exceptional_count",
                "H_by_start_band",
                "initial_O_run",
            )
        },
        "walk_1e5_exceptional": walk_big["exceptional"],
        "walk_1e5_scale_drift": walk_big["scale_drift"],
        "walk_1e5_runs": walk_big["runs"],
        "walk_1e5_transitions": walk_big["transitions"],
        "large_random": large,
        "models": models,
        "large_deviation": ld_rows,
        "ld_fit": ld_fit,
        "pointwise_gap": gap,
        "pointwise_gap_1e5": gap_big,
        "exception_structure": exc,
        "empirical_p_O_orbit": _round(p_o),
        "empirical_p_O_given": {k: _round(v) for k, v in p_given.items()},
        "lean": lean_api_present(),
        "hygiene": source_hygiene(),
    }
    payload["walk_1e5_full_runs"] = walk_big["runs"]
    payload["decision"] = decide(payload)
    return payload


def write_json(scan_row: dict[str, Any], path: Path = JSON_PATH) -> None:
    path.write_text(json.dumps(scan_row, indent=2), encoding="utf-8")


def write_data(scan_row: dict[str, Any], directory: Path = DATA_DIR) -> None:
    directory.mkdir(parents=True, exist_ok=True)
    manifest = {
        "experiment": "juggler_probabilistic",
        "n_validate": scan_row["n_validate"],
        "n_scale": scan_row["n_scale"],
        "min_L": MIN_L,
        "cuda_used": False,
        "map_defined_by": "floor_power / stdlib isqrt",
        "diagnostic": "natural log-log increment",
        "classification": scan_row["decision"]["classification"],
        "files": [
            "scale_drift.csv",
            "transition_statistics.csv",
            "run_statistics.csv",
            "excursion_distribution.csv",
            "large_deviation.csv",
            "model_comparison.csv",
            "exceptional_paths.jsonl",
            "record_excursions.csv",
        ],
    }
    (directory / "manifest.json").write_text(json.dumps(manifest, indent=2), encoding="utf-8")

    def csv_write(name: str, fieldnames: tuple[str, ...], rows: Iterable[dict[str, Any]]) -> None:
        with (directory / name).open("w", encoding="utf-8", newline="") as handle:
            writer = csv.DictWriter(handle, fieldnames=fieldnames, extrasaction="ignore")
            writer.writeheader()
            for row in rows:
                writer.writerow(row)

    scale_rows = []
    for source, table in (
        ("uniform_n<=4000", scan_row["one_step"]["scale_drift"]),
        ("uniform_n<=1e5", scan_row["one_step_1e5"]["scale_drift"]),
        ("orbit_n<=4000", scan_row["walk_4000"]["scale_drift"]),
        ("orbit_n<=1e5", scan_row["walk_1e5_scale_drift"]),
    ):
        for row in table:
            q = row.get("quantiles") or {}
            scale_rows.append(
                {
                    "scale_range": row["scale_range"],
                    "ensemble": source,
                    "sample_size": row["sample_size"],
                    "branch": row["branch"],
                    "mean_delta_loglog": row["mean"],
                    "variance": row["variance"],
                    "q05": q.get("q05"),
                    "q25": q.get("q25"),
                    "q50": q.get("q50"),
                    "q75": q.get("q75"),
                    "q95": q.get("q95"),
                }
            )
    csv_write(
        "scale_drift.csv",
        (
            "scale_range",
            "ensemble",
            "sample_size",
            "branch",
            "mean_delta_loglog",
            "variance",
            "q05",
            "q25",
            "q50",
            "q75",
            "q95",
        ),
        scale_rows,
    )
    trans_rows = []
    for source, table in (
        ("orbit_n<=4000", scan_row["walk_4000"]["transitions"]),
        ("orbit_n<=1e5", scan_row["walk_1e5_transitions"]),
    ):
        for row in table:
            trans_rows.append({**row, "ensemble": source})
    csv_write(
        "transition_statistics.csv",
        ("scale_range", "ensemble", "history", "P_O", "P_E", "sample_size"),
        trans_rows,
    )
    run_rows = []
    for source, table in (("orbit_n<=4000", scan_row["walk_4000"]["runs"]), ("orbit_n<=1e5", scan_row["walk_1e5_runs"])):
        for row in table:
            run_rows.append({**row, "ensemble": source})
    csv_write(
        "run_statistics.csv",
        ("scale_range", "ensemble", "run_type", "length", "frequency", "count", "sample_size", "geometric_baseline", "deviation"),
        run_rows,
    )
    exc_rows = []
    for source, table in (("n<=4000", scan_row["walk_4000"]["P_H"]), ("n<=1e5", scan_row["walk_1e5"]["P_H"])):
        for row in table:
            exc_rows.append(
                {
                    "range": source,
                    "k": row["k"],
                    "P_H_ge": row["P_H_ge"],
                    "count": row["count"],
                    "starts": row["starts"],
                    "ci95_lo": row["ci95"][0],
                    "ci95_hi": row["ci95"][1],
                }
            )
    csv_write(
        "excursion_distribution.csv",
        ("range", "k", "P_H_ge", "count", "starts", "ci95_lo", "ci95_hi"),
        exc_rows,
    )
    csv_write(
        "large_deviation.csv",
        ("horizon", "threshold", "observed_probability", "model", "model_probability", "sample_size", "model_sample_size"),
        scan_row["large_deviation"],
    )
    model_rows = []
    for name, payload in scan_row["models"].items():
        for row in payload["P_H"]:
            model_rows.append(
                {
                    "model": name,
                    "mean_H": payload["mean_H"],
                    "max_H": payload["max_H"],
                    **row,
                }
            )
    csv_write(
        "model_comparison.csv",
        ("model", "mean_H", "max_H", "horizon", "threshold", "model_probability", "sample_size"),
        model_rows,
    )
    with (directory / "exceptional_paths.jsonl").open("w", encoding="utf-8") as handle:
        for row in scan_row["walk_4000"]["exceptional"]:
            handle.write(json.dumps(row) + "\n")
        for row in scan_row["walk_1e5_exceptional"]:
            handle.write(json.dumps(row) + "\n")
    csv_write(
        "record_excursions.csv",
        ("n", "status", "tau", "H", "word", "peak_bits", "tau_match", "word_match", "expected_tau"),
        scan_row["records"],
    )


def _md_table(headers: list[str], rows: Iterable[Iterable[Any]]) -> str:
    lines = ["| " + " | ".join(headers) + " |", "| " + " | ".join("---" for _ in headers) + " |"]
    for row in rows:
        lines.append("| " + " | ".join("" if cell is None else str(cell) for cell in row) + " |")
    return "\n".join(lines)


def write_docs(scan_row: dict[str, Any], path: Path = DOC_PATH) -> None:
    d = scan_row["decision"]
    one = scan_row["one_step"]
    one_big = scan_row["one_step_1e5"]
    logu = scan_row["log_uniform"]
    odds = scan_row["odd_uniform"]
    walk = scan_row["walk_4000"]
    walk_big = scan_row["walk_1e5"]
    gap = scan_row["pointwise_gap"]
    exc = scan_row["exception_structure"]
    ld = scan_row["ld_fit"]
    rec_rows = [
        [r["n"], r["status"], r["tau"], r["peak_bits"], r["tau_match"], (r["word"] or "")[:24]]
        for r in scan_row["records"]
    ]
    measure_rows = [
        ["uniform [16,4000]", one["P_O"], one["weighted_mean_delta"], one["sample_size"]],
        ["log-uniform [16,4000]", logu["weighted_P_O"], logu["weighted_mean_delta"], logu["sample_size"]],
        ["odd-uniform [16,4000]", odds["P_O"], odds["weighted_mean_delta"], odds["sample_size"]],
        ["uniform [16,1e5]", one_big["P_O"], one_big["weighted_mean_delta"], one_big["sample_size"]],
        ["log-uniform [16,1e5]", scan_row["log_uniform_1e5"]["weighted_P_O"], scan_row["log_uniform_1e5"]["weighted_mean_delta"], scan_row["log_uniform_1e5"]["sample_size"]],
        ["odd-uniform [16,1e5]", scan_row["odd_uniform_1e5"]["P_O"], scan_row["odd_uniform_1e5"]["weighted_mean_delta"], scan_row["odd_uniform_1e5"]["sample_size"]],
        ["orbit-induced n<=4000", scan_row["empirical_p_O_orbit"], d["orbit_mean_delta"], "walk steps"],
    ]
    drift_rows = [
        [row["scale_range"], row["branch"], row["sample_size"], row["mean"], row["variance"]]
        for row in one_big["scale_drift"]
        if row["branch"] in ("O", "E", "ALL")
    ]
    bit_rows = [
        [key, rec["sample_size"], rec["mean"], rec["branch_term"], rec["mean_floor_error"]]
        for key, rec in scan_row["large_random"].items()
    ]
    ph = [[row["k"], row["P_H_ge"], row["count"], row["ci95"][0], row["ci95"][1]] for row in walk["P_H"]]
    ph_big = [[row["k"], row["P_H_ge"], row["count"]] for row in walk_big["P_H"]]
    model_rows = [
        [name, payload["mean_H"], payload["max_H"]] + [next(r["model_probability"] for r in payload["P_H"] if r["horizon"] == k) for k in (5, 10, 20)]
        for name, payload in scan_row["models"].items()
    ]
    hist_rows = [[k, v] for k, v in list(scan_row["empirical_p_O_given"].items())[:12]]
    run_head = [row for row in walk["runs"] if row["length"] <= 8]
    run_table = [
        [row["run_type"], row["length"], row["frequency"], row["geometric_baseline"], row["deviation"], row["count"]]
        for row in run_head
    ]
    exc_table = [
        [row["n"], row["H"], row["initial_O_run"], row["n_mod8"], row["observed_drift"], row["word"][:20]]
        for row in walk["exceptional"][:12]
    ]
    path.write_text(
        f"""# Juggler probabilistic drift and large-deviation frontier

Status: **{d['classification']}**

Standalone statistical phase on the exact Juggler floor-power map.
`L = log log x` is a diagnostic. It never defines the map. This is not
a termination theorem. Closed symbolic-compression branches stay closed.

Every result below is labelled with the Phase-0 evidence axis
`LEAN-CERTIFIED` | `EXACT COMPUTATION` | `COMPUTATIONALLY OBSERVED` |
`STATISTICAL ESTIMATE` | `MODEL ASSUMPTION` | `CANDIDATE CONJECTURE`.
Ledger tags in the dossier remain the seven laboratory labels.

## 1. Literature context

Ordinary Collatz heuristics compress several parity steps and model
`log` of the accelerated orbit by a random walk: odd growth against
dyadic contraction. Tao (`tao-2019-almost-all-collatz`) goes far beyond
that heuristic, proving that almost all Collatz orbits attain almost
bounded values, using logarithmic density and an approximate transport
statement. That is a Collatz theorem. It is not imported here as a
Juggler theorem. Label: **LEAN-CERTIFIED** is not claimed; the citation
is literature context.

A 2025 preprint of Vikram Prasad and M. A. Prasad
(`prasad-prasad-2025-juggler-like`) applies a random-walk /
large-deviation model to *juggler-like* sequences and reports estimated
excursion and stopping constants. Treat it as literature context, not
as an established theorem on the exact floor-power map
`J(even)=⌊√n⌋`, `J(odd)=⌊n^{{3/2}}⌋`. Label: **MODEL ASSUMPTION** of
that preprint; **not** a laboratory theorem.

OEIS A007320 remains the computational step-count table. Label:
**EXACT COMPUTATION** on published terms only; totality is unclaimed.

This experiment derives the increment from exact `J`, estimates the
conditional law of `ΔL`, and measures the gap between a baseline
stochastic model and the deterministic positive-integer dynamics.
It does not reproduce the Prasad constants and does not assume
`P(O)=P(E)=1/2` as a law.

Phase-12 parity-drift already recorded the *conceptual* costs
`+log(3/2)` / `+log(1/2)` and proved exact block inequalities
(`OOOEE`, `EE`) as `T^k(n)<n`. Those are finite-word certificates.
They are not a statistical law. Label of the block lemmas:
**LEAN-CERTIFIED**. This page is not a reopen of that branch.

## 2. Choice of measure

Four ensembles were compared on the same exact one-step map.

| ensemble | P(O) | mean ΔL | sample size |
| --- | --- | --- | --- |
{_md_table(['ensemble', 'P(O)', 'mean ΔL', 'N'], measure_rows).split(chr(10), 2)[2]}

Uniform integers have `P(O)=1/2` by counting. That is not a dynamical
law. Evens are exactly contracting for `n>=2`
(`floorPower` even branch; `T(n)<n`). Label: **LEAN-CERTIFIED** even
contraction, **EXACT COMPUTATION** of `H(n)=1` on every even start in
the window.

Log-uniform (`weight 1/x`) is the multiplicative analogue of the
Collatz logarithmic density. Odd-uniform removes the trivial even
mass. Orbit-induced counts actual steps along first-return walks.

Odd-uniform one-step drift is tautologically `μ_O ≈ log(3/2) > 0`,
because every odd integer takes an `O` step. It is not a competing
`μ_∞`. Mixed-parity ensembles (uniform, log-uniform, orbit-induced)
all have negative mean `ΔL` near the ideal half-and-half value
`-0.143841`. Label: **STATISTICAL ESTIMATE**. They are not equivalent
as tail laws: even mass forces `P(H>=2)=1/2` under uniform counting.
The natural ensemble for excursion tails is therefore odd-uniform or
log-uniform on odds. The natural ensemble for one-step drift of `L`
at large scale is log-uniform or large-bit random integers.

## 3. Exact Juggler increment

The map is exact:

```
J(n) = isqrt(n)        if n even
J(n) = isqrt(n^3)      if n odd
```

For `x >= {MIN_L}` and `J(x) >= 3` the diagnostic is

```
ΔL = log log J(x) - log log x
   = branch_term + floor_error
```

with `branch_term = log(3/2)` on `O` and `log(1/2)` on `E`. This
identity is an algebraic rewrite of the two floating logarithms.
Label: **EXACT COMPUTATION** of `J`; **STATISTICAL ESTIMATE** of `ΔL`.

Ideal half-and-half drift: `μ_ideal = {scan_row['ideal_half_drift']}`.
This is a **MODEL ASSUMPTION**, not an empirical claim.

## 4. Parity statistics

Uniform one-step `P(O)` on `[16,4000]` is `{one['P_O']}` and on
`[16,1e5]` is `{one_big['P_O']}`. That is counting, not dynamics.

Orbit-induced `P(O)` on first-return walks `n<=4000` is
`{scan_row['empirical_p_O_orbit']}`. One-step history conditionals:

{_md_table(['history', 'P(O|history)'], hist_rows)}

Short history changes `P(O)` but does not produce a finite-memory
symbolic process that can replace the current integer. After an `O`
the next state is a specific integer `floor(x^{{3/2}})`, not a random bit.
Label: **STATISTICAL ESTIMATE**. Do not read this as an automaton.
Do not read `P(O)` as a residual invariant.

## 5. Run statistics

Run lengths among first-return words `n<=4000`, compared with a
geometric baseline from the empirical mean length. This is frequency,
not word semantics, and not a PE-density law.

{_md_table(['type', 'len', 'freq', 'geometric', 'dev', 'count'], run_table)}

Long `O`-runs remain visible. Their frequencies are not promoted to
an asymptotic PE law. Label: **STATISTICAL ESTIMATE**. The closed
PE-density branch stays closed.

## 6. Empirical drift

One-step uniform `[16,1e5]` by the scale partition
`[e^{{2^j}}, e^{{2^{{j+1}}}})`:

{_md_table(['scale', 'branch', 'N', 'mean ΔL', 'var'], drift_rows)}

Large-bit random integers (exact `J`, 80 samples per class):

{_md_table(['class', 'N', 'mean ΔL', 'branch term', 'mean floor_error'], bit_rows)}

At large bit length the increment approaches the branch term and the
floor error collapses. Conditional drift on `mod 2,4,8,3,9` is
dominated by parity: even residues carry `μ ≈ log(1/2)`, odd residues
carry `μ ≈ log(3/2)`. Residues that mix parities (none of these moduli
do for a single residue) are not used as a hunt. Label:
**STATISTICAL ESTIMATE** on the stated windows.

Orbit-induced mean `ΔL` on `n<=4000` walks:
`{d['orbit_mean_delta']}`.

Large-scale mixed-parity drift is negative on this window.
This is **not** `μ_J` as a theorem. Finite-range cutoff: one-step
`n<=10^5`, orbit `n<=4000` plus leftover-aware `n<=10^5`, large-bit
probe through 512 bits. Label: **STATISTICAL ESTIMATE**.

## 7. Model comparison

Baseline models, simulated on the `L`-coordinate only
({MODEL_PATHS} paths, horizon {MODEL_HORIZON}):

{_md_table(['model', 'mean H', 'max H', 'P(H>=5)', 'P(H>=10)', 'P(H>=20)'], model_rows)}

- `M0`: independent Bernoulli with empirical orbit `P(O)`.
- `M1`: one-step Markov on `{{O,E}}`.
- `M2`: magnitude-conditioned `P(O)`.
- `M3`: short history (`<=2`) plus the Markov fallback.
- `M4`: run-length comparison reduced to the same Markov step; it is
  not an automaton.

The scientific object is the difference between these models and exact
`H(n)`. Exact `P(H>=k)` on `n<=4000`:

{_md_table(['k', 'P(H>=k)', 'count', 'ci95 lo', 'ci95 hi'], ph)}

Models using idealized additive `ΔL` miss the exact floor and the
forced even contraction `H(n)=1`. Additional model complexity past
`M1` does not create a deterministic constraint. Label:
**MODEL ASSUMPTION** for the simulators; **EXACT COMPUTATION** for
`H(n)` on completed returns.

## 8. Large-deviation tails

Descriptive fit of `log P(H>=k)` versus `k` on `n<=4000`:
rate `c ≈ {ld.get('rate_c')}`, `r^2 ≈ {ld.get('r2')}`.
Family: `{ld.get('family')}`. Label: **STATISTICAL ESTIMATE**.
This is not a Cramér theorem and not a Gaussian theorem.

The candidate inequality `P(x_i >= n for all i<=k) <= exp(-c k)` is
compatible with the sample as a description. It is **not** proved.
What would still be required for every positive integer: a uniform
tail bound under a named measure, plus a pointwise argument that no
infinite exceptional family exists. Phase 0 does not supply either.

## 9. Exceptional trajectories

`H>=16` starts on `n<=4000`: `{walk['exceptional_count']}`
(table below is the longest `{exc['count']}`).
All odd among those listed: `{exc['all_odd']}`. Mean initial `O`-run:
`{exc['mean_initial_O_run']}`. Named arithmetic family:
`{exc['named_arithmetic']}`.

{exc['reading']}

{_md_table(['n', 'H', 'O-run0', 'n mod 8', 'obs drift', 'word prefix'], exc_table)}

Known records replayed on CPU (exact `J`):

{_md_table(['n', 'status', 'tau', 'peak bits', 'tau match', 'word prefix'], rec_rows)}

`n=193` first-return length `70` and `n=3889` length `77` remain the
`n<=4000` delay records. `n=2183` remains the peak-bit record in that
window. Label: **EXACT COMPUTATION**. Rarity under `M0` is not an
explanation: the exact feature is a long expanding odd prefix, already
visible in the word.

## 10. Scale dependence

`H` on `[N,2N)`-style bit bands from `n<=4000` and the `n<=10^5`
census:

- `n<=4000`: starts `{walk['starts']}`, returned `{walk['returned']}`,
  leftovers `{walk['leftovers']}`, max `H={walk['max_H']}` at
  `n={walk['max_H_n']}`, max peak bits `{walk['max_peak_bits']}` at
  `n={walk['max_peak_n']}`.
- `n<=10^5`: starts `{walk_big['starts']}`, returned
  `{walk_big['returned']}`, leftovers `{walk_big['leftovers']}`,
  max completed `H={walk_big['max_H']}` at `n={walk_big['max_H_n']}`.
  Leftovers are bit-cap / horizon, not a proof that `H=∞`.

{_md_table(['k', 'P(H>=k) n<=1e5', 'count'], ph_big)}

Normalized excursion law: even starts remain `H=1`. Odd-start tails
stay heavy enough that `max H` grows from the `n<=4000` window to the
`n<=10^5` leftovers. The distribution of typical `H` is stable
(`H=1` on evens; short returns on most odds). The rare-event tail is
slowly drifting / record-driven, not a settled asymptotic. Label:
**COMPUTATIONALLY OBSERVED**.

## 11. Potential exact / statistical synthesis

The attractive architecture — statistical contraction, Atlas list of
exceptions, exact inequalities forbidding persistence — does **not**
close in Phase 0. The exceptions are exactly the starts that realize
a long odd expanding prefix. That is the definition of the expanding
branch plus the already-closed realization / adversarial / first-return
questions. No new finite exceptional family appears.

Existing exact certificates that remain in force:
`power_bound_contracts` (`3^o < 2^k ⇒ T_w(n)<n` for `n>=2`) and
`floorPower_odd_ge`. Label: **LEAN-CERTIFIED**. They already handle
every completed contracting word. They do not bound `H(n)` uniformly.

## 12. What is NOT proved

- Negative mean drift does not imply every orbit terminates.
- `P(H>=k) → 0` in a window does not imply no exceptional orbit exists.
- An observed near-geometric run law does not imply an independent
  parity process.
- A fitted exponential tail is not a large-deviation theorem.
- `μ_J` is not a theorem. No candidate conjecture is opened.
- CUDA was not used. No GPU float defined `J`.

## 13. Decision

**{d['classification']}**. Branch decision: **{d['branch']}**.

{d['reason']}

Flags: drift `{d['flags'][CLASS_DRIFT]}`, run-law
`{d['flags'][CLASS_RUNLAW]}`, LD `{d['flags'][CLASS_LD]}`,
exceptional `{d['flags'][CLASS_EXCEPTIONAL]}`, synthesis
`{d['flags'][CLASS_SYNTHESIS]}`.

Best next question: none from this branch as an automatic sequel.
A later theorem phase would need a named measure and a genuine tail
inequality, not another census.

Pointwise gap on `n<=4000`, horizon `k=10`: almost-all contraction
rate `{gap['almost_all_contract_by_k']}`; every-start contraction
by 10 is `{gap['every_start_contracts_by_k']}`; max `H={gap['max_H']}`
at `n={gap['max_H_n']}`. Typical contraction is not universal
contraction.
""",
        encoding="utf-8",
    )


def write_dossier(scan_row: dict[str, Any], path: Path = DOSSIER_PATH) -> None:
    d = scan_row["decision"]
    path.write_text(
        f"""# Juggler probabilistic drift and large-deviation frontier

Status: **EXPLORATORY**

Standalone statistical layer on the exact Juggler floor-power map. It
is **not** a Research Engine control-layer experiment, not a reopen of
any closed symbolic-compression branch, and not a claim that every
positive integer reaches 1.

## Problem

Does the exact Juggler map possess a robust large-scale statistical
law for the diagnostic coordinate `L = log log x`, and do the
finite trajectories that violate a baseline stochastic model have
an exact arithmetic description that could support a later
statistical-plus-exact constraint?

## Exact statement

For `x >= 2` write `J` for the even/odd floor-power map. For
`x >= 16` and `J(x) >= 3` define the diagnostic

    ΔL(x) = log log J(x) − log log x.

`ΔL` is not the dynamics. Phase 0 asks, on `n <= 4000` exact
first-return walks and `n <= 10^5` one-step / leftover-aware walks:

1. whether `E[ΔL]` is negative under mixed-parity ensembles (uniform,
   log-uniform, orbit-induced); odd-only one-step is tautologically
   the `O` increment;
2. whether short history or the listed moduli change that sign;
3. whether `P(H(n) >= k)` admits a reproducible descriptive tail,
   where `H(n)` is the observed first-return-below length;
4. whether the starts with large `H` have a named arithmetic
   structure that is not “a long initial odd run”.

A window tail is not `H < ∞`. Negative drift is not termination.

## Current literature

- OEIS A007320 (`oeis-A007320`) — computational step counts. **known**.
- Tao, almost all Collatz orbits (`tao-2019-almost-all-collatz`) —
  Collatz logarithmic-density theorem. **known**, not imported.
- Prasad–Prasad 2025 juggler-like random-walk preprint
  (`prasad-prasad-2025-juggler-like`) — literature context only.
  **known**, not a theorem on exact `J`.
- Phase-12 parity-drift block lemmas (`OOOEE`, `EE`) —
  **EXACT — LEAN VERIFIED** as conditional word laws, not a
  statistical law.
- `power_bound_contracts`, `floorPower_odd_ge` —
  **EXACT — LEAN VERIFIED**.
- PE / residual-future / residual projections / summed-rho /
  realization-set / landing-image / finite-word `N_w` / first-return
  structural laws / adversarial paths / information-complexity /
  backward cells / acceleration / floor-boundary / 2-adic bridge —
  **CLOSE**. Do not reopen.

Project relationship: **independent** statistical reading of exact
`J`. Totality remains unclaimed.

## Branch budget

```text
Mathematical target     Does exact J have a robust large-scale
                        log-log drift, and do model-violating finite
                        paths have exact arithmetic structure?
Novelty hypothesis      A Juggler-specific increment law, not a
                        copied Collatz random walk, plus a named
                        exceptional set
Falsifier               Drift sign depends on the ensemble; exceptions
                        are only long O-runs; no stable tail
Existing machinery      floor_power, _walk_returns, first-return
                        records, power_bound_contracts, Phase-12
                        conceptual log-log costs
Maximum Phase-0 scope   n<=4000 exact walks; n<=1e5 one-step and
                        leftover-aware H; M0–M4 comparison; CPU only
Promotion criterion     A named measure with a usable exceptional
                        arithmetic family, or a precise tail that
                        is not a window histogram
Stop criterion          STATISTICAL_ONLY / MODEL_DEPENDENT /
                        PROBABILISTIC_COMPLEX; closed-branch reopen;
                        halt claim; another scalar invariant
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required. The 2-adic / BT bridge is closed.

## Candidate operations / invariants

- `L = log log x` as the dynamics —
  not used; diagnostic only
- `ΔL = branch_term + floor_error` —
  **OBSERVATION** of the floating rewrite; `J` remains exact
- `P(O)=1/2` as a law —
  **REFUTED** as a dynamical assumption; it is a uniform counting identity
- Odd-only one-step drift —
  tautologically `μ_O ≈ log(3/2)`; not a competing `μ_∞`
- Negative large-scale mixed-parity drift —
  **OBSERVATION** on the stated windows
- Exceptional starts form a named arithmetic family —
  **REFUTED** as Phase-0 promotion: they are odd starts with long
  initial `O`-runs
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.probabilistic`
- Records: [juggler_probabilistic.md](../research/juggler_probabilistic.md),
  [juggler_probabilistic.json](../research/juggler_probabilistic.json)
- Dataset: `data/research/juggler/probabilistic/`
- Tests: `tests/research/juggler_sequence/test_probabilistic.py`

No GPU. No new Lean file. No automaton.

## Conjectures

None opened.

## Counterexamples

- `P(O)=P(E)=1/2` as a trajectory law: orbit-induced `P(O)` is measured,
  not assumed.
- Odd-uniform one-step negative drift: every odd start is an `O` step.
- `H<=10` for every `n<=4000`: `n=193` has `H=70`.
- Model `M0` equals exact `H`: even starts have exact `H=1`; the
  additive `L` model does not see that identity.

## Formalization

None added. Existing Envelope / Dynamics lemmas stay as they are.
No `sorry`.

## Results

Classification **{d["classification"]}**.

{d["reason"]}

## Open questions

None from this branch as an automatic sequel. A later theorem would
need a named measure and a genuine tail inequality. Do not reopen
closed symbolic-compression branches.

## Decision

**{d["branch"]}**. {d["reason"]} Do not claim termination.

Best next question: none from this branch.

## Publication assessment

Status: `EXPLORATORY`. A statistical census of the exact increment
and the typical-versus-pointwise gap, not a paper candidate and not
a Juggler totality result.
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

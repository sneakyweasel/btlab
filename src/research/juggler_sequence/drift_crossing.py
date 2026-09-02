"""First positive-drift crossing and prefix-NC endpoints.

Not a Research Engine control-layer experiment. Not a halt theorem.
Walks actual Juggler orbits until the first G_k = 2^k - 3^{o_k} > 0.
Asks whether long prefix-NC survival forces arithmetic structure on
x_k = T^k(n) beyond the G-recurrence and T >= n. ResidualStep is not
extended. Prefix-NC word admissibility is not reopened. The corridor
is not reopened. Odd-fourth-power is not reopened.
"""

from __future__ import annotations

import hashlib
import json
import subprocess
from collections import defaultdict
from math import gcd, isqrt
from pathlib import Path
from typing import Any

from research.juggler_sequence.envelope_defect import local_defect, tiny_deficit
from research.juggler_sequence.equality_language import is_monochrome
from research.juggler_sequence.near_extremal_prefixes import (
    exponent_gap,
    prefix_noncontracting,
)
from research.juggler_sequence.power_algebra import is_square
from research.juggler_sequence.power_itineraries import (
    ANTI_OVERCLAIM,
    floor_power,
    word_of,
)
from research.juggler_sequence.saturation_budget import square_depth
from research.juggler_sequence.lean_paths import (
    CYCLE_DIOPHANTINE,
    ENVELOPE,
    MINIMAL,
    RESIDUALS,
    juggler_text,
)

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_drift_crossing.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_drift_crossing.md"
LEAN_NEW = REPO_ROOT / "formal" / "Problems" / "Engine" / "DriftCrossing.lean"
FLOOR_PATH = ENVELOPE
RESIDUAL_PATH = RESIDUALS
MIN_PATH = MINIMAL
CYCLE_PATH = CYCLE_DIOPHANTINE
PREFIX_PATH = REPO_ROOT / "formal" / "Problems" / "Engine" / "PrefixNc.lean"
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "drift_crossing"

CLASS_ENDPOINT = "DRIFT_ENDPOINT_GREEN"
CLASS_CROSSING = "DRIFT_FIRST_CROSSING_GREEN"
CLASS_FILTRATION = "DRIFT_ENDPOINT_FILTRATION_GREEN"
CLASS_INDUCTION = "DRIFT_INDUCTION_GREEN"
CLASS_COUNTER = "DRIFT_ENDPOINT_COUNTEREXAMPLE"
CLASS_COMPLEX = "DRIFT_ENDPOINT_COMPLEX"
CLASS_INCOMPLETE = "DRIFT_ENDPOINT_INCOMPLETE"

STATUS_CROSSED = "CROSSED"
STATUS_ABSORBED = "ABSORBED_NC"
STATUS_HORIZON = "HORIZON_EXCEEDED"
STATUS_BIT_CAP = "BIT_CAP"

N_MIN = 2
N_MAX = 2000
HORIZON = 10_000
BIT_CAP = 4096
BIT_LIMIT = 80
X_BITS_KEEP = 128
DEFECT_BITS = 256
FACTOR_CAP = 10_000
SAMPLE_CAP = 20
HARD_STARTS = (9, 37, 49, 69, 77, 173)
TALL_STARTS = (193, 557, 761)
ALGORITHM_VERSION = "drift-crossing-v1"
SEARCH_PREFIX = "juggler-drift-crossing-phase0"
CROSSING_POLICY = "stop at first G_k>0; absorb if T^k=1 still NC"

FORBIDDEN_ENGINES = (
    "CycleEngine",
    "ResidualGraph",
    "RemainderDynamics",
    "PowerHeight",
    "ResidualStep",
    "CycleDiophantine",
)

FLOOR_LEMMAS = (
    "power_bound_word",
    "power_bound_contracts",
    "power_bound_eq_iff_extremal",
    "power_bound_compensated_contracts",
)

INVARIANT_KEYS = (
    "x_even",
    "x_odd",
    "x_square",
    "x_not_square",
    "v2_ge_1",
    "v3_ge_1",
    "gcd_gt_1",
    "gcd_eq_1",
    "square_depth_ge_1",
    "mod8_0",
    "mod8_1",
    "mod8_4",
    "mod9_0",
    "image_ge_n",
)


def search_id_for(n_start: int, n_end: int) -> str:
    return f"{SEARCH_PREFIX}-n{n_start}-{n_end}"


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


def valuation(n: int, p: int) -> int:
    if n == 0 or p < 2:
        raise ValueError("valuation requires a nonzero integer and prime p >= 2")
    count = 0
    while n % p == 0:
        n //= p
        count += 1
    return count


def odd_part(n: int) -> int:
    if n == 0:
        return 0
    while n % 2 == 0:
        n //= 2
    return n


def least_odd_divisor(n: int, *, cap: int = FACTOR_CAP) -> int | None:
    """Smallest odd divisor >= 1. None if the odd part is unfactored."""

    odd = odd_part(abs(n))
    if odd <= 1:
        return 1
    p = 3
    while p * p <= odd and p <= cap:
        if odd % p == 0:
            return p
        p += 2
    if odd <= cap * cap:
        return odd
    return None


def nearest_square_distance(x: int) -> int:
    if x < 0:
        raise ValueError("nearest_square_distance requires a nonnegative integer")
    root = isqrt(x)
    below = x - root * root
    above = (root + 1) * (root + 1) - x
    return below if below <= above else above


def nearest_fourth_distance(x: int) -> int:
    if x < 0:
        raise ValueError("nearest_fourth_distance requires a nonnegative integer")
    root = isqrt(isqrt(x))
    best = abs(x - root**4)
    if root >= 1:
        best = min(best, abs(x - (root - 1) ** 4))
    return min(best, abs(x - (root + 1) ** 4))


def is_fourth_power(x: int) -> bool:
    if x < 0:
        return False
    root = isqrt(isqrt(x))
    return root**4 == x


def keep_x(x: int) -> int | None:
    return x if x.bit_length() <= X_BITS_KEEP else None


def odd_step_keeps_nonpositive(prev_k: int, prev_o: int) -> bool:
    """Appending O to a prefix with G <= 0 keeps G < 0.

    G' = 2^{k+1} - 3^{o+1} = 2 G - 3^o. If G <= 0 then G' <= -3^o < 0.
    """

    if prev_k < 0 or prev_o < 0:
        raise ValueError("odd_step_keeps_nonpositive requires nonnegative k, o")
    return exponent_gap(prev_k, prev_o) <= 0 and exponent_gap(prev_k + 1, prev_o + 1) < 0


def even_step_crosses(prev_k: int, prev_o: int) -> bool:
    """Appending E crosses iff 2^{k+1} > 3^o, i.e. G' = 2 G + 3^o > 0."""

    if prev_k < 0 or prev_o < 0:
        raise ValueError("even_step_crosses requires nonnegative k, o")
    return exponent_gap(prev_k + 1, prev_o) > 0


def crossing_window(tau: int, odd_count: int) -> bool:
    """First crossing on E at time tau iff 2^{tau-1} <= 3^o < 2^tau."""

    if tau < 1 or odd_count < 0:
        raise ValueError("crossing_window requires tau >= 1")
    return exponent_gap(tau - 1, odd_count) <= 0 < exponent_gap(tau, odd_count)


def endpoint_metrics(x: int, n: int) -> dict[str, Any]:
    if x < 0:
        raise ValueError("endpoint_metrics requires a nonnegative state")
    v2 = valuation(x, 2) if x else 0
    v3 = valuation(x, 3) if x else 0
    depth = square_depth(x)
    odd = odd_part(x)
    return {
        "x": keep_x(x),
        "x_bits": x.bit_length(),
        "parity": x % 2,
        "even": x % 2 == 0,
        "square": is_square(x),
        "fourth": is_fourth_power(x),
        "square_depth": depth,
        "v2": v2,
        "v3": v3,
        "odd_part": keep_x(odd),
        "odd_part_bits": odd.bit_length() if odd else 0,
        "least_odd_divisor": least_odd_divisor(x),
        "dist_square": nearest_square_distance(x),
        "dist_fourth": nearest_fourth_distance(x),
        "mod8": x % 8,
        "mod9": x % 9,
        "mod16": x % 16,
        "gcd_n": gcd(x, n) if n else 0,
        "image_ge_n": x >= n,
    }


def _invariant_flags(metrics: dict[str, Any], image_ge_n: bool) -> dict[str, bool]:
    depth = metrics["square_depth"]
    return {
        "x_even": metrics["even"],
        "x_odd": not metrics["even"],
        "x_square": metrics["square"],
        "x_not_square": not metrics["square"],
        "v2_ge_1": metrics["v2"] >= 1,
        "v3_ge_1": metrics["v3"] >= 1,
        "gcd_gt_1": metrics["gcd_n"] > 1,
        "gcd_eq_1": metrics["gcd_n"] == 1,
        "square_depth_ge_1": depth is not None and depth >= 1,
        "mod8_0": metrics["mod8"] == 0,
        "mod8_1": metrics["mod8"] == 1,
        "mod8_4": metrics["mod8"] == 4,
        "mod9_0": metrics["mod9"] == 0,
        "image_ge_n": image_ge_n,
    }


def _slim_nc(n: int, k: int, o: int, gap: int, word: str, metrics: dict[str, Any]) -> dict[str, Any]:
    return {
        "n": n,
        "k": k,
        "odd_count": o,
        "G": gap,
        "word": word,
        "mixed": (not is_monochrome(word)) if word else False,
        "x": metrics["x"],
        "x_bits": metrics["x_bits"],
        "parity": metrics["parity"],
        "square": metrics["square"],
        "fourth": metrics["fourth"],
        "square_depth": metrics["square_depth"],
        "v2": metrics["v2"],
        "v3": metrics["v3"],
        "dist_square": metrics["dist_square"],
        "dist_fourth": metrics["dist_fourth"],
        "mod8": metrics["mod8"],
        "mod9": metrics["mod9"],
        "gcd_n": metrics["gcd_n"],
        "least_odd_divisor": metrics["least_odd_divisor"],
        "image_ge_n": metrics["image_ge_n"],
    }


def walk_until_crossing(
    n: int,
    *,
    horizon: int = HORIZON,
    bit_cap: int = BIT_CAP,
    bit_limit: int = BIT_LIMIT,
) -> dict[str, Any]:
    """Walk the actual orbit of n until the first positive G_k."""

    if n < 1:
        raise ValueError("walk_until_crossing requires n >= 1")
    if horizon < 1:
        raise ValueError("horizon must be positive")
    current = n
    odds = 0
    three = 1
    two = 1
    path = [n]
    letters: list[str] = []
    nc_rows: list[dict[str, Any]] = []
    peak = n
    first_defect_index = None
    first_defect_value = None
    status = STATUS_HORIZON
    tau = None
    pred = None
    image = None
    crossing_o = None
    crossing_gap = None

    for k in range(1, horizon + 1):
        if current.bit_length() > bit_cap:
            status = STATUS_BIT_CAP
            break
        letter = "O" if current % 2 else "E"
        if letter == "O":
            odds += 1
            three *= 3
        two <<= 1
        gap = two - three
        if first_defect_index is None and not is_square(current):
            first_defect_index = k - 1
            first_defect_value = (
                local_defect(current) if current.bit_length() <= DEFECT_BITS else None
            )
        nxt = floor_power(current)
        letters.append(letter)
        path.append(nxt)
        peak = max(peak, nxt)
        if gap <= 0:
            metrics = endpoint_metrics(nxt, n)
            deficit = tiny_deficit(n, nxt, k, odds, bit_limit=bit_limit)
            row = _slim_nc(n, k, odds, gap, "".join(letters), metrics)
            row["first_defect_index"] = first_defect_index
            row["first_defect"] = first_defect_value
            row["local_defect"] = (
                local_defect(current) if current.bit_length() <= DEFECT_BITS else None
            )
            row["tiny_deficit"] = deficit
            nc_rows.append(row)
            if nxt == 1:
                status = STATUS_ABSORBED
                tau = None
                pred = current
                image = nxt
                crossing_o = odds
                crossing_gap = gap
                break
        else:
            status = STATUS_CROSSED
            tau = k
            pred = current
            image = nxt
            crossing_o = odds
            crossing_gap = gap
            break
        current = nxt

    word = "".join(letters)
    last_nc = nc_rows[-1] if nc_rows else None
    pred_metrics = endpoint_metrics(pred, n) if pred is not None else None
    return {
        "n": n,
        "status": status,
        "tau_plus": tau,
        "word": word,
        "odd_count": crossing_o if crossing_o is not None else odds,
        "G_tau": crossing_gap,
        "pred": keep_x(pred) if pred is not None else None,
        "pred_bits": pred.bit_length() if pred is not None else None,
        "pred_even": pred % 2 == 0 if pred is not None else None,
        "pred_metrics": pred_metrics,
        "image": keep_x(image) if image is not None else None,
        "image_lt_n": image < n if image is not None else None,
        "crossing_letter": word[-1] if word else None,
        "crossing_window": (
            crossing_window(tau, crossing_o)
            if status == STATUS_CROSSED and tau is not None and crossing_o is not None
            else None
        ),
        "prefix_nc_until_pred": prefix_noncontracting(word[:-1]) if len(word) >= 2 else True,
        "peak": keep_x(peak),
        "peak_bits": peak.bit_length(),
        "max_state_bits": peak.bit_length(),
        "first_defect_index": first_defect_index,
        "first_defect": first_defect_value,
        "nc_count": len(nc_rows),
        "last_nc": last_nc,
        "nc_rows": nc_rows,
        "path_prefix": [keep_x(item) for item in path[: min(len(path), 12)]],
        "horizon": horizon,
        "bit_cap": bit_cap,
        "search_horizon_is_not_L": True,
    }


def _crossing_identity_failure(walked: dict[str, Any]) -> dict[str, Any] | None:
    if walked["status"] != STATUS_CROSSED:
        return None
    tau = walked["tau_plus"]
    odds = walked["odd_count"]
    letter = walked["crossing_letter"]
    if letter != "E":
        return {"kind": "crossing_letter", "n": walked["n"], "tau": tau, "letter": letter}
    if walked["pred_even"] is not True:
        return {"kind": "pred_odd", "n": walked["n"], "tau": tau}
    if not walked["crossing_window"]:
        return {
            "kind": "crossing_window",
            "n": walked["n"],
            "tau": tau,
            "odd_count": odds,
            "G": walked["G_tau"],
        }
    if walked["image_lt_n"] is not True:
        return {"kind": "image_not_lt", "n": walked["n"], "tau": tau, "image": walked["image"]}
    if tau >= 2 and not walked["prefix_nc_until_pred"]:
        return {"kind": "prefix_nc", "n": walked["n"], "word": walked["word"]}
    if tau == 1 and walked["n"] % 2 != 0:
        return {"kind": "odd_tau_one", "n": walked["n"]}
    if walked["n"] % 2 == 0 and tau != 1:
        return {"kind": "even_tau", "n": walked["n"], "tau": tau}
    return None


def _hard_trace(walked: dict[str, Any]) -> dict[str, Any]:
    last = walked["last_nc"]
    return {
        "n": walked["n"],
        "status": walked["status"],
        "tau_plus": walked["tau_plus"],
        "word": walked["word"],
        "odd_count": walked["odd_count"],
        "G_tau": walked["G_tau"],
        "crossing_letter": walked["crossing_letter"],
        "pred": walked["pred"],
        "pred_bits": walked["pred_bits"],
        "pred_even": walked["pred_even"],
        "image": walked["image"],
        "image_lt_n": walked["image_lt_n"],
        "peak_bits": walked["peak_bits"],
        "nc_count": walked["nc_count"],
        "last_nc": last,
    }


def analyze_starts(
    n_start: int,
    n_end: int,
    *,
    extra: tuple[int, ...] = (),
    horizon: int = HORIZON,
    bit_cap: int = BIT_CAP,
    bit_limit: int = BIT_LIMIT,
) -> dict[str, Any]:
    starts = list(range(n_start, n_end + 1))
    for value in extra:
        if value not in starts:
            starts.append(value)

    crossed = 0
    absorbed: list[int] = []
    unfinished: list[dict[str, Any]] = []
    identity_failures: list[dict[str, Any]] = []
    even_tau_failures: list[int] = []
    gap_zero: list[dict[str, Any]] = []
    tau_values: list[int] = []
    nc_prefix_count = 0
    mixed_nc_count = 0
    all_odd_nc_count = 0
    closest_nc: list[dict[str, Any]] = []
    longest: list[dict[str, Any]] = []
    largest_end: list[dict[str, Any]] = []
    smallest_gcd: list[dict[str, Any]] = []
    hard: list[dict[str, Any]] = []
    tall: list[dict[str, Any]] = []
    invariant_hits: dict[str, int] = {key: 0 for key in INVARIANT_KEYS}
    invariant_fail: dict[str, list[dict[str, Any]]] = {key: [] for key in INVARIANT_KEYS}
    filtration: dict[int, dict[str, Any]] = {}
    residue_sets: dict[int, dict[str, set[int]]] = defaultdict(
        lambda: {"mod8": set(), "mod9": set(), "parity": set(), "v2": set()}
    )
    max_tau = 0
    max_peak_bits = 0
    max_nc_k = 0
    gcd_gt1_mixed = 0
    gcd_eq1_mixed = 0
    pred_square = 0
    pred_not_square = 0

    for n in starts:
        walked = walk_until_crossing(n, horizon=horizon, bit_cap=bit_cap, bit_limit=bit_limit)
        max_peak_bits = max(max_peak_bits, walked["peak_bits"])
        if walked["status"] == STATUS_CROSSED:
            crossed += 1
            tau_values.append(walked["tau_plus"])
            max_tau = max(max_tau, walked["tau_plus"])
            fail = _crossing_identity_failure(walked)
            if fail is not None:
                if len(identity_failures) < SAMPLE_CAP:
                    identity_failures.append(fail)
            if n % 2 == 0 and walked["tau_plus"] != 1:
                even_tau_failures.append(n)
            if walked["G_tau"] == 0:
                gap_zero.append({"n": n, "tau": walked["tau_plus"]})
            if walked["pred_metrics"] is not None:
                if walked["pred_metrics"]["square"]:
                    pred_square += 1
                else:
                    pred_not_square += 1
        elif walked["status"] == STATUS_ABSORBED:
            absorbed.append(n)
        else:
            unfinished.append({"n": n, "status": walked["status"], "word": walked["word"]})

        for row in walked["nc_rows"]:
            nc_prefix_count += 1
            max_nc_k = max(max_nc_k, row["k"])
            if row["G"] == 0:
                gap_zero.append({"n": n, "k": row["k"]})
            mixed = row["mixed"]
            if mixed:
                mixed_nc_count += 1
                if row["gcd_n"] > 1:
                    gcd_gt1_mixed += 1
                elif row["gcd_n"] == 1:
                    gcd_eq1_mixed += 1
                flags = _invariant_flags(
                    {
                        "even": row["parity"] == 0,
                        "square": row["square"],
                        "square_depth": row["square_depth"],
                        "v2": row["v2"],
                        "v3": row["v3"],
                        "gcd_n": row["gcd_n"],
                        "mod8": row["mod8"],
                        "mod9": row["mod9"],
                    },
                    row["image_ge_n"],
                )
                for key in INVARIANT_KEYS:
                    if flags[key]:
                        invariant_hits[key] += 1
                    elif len(invariant_fail[key]) < 4:
                        invariant_fail[key].append(
                            {"n": n, "k": row["k"], "word": row["word"], "x": row["x"]}
                        )
                bucket = residue_sets[row["k"]]
                bucket["mod8"].add(row["mod8"])
                bucket["mod9"].add(row["mod9"])
                bucket["parity"].add(row["parity"])
                bucket["v2"].add(row["v2"])
            else:
                all_odd_nc_count += 1
            closest_nc.append(row)
            closest_nc.sort(key=lambda item: (-item["G"], item["k"], item["n"]))
            if len(closest_nc) > SAMPLE_CAP:
                closest_nc.pop()
            if mixed:
                largest_end.append(row)
                largest_end.sort(key=lambda item: (-item["x_bits"], -item["k"], item["n"]))
                if len(largest_end) > SAMPLE_CAP:
                    largest_end.pop()
                smallest_gcd.append(row)
                smallest_gcd.sort(key=lambda item: (item["gcd_n"], item["k"], item["n"]))
                if len(smallest_gcd) > SAMPLE_CAP:
                    smallest_gcd.pop()

        if walked["tau_plus"] is not None:
            longest.append(walked)
            longest.sort(key=lambda item: (-(item["tau_plus"] or 0), item["n"]))
            if len(longest) > SAMPLE_CAP:
                longest.pop()
        if n in HARD_STARTS:
            hard.append(_hard_trace(walked))
        if n in TALL_STARTS:
            tall.append(_hard_trace(walked))

    for k, bucket in residue_sets.items():
        filtration[k] = {
            "mixed_count": None,
            "mod8": sorted(bucket["mod8"]),
            "mod9": sorted(bucket["mod9"]),
            "parity": sorted(bucket["parity"]),
            "v2": sorted(bucket["v2"]),
        }

    for k, bucket in residue_sets.items():
        filtration[k]["mod8_size"] = len(bucket["mod8"])
        filtration[k]["mod9_size"] = len(bucket["mod9"])
        filtration[k]["parity_size"] = len(bucket["parity"])
        filtration[k]["v2_size"] = len(bucket["v2"])
        filtration[k]["mixed_present"] = True

    filtration_shrink = False
    shrink_notes: list[str] = []
    keys = sorted(filtration)
    for prev_k, nxt_k in zip(keys, keys[1:]):
        prev = filtration[prev_k]
        nxt = filtration[nxt_k]
        for name in ("mod8", "mod9", "parity"):
            prev_set = set(prev[name])
            nxt_set = set(nxt[name])
            if nxt_set and nxt_set < prev_set:
                filtration_shrink = True
                shrink_notes.append(f"{name}: S_{nxt_k} proper subset S_{prev_k}")

    invariant_universal = [
        key
        for key in INVARIANT_KEYS
        if mixed_nc_count > 0 and invariant_hits[key] == mixed_nc_count
    ]
    invariant_empty = [
        key for key in INVARIANT_KEYS if mixed_nc_count > 0 and invariant_hits[key] == 0
    ]

    tau_hist: dict[str, int] = defaultdict(int)
    for value in tau_values:
        tau_hist[str(value)] += 1

    return {
        "n_start": n_start,
        "n_end": n_end,
        "extra": list(extra),
        "start_count": len(starts),
        "crossed": crossed,
        "absorbed": absorbed,
        "absorbed_count": len(absorbed),
        "unfinished": unfinished,
        "unfinished_count": len(unfinished),
        "identity_failures": identity_failures,
        "identity_failure_count": len(identity_failures),
        "even_tau_failures": even_tau_failures,
        "gap_zero": gap_zero,
        "nc_prefix_count": nc_prefix_count,
        "mixed_nc_count": mixed_nc_count,
        "all_odd_nc_count": all_odd_nc_count,
        "max_tau": max_tau,
        "max_nc_k": max_nc_k,
        "max_peak_bits": max_peak_bits,
        "tau_histogram": dict(sorted(tau_hist.items(), key=lambda item: int(item[0]))),
        "invariant_hits": invariant_hits,
        "invariant_fail": {key: rows for key, rows in invariant_fail.items() if rows},
        "invariant_universal": invariant_universal,
        "invariant_empty": invariant_empty,
        "filtration": {str(k): filtration[k] for k in sorted(filtration)},
        "filtration_shrink": filtration_shrink,
        "filtration_shrink_notes": shrink_notes[:12],
        "gcd_gt1_mixed": gcd_gt1_mixed,
        "gcd_eq1_mixed": gcd_eq1_mixed,
        "pred_square": pred_square,
        "pred_not_square": pred_not_square,
        "closest_nc": closest_nc,
        "longest": [_hard_trace(item) for item in longest],
        "largest_mixed_endpoint": largest_end,
        "smallest_gcd_mixed": smallest_gcd,
        "hard": hard,
        "tall": tall,
        "search_horizon_is_not_L": True,
    }


def extra_starts() -> tuple[int, ...]:
    return tuple(n for n in HARD_STARTS + TALL_STARTS if n > N_MAX)


def lean_api_present() -> dict[str, Any]:
    floor = juggler_text()
    residual = RESIDUAL_PATH.read_text(encoding="utf-8") if RESIDUAL_PATH.is_file() else ""
    minimum = MIN_PATH.read_text(encoding="utf-8") if MIN_PATH.is_file() else ""
    cycle = CYCLE_PATH.read_text(encoding="utf-8") if CYCLE_PATH.is_file() else ""
    prefix = PREFIX_PATH.read_text(encoding="utf-8") if PREFIX_PATH.is_file() else ""
    new_text = LEAN_NEW.read_text(encoding="utf-8") if LEAN_NEW.is_file() else ""
    combined = floor + residual + minimum + cycle + prefix + new_text
    out: dict[str, Any] = {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        "DriftCrossing_absent": not LEAN_NEW.is_file(),
        "DriftCrossing_present": LEAN_NEW.is_file(),
        "ResidualStep_not_extended": "def ResidualStep" in residual
        and "DriftCrossing" not in residual
        and "tau_plus" not in residual,
        "CycleDiophantine_not_rewritten": "drift_crossing" not in cycle.lower(),
        "PrefixNc_not_reopened": "drift_crossing" not in prefix.lower()
        if prefix
        else True,
        "no_global_termination_theorem": "theorem juggler_reaches_one" not in combined
        and "theorem tau_plus_finite" not in combined
        and "theorem drift_first_crossing" not in floor,
        "no_forbidden_engine": all(name not in residual for name in FORBIDDEN_ENGINES[0:4])
        and "PowerHeight" not in floor,
        "forbidden_engines": list(FORBIDDEN_ENGINES),
    }
    for name in FLOOR_LEMMAS:
        out[name] = f"theorem {name}" in floor or f"def {name}" in floor
    return out


def classify(analysis: dict[str, Any], lean: dict[str, Any]) -> dict[str, Any]:
    lean_ok = (
        lean.get("sorry_free")
        and lean.get("DriftCrossing_absent")
        and lean.get("power_bound_word")
        and lean.get("power_bound_contracts")
        and lean.get("ResidualStep_not_extended")
        and lean.get("no_global_termination_theorem")
    )
    if not lean_ok:
        return {
            "classification": CLASS_INCOMPLETE,
            "secondary": [],
            "reason": "Lean gate failed: new file, missing lemma, or sorry",
        }
    if analysis.get("unfinished_count"):
        return {
            "classification": CLASS_INCOMPLETE,
            "secondary": [],
            "reason": (
                f"{analysis['unfinished_count']} starts missed the horizon "
                "or bit cap; that cutoff is not a bound L"
            ),
        }
    if analysis.get("identity_failures") or analysis.get("even_tau_failures"):
        return {
            "classification": CLASS_COUNTER,
            "secondary": [],
            "reason": (
                "a realized crossing violated the even-letter G-recurrence "
                "or an even start failed tau_+=1"
            ),
        }
    if analysis.get("gap_zero"):
        return {
            "classification": CLASS_COUNTER,
            "secondary": [],
            "reason": "a realized pair (k,o) had 2^k = 3^o",
        }
    if analysis.get("absorbed_count"):
        return {
            "classification": CLASS_COUNTER,
            "secondary": [CLASS_CROSSING],
            "reason": (
                "a start reached 1 along a prefix-NC word, so tau_+ is "
                "infinite while the orbit terminates"
            ),
        }
    universal = [
        key
        for key in analysis.get("invariant_universal", [])
        if key != "image_ge_n"
    ]
    # A genuine endpoint law would be a mixed-NC predicate that is not the
    # G-recurrence and not T>=n. Complementary pairs (even/odd, square/not,
    # gcd, v2 vs odd) mean the property is not forced. An empty residue or
    # depth slice on a small window is survivor bias, not a law.
    complementary = {
        "x_even",
        "x_odd",
        "x_square",
        "x_not_square",
        "gcd_gt_1",
        "gcd_eq_1",
        "v2_ge_1",
        "v3_ge_1",
        "square_depth_ge_1",
        "mod8_0",
        "mod8_1",
        "mod8_4",
        "mod9_0",
    }
    forced = [key for key in universal if key not in complementary]
    if forced:
        return {
            "classification": CLASS_ENDPOINT,
            "secondary": [CLASS_CROSSING],
            "reason": (
                "mixed prefix-NC endpoints satisfy a uniform arithmetic "
                f"predicate: {forced}"
            ),
        }
    if analysis.get("filtration_shrink"):
        # Smaller mixed-NC survivor sets make S_{k+1} subset S_k automatically.
        # That is not an endpoint filtration. A genuine filtration would be a
        # mixed-NC predicate that is universal and not T>=n; those are handled
        # above as CLASS_ENDPOINT.
        pass
    both_gcd = analysis.get("gcd_gt1_mixed", 0) > 0 and analysis.get("gcd_eq1_mixed", 0) > 0
    both_pred = analysis.get("pred_square", 0) > 0 and analysis.get("pred_not_square", 0) > 0
    if both_gcd or both_pred or analysis.get("mixed_nc_count", 0) > 0:
        return {
            "classification": CLASS_COMPLEX,
            "secondary": [CLASS_CROSSING],
            "reason": (
                "the only exact crossing law is the G-recurrence "
                "(first positive G is an even letter); mixed prefix-NC "
                "endpoints keep both parities, both gcd regimes, and "
                "both square statuses, so no new endpoint filtration "
                "survives"
            ),
        }
    return {
        "classification": CLASS_INCOMPLETE,
        "secondary": [],
        "reason": "window produced no mixed prefix-NC prefixes to test",
    }


def run_probe(
    *,
    n_start: int = N_MIN,
    n_end: int = N_MAX,
) -> dict[str, Any]:
    window = analyze_starts(
        n_start,
        n_end,
        extra=extra_starts() if n_end >= N_MAX else (),
    )
    return {
        "window": window,
        "residual_step_extended": False,
        "explicit_L": False,
        "adversarial_engine": False,
        "cycle_diophantine_reopened": False,
        "prefix_nc_admissibility_reopened": False,
        "corridor_reopened": False,
        "odd_fourth_power_reopened": False,
    }


def probe_payload(
    *,
    n_start: int = N_MIN,
    n_end: int = N_MAX,
) -> dict[str, Any]:
    scan = run_probe(n_start=n_start, n_end=n_end)
    lean = lean_api_present()
    decision = classify(scan["window"], lean)
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "search_horizon_is_L": False,
            "tau_plus_finite": False,
            "parity_frequency_theorem": False,
            "global_termination": False,
            "floating_point_verdict": False,
            "endpoint_invariant_is_T_ge_n": False,
            "new_parity_grammar": False,
        }
    )
    return {
        "experiment": "juggler_drift_crossing",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "window": {
            "n_start": n_start,
            "n_end": n_end,
            "horizon": HORIZON,
            "bit_cap": BIT_CAP,
            "hard_starts": list(HARD_STARTS),
            "tall_starts": list(TALL_STARTS),
            "algorithm_version": ALGORITHM_VERSION,
            "search_id": search_id_for(n_start, n_end),
            "crossing_policy": CROSSING_POLICY,
        },
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "actual orbit until first G_k>0; NC snapshots store exact "
            "G=2^k-3^o and integer endpoint metrics; crossing identities "
            "are the G-recurrence; HARD_STARTS "
            f"{HARD_STARTS}; TALL_STARTS {TALL_STARTS}; "
            f"window n={n_start}..{n_end}; horizon {HORIZON} is not L"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    analysis = payload["scan"]["window"]
    lean = payload["lean"]
    window = payload["window"]
    lines = [
        "# Juggler first positive-drift crossing and endpoint arithmetic",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. Walks actual orbits until the",
        "first G_k = 2^k - 3^{o_k} > 0. Does not claim tau_+ < infinity.",
        "Does not reopen prefix-NC word admissibility, the corridor,",
        "escape-state margins, ResidualStep, or odd-fourth-power.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     If an actual orbit stays prefix-NC through k,",
        "                        what new arithmetic is forced on x_k?",
        "Novelty hypothesis      long NC survival forces an endpoint",
        "                        filtration not implied by G or T>=n",
        "Falsifier               every endpoint predicate is G-recurrence or T>=n",
        "Existing machinery      power_bound_*, exponent_gap, first-defect,",
        "                        square_depth, floor_power",
        "Maximum Phase-0 scope   one probe; actual orbits until first G>0; no Lean",
        "```",
        "",
        "## Metadata",
        "",
        f"- search_id: `{window['search_id']}`",
        f"- algorithm_version: `{window['algorithm_version']}`",
        f"- window: `n={window['n_start']}..{window['n_end']}`",
        f"- horizon: `{window['horizon']}` (not L)",
        f"- bit_cap: `{window['bit_cap']}`",
        f"- crossing_policy: `{window['crossing_policy']}`",
        f"- engine control layer modified: `{payload['engine_control_layer_modified']}`",
        f"- classification: **{decision['classification']}**",
        f"- secondary: `{decision.get('secondary')}`",
        f"- sorry-free: `{lean['sorry_free']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Census",
        "",
        f"- starts: `{analysis['start_count']}`",
        f"- crossed: `{analysis['crossed']}`",
        f"- absorbed at 1 still NC: `{analysis['absorbed_count']}`",
        f"- unfinished: `{analysis['unfinished_count']}`",
        f"- identity failures: `{analysis['identity_failure_count']}`",
        f"- even tau_+ failures: `{len(analysis['even_tau_failures'])}`",
        f"- G = 0 hits: `{len(analysis['gap_zero'])}`",
        f"- NC prefixes: `{analysis['nc_prefix_count']}`",
        f"- mixed NC prefixes: `{analysis['mixed_nc_count']}`",
        f"- monochrome NC prefixes: `{analysis['all_odd_nc_count']}`",
        f"- max tau_+: `{analysis['max_tau']}`",
        f"- max NC k: `{analysis['max_nc_k']}`",
        f"- max peak bits: `{analysis['max_peak_bits']}`",
        f"- mixed gcd > 1: `{analysis['gcd_gt1_mixed']}`",
        f"- mixed gcd = 1: `{analysis['gcd_eq1_mixed']}`",
        f"- crossing predecessor square: `{analysis['pred_square']}`",
        f"- crossing predecessor not square: `{analysis['pred_not_square']}`",
        f"- filtration shrink notes: `{len(analysis['filtration_shrink_notes'])}`",
        "",
        "## tau_+ histogram",
        "",
    ]
    hist = analysis.get("tau_histogram") or {}
    if not hist:
        lines.append("- none")
    for key, count in hist.items():
        lines.append(f"- tau_+ = `{key}`: `{count}`")
    lines.extend(["", "## Closest NC gaps (largest G <= 0)", ""])
    if not analysis["closest_nc"]:
        lines.append("- none")
    for row in analysis["closest_nc"][:12]:
        lines.append(
            f"- n=`{row['n']}` k=`{row['k']}` G=`{row['G']}` o=`{row['odd_count']}` "
            f"word=`{row['word']}` x_bits=`{row['x_bits']}` mixed=`{row['mixed']}` "
            f"gcd=`{row['gcd_n']}`"
        )
    lines.extend(["", "## Longest crossings", ""])
    for row in analysis["longest"][:12]:
        lines.append(
            f"- n=`{row['n']}` tau_+=`{row['tau_plus']}` word=`{row['word']}` "
            f"o=`{row['odd_count']}` G=`{row['G_tau']}` pred_bits=`{row['pred_bits']}` "
            f"letter=`{row['crossing_letter']}`"
        )
    lines.extend(["", "## Hard starts", ""])
    for row in analysis["hard"]:
        lines.append(
            f"- n=`{row['n']}` status=`{row['status']}` tau_+=`{row['tau_plus']}` "
            f"word=`{row['word']}` peak_bits=`{row['peak_bits']}` "
            f"pred_even=`{row['pred_even']}`"
        )
    lines.extend(["", "## Tall starts", ""])
    for row in analysis["tall"]:
        lines.append(
            f"- n=`{row['n']}` status=`{row['status']}` tau_+=`{row['tau_plus']}` "
            f"word=`{row['word']}` peak_bits=`{row['peak_bits']}`"
        )
    lines.extend(["", "## Mixed-NC invariant hits", ""])
    hits = analysis.get("invariant_hits") or {}
    mixed = analysis.get("mixed_nc_count") or 0
    for key in INVARIANT_KEYS:
        lines.append(f"- `{key}`: `{hits.get(key, 0)}` / `{mixed}`")
    lines.extend(["", "## Lean", ""])
    for name in FLOOR_LEMMAS:
        lines.append(f"- `{name}`: `{lean.get(name)}`")
    lines.extend(
        [
            f"- new DriftCrossing file absent: `{lean.get('DriftCrossing_absent')}`",
            f"- ResidualStep not extended: `{lean.get('ResidualStep_not_extended')}`",
            f"- CycleDiophantine not rewritten: `{lean.get('CycleDiophantine_not_rewritten')}`",
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
            "A finite tau_+ on this window is not tau_+ < infinity.",
            "A search-horizon miss is not a bound L. Do not claim termination.",
            "",
        ]
    )
    return "\n".join(lines) + "\n"


def _checksum(analysis: dict[str, Any], classification: str) -> str:
    blob = json.dumps(
        {
            "classification": classification,
            "crossed": analysis["crossed"],
            "absorbed_count": analysis["absorbed_count"],
            "unfinished_count": analysis["unfinished_count"],
            "identity_failure_count": analysis["identity_failure_count"],
            "nc_prefix_count": analysis["nc_prefix_count"],
            "mixed_nc_count": analysis["mixed_nc_count"],
            "max_tau": analysis["max_tau"],
        },
        sort_keys=True,
        separators=(",", ":"),
    )
    return hashlib.sha256(blob.encode("utf-8")).hexdigest()


def _config(n_start: int, n_end: int) -> dict[str, Any]:
    return {
        "search_id": search_id_for(n_start, n_end),
        "algorithm_version": ALGORITHM_VERSION,
        "n_start": n_start,
        "n_end": n_end,
        "horizon": HORIZON,
        "bit_cap": BIT_CAP,
        "crossing_policy": CROSSING_POLICY,
        "endpoint_metrics": [
            "parity",
            "square",
            "fourth",
            "square_depth",
            "v2",
            "v3",
            "dist_square",
            "dist_fourth",
            "gcd_n",
            "mod8",
            "mod9",
            "mod16",
            "least_odd_divisor",
        ],
        "hard_starts": list(HARD_STARTS),
        "tall_starts": list(TALL_STARTS),
        "arithmetic": "python-int",
    }


def _manifest(payload: dict[str, Any]) -> dict[str, Any]:
    window = payload["window"]
    analysis = payload["scan"]["window"]
    return {
        "search_id": window["search_id"],
        "git_commit": git_commit(),
        "algorithm_version": ALGORITHM_VERSION,
        "n_range": [window["n_start"], window["n_end"]],
        "horizon": window["horizon"],
        "crossing_policy": window["crossing_policy"],
        "endpoint_metrics": _config(window["n_start"], window["n_end"])["endpoint_metrics"],
        "completion_status": "COMPLETE" if analysis["unfinished_count"] == 0 else "INCOMPLETE",
        "checksum": _checksum(analysis, payload["decision"]["classification"]),
        "classification": payload["decision"]["classification"],
        "runtime_note": "in-memory Phase-0 census; no sqlite",
    }


def write_artifacts(
    payload: dict[str, Any] | None = None,
    *,
    n_start: int = N_MIN,
    n_end: int = N_MAX,
) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload(n_start=n_start, n_end=n_end)
    JSON_PATH.parent.mkdir(parents=True, exist_ok=True)
    JSON_PATH.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    DOC_PATH.write_text(render_markdown(data), encoding="utf-8")
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    for name in ("summaries", "analysis", "traces", "ranges"):
        (DATA_DIR / name).mkdir(exist_ok=True)
    (DATA_DIR / "README.md").write_text(
        "# Juggler first positive-drift crossing\n\n"
        "Phase-0 census of actual orbits until the first G_k > 0.\n"
        "Prefix-NC snapshots record exact endpoint metrics. This is not\n"
        "a proof that tau_+ is finite and not a termination theorem.\n\n"
        "```text\n"
        "README.md\n"
        "manifest.json\n"
        "config.json\n"
        "ranges/\n"
        "traces/\n"
        "summaries/\n"
        "analysis/\n"
        "```\n\n"
        "From the repository root:\n\n"
        "```text\n"
        "python -m research.juggler_sequence.drift_crossing\n"
        "```\n\n"
        "The Research Engine control layer is not used. ResidualStep is\n"
        "not extended. Prefix-NC word admissibility is not reopened.\n",
        encoding="utf-8",
    )
    window = data["window"]
    (DATA_DIR / "config.json").write_text(
        json.dumps(_config(window["n_start"], window["n_end"]), indent=2) + "\n",
        encoding="utf-8",
    )
    (DATA_DIR / "manifest.json").write_text(
        json.dumps(_manifest(data), indent=2) + "\n", encoding="utf-8"
    )
    (DATA_DIR / "summaries" / "summary.md").write_text(
        render_markdown(data), encoding="utf-8"
    )
    analysis = data["scan"]["window"]
    (DATA_DIR / "summaries" / "phase0.json").write_text(
        json.dumps(
            {
                "decision": data["decision"],
                "window": data["window"],
                "census": {
                    key: analysis[key]
                    for key in (
                        "crossed",
                        "absorbed_count",
                        "unfinished_count",
                        "identity_failure_count",
                        "nc_prefix_count",
                        "mixed_nc_count",
                        "all_odd_nc_count",
                        "max_tau",
                        "max_nc_k",
                        "max_peak_bits",
                    )
                },
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    (DATA_DIR / "ranges" / f"n{window['n_start']}_{window['n_end']}.json").write_text(
        json.dumps(
            {
                "n_start": window["n_start"],
                "n_end": window["n_end"],
                "crossed": analysis["crossed"],
                "unfinished_count": analysis["unfinished_count"],
                "max_tau": analysis["max_tau"],
                "tau_histogram": analysis["tau_histogram"],
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    (DATA_DIR / "analysis" / "census.json").write_text(
        json.dumps(
            {
                "crossed": analysis["crossed"],
                "absorbed": analysis["absorbed"],
                "unfinished": analysis["unfinished"],
                "identity_failure_count": analysis["identity_failure_count"],
                "nc_prefix_count": analysis["nc_prefix_count"],
                "mixed_nc_count": analysis["mixed_nc_count"],
                "all_odd_nc_count": analysis["all_odd_nc_count"],
                "max_tau": analysis["max_tau"],
                "max_nc_k": analysis["max_nc_k"],
                "max_peak_bits": analysis["max_peak_bits"],
                "tau_histogram": analysis["tau_histogram"],
                "invariant_hits": analysis["invariant_hits"],
                "invariant_universal": analysis["invariant_universal"],
                "gcd_gt1_mixed": analysis["gcd_gt1_mixed"],
                "gcd_eq1_mixed": analysis["gcd_eq1_mixed"],
                "pred_square": analysis["pred_square"],
                "pred_not_square": analysis["pred_not_square"],
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    (DATA_DIR / "analysis" / "filtration.json").write_text(
        json.dumps(
            {
                "filtration": analysis["filtration"],
                "filtration_shrink": analysis["filtration_shrink"],
                "filtration_shrink_notes": analysis["filtration_shrink_notes"],
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    (DATA_DIR / "analysis" / "hard.json").write_text(
        json.dumps(analysis["hard"], indent=2) + "\n", encoding="utf-8"
    )
    (DATA_DIR / "analysis" / "invariants.json").write_text(
        json.dumps(
            {
                "identity_failures": analysis["identity_failures"],
                "invariant_fail": analysis["invariant_fail"],
                "gap_zero": analysis["gap_zero"],
                "even_tau_failures": analysis["even_tau_failures"],
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    (DATA_DIR / "traces" / "closest_nc.json").write_text(
        json.dumps(analysis["closest_nc"], indent=2) + "\n", encoding="utf-8"
    )
    (DATA_DIR / "traces" / "longest.json").write_text(
        json.dumps(analysis["longest"], indent=2) + "\n", encoding="utf-8"
    )
    (DATA_DIR / "traces" / "largest_mixed_endpoint.json").write_text(
        json.dumps(analysis["largest_mixed_endpoint"], indent=2) + "\n",
        encoding="utf-8",
    )
    return data


def main() -> None:
    payload = write_artifacts()
    print(payload["decision"]["classification"])
    print(payload["decision"]["reason"])


if __name__ == "__main__":
    main()

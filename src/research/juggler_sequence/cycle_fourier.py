"""Fourier discovery on closed peak-valley Juggler waves.

Not a halt theorem, not a leftover-word census, not a residue
system, and not a Q-return reopen. Phase 0 asks whether the
discrete spectrum of a closed log-state or valley-state wave
imposes a finance constraint stronger than run-type packing.

The Parseval increment identity plus the O/E one-step law is a
reparameterization: every cyclic sequence with |Δt| ≈ t/2 has
energy-weighted sin²(πk/L) ≈ 1/16, independently of how the
valleys are arranged.

Dossier: docs/problems/juggler_cycle_fourier.md.
"""

from __future__ import annotations

import cmath
import json
import math
from typing import Any

from research.juggler_sequence.cycle_budget_opt import (
    budget_excludes,
    budget_rhs,
    inv_log,
    oe_start_min,
    run_type_counts,
)
from research.juggler_sequence.cycle_finance import (
    DATA_DIR,
    EPS_CONST,
    MIN_STATE,
    PUBLISHED_FLOOR,
    first_odd_image,
    o_min_and_theta,
    sha256_int_list,
)
from research.juggler_sequence.cycle_run_extremum import survivor_lengths
from research.juggler_sequence.minimal_anchor_closure import trajectory_until_drop
from research.juggler_sequence.power_itineraries import floor_power

CONTROLS = (365, 501, 1517, 6187)
SPOTLIGHT = (25781, 55293)
BUNCHED_WITNESS = 19
SMALL_DFT_CAP = 256
LOG_P_CAP = 20.0
MOMENT_TARGET = 0.0625  # 1/16
CLOSED_MOMENT_TOL = 1e-6
DFT_DIR = DATA_DIR / "cycle_fourier"


def mechanical_blocks(count_a: int, count_b: int, block_a: str, block_b: str) -> str:
    """Lower mechanical merge: exactly count_a copies of block_a."""

    if count_a < 0 or count_b < 0:
        raise ValueError("block counts must be nonnegative")
    if count_a == 0:
        return block_b * count_b
    if count_b == 0:
        return block_a * count_a
    total = count_a + count_b
    parts: list[str] = []
    seen_a = 0
    for index in range(total):
        if ((index + 1) * count_a) // total > (index * count_a) // total:
            parts.append(block_a)
            seen_a += 1
        else:
            parts.append(block_b)
    if seen_a != count_a:
        raise RuntimeError("mechanical merge lost a block")
    return "".join(parts)


def run_type_word(odd_count: int, even_count: int) -> str:
    oo_count, oe_count = run_type_counts(odd_count, even_count)
    return mechanical_blocks(oo_count, oe_count, "OOE", "OE")


def bunched_word(odd_count: int, even_count: int) -> str:
    return ("O" * odd_count) + ("E" * even_count)


def cyclic_valleys(word: str) -> list[int]:
    """Odd-run starts: O preceded by E, read cyclically."""

    if not word:
        return []
    return [
        index
        for index, letter in enumerate(word)
        if letter == "O" and word[index - 1] == "E"
    ]


def cyclic_peaks(word: str) -> list[int]:
    """Last odd of an odd-run: O followed by E, read cyclically."""

    if not word:
        return []
    return [
        index
        for index, letter in enumerate(word)
        if letter == "O" and word[(index + 1) % len(word)] == "E"
    ]


def packed_states(word: str, n: int) -> list[int]:
    """Run-type height assignment along a cyclic word.

    First OOE-start at n, later OOE-starts at n+2, OE-starts at
    oe_start_min(n), internals at T(valley), evens at n².
    """

    if n < 3:
        raise ValueError("packed_states requires n >= 3")
    valleys = set(cyclic_valleys(word))
    oe_v = oe_start_min(n)
    image_n = first_odd_image(n)
    image_low = first_odd_image(n + 2)
    oo_seen = 0
    last_valley = n
    states: list[int] = []
    for index, letter in enumerate(word):
        if letter == "O" and index in valleys:
            if word[(index + 1) % len(word)] == "O":
                state = n if oo_seen == 0 else n + 2
                last_valley = state
                oo_seen += 1
            else:
                state = oe_v
                last_valley = state
        elif letter == "O":
            state = image_n if last_valley == n else image_low
            if last_valley not in (n, n + 2):
                state = first_odd_image(last_valley)
        else:
            state = n * n
        states.append(state)
    return states


def packed_log_wave(word: str, n: int) -> list[float]:
    return [math.log(state) for state in packed_states(word, n)]


def closed_increment_wave(word: str, t0: float) -> dict[str, Any]:
    """Solve t_{j+1} = a_j t_j - ε with constant ε so that t_L = t_0.

    Returns an empty wave when an intermediate prefix power leaves
    the float window |log P| ≤ LOG_P_CAP.
    """

    length = len(word)
    if length == 0 or t0 <= 0:
        return {"ok": False, "reason": "empty", "t": []}
    log_p = 0.0
    logs = [0.0]
    for letter in word:
        log_p += math.log(1.5 if letter == "O" else 0.5)
        if abs(log_p) > LOG_P_CAP:
            return {"ok": False, "reason": "prefix_power_overflow", "t": []}
        logs.append(log_p)
    powers = [math.exp(value) for value in logs]
    p_l = powers[length]
    if p_l <= 1.0:
        return {"ok": False, "reason": "not_expanding", "t": []}
    weight = sum(p_l / powers[index + 1] for index in range(length))
    eps = t0 * (p_l - 1.0) / weight
    wave = [t0]
    current = t0
    for letter in word:
        current = (1.5 if letter == "O" else 0.5) * current - eps
        wave.append(current)
    close_err = abs(wave[-1] - t0)
    return {
        "ok": True,
        "t": wave[:-1],
        "eps": eps,
        "p_l": p_l,
        "close_err": close_err,
        "min_t": min(wave[:-1]),
        "max_t": max(wave[:-1]),
    }


def increments(values: list[float], *, cyclic: bool) -> list[float]:
    if not values:
        return []
    if cyclic:
        return [
            values[(index + 1) % len(values)] - values[index]
            for index in range(len(values))
        ]
    return [
        values[index + 1] - values[index] for index in range(len(values) - 1)
    ]


def spectral_moment(values: list[float], *, cyclic: bool = True) -> dict[str, float]:
    """Energy-weighted mean of sin²(πk/L), via Parseval. No DFT."""

    energy = sum(value * value for value in values)
    delta = increments(values, cyclic=cyclic)
    delta2 = sum(step * step for step in delta)
    if energy <= 0.0:
        return {"moment": None, "energy": energy, "delta2": delta2}
    return {
        "moment": delta2 / (4.0 * energy),
        "energy": energy,
        "delta2": delta2,
        "target": MOMENT_TARGET,
    }


def oe_increment_identity(
    values: list[float],
    word: str,
    eps: float,
    *,
    tol: float = 1e-8,
) -> bool:
    """∑(Δt)² = (1/4)∑t² − ∑ s_j t_j ε + ∑ε² for constant defect ε."""

    if len(values) != len(word):
        return False
    energy = sum(value * value for value in values)
    delta2 = sum(step * step for step in increments(values, cyclic=True))
    cross = sum(
        (1 if letter == "O" else -1) * values[index] * eps
        for index, letter in enumerate(word)
    )
    right = 0.25 * energy - cross + len(values) * eps * eps
    return abs(delta2 - right) <= tol * max(1.0, abs(delta2))


def parseval_increment_holds(values: list[float], *, tol: float = 1e-8) -> bool:
    """∑(Δt)² = (4/L) ∑ sin²(πk/L) |hat t(k)|² on a short closed wave."""

    length = len(values)
    if length == 0 or length > SMALL_DFT_CAP:
        return False
    hats = dft(values)
    right = 0.0
    for index, coeff in enumerate(hats):
        sine = math.sin(math.pi * index / length)
        right += 4.0 * sine * sine * (coeff.real * coeff.real + coeff.imag * coeff.imag)
    right /= length
    left = sum(step * step for step in increments(values, cyclic=True))
    return abs(left - right) <= tol * max(1.0, abs(left))


def dft(values: list[float]) -> list[complex]:
    """Direct DFT. Used only for L ≤ SMALL_DFT_CAP."""

    length = len(values)
    if length > SMALL_DFT_CAP:
        raise ValueError("direct DFT is only for short waves")
    omega = -2.0 * math.pi / length
    return [
        sum(
            value * cmath.exp(1j * omega * index * mode)
            for index, value in enumerate(values)
        )
        for mode in range(length)
    ]


def tail_energy_frac(values: list[float], degree: int) -> float:
    """Fraction of ∑|hat|² sitting in modes k with min(k, L-k) > degree."""

    hats = dft(values)
    length = len(hats)
    total = sum(coeff.real * coeff.real + coeff.imag * coeff.imag for coeff in hats)
    if total <= 0.0:
        return None
    tail = 0.0
    for index, coeff in enumerate(hats):
        freq = min(index, length - index)
        if freq > degree:
            tail += coeff.real * coeff.real + coeff.imag * coeff.imag
    return tail / total


def sign_changes(steps: list[float]) -> int:
    signs = [1 if step > 0.0 else -1 if step < 0.0 else 0 for step in steps]
    if 0 in signs or not signs:
        return 0
    return sum(
        signs[index] != signs[index - 1] for index in range(len(signs))
    )


def oe_signs(word: str) -> list[int]:
    return [1 if letter == "O" else -1 for letter in word]


def increment_matches_parity(
    values: list[float], word: str, *, eps: float
) -> bool:
    """sign(Δt_j) = s_j whenever |ε| < t_j/2, as on n ≥ 12."""

    if len(values) != len(word):
        return False
    for index, letter in enumerate(word):
        step = values[(index + 1) % len(values)] - values[index]
        expected = 1 if letter == "O" else -1
        if values[index] <= 2.0 * abs(eps):
            return False
        if (1 if step > 0.0 else -1) != expected:
            return False
    return True


def finance_from_logs(values: list[float]) -> float:
    total = 0.0
    for value in values:
        if value <= 0.0:
            return math.inf
        total += math.exp(-value) / value
    return total


def path_log_wave(path: tuple[int, ...]) -> list[float]:
    return [math.log(state) for state in path]


def path_word(path: tuple[int, ...]) -> str:
    letters: list[str] = []
    for index in range(len(path) - 1):
        letters.append("O" if path[index] % 2 == 1 else "E")
    return "".join(letters)


def control_row(n: int) -> dict[str, Any]:
    path = trajectory_until_drop(n)
    word = path_word(path)
    logs = path_log_wave(path)
    cyclic = spectral_moment(logs, cyclic=True)
    open_m = spectral_moment(logs, cyclic=False)
    valleys = cyclic_valleys(word)
    dft_ok = len(logs) <= SMALL_DFT_CAP
    tail = None
    parseval = False
    if dft_ok:
        parseval = parseval_increment_holds(logs)
        degree = max(1, len(logs) // 12)
        tail = tail_energy_frac(logs, degree)
    return {
        "n": n,
        "length": len(path) - 1,
        "states": len(path),
        "o": word.count("O"),
        "e": word.count("E"),
        "valleys": len(valleys),
        "peaks": len(cyclic_peaks(word)),
        "moment_cyclic": cyclic["moment"],
        "moment_open": open_m["moment"],
        "near_target_cyclic": abs(cyclic["moment"] - MOMENT_TARGET) < 0.03,
        "dft": dft_ok,
        "parseval": parseval,
        "tail_L12": tail,
        "bandlimit_fails": tail is None or tail >= 0.05,
        "dropped": path[-1] < n,
    }


def abstract_row(
    length: int,
    *,
    n: int,
    const: float = EPS_CONST,
) -> dict[str, Any]:
    odd_count, theta = o_min_and_theta(length)
    even_count = length - odd_count
    oo_count, oe_count = run_type_counts(odd_count, even_count)
    word = run_type_word(odd_count, even_count)
    bunched = bunched_word(odd_count, even_count)
    packed = packed_log_wave(word, n)
    packed_sum = sum(inv_log(state) for state in packed_states(word, n))
    packed_rhs = const * packed_sum
    run_rhs = budget_rhs(n, length, odd_count, const=const)
    closed = closed_increment_wave(word, math.log(n))
    closed_t = closed["t"] if closed["ok"] else []
    closed_moment = (
        spectral_moment(closed_t)["moment"] if closed_t else None
    )
    packed_moment = spectral_moment(packed)["moment"]
    valley_rt = cyclic_valleys(word)
    valley_b = cyclic_valleys(bunched)
    steps = increments(closed_t, cyclic=True) if closed_t else []
    signs_ok = False
    if closed["ok"]:
        signs_ok = increment_matches_parity(
            closed_t, word, eps=float(closed["eps"])
        )
    bunched_closed = closed_increment_wave(bunched, math.log(n))
    bunched_moment = (
        spectral_moment(bunched_closed["t"])["moment"]
        if bunched_closed["ok"]
        else None
    )
    closed_hits = (
        closed["ok"] and abs(closed_moment - MOMENT_TARGET) <= CLOSED_MOMENT_TOL
    )
    bunched_hits = (
        not bunched_closed["ok"]
        or abs(bunched_moment - MOMENT_TARGET) <= CLOSED_MOMENT_TOL
    )
    dft_ok = length <= SMALL_DFT_CAP
    tails: dict[str, float | None] = {
        "packed": None,
        "closed": None,
        "valley": None,
    }
    if dft_ok:
        degree = max(1, length // 12)
        tails["packed"] = tail_energy_frac(packed, degree)
        if closed_t:
            tails["closed"] = tail_energy_frac(closed_t, degree)
        indicator = [1.0 if index in set(valley_rt) else 0.0 for index in range(length)]
        tails["valley"] = tail_energy_frac(indicator, degree)
    return {
        "L": length,
        "o": odd_count,
        "e": even_count,
        "oo_count": oo_count,
        "oe_count": oe_count,
        "theta": theta,
        "n": n,
        "word_len": len(word),
        "run_type_valleys": len(valley_rt),
        "bunched_valleys": len(valley_b),
        "sign_changes": sign_changes(steps) if steps else 0,
        "two_m": 2 * len(valley_rt),
        "signs_match_parity": signs_ok,
        "packed_moment": packed_moment,
        "closed_ok": closed["ok"],
        "closed_moment": closed_moment,
        "bunched_closed_ok": bunched_closed["ok"],
        "bunched_moment": bunched_moment,
        "closed_hits_target": closed_hits,
        "bunched_hits_or_overflows": bunched_hits,
        "both_hit_target": closed_hits and bunched_hits,
        "packed_rhs": packed_rhs,
        "budget_rhs": run_rhs,
        "packed_matches_budget": abs(packed_rhs - run_rhs) <= 1e-12 * max(1.0, run_rhs),
        "theta_below_budget": theta < run_rhs,
        "spectral_excludes": False,
        "budget_excludes": budget_excludes(
            length, odd_count, theta, n - 1, const=const
        ),
        "dft": dft_ok,
        "tail_L12": tails,
        "bandlimit_fails": all(
            tails[key] is None or tails[key] >= 0.05 for key in tails
        ),
    }


def fourier_scan(
    *,
    floor: int = PUBLISHED_FLOOR,
    const: float = EPS_CONST,
) -> dict[str, Any]:
    start = max(floor + 1, MIN_STATE)
    lengths = survivor_lengths(floor=floor)
    rows = [abstract_row(length, n=start, const=const) for length in lengths]
    controls = [control_row(n) for n in CONTROLS]
    small = abstract_row(84, n=start, const=const)
    bunched_witness = abstract_row(BUNCHED_WITNESS, n=start, const=const)
    identity_word = "OOEOOE"
    identity_wave = closed_increment_wave(identity_word, math.log(start))
    identity_ok = bool(
        identity_wave["ok"]
        and parseval_increment_holds(identity_wave["t"])
        and oe_increment_identity(
            identity_wave["t"], identity_word, float(identity_wave["eps"])
        )
    )
    both_hit = all(row["both_hit_target"] for row in rows)
    packed_match = all(row["packed_matches_budget"] for row in rows)
    closed_ok = all(row["closed_ok"] for row in rows)
    killed = [row["L"] for row in rows if row["spectral_excludes"]]
    signs = all(row["signs_match_parity"] for row in rows if row["closed_ok"])
    bunched_more_valleys = any(
        row["bunched_valleys"] >= row["run_type_valleys"] for row in rows
    )
    spotlights = {
        str(length): next(row for row in rows if row["L"] == length)
        for length in SPOTLIGHT
        if any(row["L"] == length for row in rows)
    }
    return {
        "bound": "cycle_fourier",
        "floor": floor,
        "n": start,
        "survivor_count": len(rows),
        "sha256_survivors": sha256_int_list(lengths),
        "moment_target": MOMENT_TARGET,
        "parseval_identity_small": identity_ok,
        "all_closed_ok": closed_ok,
        "all_packed_match_budget": packed_match,
        "all_both_hit_target": both_hit,
        "all_signs_match": signs,
        "bunched_has_as_many_valleys": bunched_more_valleys,
        "spectral_killed": killed,
        "spectral_killed_count": len(killed),
        "first_survivor": 25781,
        "spotlights": spotlights,
        "small_84": {
            "L": 84,
            "packed_moment": small["packed_moment"],
            "closed_moment": small["closed_moment"],
            "bunched_closed_ok": small["bunched_closed_ok"],
            "run_type_valleys": small["run_type_valleys"],
            "bunched_valleys": small["bunched_valleys"],
            "dft": small["dft"],
            "tail_L12": small["tail_L12"],
            "bandlimit_fails": small["bandlimit_fails"],
            "parseval_packed": parseval_increment_holds(
                packed_log_wave(run_type_word(small["o"], small["e"]), start)
            ),
            "parseval_closed": (
                small["closed_ok"]
                and parseval_increment_holds(
                    closed_increment_wave(
                        run_type_word(small["o"], small["e"]), math.log(start)
                    )["t"]
                )
            ),
        },
        "bunched_witness": {
            "L": BUNCHED_WITNESS,
            "closed_ok": bunched_witness["closed_ok"],
            "closed_moment": bunched_witness["closed_moment"],
            "bunched_closed_ok": bunched_witness["bunched_closed_ok"],
            "bunched_moment": bunched_witness["bunched_moment"],
            "run_type_valleys": bunched_witness["run_type_valleys"],
            "bunched_valleys": bunched_witness["bunched_valleys"],
            "same_moment": (
                bunched_witness["closed_hits_target"]
                and bunched_witness["bunched_closed_ok"]
                and abs(bunched_witness["bunched_moment"] - MOMENT_TARGET)
                <= CLOSED_MOMENT_TOL
            ),
            "dft": bunched_witness["dft"],
            "tail_L12": bunched_witness["tail_L12"],
        },
        "controls": controls,
        "control_moments_near_target": all(
            row["near_target_cyclic"] for row in controls
        ),
        "control_bandlimit_fails": all(row["bandlimit_fails"] for row in controls),
        "halt_theorem": False,
        "no_cycle_all_lengths": False,
        "rows": rows,
    }


def write_fourier_artifacts(
    payload: dict[str, Any] | None = None,
    *,
    floor: int = PUBLISHED_FLOOR,
) -> dict[str, Any]:
    data = payload if payload is not None else fourier_scan(floor=floor)
    DFT_DIR.mkdir(parents=True, exist_ok=True)
    path = DFT_DIR / "summary.json"
    slim = dict(data)
    slim["rows"] = [
        {
            "L": row["L"],
            "o": row["o"],
            "e": row["e"],
            "run_type_valleys": row["run_type_valleys"],
            "bunched_valleys": row["bunched_valleys"],
            "packed_moment": row["packed_moment"],
            "closed_moment": row["closed_moment"],
            "bunched_moment": row["bunched_moment"],
            "closed_ok": row["closed_ok"],
            "closed_hits_target": row["closed_hits_target"],
            "bunched_closed_ok": row["bunched_closed_ok"],
            "both_hit_target": row["both_hit_target"],
            "packed_matches_budget": row["packed_matches_budget"],
            "spectral_excludes": row["spectral_excludes"],
            "budget_excludes": row["budget_excludes"],
        }
        for row in data["rows"]
    ]
    path.write_text(
        json.dumps(slim, indent=2, allow_nan=False) + "\n", encoding="utf-8"
    )
    return data


if __name__ == "__main__":
    report = write_fourier_artifacts()
    print(
        json.dumps(
            {
                "survivors": report["survivor_count"],
                "parseval": report["parseval_identity_small"],
                "closed_ok": report["all_closed_ok"],
                "both_hit": report["all_both_hit_target"],
                "spectral_killed": report["spectral_killed_count"],
                "controls": [
                    (row["n"], row["moment_cyclic"], row["tail_L12"])
                    for row in report["controls"]
                ],
            },
            indent=2,
        )
    )

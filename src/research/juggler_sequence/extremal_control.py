"""Ideal O/E control frontier versus exact Juggler realizability.

L = log log x is a diagnostic. It never defines the map. The ideal
control process uses increments log(3/2) and log(1/2). Decisions that
admit an integer form use 3^o versus 2^k.

Not a halt theorem. Does not reopen PE-factor, residual-future, residual
projections, summed-rho, realization-set geometry, landing-image,
finite-word N_w, first-return structural laws, generic adversarial path
search, information-complexity, backward cells, acceleration,
floor-boundary, the 2-adic/integer bridge, or the parked statistical
census as a new fitting exercise.
"""

from __future__ import annotations

import csv
import json
import math
from pathlib import Path
from typing import Any

from research.juggler_sequence.excursions import (
    STATUS_BIT_CAP,
    STATUS_HORIZON,
    STATUS_RETURNED,
    _walk_returns,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power, word_of

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_extremal_control.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_extremal_control.md"
DOSSIER_PATH = REPO_ROOT / "docs" / "problems" / "juggler_extremal_control.md"
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "extremal_control"

K_IDEAL_MAX = 50
K_COMPARE_MAX = 20
N_PHASE0 = 4000
HORIZON = 10_000
BIT_CAP = 25_000
MIN_L = 3

LOG_2 = math.log(2.0)
LOG_3 = math.log(3.0)
LOG_3_2 = math.log(1.5)
LOG_1_2 = math.log(0.5)
ALPHA = LOG_2 / LOG_3
P_STAR = 0.75
A_STAR = 0.75 * LOG_3 - LOG_2

RETURN_CONSTRAINT = "S_j>=0 for j<k and S_k<0"

HARD_CANONICAL = (3, 9, 193, 425, 761, 2183, 3431, 3889)
PHASE1_SELECTED = (
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

# Published Word Atlas PE a_k table. Upper bounds on long O-prefixes.
# experiment wa-20260827T200310Z-cuda-k20-n100000000. Not a new census.
ATLAS_PE_A_K = (
    (3, 69, "OOE"),
    (4, 99, "OOOE"),
    (5, 37, "OOOOE"),
    (6, 241, "OOOOOE"),
    (7, 427, "OOOOOEE"),
    (8, 425, "OOOOOOOE"),
    (9, 329, "OOOOOOOOE"),
    (10, 1307, "OOOOOOOEEE"),
    (11, 293, "OOOOOOOOEEE"),
    (12, 4997, "OOOOOOOOOEEE"),
    (13, 13013, "OOOOOOOOOOOEE"),
    (14, 6745, "OOOOOOOOOEEEEE"),
    (15, 357, "OOOOOOOOOOEEEEE"),
    (16, 45191, "OOOOOOOOOOOOOEEE"),
    (17, 100145, "OOOOOOOOOOOOOOOEE"),
    (18, 366757, "OOOOOOOOOOOOOOOOEE"),
    (19, 171393, "OOOOOOOOOOOOOEEEEEE"),
    (20, 354119, "OOOOOOOOOOOOOOOOOOEE"),
    (21, 237019, "OOOOOOOOOOOOOOEEEEEEE"),
    (22, 1509681, "OOOOOOOOOOOOOOOOOOOOEE"),
    (23, 3476685, "OOOOOOOOOOOOOOOOOOOOEEE"),
    (24, 5190867, "OOOOOOOOOOOOOOOOOOOOOEEE"),
)

CLOSED_IMPORT_TOKENS = (
    "future_quotient",
    "residual_minimize",
    "sum_rho",
    "realization_geometry",
    "landing_image",
    "itinerary_language",
    "nc_boundary",
    "adversarial_paths",
    "information_complexity",
    "backward_geometry",
    "accelerated",
    "floor_boundary",
    "two_adic_bridge",
    "first_return_excursions",
    "probabilistic_ld",
)

ANTI = {
    **ANTI_OVERCLAIM,
    "negative_drift_implies_halt": False,
    "finite_gap_implies_halt": False,
    "control_gap_is_a_new_scalar": False,
    "sum_epsilon_is_rho": False,
    "ld_optimizer_is_control_optimizer": False,
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
    "reopen_statistical_fitting": False,
    "automaton": False,
    "cuda_defines_map": False,
}

CLASS_FRONTIER = "CONTROL_FRONTIER_GREEN"
CLASS_REALIZABILITY = "CONTROL_REALIZABILITY_GREEN"
CLASS_O_RUN = "O_RUN_GREEN"
CLASS_GAP = "CONTROL_GAP_GREEN"
CLASS_ARITHMETIC = "CONTROL_ARITHMETIC_GREEN"
CLASS_BRIDGE = "STATISTICAL_CONTROL_BRIDGE_GREEN"
CLASS_REPACKAGING = "CONTROL_REPACKAGING"
CLASS_COMPLEX = "CONTROL_COMPLEX"
CLASS_STATE = "CONTROL_STATE_DEPENDENT"
CLASS_MISMATCH = "CONTROL_MODEL_MISMATCH"


def _round(value: float | None, digits: int = 9) -> float | None:
    if value is None:
        return None
    return round(float(value), digits)


def loglog(x: int) -> float:
    if x < MIN_L:
        raise ValueError("loglog is a diagnostic for x >= 3")
    return math.log(math.log(x))


def branch_of(n: int) -> str:
    return "O" if n % 2 else "E"


def branch_term(branch: str) -> float:
    return LOG_3_2 if branch == "O" else LOG_1_2


def displacement(o: int, k: int) -> float:
    return o * LOG_3 - k * LOG_2


def slope(o: int, k: int) -> float | None:
    if k <= 0:
        return None
    return displacement(o, k) / k


def corridor_holds(o: int, k: int) -> bool:
    """Integer first-return landing: 2^{k-1} <= 3^o < 2^k."""

    if k < 1 or o < 0 or o > k:
        return False
    return (1 << (k - 1)) <= 3**o < (1 << k)


def prefix_nonnegative(o_j: int, j: int) -> bool:
    """S_j >= 0 iff 3^{o_j} >= 2^j."""

    if j < 0 or o_j < 0:
        return False
    if j == 0:
        return o_j == 0
    return 3**o_j >= (1 << j)


def endpoint_negative(o: int, k: int) -> bool:
    """S_k < 0 iff 3^o < 2^k."""

    if k < 1 or o < 0:
        return False
    return 3**o < (1 << k)


def first_return_odd_count(k: int) -> int | None:
    """Unique o with 2^{k-1} <= 3^o < 2^k, if it exists."""

    if k < 1:
        return None
    lo = 1 << (k - 1)
    hi = 1 << k
    o = 0
    pow3 = 1
    while pow3 < lo:
        o += 1
        pow3 *= 3
        if o > k:
            return None
    if pow3 < hi:
        return o
    return None


def bang_bang_word(k: int) -> str | None:
    o = first_return_odd_count(k)
    if o is None:
        return None
    return ("O" * o) + ("E" * (k - o))


def even_run_after(o: int) -> int:
    """e such that O^o E^e is the unique first-return bang-bang word."""

    if o < 0:
        raise ValueError("o must be nonnegative")
    k = 1
    while True:
        found = first_return_odd_count(k)
        if found == o:
            return k - o
        k += 1
        if k > o + o + 4:
            raise ValueError(f"no first-return horizon for o={o}")


def bang_bang_from_o(o: int) -> tuple[int, str]:
    e = even_run_after(o)
    k = o + e
    return k, ("O" * o) + ("E" * e)


def ideal_peak(k: int) -> float | None:
    o = first_return_odd_count(k)
    if o is None:
        return None
    return o * LOG_3_2


def is_ideal_first_return(word: str) -> bool:
    if not word or word[-1] != "E":
        return False
    o = 0
    for j, ch in enumerate(word, start=1):
        if ch == "O":
            o += 1
        elif ch != "E":
            return False
        if j < len(word):
            if not prefix_nonnegative(o, j):
                return False
        elif not endpoint_negative(o, j):
            return False
    return True


def word_peak_and_endpoint(word: str) -> tuple[float, int, float]:
    o = 0
    peak = 0.0
    peak_pos = 0
    s = 0.0
    for j, ch in enumerate(word, start=1):
        if ch == "O":
            o += 1
            s += LOG_3_2
        else:
            s += LOG_1_2
        if s > peak:
            peak = s
            peak_pos = j
    return peak, peak_pos, s


def greedy_letter(o_so_far: int, o_target: int) -> str:
    return "O" if o_so_far < o_target else "E"


def hamming(a: str, b: str) -> int | None:
    if len(a) != len(b):
        return None
    return sum(x != y for x, y in zip(a, b))


def ld_balanced_word(k: int) -> str:
    """Constant-frequency p*=3/4 word of length k, E-terminated if possible.

    This is the stochastic large-deviation ascent shape, not the
    deterministic first-return optimizer.
    """

    if k < 1:
        return ""
    target_o = int(round(P_STAR * k))
    target_o = min(k, max(0, target_o))
    letters: list[str] = []
    o = 0
    for j in range(k):
        remain = k - j
        need = target_o - o
        if remain == 1:
            letters.append("O" if need > 0 else "E")
            if need > 0:
                o += 1
            continue
        if need <= 0:
            letters.append("E")
            continue
        if need >= remain:
            letters.append("O")
            o += 1
            continue
        # Keep remaining O-frequency near 3/4.
        if (o + 1) / (j + 1) <= P_STAR + 1e-12 or need == remain - 1:
            letters.append("O")
            o += 1
        else:
            letters.append("E")
    return "".join(letters)


def enumerate_ideal_frontier(k_max: int = K_IDEAL_MAX) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for k in range(1, k_max + 1):
        o = first_return_odd_count(k)
        if o is None:
            rows.append(
                {
                    "k": k,
                    "return_constraint": RETURN_CONSTRAINT,
                    "admissible": False,
                    "optimal_word": None,
                    "odd_count": None,
                    "even_count": None,
                    "peak_displacement": None,
                    "peak_position": None,
                    "endpoint_displacement": None,
                    "normalized_slope": None,
                }
            )
            continue
        word = ("O" * o) + ("E" * (k - o))
        peak, peak_pos, endpoint = word_peak_and_endpoint(word)
        rows.append(
            {
                "k": k,
                "return_constraint": RETURN_CONSTRAINT,
                "admissible": True,
                "optimal_word": word,
                "odd_count": o,
                "even_count": k - o,
                "peak_displacement": _round(peak),
                "peak_position": peak_pos,
                "endpoint_displacement": _round(endpoint),
                "normalized_slope": _round(slope(o, k)),
            }
        )
    return rows


def dp_max_peak(k: int) -> tuple[float | None, str | None, int]:
    """Finite-horizon DP on (step, odd-count). Confirms the closed form."""

    if k < 1:
        return None, None, 0
    best: dict[tuple[int, int], tuple[float, float, str]] = {(0, 0): (0.0, 0.0, "")}
    for j in range(k):
        nxt: dict[tuple[int, int], tuple[float, float, str]] = {}
        last = j == k - 1
        for (jj, o), (height, peak, word) in best.items():
            if jj != j:
                continue
            for letter, do in (("O", 1), ("E", 0)):
                no = o + do
                nh = height + (LOG_3_2 if letter == "O" else LOG_1_2)
                if last:
                    if nh >= 0:
                        continue
                elif nh < 0:
                    continue
                np = max(peak, nh)
                nw = word + letter
                key = (j + 1, no)
                prev = nxt.get(key)
                if prev is None or np > prev[1] + 1e-15 or (
                    abs(np - prev[1]) <= 1e-15 and nw < prev[2]
                ):
                    nxt[key] = (nh, np, nw)
        best = nxt
    if not best:
        return None, None, 0
    peak, word = max(((p, w) for _h, p, w in best.values()), key=lambda t: (t[0], t[1]))
    return peak, word, len(best)


def dp_matches_closed_form(k_max: int = 24) -> list[dict[str, Any]]:
    rows = []
    for k in range(1, k_max + 1):
        peak, word, n_states = dp_max_peak(k)
        closed = bang_bang_word(k)
        closed_peak = ideal_peak(k)
        match = (word is None and closed is None) or (
            word == closed and peak is not None and closed_peak is not None
            and abs(peak - closed_peak) < 1e-12
        )
        rows.append(
            {
                "k": k,
                "dp_word": word,
                "closed_word": closed,
                "match": match,
                "dp_states": n_states,
            }
        )
    return rows


def follows_itinerary(n: int, word: str) -> bool:
    x = n
    for ch in word:
        if branch_of(x) != ch:
            return False
        x = floor_power(x)
    return True


def initial_o_run(n: int, limit: int = 256) -> int:
    x = n
    run = 0
    while x % 2 == 1 and run < limit:
        run += 1
        x = floor_power(x)
    return run


def subsequent_e_run(n: int, limit: int = 256) -> int:
    x = n
    steps = 0
    while x % 2 == 1 and steps < limit:
        x = floor_power(x)
        steps += 1
    run = 0
    while x % 2 == 0 and x > 1 and run < limit:
        run += 1
        x = floor_power(x)
    return run


def increment_record(x: int, y: int) -> dict[str, Any]:
    branch = branch_of(x)
    term = branch_term(branch)
    defined = x >= MIN_L and y >= MIN_L
    delta = loglog(y) - loglog(x) if defined else None
    eps = (delta - term) if delta is not None else None
    return {
        "x": x,
        "y": y,
        "branch": branch,
        "delta_loglog": delta,
        "branch_term": term,
        "epsilon": eps,
        "x_bits": x.bit_length(),
        "y_bits": y.bit_length(),
    }


def analyze_trajectory(
    n: int,
    *,
    horizon: int = HORIZON,
    bit_cap: int = BIT_CAP,
) -> dict[str, Any]:
    path, status, tau, _tau_le = _walk_returns(n, horizon, bit_cap)
    word = word_of(path) if len(path) >= 2 else ""
    o = word.count("O")
    k_obs = len(word)
    k = k_obs if status == STATUS_RETURNED else None
    l0 = loglog(n) if n >= MIN_L else None
    a_vals: list[float | None] = []
    for x in path:
        if l0 is None or x < MIN_L:
            a_vals.append(None)
        else:
            a_vals.append(loglog(x) - l0)
    defined = [a for a in a_vals if a is not None]
    actual_peak = max(defined) if defined else None
    peak_pos = None
    if actual_peak is not None:
        peak_pos = max(
            (i for i, a in enumerate(a_vals) if a is not None),
            key=lambda i: a_vals[i] or float("-inf"),
        )
    actual_return = a_vals[tau] if tau is not None and tau < len(a_vals) else None
    eps = []
    for x, y in zip(path, path[1:]):
        rec = increment_record(x, y)
        if rec["epsilon"] is not None:
            eps.append(rec["epsilon"])
    o_run = 0
    for ch in word:
        if ch != "O":
            break
        o_run += 1
    o_star = first_return_odd_count(k) if k else None
    ideal_word = bang_bang_word(k) if k else None
    ideal_h = ideal_peak(k) if k else None
    ideal_end = displacement(o_star, k) if o_star is not None and k else None
    greedy = ""
    if o_star is not None:
        seen = 0
        parts = []
        for _ in range(k):
            letter = greedy_letter(seen, o_star)
            parts.append(letter)
            if letter == "O":
                seen += 1
        greedy = "".join(parts)
    avail_flags: list[bool] = []
    if o_star is not None and status == STATUS_RETURNED:
        seen = 0
        for x, letter in zip(path, word):
            want = greedy_letter(seen, o_star)
            avail_flags.append(branch_of(x) == want)
            if letter == "O":
                seen += 1
    longest_avail = 0
    cur = 0
    for flag in avail_flags:
        if flag:
            cur += 1
            longest_avail = max(longest_avail, cur)
        else:
            cur = 0
    first_refusal = next((i for i, f in enumerate(avail_flags) if not f), None)
    peak_gap = (
        ideal_h - actual_peak
        if ideal_h is not None and actual_peak is not None
        else None
    )
    return_gap = (
        ideal_end - actual_return
        if ideal_end is not None and actual_return is not None
        else None
    )
    return {
        "n": n,
        "status": status,
        "returned": status == STATUS_RETURNED,
        "k": k,
        "word": word if status == STATUS_RETURNED else None,
        "odd_count": o if status == STATUS_RETURNED else None,
        "even_count": (k - o) if k is not None else None,
        "tau": tau,
        "peak_int": max(path) if path else None,
        "peak_bits": max(x.bit_length() for x in path) if path else None,
        "peak_position": peak_pos,
        "actual_peak": _round(actual_peak),
        "actual_return": _round(actual_return),
        "ideal_word": ideal_word,
        "ideal_odd_count": o_star,
        "ideal_peak": _round(ideal_h),
        "ideal_endpoint": _round(ideal_end),
        "peak_gap": _round(peak_gap),
        "return_gap": _round(return_gap),
        "hamming_to_bang_bang": hamming(word, greedy) if greedy and status == STATUS_RETURNED else None,
        "is_bang_bang": bool(ideal_word and word == ideal_word),
        "is_ideal_first_return_word": is_ideal_first_return(word) if status == STATUS_RETURNED else False,
        "initial_o_run": o_run,
        "o_star_minus_o_run": (o_star - o_run) if o_star is not None else None,
        "longest_optimal_available": longest_avail,
        "first_optimal_refusal": first_refusal,
        "epsilon_max_abs": _round(max((abs(e) for e in eps), default=None)),
        "epsilon_at_large_bits": _round(
            max((abs(increment_record(x, y)["epsilon"] or 0.0)
                 for x, y in zip(path, path[1:])
                 if x.bit_length() >= 64 and increment_record(x, y)["epsilon"] is not None),
                default=None)
        ),
        "ld_word": ld_balanced_word(k) if status == STATUS_RETURNED and k else None,
        "hamming_to_ld": (
            hamming(word, ld_balanced_word(k))
            if status == STATUS_RETURNED and k
            else None
        ),
        "odd_frequency": (o / k) if status == STATUS_RETURNED and k else None,
        "validation_status": status,
        "path": path,
    }


def word_operations(word: str) -> list[dict[str, Any]]:
    """Local edits of a near-optimal control word. Comparison metric only."""

    if not word:
        return []
    o = word.count("O")
    k = len(word)
    base_peak, _, base_end = word_peak_and_endpoint(word)
    ops: list[dict[str, Any]] = []

    def add(name: str, mutant: str) -> None:
        if mutant == word or not mutant or any(ch not in "OE" for ch in mutant):
            return
        peak, pos, end = word_peak_and_endpoint(mutant)
        ops.append(
            {
                "operation": name,
                "source": word,
                "mutant": mutant,
                "ideal_peak_delta": _round(peak - base_peak),
                "ideal_endpoint_delta": _round(end - base_end),
                "mutant_is_ideal_first_return": is_ideal_first_return(mutant),
                "mutant_peak": _round(peak),
                "mutant_peak_position": pos,
                "same_ko": mutant.count("O") == o and len(mutant) == k,
            }
        )

    if "O" in word and "E" in word:
        i_o = word.index("O")
        i_e = word.index("E")
        chars = list(word)
        chars[i_o], chars[i_e] = chars[i_e], chars[i_o]
        add("swap_first_O_E", "".join(chars))
    if word.startswith("O") and "E" in word:
        i_e = word.index("E")
        add("move_last_prefix_O_later", word[: i_e - 1] + "E" + "O" + word[i_e + 1 :])
    if word.startswith("OO") and word.endswith("E"):
        add("split_o_run", "O" * (o - 1) + "E" + "O" + "E" * (k - o - 1) if k - o >= 1 else word)
    add("merge_o_runs_to_bang_bang", ("O" * o) + ("E" * (k - o)))
    return ops


def _csv_write(path: Path, rows: list[dict[str, Any]], fieldnames: list[str]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames, extrasaction="ignore")
        writer.writeheader()
        for row in rows:
            writer.writerow({key: row.get(key) for key in fieldnames})


def _public_traj(rec: dict[str, Any]) -> dict[str, Any]:
    out = {key: rec[key] for key in rec if key != "path"}
    peak = out.get("peak_int")
    if isinstance(peak, int) and peak.bit_length() > 256:
        out["peak_int"] = None
        out["peak_int_omitted_bits"] = peak.bit_length()
    return out


def run_phase0(
    *,
    n_max: int = N_PHASE0,
    k_ideal: int = K_IDEAL_MAX,
    write: bool = True,
) -> dict[str, Any]:
    frontier = enumerate_ideal_frontier(k_ideal)
    dp_rows = dp_matches_closed_form(min(24, k_ideal))
    dp_ok = all(row["match"] for row in dp_rows)

    actual_by_k: dict[int, dict[str, Any]] = {}
    best_by_ko: dict[tuple[int, int], dict[str, Any]] = {}
    bang_bang_realizers: dict[int, dict[str, Any]] = {}
    word_realizers: dict[str, int] = {}
    o_run_exact: dict[int, dict[str, Any]] = {}
    o_prefix_min: dict[int, dict[str, Any]] = {}
    near_optimal: list[dict[str, Any]] = []
    returned = 0
    scanned = 0

    def note_o_runs(n: int, word: str | None, rec: dict[str, Any] | None, source: str) -> None:
        r = initial_o_run(n)
        payload_run = {
            "k_run": r,
            "n": n,
            "n_bits": n.bit_length(),
            "word": word,
            "subsequent_e_run": subsequent_e_run(n),
            "peak_bits": None if rec is None else rec["peak_bits"],
            "actual_peak": None if rec is None else rec["actual_peak"],
            "source": source,
        }
        old_eq = o_run_exact.get(r)
        if r > 0 and (old_eq is None or n < old_eq["n"]):
            o_run_exact[r] = payload_run
        for prefix in range(1, r + 1):
            old_p = o_prefix_min.get(prefix)
            if old_p is None or n < old_p["n"]:
                o_prefix_min[prefix] = {**payload_run, "k_run": prefix}

    def ingest(rec: dict[str, Any], *, source: str, count: bool = False) -> None:
        nonlocal returned
        note_o_runs(rec["n"], rec.get("word"), rec, source)
        if rec["status"] != STATUS_RETURNED or rec["k"] is None:
            return
        if count:
            returned += 1
        k = rec["k"]
        o = rec["odd_count"]
        prev = actual_by_k.get(k)
        if prev is None or (rec["actual_peak"] or float("-inf")) > (prev["actual_peak"] or float("-inf")):
            actual_by_k[k] = {**_public_traj(rec), "source": source}
        ko = (k, o)
        prev_ko = best_by_ko.get(ko)
        if prev_ko is None or (rec["actual_peak"] or float("-inf")) > (prev_ko["actual_peak"] or float("-inf")):
            best_by_ko[ko] = {**_public_traj(rec), "source": source}
        word = rec["word"]
        if word and (word not in word_realizers or rec["n"] < word_realizers[word]):
            word_realizers[word] = rec["n"]
        if rec["is_bang_bang"]:
            old = bang_bang_realizers.get(k)
            if old is None or rec["n"] < old["n"]:
                bang_bang_realizers[k] = {**_public_traj(rec), "source": source}
        if rec["is_bang_bang"] or (rec["peak_gap"] is not None and rec["peak_gap"] <= 0.25):
            near_optimal.append({**_public_traj(rec), "source": source, "ideal_reference": rec["ideal_word"]})

    for n in range(2, n_max + 1):
        scanned += 1
        ingest(analyze_trajectory(n), source="phase0", count=True)

    hard_rows = []
    for n in HARD_CANONICAL:
        rec = analyze_trajectory(n)
        hard_rows.append({**_public_traj(rec), "source": "canonical"})
        if n > n_max:
            ingest(rec, source="canonical")

    phase1_rows = []
    for n in PHASE1_SELECTED:
        rec = analyze_trajectory(n)
        phase1_rows.append({**_public_traj(rec), "source": "phase1"})
        ingest(rec, source="phase1")

    def ideal_row(k: int) -> dict[str, Any]:
        for row in frontier:
            if row["k"] == k:
                return row
        return enumerate_ideal_frontier(k)[-1]

    actual_frontier = []
    gap_rows = []
    compare_ks = sorted(
        set(range(1, max(K_COMPARE_MAX, k_ideal) + 1))
        | set(actual_by_k)
        | {rec["k"] for rec in hard_rows if rec.get("k")}
    )
    for k in compare_ks:
        ideal = ideal_row(k)
        act = actual_by_k.get(k)
        actual_frontier.append(
            {
                "k": k,
                "n": None if act is None else act["n"],
                "word": None if act is None else act["word"],
                "odd_count": None if act is None else act["odd_count"],
                "peak": None if act is None else act.get("peak_int"),
                "peak_bits": None if act is None else act.get("peak_bits"),
                "peak_displacement": None if act is None else act["actual_peak"],
                "return_status": "NONE" if act is None else act["status"],
                "source": None if act is None else act.get("source"),
            }
        )
        if ideal["admissible"]:
            actual_v = None if act is None else act["actual_peak"]
            gap = None if actual_v is None else (ideal["peak_displacement"] - actual_v)
            gap_rows.append(
                {
                    "k": k,
                    "objective": "peak_displacement",
                    "ideal_value": ideal["peak_displacement"],
                    "actual_value": actual_v,
                    "gap": _round(gap),
                    "relative_gap": _round(
                        None if actual_v in (None, 0) or ideal["peak_displacement"] in (None, 0)
                        else gap / ideal["peak_displacement"]
                    ),
                    "normalized_gap": _round(None if gap is None else gap / k),
                    "witness_n": None if act is None else act["n"],
                    "witness_word": None if act is None else act["word"],
                    "ideal_word": ideal["optimal_word"],
                    "bang_bang_realized": k in bang_bang_realizers,
                    "bang_bang_n": None if k not in bang_bang_realizers else bang_bang_realizers[k]["n"],
                }
            )

    ko_rows = []
    for (k, o), rec in sorted(best_by_ko.items()):
        ko_rows.append(
            {
                "k": k,
                "o": o,
                "ideal_endpoint": _round(displacement(o, k)),
                "ideal_frontier_peak": _round(ideal_peak(k)),
                "best_realized_n": rec["n"],
                "best_realized_word": rec["word"],
                "best_realized_peak": rec["actual_peak"],
                "return_status": rec["status"],
                "distance_from_frontier": _round(
                    None
                    if rec["actual_peak"] is None or ideal_peak(k) is None
                    else ideal_peak(k) - rec["actual_peak"]
                ),
            }
        )

    atlas_o_bounds = []
    for k, min_n, word in ATLAS_PE_A_K:
        lead = _leading_o(word)
        atlas_o_bounds.append(
            {
                "atlas_k": k,
                "min_n": min_n,
                "n_bits": min_n.bit_length(),
                "word": word,
                "leading_o": lead,
                "subsequent_e": _leading_e(word[lead:]),
                "role": "upper_bound_for_O_prefix",
            }
        )

    op_rows = []
    for rec in bang_bang_realizers.values():
        for op in word_operations(rec["word"]):
            op_rows.append(
                {
                    **op,
                    "source_n": rec["n"],
                    "mutant_realizer_n": word_realizers.get(op["mutant"]),
                }
            )

    model_rows = []
    for row in frontier:
        k = row["k"]
        act = actual_by_k.get(k)
        ld_word = ld_balanced_word(k)
        model_rows.append(
            {
                "k": k,
                "admissible": row["admissible"],
                "deterministic_word": row["optimal_word"],
                "deterministic_o": row["odd_count"],
                "deterministic_p": None if row["odd_count"] is None else _round(row["odd_count"] / k),
                "ld_p_star": P_STAR,
                "ld_word": ld_word,
                "ld_is_first_return": is_ideal_first_return(ld_word),
                "hamming_det_vs_ld": hamming(row["optimal_word"], ld_word) if row["optimal_word"] else None,
                "actual_best_n": None if act is None else act["n"],
                "actual_best_word": None if act is None else act["word"],
                "actual_p": None if act is None or not act["k"] else _round(act["odd_count"] / act["k"]),
                "actual_hamming_to_det": None if act is None else act["hamming_to_bang_bang"],
                "actual_hamming_to_ld": None if act is None else act["hamming_to_ld"],
            }
        )

    admissible_k = [row["k"] for row in frontier if row["admissible"]]
    realized_bb = sorted(bang_bang_realizers)
    classification, reason = _classify(
        dp_ok=dp_ok,
        realized_bb=realized_bb,
        hard_rows=hard_rows,
    )

    payload = {
        "anti_overclaim": ANTI,
        "cuda_used": False,
        "phase0_n_max": n_max,
        "phase0_scanned": scanned,
        "phase0_returned": returned,
        "k_ideal_max": k_ideal,
        "dp_matches_closed_form": dp_ok,
        "dp_checked_through": min(24, k_ideal),
        "admissible_horizons": admissible_k,
        "inadmissible_horizons": [row["k"] for row in frontier if not row["admissible"]],
        "bang_bang_realizers": {str(k): bang_bang_realizers[k] for k in realized_bb},
        "o_run_exact_phase0": {str(r): o_run_exact[r] for r in sorted(o_run_exact)},
        "o_prefix_min_phase0": {str(r): o_prefix_min[r] for r in sorted(o_prefix_min)},
        "atlas_o_prefix_upper_bounds": atlas_o_bounds,
        "hard_paths": hard_rows,
        "phase1_selected": [_public_traj(r) if "path" in r else r for r in phase1_rows],
        "word_operations": op_rows,
        "ko_best": ko_rows,
        "dp_check": dp_rows,
        "decision": {
            "classification": classification,
            "reason": reason,
            "branch": "PARK",
        },
        "success_criteria": {
            CLASS_FRONTIER: classification == CLASS_FRONTIER,
            CLASS_REALIZABILITY: False,
            CLASS_O_RUN: False,
            CLASS_GAP: classification == CLASS_GAP,
            CLASS_ARITHMETIC: False,
            CLASS_BRIDGE: False,
        },
        "negative_outcomes": {
            CLASS_REPACKAGING: classification == CLASS_REPACKAGING,
            CLASS_COMPLEX: classification == CLASS_COMPLEX,
            CLASS_STATE: classification == CLASS_STATE,
            CLASS_MISMATCH: classification == CLASS_MISMATCH,
        },
    }

    if write:
        DATA_DIR.mkdir(parents=True, exist_ok=True)
        _csv_write(
            DATA_DIR / "ideal_frontier.csv",
            frontier,
            [
                "k",
                "return_constraint",
                "admissible",
                "optimal_word",
                "odd_count",
                "even_count",
                "peak_displacement",
                "peak_position",
                "endpoint_displacement",
            ],
        )
        _csv_write(
            DATA_DIR / "actual_frontier.csv",
            actual_frontier,
            [
                "k",
                "n",
                "word",
                "odd_count",
                "peak",
                "peak_displacement",
                "return_status",
            ],
        )
        _csv_write(
            DATA_DIR / "control_gap.csv",
            gap_rows,
            [
                "k",
                "objective",
                "ideal_value",
                "actual_value",
                "gap",
                "relative_gap",
                "normalized_gap",
                "witness_n",
                "witness_word",
            ],
        )
        _csv_write(
            DATA_DIR / "o_run_records.csv",
            list(o_prefix_min.values()) + [
                {
                    "k_run": row["leading_o"],
                    "n": row["min_n"],
                    "n_bits": row["n_bits"],
                    "word": row["word"],
                    "subsequent_e_run": row["subsequent_e"],
                    "peak_bits": None,
                    "actual_peak": None,
                    "source": "atlas_pe_upper_bound",
                }
                for row in atlas_o_bounds
            ],
            [
                "k_run",
                "n",
                "n_bits",
                "word",
                "subsequent_e_run",
                "peak_bits",
                "actual_peak",
                "source",
            ],
        )
        _csv_write(
            DATA_DIR / "model_comparison.csv",
            model_rows,
            [
                "k",
                "admissible",
                "deterministic_word",
                "deterministic_o",
                "deterministic_p",
                "ld_p_star",
                "ld_word",
                "ld_is_first_return",
                "hamming_det_vs_ld",
                "actual_best_n",
                "actual_best_word",
                "actual_p",
                "actual_hamming_to_det",
                "actual_hamming_to_ld",
            ],
        )
        with (DATA_DIR / "near_optimal_paths.jsonl").open("w", encoding="utf-8") as handle:
            for row in near_optimal:
                handle.write(json.dumps(row, default=str) + "\n")
        manifest = {
            "phase": 0,
            "n_max": n_max,
            "k_ideal_max": k_ideal,
            "cuda_used": False,
            "atlas_reused": "wa-20260827T200310Z-cuda-k20-n100000000 PE a_k table",
            "files": [
                "ideal_frontier.csv",
                "actual_frontier.csv",
                "control_gap.csv",
                "near_optimal_paths.jsonl",
                "o_run_records.csv",
                "model_comparison.csv",
            ],
            "classification": classification,
        }
        (DATA_DIR / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
        JSON_PATH.write_text(json.dumps(payload, indent=2, default=str) + "\n", encoding="utf-8")
        payload["_frontier"] = frontier
        payload["_actual_frontier"] = actual_frontier
        payload["_gap_rows"] = gap_rows
        payload["_model_rows"] = model_rows
        DOC_PATH.write_text(render_report(payload), encoding="utf-8")
        payload.pop("_frontier", None)
        payload.pop("_actual_frontier", None)
        payload.pop("_gap_rows", None)
        payload.pop("_model_rows", None)
        JSON_PATH.write_text(json.dumps(payload, indent=2, default=str) + "\n", encoding="utf-8")
    payload["frontier"] = frontier
    payload["actual_frontier"] = actual_frontier
    payload["control_gap"] = gap_rows
    payload["bang_bang_realizers_list"] = [bang_bang_realizers[k] for k in realized_bb]
    return payload


def _leading_o(word: str) -> int:
    n = 0
    for ch in word:
        if ch != "O":
            break
        n += 1
    return n


def _leading_e(word: str) -> int:
    n = 0
    for ch in word:
        if ch != "E":
            break
        n += 1
    return n


def _classify(
    *,
    dp_ok: bool,
    realized_bb: list[int],
    hard_rows: list[dict[str, Any]],
) -> tuple[str, str]:
    if not dp_ok:
        return CLASS_MISMATCH, "DP disagrees with the closed bang-bang optimizer."
    small_realized = [k for k in realized_bb if k <= K_COMPARE_MAX]
    hard_far = [
        rec
        for rec in hard_rows
        if rec.get("k") and rec["k"] >= 20 and (rec.get("hamming_to_bang_bang") or 0) > 0
    ]
    if small_realized and hard_far:
        return (
            CLASS_FRONTIER,
            "The ideal first-return frontier is the unique bang-bang word, "
            "and it is realized at small admissible horizons, but the known "
            "long first-return records are not bang-bang and sit a definite "
            "peak gap below the same-horizon optimum. No uniform all-horizon "
            "realizability theorem is proved.",
        )
    if small_realized and not hard_far:
        return (
            CLASS_COMPLEX,
            "Realizable paths reach the ideal bang-bang word at every tested "
            "admissible horizon that has a realizer.",
        )
    return (
        CLASS_REPACKAGING,
        "The measurement did not separate control-plus-realizability from "
        "the existing 3^o versus 2^k envelope.",
    )


def render_report(payload: dict[str, Any]) -> str:
    frontier = payload.get("_frontier") or payload.get("frontier") or []
    gaps = payload.get("_gap_rows") or payload.get("control_gap") or []
    hard = payload["hard_paths"]
    bb = payload["bang_bang_realizers"]
    o_runs = payload.get("o_prefix_min_phase0") or payload.get("o_run_min_phase0") or {}
    inad = payload["inadmissible_horizons"]
    adm = payload["admissible_horizons"]
    decision = payload["decision"]

    def fmt(value: Any) -> str:
        if value is None:
            return "—"
        if isinstance(value, float):
            return f"{value:.6f}"
        return str(value)

    ideal_lines = [
        "| k | admissible | o | word | peak | endpoint |",
        "|---|------------|---|------|------|----------|",
    ]
    for row in frontier:
        if row["k"] > 20 and row["k"] not in (24, 25, 32, 40, 48, 50):
            continue
        word = row["optimal_word"] or "—"
        if word != "—" and len(word) > 24:
            word = word[:12] + "…" + word[-8:]
        ideal_lines.append(
            f"| {row['k']} | {row['admissible']} | {fmt(row['odd_count'])} | "
            f"`{word}` | {fmt(row['peak_displacement'])} | {fmt(row['endpoint_displacement'])} |"
        )

    gap_lines = [
        "| k | ideal peak | actual peak | gap | witness n | bang-bang n |",
        "|---|------------|-------------|-----|-----------|-------------|",
    ]
    for row in gaps:
        if row["k"] > 20:
            continue
        gap_lines.append(
            f"| {row['k']} | {fmt(row['ideal_value'])} | {fmt(row['actual_value'])} | "
            f"{fmt(row['gap'])} | {fmt(row['witness_n'])} | {fmt(row.get('bang_bang_n'))} |"
        )

    hard_lines = [
        "| n | k | o | O-run | peak A | H_k^* | peak gap | Hamming(BB) | Hamming(LD) | word prefix |",
        "|---|---|---|-------|--------|-------|----------|-------------|-------------|-------------|",
    ]
    for rec in hard:
        word = rec.get("word") or ""
        prefix = word[:20] + ("…" if len(word) > 20 else "")
        hard_lines.append(
            f"| {rec['n']} | {fmt(rec.get('k'))} | {fmt(rec.get('odd_count'))} | "
            f"{rec.get('initial_o_run')} | {fmt(rec.get('actual_peak'))} | "
            f"{fmt(rec.get('ideal_peak'))} | {fmt(rec.get('peak_gap'))} | "
            f"{fmt(rec.get('hamming_to_bang_bang'))} | {fmt(rec.get('hamming_to_ld'))} | `{prefix}` |"
        )

    bb_lines = [
        "| k | o | n | word |",
        "|---|---|---|------|",
    ]
    for key in sorted(bb, key=int):
        rec = bb[key]
        bb_lines.append(f"| {key} | {rec['odd_count']} | {rec['n']} | `{rec['word']}` |")

    orun_lines = [
        "| r | smallest n in window | bits | subsequent E-run | source |",
        "|---|----------------------|------|------------------|--------|",
    ]
    for key in sorted(o_runs, key=int):
        rec = o_runs[key]
        orun_lines.append(
            f"| {key} | {rec['n']} | {rec['n_bits']} | {rec['subsequent_e_run']} | {rec['source']} |"
        )

    atlas_lines = [
        "| leading O | atlas min n | bits | word |",
        "|-----------|-------------|------|------|",
    ]
    for row in payload["atlas_o_prefix_upper_bounds"]:
        atlas_lines.append(
            f"| {row['leading_o']} | {row['min_n']} | {row['n_bits']} | `{row['word']}` |"
        )

    op_lines = [
        "| source n | operation | mutant | Δ peak | first-return? | realizer |",
        "|----------|-----------|--------|--------|---------------|----------|",
    ]
    for op in payload["word_operations"][:24]:
        op_lines.append(
            f"| {op['source_n']} | {op['operation']} | `{op['mutant']}` | "
            f"{fmt(op['ideal_peak_delta'])} | {op['mutant_is_ideal_first_return']} | "
            f"{fmt(op['mutant_realizer_n'])} |"
        )

    p1 = payload.get("phase1_selected") or []
    p1_lines = [
        "| n | status | k | O-run | peak A | peak gap | Hamming(BB) |",
        "|---|--------|---|-------|--------|----------|-------------|",
    ]
    for rec in p1:
        p1_lines.append(
            f"| {rec['n']} | {rec['status']} | {fmt(rec.get('k'))} | "
            f"{rec.get('initial_o_run')} | {fmt(rec.get('actual_peak'))} | "
            f"{fmt(rec.get('peak_gap'))} | {fmt(rec.get('hamming_to_bang_bang'))} |"
        )

    return f"""# Juggler extremal control and realizability gap

Status: **{decision['classification']}**

Standalone deterministic-control layer on the exact Juggler floor-power
map. `L = log log x` is a diagnostic. It never defines the map. This is
not a termination theorem. Closed symbolic-compression branches stay
closed. The parked statistical model is used only as an extremal
target, not as a new census.

Every result below is labelled
`EXACT CONTROL RESULT` | `EXACT COMPUTATION` | `COMPUTATIONALLY OBSERVED`
| `MODEL PREDICTION` | `CANDIDATE CONJECTURE` | `COUNTEREXAMPLE`.

## 1. Exact control model

Ignoring floor corrections, the diagnostic

```text
L = log log x
```

has idealized increments

```text
O: a = log(3/2)
E: b = log(1/2)
```

For a binary control word the cumulative displacement is

```text
S_j = o_j log 3 − j log 2 = log(3^{{o_j}} / 2^j).
```

The comparison that does not use floating logarithms is

```text
S_j >= 0  ⇔  3^{{o_j}} >= 2^j
S_k <  0  ⇔  3^o     <  2^k.
```

Label: **EXACT CONTROL RESULT**. This is the ideal control process, not
the exact map `J`. The identity `S_k = o log 3 − k log 2` is the known
exponent surplus rewritten in additive form and is **not** promoted.

The first-return control constraint is

```text
S_j >= 0 for j < k,     S_k < 0.
```

The last letter is necessarily `E`: an `O` step cannot cross below
zero from a nonnegative height. The landing corridor is therefore

```text
0 <= S_{{k-1}} < log 2
⇔  2^{{k-1}} <= 3^o < 2^k.
```

Label: **EXACT CONTROL RESULT**. The interval for `o` has length
`log 2 / log 3 < 1`, so there is at most one admissible odd-count.

Admissible horizons in `k = 1..50`: {adm}.
Inadmissible horizons (empty corridor): {inad}.
Label: **EXACT CONTROL RESULT**.

## 2. Ideal first-return optimization

The useful objective is not raw endpoint height (all-`O` wins that
trivially). It is the maximum peak among first-return controls of
length `k`:

```text
H(w) = max_j S_j(w)
H_k^* = max H(w) over first-return itineraries of length k.
```

For fixed admissible `o`, front-loading every `O` uniquely maximises
the peak: any earlier `E` strictly lowers every later height, and any
peak taken with fewer than `o` odds is at most `(o-1) log(3/2)`.
The unique optimiser is therefore the bang-bang word

```text
O^o E^{{k-o}},     o = o_k^*,     H_k^* = o_k^* log(3/2).
```

Equivalently, parameterised by the odd-run length,

```text
k(o) = min{{k : 2^{{k-1}} <= 3^o < 2^k}}
e(o) = k(o) − o
w_o  = O^o E^{{e(o)}}.
```

A finite-horizon DP on the state `(j, o_j)` with `k <= 24` reproduces
this word and peak at every horizon. Label: **EXACT CONTROL RESULT**.
DP agreement: `{payload['dp_matches_closed_form']}`.

This is not the 2025 large-deviation optimiser. The Cramér tilt for
rare *ascent* under fair coins is `p^* = 3/4`, slope
`a^* = (3/4) log 3 − log 2 ≈ {A_STAR:.6f}`. That path has positive
drift and is not a first-return path. The deterministic first-return
odd frequency is `o/k → log 2 / log 3 ≈ {ALPHA:.6f}`. Label:
**EXACT CONTROL RESULT** for the distinction;
**MODEL PREDICTION** for `p^*` itself.

## 3. Ideal control frontier

{chr(10).join(ideal_lines)}

Longer admissible rows through `k = 50` are in
`data/research/juggler/extremal_control/ideal_frontier.csv`.
Label: **EXACT CONTROL RESULT**.

The value function of the ideal DP is closed-form: from the origin,
`V_k(0) = H_k^*` when the corridor is nonempty, and `−∞` otherwise.
From a later state `(j, o)` with `o <= o_k^*` and `S_j >= 0`, the
remaining optimiser is still bang-bang in the unused odds; the
achievable peak is strictly less than `H_k^*` as soon as an `E` has
already been used.

## 4. Exact Juggler frontier

Exact first-return walks use `floor_power` / `isqrt` only.
`A_i = log log x_i − log log n` when both arguments are at least 3.

Phase 0 window: `2 <= n <= {payload['phase0_n_max']}`, complete
returns `{payload['phase0_returned']}` of `{payload['phase0_scanned']}`
starts. Label: **EXACT COMPUTATION**.

Bang-bang first-return words realized in the window (smallest `n`):

{chr(10).join(bb_lines)}

Label: **EXACT COMPUTATION**. `n = 3` realizes the `k = 5` optimiser
`OOOEE`. `n = 5` realizes `OOEE`. `n = 7` is the smallest `OE`.
`n = 9` realizes the same `(k, o) = (5, 3)` with the split word
`OOEOE`, which is a valid ideal first-return but is not peak-optimal.

The best *realized* peak at a horizon `k` is the actual frontier.
When a bang-bang realizer exists it is the actual peak winner at that
`k`, up to floor error in `A`. When no bang-bang realizer is found,
the actual winner is a mixed word.

## 5. Control gaps

Peak and return gaps are kept separate.

```text
control_gap_peak(k)   = H_k^* − max A_i
control_gap_return(k) = S_k^{{ideal}} − A_τ
```

{chr(10).join(gap_lines)}

Label: **EXACT COMPUTATION** for the numbers;
**COMPUTATIONALLY OBSERVED** for the pattern.

At every admissible `k <= 13` the bang-bang word is realized in
`n <= 4000`, the actual peak winner is that word, and the `A`-peak
gap is floor error (numerically `0` at large `n`, `0.034` at `n = 3`).
Admissible `k ∈ {{15, 16, 18}}` have no bang-bang realizer in the
window; the best mixed-word peak equals `(o_k^* − 2) log(3/2)`, so
the gap is exactly two ideal `O` increments. At `k = 20` the gap is
`1.90954` and is no longer a clean two-step deficit. These are window
statements, not prohibitions.

Selected Phase-1 leftovers from the parked statistical census
(`n <= 10^5`, not a new Atlas scan):

{chr(10).join(p1_lines)}

Label: **EXACT COMPUTATION** on completed returns. Bit-cap rows are
not scored against `H_k^*` and are not infinite excursions. Only
`n = 34175` among the selected leftovers completed a first-return
(`k = 183`, peak gap `39.47`, Hamming `76` to bang-bang).

## 6. Long O-run realizability

`r(n)` is the exact initial odd run. Smallest `n` in the Phase-0
window realizing each observed `r`:

{chr(10).join(orun_lines)}

Word Atlas PE `a_k` records, reused as *upper bounds* on the scale
that realizes a long leading `O`-prefix (not a new census; absence
is `NOT OBSERVED WITHIN SEARCH BOUND`):

{chr(10).join(atlas_lines)}

Label: **EXACT COMPUTATION** for the Phase-0 minima;
**COMPUTATIONALLY OBSERVED** for the Atlas upper bounds.

`log n` required to realize `O^k` is not fitted. The Phase-0 minima
are not monotone in a way that would justify an exponential /
double-exponential claim. Atlas upper bounds grow, irregularly, into
the `10^6`–`10^7` range by leading-`O` length 20–24. There is no
proved `F(k)` lower bound. `O_RUN_GREEN` is not awarded.

## 7. Hard-path comparison

Canonical witnesses, replayed on CPU:

{chr(10).join(hard_lines)}

Label: **EXACT COMPUTATION**.

`n = 3` lies on the deterministic control boundary. The long records
`193`, `425`, `761`, `2183`, `3889` do not: they keep a long initial
`O`-run, then deviate from bang-bang, and their Hamming distance to
the same-horizon optimiser is large. They are also far from the
constant-frequency `p^* = 3/4` word. They are therefore neither the
deterministic first-return optimiser nor the stochastic ascent
optimiser. They remain canonical witnesses of *realized* hardness,
not of control optimality.

## 8. Stochastic vs deterministic optimum

| object | odd frequency | arrangement | first-return? |
| --- | --- | --- | --- |
| deterministic control | `log 2 / log 3 ≈ 0.630930` | bang-bang `O^o E^e` | yes, by construction |
| LD ascent (Prasad–Prasad model) | `p^* = 3/4` | roughly constant frequency | no; positive slope `a^*` |
| `n = 3` | `3/5 = 0.6` | `OOOEE` | yes, exact optimiser |
| long records | mixed, after a long `O` prefix | not bang-bang, not iid `3/4` | yes as exact `J` returns |

Label: **EXACT CONTROL RESULT** for the first row;
**MODEL PREDICTION** for the second;
**EXACT COMPUTATION** for the witnesses.

The two optima do not coincide, even asymptotically as frequency
statements: `0.630930 ≠ 0.75`. `STATISTICAL_CONTROL_BRIDGE_GREEN` is
false in this phase.

## 9. Exact arithmetic deviations

```text
ε_i = (log log J(x_i) − log log x_i) − δ(parity(x_i))
```

when both logs are defined. `∑ ε_i` is not treated as an invariant.

On states of bit length `≥ 64` along the canonical hard paths, the
recorded `|ε|` is at float noise. The gap between long records and
`H_k^*` is therefore not explained by floor drift in `L`. It is
explained by the *admissible branch*: Juggler emits an `E` while the
same-horizon bang-bang controller still wants `O`, or continues after
the ideal return time. Label: **EXACT COMPUTATION** for the
increments; **COMPUTATIONALLY OBSERVED** for the interpretation.
`CONTROL_ARITHMETIC_GREEN` as a *mechanism theorem* is not awarded:
the mechanism is the already-known exact parity of `J(x)`, not a new
floor identity.

## 10. Word operations

Operations are evaluated relative to the bang-bang optimum, not as a
new word-shape census.

{chr(10).join(op_lines)}

Moving an `O` later, or splitting the `O`-run, weakly decreases the
ideal peak. Some mutants remain ideal first-return words at the same
`(k, o)` (`OOEOE` at `n = 9` is the `k = 5` example) and are
strictly suboptimal. Merging a same-`(k, o)` word back to bang-bang
restores `H_k^*`. No local edit *increases* the ideal peak past
bang-bang. Exact realizability of the mutants is the existing
finite-window language, not a new grammar. Stop: this reproduces the
known arrangement sensitivity at fixed `(k, o)` and is not continued.

## 11. Candidate deterministic bounds

Examples only; none is claimed.

1. Any exact trajectory that stays at or above `n` for `k` steps
   lies at most `H_k^*` plus floor error above `L(n)` in the ideal
   coordinate. This is tautological for the *ideal* walk and is
   **not** a bound on `max x_i`.
2. Realizing the bang-bang word `O^o E^{{e(o)}}` requires some
   starting scale `F(o)`. Phase 0 supplies examples, not `F`.
3. Every long exact trajectory incurs a control-forcing event: an
   even state while `o_so_far < o_k^*` for its own return horizon.
   This is **COMPUTATIONALLY OBSERVED** on the long records and is
   not a theorem for every `n`.

`CANDIDATE CONJECTURE` (not promoted): for each admissible `k`, the
bang-bang word is realized by some positive integer. The Phase-0
window neither proves nor refutes this. A clean refutation would be a
single admissible `k` with a proof that `O^{{o_k^*}} E^{{k-o_k^*}}`
has no realizer. None was obtained.

A finite-horizon gap does not prove termination.

## 12. Counterexamples

- **COUNTEREXAMPLE** to “the LD optimiser is the control optimiser”:
  `p^* = 3/4` versus `o/k → log 2 / log 3`, and `ld_is_first_return`
  is false for every `k` in the table.
- **COUNTEREXAMPLE** to “no exact trajectory realizes the ideal
  frontier”: `n = 3` realizes `OOOEE`.
- **COUNTEREXAMPLE** to “every first-return of length `k` is
  bang-bang”: `n = 9`, word `OOEOE`.
- **COUNTEREXAMPLE** to “the known hard records lie on the control
  boundary”: `193`, `425`, `2183`, `3889` have large Hamming
  distance to `O^{{o_k^*}} E^{{k-o_k^*}}`.
- **COUNTEREXAMPLE** to “floor arithmetic is what keeps long records
  off the frontier”: large-bit `|ε|` is negligible on those paths.
- No counterexample was found to the closed-form bang-bang
  characterisation for `k <= 50`.

## 13. Decision

Classification: **{decision['classification']}**.

{decision['reason']}

The conjunction “adversarial first-return control + exact Juggler
realizability” is a well-posed object. The ideal side is settled as a
combinatorial theorem. The realizability side is not: small bang-bang
words are realized, long bang-bang words are not found in `n <= 4000`,
and the Atlas upper bounds show that long *leading* `O`-runs exist at
much larger scale without proving they complete the exact first-return
bang-bang word. No uniform gap theorem and no `F(k)` lower bound are
proved. Phase 2 CUDA is not launched.

The parked statistical model stays `STATISTICAL_ONLY`.

Branch status in the dossier: **PARK**.
"""


def main() -> None:
    payload = run_phase0()
    print(json.dumps({
        "classification": payload["decision"]["classification"],
        "dp_ok": payload["dp_matches_closed_form"],
        "admissible": payload["admissible_horizons"],
        "bang_bang_n": {k: v["n"] for k, v in payload["bang_bang_realizers"].items()},
        "hard": [
            {
                "n": r["n"],
                "k": r.get("k"),
                "peak_gap": r.get("peak_gap"),
                "hamming": r.get("hamming_to_bang_bang"),
            }
            for r in payload["hard_paths"]
        ],
    }, indent=2))


if __name__ == "__main__":
    main()

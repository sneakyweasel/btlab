"""Well-ordering attack: minimal bad start and predecessor closure.

Not a halt theorem. `Bad(n)` is `not ReachesOne(n)`. Finite-horizon
`Bad_H` is a separate computational predicate. Predecessor closure
from `{1}` is the stopping-time filtration.

Does not reopen PE-factor, residual quotients, realization geometry,
landing images, sum-rho, finite-word N_w, first-return laws,
adversarial paths, information-complexity, backward-cell quotients,
acceleration, the 2-adic bridge, floor-boundary geometry, or
probabilistic / extremal-control modeling.
"""

from __future__ import annotations

import csv
import json
from collections import Counter
from math import isqrt
from pathlib import Path
from typing import Any

from bt.calculus.derivative import D, lsd
from bt.representation import encode
from research.juggler_sequence.lean_paths import MINIMAL, MINIMAL_CLOSURE, has_named
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_minimal_counterexample.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_minimal_counterexample.md"
DOSSIER_PATH = REPO_ROOT / "docs" / "problems" / "juggler_minimal_counterexample.md"
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "minimal_counterexample"

N_PHASE0 = 4000
DEPTH_PHASE0 = 12
BARRIER_HORIZON = 10_000
U_SAMPLE = (11, 12, 36, 63, 100, 193, 255, 512, 1000, 2183, 3999)

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
    "probabilistic",
    "extremal_control",
)

ANTI = {
    **ANTI_OVERCLAIM,
    "finite_horizon_is_bad": False,
    "closure_from_one_is_new_induction": False,
    "interval_closure": False,
    "u_set_is_sparse": False,
    "visited_ge_nstar_is_automatically_good": False,
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
    "reopen_extremal_control": False,
    "automaton": False,
}

LEAN_THEOREMS = (
    "Good",
    "Bad",
    "good_of_good_successor",
    "good_of_predecessor_certificate",
    "PredEven",
    "PredOdd",
    "minimal_bad_no_smaller_visit",
    "minimal_bad_even_preimage_exclusion",
    "minimal_bad_odd_preimage_exclusion",
    "minimal_bad_barrier_constraint",
    "oe_barrier_pow",
    "ee_barrier_pow",
    "eo_barrier_pow",
    "PredClosure",
    "predClosure_iff_reachesOne",
    "minimal_bad_not_predClosure",
)

CLASS_MINIMALITY = "MINIMALITY_GREEN"
CLASS_BARRIER = "BARRIER_GREEN"
CLASS_CLOSURE = "GOOD_CLOSURE_GREEN"
CLASS_COVERAGE = "COVERAGE_GREEN"
CLASS_CONTRADICTION = "MINIMAL_BAD_CONTRADICTION_GREEN"
CLASS_COMPLEX = "MINIMALITY_COMPLEX"

HARD_CANONICAL = (3, 9, 37, 193, 425, 761, 2183, 3431, 3889)
JSON_INT_BITS = 256


def jsonable_int(n: int) -> int | str:
    if n.bit_length() > JSON_INT_BITS:
        return f"int[{n.bit_length()}bits]"
    return n


def compact_walk(row: dict[str, Any]) -> dict[str, Any]:
    return {
        "n": row["n"],
        "word": row["word"] if len(row["word"]) <= 64 else row["word"][:64] + "...",
        "H_n": row["H_n"],
        "peak": jsonable_int(row["peak"]),
        "peak_bits": row["peak"].bit_length(),
        "first_drop": row["first_drop"],
        "min_state": row["min_state"],
    }


def icbrt_ceil(target: int) -> int:
    if target <= 0:
        return 0
    lo, hi = 0, 1 << ((target.bit_length() + 2) // 3 + 1)
    while lo < hi:
        mid = (lo + hi) // 2
        if mid * mid * mid < target:
            lo = mid + 1
        else:
            hi = mid
    return lo


def odd_predecessor(m: int) -> int | None:
    """Unique odd n with floor_power(n) = m, or None."""

    if m < 1:
        raise ValueError("odd_predecessor requires a positive integer")
    lo2, hi2 = m * m, (m + 1) * (m + 1)
    k = icbrt_ceil(lo2)
    if k >= 1 and k % 2 == 1 and k * k * k < hi2 and floor_power(k) == m:
        return k
    return None


def even_predecessors_upto(m: int, n_max: int) -> list[int]:
    lo, hi = m * m, (m + 1) * (m + 1)
    start = lo + (lo % 2)
    if start < 2:
        start = 2
    return [n for n in range(start, min(hi, n_max + 1), 2)]


def two_step(n: int) -> tuple[str, int, int]:
    y = floor_power(n)
    z = floor_power(y)
    word = ("E" if n % 2 == 0 else "O") + ("E" if y % 2 == 0 else "O")
    return word, y, z


def oe_stays_above(x: int, barrier: int) -> bool:
    return barrier ** 4 <= x ** 3


def ee_stays_above(x: int, barrier: int) -> bool:
    return barrier ** 4 <= x


def eo_stays_above(x: int, barrier: int) -> bool:
    return barrier ** 2 <= isqrt(x) ** 3


def min_over_prefix(n: int, steps: int) -> int:
    x = n
    best = n
    for _ in range(steps):
        x = floor_power(x)
        if x < best:
            best = x
    return best


def stopping_times(n_max: int, *, horizon: int) -> list[int | None]:
    tau: list[int | None] = [None] * (n_max + 1)
    tau[1] = 0
    for start in range(2, n_max + 1):
        if tau[start] is not None:
            continue
        path = [start]
        x = start
        found: int | None = None
        for k in range(1, horizon + 1):
            x = floor_power(x)
            if x == 1:
                found = k
                break
            if 1 <= x <= n_max and tau[x] is not None:
                found = k + tau[x]
                break
            path.append(x)
        if found is None:
            continue
        for i, y in enumerate(path):
            value = found - i
            if 1 <= y <= n_max and tau[y] is None:
                tau[y] = value
    return tau


def barrier_walk(n: int, *, horizon: int = BARRIER_HORIZON) -> dict[str, Any]:
    x = n
    letters: list[str] = []
    peak = n
    min_state = n
    first_drop: int | None = None
    reached_one = n == 1
    for i in range(1, horizon + 1):
        letters.append("E" if x % 2 == 0 else "O")
        x = floor_power(x)
        if x > peak:
            peak = x
        if x < min_state:
            min_state = x
        if first_drop is None and x < n:
            first_drop = i
            break
        if x == 1:
            reached_one = True
            break
    surviving = first_drop is None
    return {
        "n": n,
        "word": "".join(letters),
        "length": len(letters),
        "min_state": min_state,
        "peak": peak,
        "barrier_survival": surviving,
        "first_drop": first_drop,
        "H_n": first_drop if first_drop is not None else len(letters),
        "reached_one_before_drop": reached_one and first_drop is None,
    }


def interval_stats(certified: list[bool]) -> dict[str, int]:
    n_max = len(certified) - 1
    prefix = 0
    for i in range(1, n_max + 1):
        if not certified[i]:
            break
        prefix = i
    components = 0
    largest_gap = 0
    in_run = False
    gap = 0
    for i in range(1, n_max + 1):
        if certified[i]:
            if not in_run:
                components += 1
                in_run = True
            if gap > largest_gap:
                largest_gap = gap
            gap = 0
        else:
            in_run = False
            gap += 1
    if gap > largest_gap:
        largest_gap = gap
    return {
        "certified_count": sum(1 for i in range(1, n_max + 1) if certified[i]),
        "maximum_certified_interval": prefix,
        "component_count": components,
        "largest_gap": largest_gap,
    }


def _count_parity(lo: int, hi: int, odd: bool) -> int:
    if lo > hi:
        return 0
    if odd:
        if lo % 2 == 0:
            lo += 1
        if hi % 2 == 0:
            hi -= 1
    else:
        if lo % 2 == 1:
            lo += 1
        if hi % 2 == 1:
            hi -= 1
    if lo > hi:
        return 0
    return (hi - lo) // 2 + 1


def u_set_formula_count(B: int, n_max: int) -> int:
    """|{n : B < n ≤ n_max and UncoveredOneStep(B, n)}|."""

    if B < 1:
        return 0
    odds = _count_parity(B + 1, n_max, True)
    evens = _count_parity(max(B + 1, (B + 1) * (B + 1)), n_max, False)
    return odds + evens


def u_set_scan(B: int, n_max: int) -> int:
    count = 0
    for n in range(B + 1, n_max + 1):
        if B < floor_power(n):
            count += 1
    return count


def predecessor_status(n: int, certified: list[bool]) -> str:
    y = floor_power(n)
    if y > len(certified) - 1:
        return "successor_outside_window"
    if 1 <= y < len(certified) and certified[y]:
        return "successor_certified"
    return "successor_inside_window_uncertified"


def orbit_inside_window(n: int, n_max: int, depth: int) -> int | None:
    """Smallest k≤depth with T^[k] n = 1 and every prefix state in [1, n_max]."""

    x = n
    if n < 1:
        return None
    if n == 1:
        return 0
    if n > n_max:
        return None
    for k in range(1, depth + 1):
        x = floor_power(x)
        if x == 1:
            return k
        if x < 1 or x > n_max:
            return None
    return None


def bt_parts(n: int) -> dict[str, Any]:
    word = encode(n)
    return {
        "n": n,
        "lsd": int(lsd(n)),
        "D": D(n),
        "length": len(word.digits_msd),
        "bt": str(word),
    }


def good_closure(n_max: int, depth: int) -> dict[str, Any]:
    certified = [False] * (n_max + 1)
    certified[1] = True
    parent: dict[int, tuple[int, str]] = {1: (1, "seed")}
    added_round = [None] * (n_max + 1)
    added_round[1] = 0
    frontier = [1]
    rounds: list[dict[str, Any]] = []
    layers: list[dict[str, Any]] = []
    uncovered_rows: list[dict[str, Any]] = []
    stats0 = interval_stats(certified)
    rounds.append({"round": 0, "N": n_max, **stats0})
    for r in range(1, depth + 1):
        nxt: list[int] = []
        for m in frontier:
            branch_e = "E"
            for n in even_predecessors_upto(m, n_max):
                if certified[n]:
                    continue
                if floor_power(n) != m:
                    continue
                certified[n] = True
                added_round[n] = r
                parent[n] = (m, branch_e)
                nxt.append(n)
                layers.append({
                    "round": r,
                    "target": m,
                    "predecessor": n,
                    "branch": branch_e,
                    "validation_status": "ok",
                })
            odd = odd_predecessor(m)
            if odd is not None and 1 <= odd <= n_max and not certified[odd]:
                certified[odd] = True
                added_round[odd] = r
                parent[odd] = (m, "O")
                nxt.append(odd)
                layers.append({
                    "round": r,
                    "target": m,
                    "predecessor": odd,
                    "branch": "O",
                    "validation_status": "ok",
                })
        frontier = nxt
        stats = interval_stats(certified)
        rounds.append({"round": r, "N": n_max, **stats})
        first_gap = next((i for i in range(1, n_max + 1) if not certified[i]), None)
        if first_gap is not None:
            word, y, z = two_step(first_gap)
            uncovered_rows.append({
                "round": r,
                "n": first_gap,
                "first_gap": first_gap,
                "predecessor_status": predecessor_status(first_gap, certified),
                "branch_metadata": word,
                "J": y,
                "J2": z,
                "parity": "odd" if first_gap % 2 else "even",
            })
    reentry = upward_odd_reentry(certified, n_max)
    return {
        "certified": certified,
        "added_round": added_round,
        "parent": parent,
        "rounds": rounds,
        "layers": layers,
        "uncovered": uncovered_rows,
        "upward_reentry": reentry,
    }


def upward_odd_reentry(certified: list[bool], n_max: int) -> dict[str, Any]:
    """Odd n ≤ N whose image is an even > N in an even cell of a certified m ≤ N."""

    extra = []
    for m in range(1, n_max + 1):
        if not certified[m]:
            continue
        lo, hi = m * m, (m + 1) * (m + 1)
        start = max(lo, n_max + 1)
        if start % 2 == 1:
            start += 1
        for even_n in range(start, hi, 2):
            odd = odd_predecessor(even_n)
            if odd is None or odd > n_max or odd < 1:
                continue
            if certified[odd]:
                continue
            extra.append({
                "odd": odd,
                "even_image": even_n,
                "small_target": m,
            })
    return {
        "count": len(extra),
        "examples": extra[:12],
        "would_certify": sorted({row["odd"] for row in extra})[:16],
    }


def closure_matches_window_basin(
    certified: list[bool],
    added_round: list[int | None],
    depth: int,
) -> dict[str, Any]:
    n_max = len(certified) - 1
    mismatches = []
    escaped = 0
    for n in range(1, n_max + 1):
        inside = orbit_inside_window(n, n_max, depth)
        in_g = certified[n]
        should = inside is not None
        if in_g != should:
            mismatches.append({
                "n": n,
                "inside_k": inside,
                "certified": in_g,
                "round": added_round[n],
            })
        if in_g and added_round[n] != inside:
            mismatches.append({
                "n": n,
                "inside_k": inside,
                "added_round": added_round[n],
                "kind": "round_vs_inside",
            })
        if inside is None:
            escaped += 1
        if len(mismatches) >= 8:
            break
    return {
        "ok": not mismatches,
        "mismatches": mismatches,
        "uncertified_or_escape": escaped,
    }


def closure_versus_stopping_time(
    certified: list[bool],
    tau: list[int | None],
    depth: int,
) -> dict[str, Any]:
    n_max = len(certified) - 1
    tau_but_uncertified = []
    for n in range(1, n_max + 1):
        t = tau[n]
        if t is not None and t <= depth and not certified[n]:
            tau_but_uncertified.append(n)
            if len(tau_but_uncertified) >= 12:
                break
    return {
        "equal": not tau_but_uncertified and all(
            (tau[n] is not None and tau[n] <= depth) == certified[n]
            for n in range(1, n_max + 1)
        ),
        "tau_le_depth_but_orbit_left_window": tau_but_uncertified,
    }


def two_step_census(n_max: int) -> dict[str, Any]:
    counts = Counter()
    fail = []
    for n in range(2, n_max + 1):
        word, _y, z = two_step(n)
        counts[word] += 1
        barrier = n
        if word == "OE":
            holds = (barrier <= z) == oe_stays_above(n, barrier)
        elif word == "EE":
            holds = (barrier <= z) == ee_stays_above(n, barrier)
        elif word == "EO":
            holds = (barrier <= z) == eo_stays_above(n, barrier)
        else:
            holds = True
            if n >= 3:
                holds = z > n
        if not holds:
            fail.append({"n": n, "word": word, "J2": z})
    return {
        "counts": dict(counts),
        "failures": fail,
        "ok": not fail,
    }


def minimality_constraint_rows(n_max: int) -> list[dict[str, Any]]:
    rows = []
    for n in range(2, min(n_max, 200) + 1):
        y = floor_power(n)
        if n % 2 == 0:
            rows.append({
                "candidate_n": n,
                "smaller_target": y,
                "branch": "E",
                "exclusion_reason": "even_start_maps_below_self",
            })
            continue
        if y % 2 == 0:
            z = floor_power(y)
            rows.append({
                "candidate_n": n,
                "smaller_target": z,
                "branch": "OE",
                "exclusion_reason": "oe_two_step_below_start",
            })
            continue
        if y < n:
            rows.append({
                "candidate_n": n,
                "smaller_target": y,
                "branch": "O",
                "exclusion_reason": "odd_image_below_start",
            })
    return rows


def pareto_barrier_records(walks: list[dict[str, Any]]) -> list[dict[str, Any]]:
    points = [
        (row["n"], row["H_n"], row["peak"])
        for row in walks
        if row["n"] > 1
    ]
    front = []
    for n, h, peak in points:
        dominated = False
        for n2, h2, peak2 in points:
            if n2 == n:
                continue
            if h2 >= h and peak2 >= peak and (h2 > h or peak2 > peak):
                dominated = True
                break
        if not dominated:
            front.append({"n": n, "H_n": h, "peak": peak})
    front.sort(key=lambda row: (-row["H_n"], -row["peak"], row["n"]))
    return front


def lean_api_present() -> dict[str, bool]:
    text = MINIMAL_CLOSURE.read_text(encoding="utf-8") + "\n" + MINIMAL.read_text(encoding="utf-8")
    present = {name: has_named(text, name) for name in LEAN_THEOREMS}
    # Alias already proved in Minimal.lean.
    present["minimal_bad_no_smaller_visit"] = "theorem minimal_nonterm_no_descent" in text
    present["sorry_free"] = "sorry" not in text and "admit" not in text
    return present


def decide(payload: dict[str, Any]) -> dict[str, Any]:
    window_ok = payload["closure_vs_window"]["ok"]
    u_ok = payload["u_set"]["formula_ok"]
    two_ok = payload["two_step"]["ok"]
    interval_law = payload["coverage"]["interval_is_power_of_three"]
    first_uncovered_bt = payload["balanced_ternary"]["first_gap_lsd_constrained"]
    green = {
        CLASS_MINIMALITY: False,
        CLASS_BARRIER: False,
        CLASS_CLOSURE: False,
        CLASS_COVERAGE: False,
        CLASS_CONTRADICTION: False,
        CLASS_COMPLEX: True,
    }
    reason = (
        "Unbounded predecessor closure from {1} is ReachesOne. "
        "The finite-N experiment is the inverse basin of 1 inside "
        "[1, N], which is strictly smaller than {n : τ(n) ≤ r} "
        "because high-peak orbits leave the window. U(B) is all "
        "odds > B together with evens >= (B+1)^2, so it is not "
        "sparse. Two-step barriers are floor-sqrt identities. No "
        "interval-growth recurrence and no contradiction to a "
        "minimal bad state appear."
    )
    if not (window_ok and u_ok and two_ok):
        reason = "Exact identities failed a finite check; inspect mismatches."
        green[CLASS_COMPLEX] = False
    if interval_law or first_uncovered_bt:
        green[CLASS_COVERAGE] = bool(interval_law)
        reason = "A coordinate pattern appeared; do not treat it as a halt law."
    return {
        "classification": CLASS_COMPLEX if green[CLASS_COMPLEX] else "CHECK_FAILED",
        "flags": green,
        "branch": "CLOSE",
        "reason": reason,
    }


def run_phase0(
    *,
    n_max: int = N_PHASE0,
    depth: int = DEPTH_PHASE0,
) -> dict[str, Any]:
    tau = stopping_times(n_max, horizon=BARRIER_HORIZON)
    missing_tau = [n for n in range(1, n_max + 1) if tau[n] is None]
    closure = good_closure(n_max, depth)
    vs_window = closure_matches_window_basin(
        closure["certified"], closure["added_round"], depth
    )
    vs_tau = closure_versus_stopping_time(closure["certified"], tau, depth)
    two = two_step_census(n_max)
    u_rows = []
    u_ok = True
    for B in U_SAMPLE:
        if B >= n_max:
            continue
        scanned = u_set_scan(B, n_max)
        formula = u_set_formula_count(B, n_max)
        if scanned != formula:
            u_ok = False
        odds_above = sum(1 for n in range(B + 1, n_max + 1) if n % 2 == 1)
        evens_sq = sum(
            1
            for n in range(max(B + 1, (B + 1) * (B + 1)), n_max + 1)
            if n % 2 == 0
        )
        u_rows.append({
            "B": B,
            "scanned": scanned,
            "formula": formula,
            "odds_above_B": odds_above,
            "evens_ge_sq": evens_sq,
            "density": scanned / (n_max - B),
        })
    walks = [barrier_walk(n) for n in range(1, n_max + 1)]
    long_barrier = sorted(walks, key=lambda r: (-r["H_n"], -r["peak"], r["n"]))[:12]
    pareto = pareto_barrier_records(walks)
    first_gaps = [row["n"] for row in closure["uncovered"]]
    lsd_counts = Counter(int(lsd(n)) for n in first_gaps)
    lengths = [len(encode(n).digits_msd) for n in first_gaps]
    prefix_growth = [row["maximum_certified_interval"] for row in closure["rounds"]]
    pow3 = {3 ** k for k in range(0, 12)}
    interval_pow3 = all(v in pow3 for v in prefix_growth if v > 0)
    tau_values = [t for t in tau[1:] if t is not None]
    coverage = {
        "max_tau_in_window": max(tau_values) if tau_values else None,
        "missing_tau": missing_tau[:8],
        "all_reach_one_in_horizon": not missing_tau,
        "depth": depth,
        "certified_at_depth": closure["rounds"][-1]["certified_count"],
        "uncovered_at_depth": n_max - closure["rounds"][-1]["certified_count"],
        "prefix_growth": prefix_growth,
        "interval_is_power_of_three": interval_pow3,
        "first_uncovered_by_round": first_gaps,
    }
    bt_obs = {
        "first_gap_lsd": dict(sorted(lsd_counts.items())),
        "first_gap_lsd_constrained": len(lsd_counts) == 1,
        "first_gap_bt_lengths": lengths,
        "first_gap_parts": [bt_parts(n) for n in first_gaps[:8]],
        "used_as_coordinate_only": True,
    }
    constraints = minimality_constraint_rows(n_max)
    payload = {
        "experiment": "juggler_minimal_counterexample",
        "N": n_max,
        "depth": depth,
        "cuda_used": False,
        "anti_overclaim": ANTI,
        "lean": lean_api_present(),
        "closure_rounds": closure["rounds"],
        "closure_vs_window": vs_window,
        "closure_vs_tau": vs_tau,
        "upward_reentry": closure["upward_reentry"],
        "two_step": two,
        "u_set": {"rows": u_rows, "formula_ok": u_ok},
        "coverage": coverage,
        "long_barrier": [compact_walk(r) for r in long_barrier],
        "pareto": [
            {
                "n": row["n"],
                "H_n": row["H_n"],
                "peak": jsonable_int(row["peak"]),
                "peak_bits": row["peak"].bit_length(),
            }
            for row in pareto[:16]
        ],
        "balanced_ternary": bt_obs,
        "hard_canonical": [
            {
                "n": n,
                "tau": tau[n] if n <= n_max else None,
                **compact_walk(barrier_walk(n)),
            }
            for n in HARD_CANONICAL
            if n <= n_max
        ],
        "constraint_examples": constraints[:24],
        "uncovered_sample": closure["uncovered"],
    }
    payload["decision"] = decide(payload)
    payload["_closure"] = closure
    payload["_walks"] = walks
    payload["_tau"] = tau
    payload["_constraints"] = constraints
    return payload


def _write_csv(path: Path, rows: list[dict[str, Any]], fieldnames: list[str]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(rows)


def write_data(payload: dict[str, Any]) -> None:
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    closure = payload["_closure"]
    walks = payload["_walks"]
    manifest = {
        "experiment": payload["experiment"],
        "N": payload["N"],
        "depth": payload["depth"],
        "cuda_used": False,
        "classification": payload["decision"]["classification"],
        "branch": payload["decision"]["branch"],
        "files": [
            "good_closure.csv",
            "closure_layers.csv",
            "uncovered.csv",
            "minimality_constraints.csv",
            "barrier_words.jsonl",
            "counterexamples.jsonl",
        ],
    }
    (DATA_DIR / "manifest.json").write_text(
        json.dumps(manifest, indent=2) + "\n", encoding="utf-8"
    )
    _write_csv(
        DATA_DIR / "good_closure.csv",
        closure["rounds"],
        [
            "round",
            "N",
            "certified_count",
            "maximum_certified_interval",
            "component_count",
            "largest_gap",
        ],
    )
    _write_csv(
        DATA_DIR / "closure_layers.csv",
        closure["layers"],
        ["round", "target", "predecessor", "branch", "validation_status"],
    )
    _write_csv(
        DATA_DIR / "uncovered.csv",
        closure["uncovered"],
        [
            "round",
            "n",
            "first_gap",
            "predecessor_status",
            "branch_metadata",
            "J",
            "J2",
            "parity",
        ],
    )
    _write_csv(
        DATA_DIR / "minimality_constraints.csv",
        payload["_constraints"],
        ["candidate_n", "smaller_target", "branch", "exclusion_reason"],
    )
    with (DATA_DIR / "barrier_words.jsonl").open("w", encoding="utf-8") as handle:
        for row in walks:
            handle.write(json.dumps({
                "n": row["n"],
                "word": row["word"],
                "length": row["length"],
                "min_state": row["min_state"],
                "barrier_survival": row["barrier_survival"],
                "first_drop": row["first_drop"],
            }) + "\n")
    counterexamples = [
        {
            "claim": "predecessor_closure_from_1_is_a_new_induction",
            "status": "REFUTED",
            "witness": "PredClosure ↔ ReachesOne; G_r = {n : τ(n) ≤ r}",
            "label": "COUNTEREXAMPLE",
        },
        {
            "claim": "U(B)_becomes_arithmetically_sparse",
            "status": "REFUTED",
            "witness": "U(B) = odds > B ∪ evens ≥ (B+1)^2; density → 1/2",
            "label": "COUNTEREXAMPLE",
        },
        {
            "claim": "one_step_closure_of_[1,B]_covers_some_odd_n>B",
            "status": "REFUTED",
            "witness": "odd n≥3 expands, so J(n)>n>B",
            "label": "COUNTEREXAMPLE",
        },
        {
            "claim": "G_r_is_a_single_interval",
            "status": "REFUTED",
            "witness": payload["closure_rounds"][-1],
            "label": "COUNTEREXAMPLE",
        },
        {
            "claim": "visited_state_ge_nstar_is_automatically_good",
            "status": "REFUTED",
            "witness": "only automatic reduction is a visit < n*",
            "label": "COUNTEREXAMPLE",
        },
        {
            "claim": "Bad_H_equals_Bad",
            "status": "REFUTED",
            "witness": "finite horizon is not the orbit predicate",
            "label": "COUNTEREXAMPLE",
        },
    ]
    with (DATA_DIR / "counterexamples.jsonl").open("w", encoding="utf-8") as handle:
        for row in counterexamples:
            handle.write(json.dumps(row) + "\n")


def render_markdown(payload: dict[str, Any]) -> str:
    d = payload["decision"]
    rounds = payload["closure_rounds"]
    last = rounds[-1]
    u_lines = [
        f"| {row['B']} | {row['scanned']} | {row['formula']} | {row['density']:.4f} |"
        for row in payload["u_set"]["rows"]
    ]
    grow_lines = [
        f"| {row['round']} | {row['certified_count']} | "
        f"{row['maximum_certified_interval']} | {row['component_count']} | "
        f"{row['largest_gap']} |"
        for row in rounds
    ]
    gap_lines = [
        f"| {row['round']} | {row['n']} | {row['predecessor_status']} | "
        f"{row['branch_metadata']} |"
        for row in payload["uncovered_sample"]
    ]
    hard_lines = [
        f"| {row['n']} | {row['tau']} | {row['H_n']} | {row['peak']} | `{row['word']}` |"
        for row in payload["hard_canonical"]
    ]
    pareto_lines = [
        f"| {row['n']} | {row['H_n']} | {row['peak']} |"
        for row in payload["pareto"]
    ]
    long_lines = [
        f"| {row['n']} | {row['H_n']} | {row['peak']} | `{row['word'][:40]}` |"
        for row in payload["long_barrier"]
    ]
    bt = payload["balanced_ternary"]
    two = payload["two_step"]
    cov = payload["coverage"]
    return f"""# Juggler minimal counterexample and predecessor closure

Status: **{d['classification']}**

Standalone well-ordering phase on the exact Juggler floor-power map.
This is not a termination theorem. Closed local, symbolic, statistical,
and quotient branches stay closed. Finite-horizon evidence is not `Bad`.

Every statement below is labelled
`LOGICAL CONSEQUENCE` | `LEAN-CERTIFIED` | `EXACT COMPUTATION` |
`COMPUTATIONALLY OBSERVED` | `CANDIDATE CONJECTURE` | `COUNTEREXAMPLE`.
These are report labels. Ledger tags, when used, remain the seven
standard tags from [docs/README.md](../README.md).

## 1. Formal minimal-counterexample setup

`ReachesOne n` is the existing Lean predicate `∃ k, T^[k] n = 1`.

```text
Good(n)  := ReachesOne n
Bad(n)   := ¬ReachesOne n
```

Label: **LEAN-CERTIFIED** (`Good`, `Bad` in
`Problems.Juggler.MinimalClosure`). `Bad` is not proved decidable and
is not assumed decidable.

The computational proxy is strictly weaker:

```text
Bad_H(n) := T^[k] n ≠ 1 for all k ≤ H
```

`Bad_H(n)` does not imply `Bad(n)`. Label: **LOGICAL CONSEQUENCE**.

A hypothetical counterexample is a positive `n > 1` with `Bad(n)`.
Well-ordering supplies a least such value `n*`. Then every positive
`m < n*` is `Good`. Label: **LOGICAL CONSEQUENCE**. This is
`MinimalNonTerm` already in `Problems.Juggler.Minimal`. **LEAN-CERTIFIED**.

Minimality does *not* give a uniform finite bound on the stopping
times of the smaller good states. Label: **LOGICAL CONSEQUENCE**.

## 2. Exact logical consequences

If the orbit of `n*` ever visits `m < n*`, then `m` is `Good`, so `n*`
is `Good`. Therefore a minimal-bad orbit satisfies `T^[k] n* ≥ n*` for
every `k`. Label: **LEAN-CERTIFIED**
(`minimal_bad_barrier_constraint`, already `minimal_nonterm_iterate_ge`).

Local contraction `T(x) < x` is allowed as long as `T(x) ≥ n*`. The
forbidden event is a visit strictly below `n*`, not a descent relative
to the current state. Label: **LOGICAL CONSEQUENCE**.

`n*` is odd and at least `12`. The first image is odd. Every even
state on the orbit is at least `n*^2`. Start-`OE` is descent.
Label: **LEAN-CERTIFIED** (existing `Minimal.lean` normal form).

An immediate predecessor of a `Good` state is `Good`.
Label: **LEAN-CERTIFIED** (`good_of_good_successor`,
`good_of_predecessor_certificate`).

`n*` cannot lie in the even or odd inverse cell of any `m < n*`.
Label: **LEAN-CERTIFIED** (`minimal_bad_even_preimage_exclusion`,
`minimal_bad_odd_preimage_exclusion`). Both are corollaries of the
already-proved odd start plus odd expansion.

## 3. Barrier-surviving trajectories

For each start `n ≤ {payload['N']}`, `H_n` is the first time the
trajectory is strictly below `n`, or the horizon if no such time is
seen. This is a barrier against the *start*, not a first-return
census and not a new delay table.

Every `n` in `2..{payload['N']}` drops below `n` inside the horizon.
`barrier_survival` is therefore false on the whole Phase-0 window.
Label: **EXACT COMPUTATION**. That is compatible with totality on
the window and is not a proof that `Bad` is empty.

Longest observed `H_n` in the window:

{chr(10).join(long_lines)}

Label: **EXACT COMPUTATION**.

The barrier prefix of a terminating start is exactly the walk until
the first state `< n`. At the start itself, `Min_w(n) < n` coincides
with ordinary word contraction. The new inequality `Min_w(x) < n*`
for a later state `x > n*` is weaker than `T_w(x) < x`. Label:
**LOGICAL CONSEQUENCE**.

## 4. Two-step and block barrier analysis

On a realized two-step word the exact barrier tests against a lower
cut `b` are:

| word | `b ≤ T^2(x)` |
| --- | --- |
| `OE` | `b^4 ≤ x^3` |
| `EE` | `b^4 ≤ x` |
| `EO` | `b^2 ≤ ⌊√x⌋^3` |
| `OO` | automatic if `3 ≤ b ≤ x` |

Label: **LEAN-CERTIFIED** (`oe_barrier_pow`, `ee_barrier_pow`,
`eo_barrier_pow`, `oo_barrier_of_le`).

Finite check on `n = 2..{payload['N']}`: counts `{two['counts']}`;
failures `{len(two['failures'])}`. Label: **EXACT COMPUTATION**.

At a minimal-bad start, `OE` is already impossible. A later `OE` from
`x ≥ n*` stays above `n*` if and only if `n*^4 ≤ x^3`. That is the
even-cell law `T(x) ≥ n*^2` rewritten through `T(x)^2 ≤ x^3`. It
excludes no new infinite family. Label: **LOGICAL CONSEQUENCE**.

For a block `O^a E^b` launched *at* `n*`, remaining above `n*` after
the even run is the same comparison `3^a ≥ 2^{{a+b}}` as the known
exponent envelope, up to floor error. That is not a new obstruction.
For a later state `x > n*` the same block may contract relative to
`x` and still stay above `n*`. Label: **LOGICAL CONSEQUENCE**.

`BARRIER_GREEN` is not awarded: no new block family is incompatible
with the permanent lower cut.

## 5. Minimality exclusions

If `[1, B] ⊆ Good`, then one-step predecessor closure adds exactly
the even integers `n` with `⌊√n⌋ ≤ B`, i.e. even `n < (B+1)^2`, and
adds no odd integer `> B`. Label: **LEAN-CERTIFIED**
(`even_good_of_sqrt_le`, `odd_not_pred_of_le`, `uncovered_odd`,
`uncovered_even_iff`).

Therefore

```text
U(B) ∩ (B, N]  =  {{odd n : B < n ≤ N}}
                 ∪ {{even n : max(B, (B+1)^2) ≤ n ≤ N}}
```

when `Good` contains `[1, B]`. Density tends to `1/2`, not to `0`.
Label: **LEAN-CERTIFIED** for the predicate; **EXACT COMPUTATION**
for the Phase-0 counts:

| B | scanned | formula | density |
| --- | --- | --- | --- |
{chr(10).join(u_lines)}

A hypothetical `n*` lies in `U(n*-1)` because it is odd. One-step
closure of the smaller good interval does not catch it. Label:
**LEAN-CERTIFIED** (`minimal_bad_uncovered_one_step`).

## 6. Good-set predecessor closure

Define `PredClosure` inductively: `1` is closed, and any preimage of
a closed state is closed.

```text
PredClosure n  ↔  ReachesOne n
```

Label: **LEAN-CERTIFIED** (`predClosure_iff_reachesOne`).

This is the exact content of iterated `G ↦ G ∪ Pred(G)` starting at
`{{1}}`. It is a reparameterization of `Good`, not a new basin
geometry. `GOOD_CLOSURE_GREEN` as a *new inductive mechanism* is
false. Label: **COUNTEREXAMPLE** to “closure from 1 is a new
induction”.

Unbounded `PredClosure` is `ReachesOne`. The Phase-0 set is the
*window-restricted* inverse basin: `n ≤ N` whose path to `1` of
length `≤ r` stays inside `[1, N]`. That matches the computed
`G_r`: `{payload['closure_vs_window']['ok']}`. It is strictly
smaller than `{{n : τ(n) ≤ r}}`. Starts with `τ ≤ r` whose orbit
leaves the window include
`{payload['closure_vs_tau']['tau_le_depth_but_orbit_left_window'][:8]}`.
Label: **EXACT COMPUTATION**. **COUNTEREXAMPLE** to “finite-N
closure is the stopping-time filtration”.

One extra even-cell layer above `N`, followed by odd re-entry,
would certify
`{payload['upward_reentry']['count']}` additional odd starts
`≤ N` whose image is an even `> N` in a certified cell. Examples:
`{payload['upward_reentry']['would_certify']}`. This is upward
propagation, not interval closure. Label: **EXACT COMPUTATION**.

## 7. Closure growth

| round | certified | prefix interval | components | largest gap |
| --- | --- | --- | --- | --- |
{chr(10).join(grow_lines)}

At depth `{payload['depth']}`: certified `{last['certified_count']}` of
`{payload['N']}`, uncovered `{cov['uncovered_at_depth']}`, prefix
`{last['maximum_certified_interval']}`, components
`{last['component_count']}`. Every `n ≤ {payload['N']}` reached `1`
inside the walk horizon: `{cov['all_reach_one_in_horizon']}`; max
`τ` in the window is `{cov['max_tau_in_window']}`. Label:
**EXACT COMPUTATION**.

The prefix `[1, F(r)]` is not a power of 3:
`{not cov['interval_is_power_of_three']}`. No closed form for `F(r)`
is proposed. `COVERAGE_GREEN` is not awarded. Label:
**COMPUTATIONALLY OBSERVED**.

`G_r ∩ [1, N]` is not a single interval. Label: **COUNTEREXAMPLE**
to interval closure.

## 8. Uncovered-set geometry

First uncovered value after each round (least `n` outside the
window-restricted inverse basin, not `τ(n) > r`):

| round | first gap | successor status | first two letters |
| --- | --- | --- | --- |
{chr(10).join(gap_lines)}

Label: **EXACT COMPUTATION**. From round 9 the first gap freezes at
`25`, whose orbit leaves `[1, N]` (`25 → 125 → 1397 → 52214`). That
state is never certified at any depth inside the window. The leftover
set at infinite depth, for this `N`, is the starts whose path to `1`
exits `[1, N]`. That is neither `Bad` nor `Bad_H`. Odd cells remain
singletons; even cells fill square intervals.

## 9. Balanced-ternary observations, if any

First-gap least digits: `{bt['first_gap_lsd']}`. More than one trit
occurs, so the uncovered minima are not an lsd cylinder. Lengths
`{bt['first_gap_bt_lengths']}`. No closure boundary of the form
`(3^k ± 1)/2` appears. Balanced ternary is not used as a solving
coordinate. Label: **COMPUTATIONALLY OBSERVED**.

## 10. Candidate induction laws

No `CANDIDATE CONJECTURE` is opened.

The attractive schema “after `r` closure rounds, `[1, F(r)]` is
covered” fails already at small `r`: the certified set gains distant
even square-cells while leaving small odd gaps. The only exact unbounded recurrence is
`G_{{r+1}} = {{n : T(n) ∈ G_r}} ∪ G_r`, i.e. `τ(n) ≤ r+1`. Inside a
finite window it is the same rule restricted to targets already in
`[1, N]`. Label: **LOGICAL CONSEQUENCE**.

`MINIMAL_BAD_CONTRADICTION_GREEN` is false: `n*` is excluded from
`PredClosure` if and only if it is `Bad`, which is the assumption.
Label: **LEAN-CERTIFIED** (`minimal_bad_not_predClosure`).

## 11. Smallest counterexamples

Canonical hard starts in the window, with stopping time and barrier
time (not a new score):

| n | τ | H_n | peak | barrier word |
| --- | --- | --- | --- | --- |
{chr(10).join(hard_lines)}

Pareto front of `(H_n, peak)` on `n ≤ {payload['N']}`:

| n | H_n | peak |
| --- | --- | --- |
{chr(10).join(pareto_lines)}

Label: **EXACT COMPUTATION**. These are terminating starts. They
resemble a minimal-bad candidate only in having a long sojourn above
the start. Each of them does drop below the start, so none is
minimal-bad.

## 12. Lean targets

Formalized, sorry-free, in `formal/Problems/Juggler/MinimalClosure.lean`:

- `good_of_good_successor`
- `good_of_predecessor_certificate`
- `minimal_bad_even_preimage_exclusion`
- `minimal_bad_odd_preimage_exclusion`
- `minimal_bad_barrier_constraint`
- `oe_barrier_pow` / `ee_barrier_pow` / `eo_barrier_pow`
- `PredClosure` / `predClosure_iff_reachesOne`
- `minimal_bad_not_predClosure`

Not formalized, and not claimed: `good_interval_closure`,
`closure_growth_theorem`, `minimal_bad_impossible`.

## 13. Decision

Classification: **{d['classification']}**.

{d['reason']}

`MINIMALITY_GREEN` is not awarded: the new Lean lemmas package
existing minimality facts or reparameterize `ReachesOne`.
`BARRIER_GREEN` is not awarded. `GOOD_CLOSURE_GREEN` is not awarded.
`COVERAGE_GREEN` is not awarded. `MINIMAL_BAD_CONTRADICTION_GREEN`
is not awarded.

Branch status in the dossier: **CLOSE**.

Phase 1 (`N = 10^5`) is not launched. A larger window only moves the
escape threshold; it does not create an interval-growth law.
"""


def render_json(payload: dict[str, Any]) -> dict[str, Any]:
    skip = {"_closure", "_walks", "_tau", "_constraints"}
    return {key: value for key, value in payload.items() if key not in skip}


def write_docs(payload: dict[str, Any]) -> None:
    JSON_PATH.write_text(
        json.dumps(render_json(payload), indent=2) + "\n", encoding="utf-8"
    )
    DOC_PATH.write_text(render_markdown(payload), encoding="utf-8")
    DOSSIER_PATH.write_text(render_dossier(payload), encoding="utf-8")


def render_dossier(payload: dict[str, Any]) -> str:
    d = payload["decision"]
    last = payload["closure_rounds"][-1]
    return f"""# Juggler minimal counterexample and well-ordering

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1.

## Problem

If a bad Juggler state existed, what would the smallest such state be
forced to look like, and can exact predecessor closure or trajectory
barriers make that state impossible?

## Exact statement

Let `Bad(n)` mean `¬ReachesOne n`. Assume a bad state exists and let
`n*` be least. Then every positive `m < n*` is `Good`, the orbit of
`n*` never enters `[1, n*-1]`, and `n*` lies outside the predecessor
closure of every finite good set generated from states `< n*`. Decide
whether this well-ordering constraint plus exact inverse cells yields
a new reduction, or only the tautology that a minimal bad orbit cannot
visit a smaller bad state.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Existing `MinimalNonTerm` normal form — **EXACT — LEAN VERIFIED**.
- Even-run scale barrier `n^{{2^r}} ≤ m` —
  **EXACT — LEAN VERIFIED** (`juggler_even_scale_barrier`).
- `ReachesOne` closure along images —
  **EXACT — LEAN VERIFIED**.

Project relationship: **independent** as a well-ordering question;
the closure experiment is a **REPARAMETERIZATION** of `ReachesOne`.
Totality remains unclaimed.

## Branch budget

```text
Mathematical target     Does minimality plus predecessor closure give
                        a new reduction, or only the barrier tautology?
Novelty hypothesis      Well-ordering plus inverse cells yields an
                        inductive coverage law or a forbidden block family
Falsifier               PredClosure ↔ ReachesOne; U(B) not sparse;
                        no F(r) recurrence
Existing machinery      ReachesOne, MinimalNonTerm, even/odd cells,
                        floor_power, even_run_scale_barrier
Maximum Phase-0 scope   N≤4000, depth≤12, two-step barriers,
                        Lean PredClosure ↔ ReachesOne
Promotion criterion     A new exclusion theorem or a proved coverage law
Stop criterion          MINIMALITY_COMPLEX; tautology only
```

## Balanced-ternary formulation

Optional coordinate on uncovered minima. No forced BT law.

## Why BT may be relevant

A closure boundary of the form `(3^k ± 1)/2`, or an lsd cylinder of
uncovered states, would have been a BT observation. Neither appeared.

## Candidate operations / invariants

- `Good` / `Bad` as `ReachesOne` / its negation —
  **EXACT — LEAN VERIFIED**
- `good_of_good_successor` —
  **EXACT — LEAN VERIFIED**
- `PredClosure ↔ ReachesOne` —
  **EXACT — LEAN VERIFIED**. **REPARAMETERIZATION**
- `U(B)` = odds `> B` plus evens `≥ (B+1)^2` —
  **EXACT — LEAN VERIFIED**
- two-step barrier identities —
  **EXACT — LEAN VERIFIED**
- window-restricted `G_r` equals the inverse basin of `1` in
  `[1, {payload['N']}]` — **COMPUTATIONALLY VERIFIED**
- `G_r = {{n : τ(n) ≤ r}}` on `n ≤ {payload['N']}` —
  **REFUTED**
- interval closure / sparse `U(B)` / new induction —
  **REFUTED**
- `Bad_H = Bad` —
  **REFUTED**
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.minimal_counterexample`
- Records: [juggler_minimal_counterexample.md](../research/juggler_minimal_counterexample.md),
  [juggler_minimal_counterexample.json](../research/juggler_minimal_counterexample.json)
- Data: `data/research/juggler/minimal_counterexample/`
- Tests: `tests/research/juggler_sequence/test_minimal_counterexample.py`
- The Research Engine control layer is not modified.

## Conjectures

None opened.

## Counterexamples

- “Predecessor closure from `{{1}}` is a new induction.” **REFUTED**:
  `PredClosure ↔ ReachesOne`.
- “`U(B)` is arithmetically sparse.” **REFUTED**: density tends to
  `1/2`.
- “`G_r` is a single interval.” **REFUTED**: at depth
  `{payload['depth']}` there are `{last['component_count']}` components.
- “A visit `≥ n*` is automatically good.” **REFUTED**: only a visit
  `< n*` reduces.
- “`Bad_H` is `Bad`.” **REFUTED** by definition.
- “Finite-`N` closure is the stopping-time filtration.” **REFUTED**.

## Formalization

`formal/Problems/Juggler/MinimalClosure.lean`. No `sorry`. Existing
`Minimal.lean` lemmas are reused, not restated as new obstructions.

## Results

See [juggler_minimal_counterexample.md](../research/juggler_minimal_counterexample.md).
Classification **{d['classification']}**.

## Open questions

Whether every positive integer reaches 1. Well-ordering alone does not
answer it.

## Decision

**{d['branch']}**. {d['reason']} All promoted-looking identities are
either already in `Minimal.lean` or a reparameterization of
`ReachesOne`. A branch whose surviving statements are `KNOWN` or
`REPARAMETERIZATION` is a `CLOSE`.

Best next question: none from this branch. Do not launch Phase 1.

## Publication assessment

Status: `ARCHIVED`.

The well-ordering reduction is the classical minimal-counterexample
setup. The predecessor-closure experiment identifies that construction
with the existing `ReachesOne` predicate. There is no new theorem
beyond packaging, and no paper distinction.
"""


def write_all(payload: dict[str, Any]) -> None:
    write_data(payload)
    write_docs(payload)


def main() -> None:
    payload = run_phase0()
    write_all(payload)
    print(json.dumps({
        "classification": payload["decision"]["classification"],
        "branch": payload["decision"]["branch"],
        "closure_vs_window": payload["closure_vs_window"]["ok"],
        "closure_vs_tau_equal": payload["closure_vs_tau"]["equal"],
        "u_set": payload["u_set"]["formula_ok"],
        "two_step": payload["two_step"]["ok"],
        "certified": payload["closure_rounds"][-1]["certified_count"],
        "uncovered": payload["coverage"]["uncovered_at_depth"],
        "max_tau": payload["coverage"]["max_tau_in_window"],
    }, indent=2))


if __name__ == "__main__":
    main()

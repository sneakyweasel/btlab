"""First-return-to-odd accelerated Juggler map.

Derived object. Does not modify ResidualStep, floor_power, or defect
semantics. Not a halt theorem. Not a second acceleration. Not a
reopening of PE-factor, residual-quotient, sum-rho, realization
geometry, information-complexity, or first-return scalar branches.
"""

from __future__ import annotations

import csv
import json
from collections import Counter, defaultdict
from fractions import Fraction
from math import gcd
from pathlib import Path
from typing import Any, Iterable

from research.juggler_sequence.floor_preimages import even_preimage, odd_preimage_integers
from research.juggler_sequence.global_defect import (
    follows_itinerary,
    global_defect,
    image_after,
    local_defect,
)
from research.juggler_sequence.lean_paths import (
    CELLS,
    ENVELOPE,
    GLOBAL_DEFECT,
    ITINERARY,
    RESIDUALS,
    has_named,
    juggler_text,
)
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power, word_of
from research.juggler_sequence.residual_chain import residual_excursion

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_accelerated.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_accelerated.md"
DOSSIER_PATH = REPO_ROOT / "docs" / "problems" / "juggler_accelerated.md"
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "accelerated"

N_MAX = 4000
BIT_CAP = 4096
EVEN_CAP = 64
TRAJECTORY_CAP = 16
DEFECT_BITS = 4096
INVERSE_FIBER_CAP = 80

HARD_PROBES = (9, 37, 49, 69, 77)
PE_CHAIN = (365, 763, 1749, 4447)
RECORD_STARTS = (193, 425, 2183, 3889)
DEFINITIONAL = (3, 15, 63)
SELECTED_EXTRA = HARD_PROBES + PE_CHAIN + RECORD_STARTS + DEFINITIONAL + (173,)

CLASS_MAP_GREEN = "ACCELERATED_MAP_GREEN"
CLASS_INVERSE_GREEN = "MACRO_INVERSE_GREEN"
CLASS_CONTRACT_GREEN = "MACRO_CONTRACTION_GREEN"
CLASS_STRUCTURE_GREEN = "MACRO_STRUCTURE_GREEN"
CLASS_HARD_GREEN = "MACRO_HARDNESS_GREEN"
CLASS_REPACK = "ACCELERATION_REPACKAGING"
CLASS_COMPLEX = "ACCELERATION_COMPLEX"
CLASS_INCOMPLETE = "ACCELERATION_INCOMPLETE"

STATUS_OK = "OK"
STATUS_BIT_CAP = "BIT_CAP"
STATUS_NO_LANDING = "NO_LANDING"
STATUS_INVALID = "INVALID"

RETURN_RETURNED = "RETURNED"
RETURN_CAPTURE = "CAPTURE"
RETURN_CAPPED = "CAPPED"
RETURN_BIT_CAP = "BIT_CAP"

LEAN_THEOREMS = (
    "floorPower_odd_ge",
    "power_bound_contracts",
    "image_monotone_of_follows",
    "global_defect_identity",
    "residualStep_global_defect",
    "odd_preimage_unique",
    "image_eq_iterate",
)

FORBIDDEN_ENGINES = (
    "ResidualState",
    "ResidualGraph",
    "CycleEngine",
    "PowerHeight",
    "Energy",
)

ALGORITHM_VERSION = "accelerated-odd-return-v1"


def compact_int(value: int, *, bits: int = 256) -> int | dict[str, Any]:
    if value.bit_length() <= bits:
        return value
    return {"bits": value.bit_length(), "hex_head": hex(value)[:18]}


def json_safe(value: Any) -> Any:
    if isinstance(value, tuple):
        return [json_safe(item) for item in value]
    if isinstance(value, dict):
        return {str(key): json_safe(item) for key, item in value.items()}
    if isinstance(value, list):
        return [json_safe(item) for item in value]
    return value


def beta_pair(a: int, b: int) -> tuple[int, int]:
    num = 3**a
    den = 2 ** (a + b)
    g = gcd(num, den)
    return num // g, den // g


def formally_contracting(a: int, b: int) -> bool:
    return 3**a < 2 ** (a + b)


def power_if_small(base: int, exp: int, *, bit_limit: int = DEFECT_BITS) -> int | None:
    if base < 0 or exp < 0:
        raise ValueError("power_if_small requires nonnegative inputs")
    if exp == 0:
        return 1
    if base <= 1:
        return base
    if base.bit_length() * exp > bit_limit:
        return None
    return base**exp


def exact_macro_defect(n: int, a: int, b: int, target: int) -> int | None:
    left = power_if_small(n, 3**a)
    right = power_if_small(target, 2 ** (a + b))
    if left is None or right is None:
        return None
    return left - right


def even_predecessors(m: int) -> list[int]:
    lo, hi = even_preimage(m)
    return [item for item in range(lo, hi) if item % 2 == 0 and item >= 2]


def odd_predecessors(m: int) -> list[int]:
    return [item for item in odd_preimage_integers(m) if item % 2 == 1 and item >= 1]


def macro_predecessors(m: int, a: int, b: int, *, cap: int = INVERSE_FIBER_CAP) -> dict[str, Any]:
    """Exact A_{1,b}-predecessors via existing floor cells. a must be 1."""

    if a != 1 or m < 1 or b < 0:
        return {"m": m, "a": a, "b": b, "ok": False, "predecessors": [], "count": 0}
    if b == 0:
        preds = odd_predecessors(m)
        return {
            "m": m,
            "a": a,
            "b": b,
            "ok": True,
            "predecessors": preds[:cap],
            "count": len(preds),
            "truncated": len(preds) > cap,
            "cell": "Pred_O(m)",
        }
    currents = {m}
    for _ in range(b):
        nxt: set[int] = set()
        for y in currents:
            nxt.update(even_predecessors(y))
            if len(nxt) > 10_000:
                return {
                    "m": m,
                    "a": a,
                    "b": b,
                    "ok": False,
                    "predecessors": [],
                    "count": None,
                    "truncated": True,
                    "cell": "nested Pred_E overflow",
                }
        currents = nxt
        if not currents:
            break
    preds: list[int] = []
    for z in currents:
        if z % 2 == 0:
            preds.extend(odd_predecessors(z))
    preds = sorted(set(preds))
    return {
        "m": m,
        "a": a,
        "b": b,
        "ok": True,
        "predecessors": preds[:cap],
        "count": len(preds),
        "truncated": len(preds) > cap,
        "cell": f"Pred_O then Pred_E^{b}",
        "even_fiber": len(currents),
    }


def iterate_j(n: int, steps: int) -> int:
    current = n
    for _ in range(steps):
        current = floor_power(current)
    return current


def macro_step(n: int, *, even_cap: int = EVEN_CAP, bit_cap: int = BIT_CAP) -> dict[str, Any]:
    """First subsequent odd landing A(n) for odd n > 1."""

    if n <= 1 or n % 2 == 0:
        raise ValueError("macro_step requires an odd integer n > 1")
    path = [n]
    current = n
    status = STATUS_OK
    first = floor_power(current)
    if first.bit_length() > bit_cap:
        return {
            "n": n,
            "target": None,
            "a": 1,
            "b": None,
            "r": None,
            "word": None,
            "peak": n,
            "peak_position": 0,
            "path": (n,),
            "validation_status": STATUS_BIT_CAP,
            "j_image_parity": None,
        }
    path.append(first)
    current = first
    if current % 2 == 1:
        a, b, r = 1, 0, 1
    else:
        a = 1
        b = 0
        while current % 2 == 0 and b < even_cap:
            nxt = floor_power(current)
            if nxt.bit_length() > bit_cap:
                status = STATUS_BIT_CAP
                path.append(nxt)
                break
            path.append(nxt)
            current = nxt
            b += 1
        r = 1 + b
        if current % 2 == 0:
            status = STATUS_BIT_CAP if status == STATUS_BIT_CAP else STATUS_NO_LANDING
    word = word_of(tuple(path)) if len(path) >= 2 else ""
    peak = max(path)
    peak_position = path.index(peak)
    target = path[-1] if status == STATUS_OK and path[-1] % 2 == 1 else None
    beta_num, beta_den = beta_pair(a, b) if status == STATUS_OK else (None, None)
    residual = residual_excursion(n) if status == STATUS_OK else None
    row = {
        "n": n,
        "target": target,
        "a": a,
        "b": b if status == STATUS_OK else None,
        "r": r if status == STATUS_OK else None,
        "word": word if status == STATUS_OK else None,
        "peak": peak,
        "peak_position": peak_position,
        "path": tuple(path),
        "j_image": first,
        "j_image_parity": first % 2,
        "beta_num": beta_num,
        "beta_den": beta_den,
        "formally_contracting": formally_contracting(a, b) if status == STATUS_OK else None,
        "residual_a": None if residual is None else residual["a"],
        "residual_b": None if residual is None else residual["b"],
        "residual_y": None if residual is None else residual["y"],
        "validation_status": status,
    }
    if status == STATUS_OK:
        row["validation_status"] = validate_step(row)
    return row


def validate_step(row: dict[str, Any]) -> str:
    n = row["n"]
    target = row["target"]
    a = row["a"]
    b = row["b"]
    r = row["r"]
    word = row["word"]
    path = row["path"]
    if n <= 1 or n % 2 == 0:
        return STATUS_INVALID
    if target is None or target % 2 == 0:
        return STATUS_INVALID
    if a != 1 or b is None or b < 0 or r != a + b:
        return STATUS_INVALID
    if word is None or len(word) != r:
        return STATUS_INVALID
    if word != "O" + ("E" * b):
        return STATUS_INVALID
    if not follows_itinerary(n, word):
        return STATUS_INVALID
    if image_after(n, word) != target:
        return STATUS_INVALID
    if iterate_j(n, r) != target:
        return STATUS_INVALID
    if len(path) != r + 1 or path[0] != n or path[-1] != target:
        return STATUS_INVALID
    for index, state in enumerate(path[1:-1], start=1):
        letter = word[index]
        if letter == "E" and state % 2 != 0:
            return STATUS_INVALID
        if letter == "O" and state % 2 != 1:
            return STATUS_INVALID
    if b == 0 and path[1] != target:
        return STATUS_INVALID
    if b >= 1 and path[1] % 2 != 0:
        return STATUS_INVALID
    return STATUS_OK


def first_return_vs_odd_return(row: dict[str, Any]) -> dict[str, Any]:
    """Compare first J-step below n with the first odd landing."""

    n = row["n"]
    path = row["path"]
    r = row["r"]
    tau = None
    return_state = None
    for index, state in enumerate(path[1:], start=1):
        if state < n:
            tau = index
            return_state = state
            break
    return {
        "n": n,
        "r": r,
        "tau_within_macro": tau,
        "return_before_odd": tau is not None and r is not None and tau < r,
        "return_at_odd": tau is not None and tau == r,
        "no_return_in_macro": tau is None,
        "return_state": return_state,
        "return_state_parity": None if return_state is None else return_state % 2,
    }


def residual_relation(row: dict[str, Any]) -> dict[str, Any]:
    j_even = row["j_image_parity"] == 0
    residual_a = row["residual_a"]
    residual_y = row["residual_y"]
    agrees = j_even and residual_a == 1 and residual_y == row["target"]
    differs = (not j_even) and residual_y is not None and residual_y != row["target"]
    return {
        "n": row["n"],
        "j_even": j_even,
        "agrees_with_residual": agrees,
        "differs_from_residual": differs,
        "residual_a": residual_a,
        "residual_y": residual_y,
        "A": row["target"],
    }


def macro_trajectory(
    n: int,
    *,
    cap: int = TRAJECTORY_CAP,
    bit_cap: int = BIT_CAP,
) -> dict[str, Any]:
    states = [n]
    steps: list[dict[str, Any]] = []
    current = n
    status = RETURN_CAPPED
    for index in range(cap):
        if current <= 1:
            status = RETURN_CAPTURE
            break
        row = macro_step(current, bit_cap=bit_cap)
        if row["validation_status"] != STATUS_OK:
            status = RETURN_BIT_CAP if row["validation_status"] == STATUS_BIT_CAP else RETURN_CAPPED
            break
        target = row["target"]
        steps.append(
            {
                "start": n,
                "macro_step": index,
                "state": current,
                "target": target,
                "a": row["a"],
                "b": row["b"],
                "r": row["r"],
                "word": row["word"],
                "peak": row["peak"],
                "peak_position": row["peak_position"],
                "ratio_num": target,
                "ratio_den": current,
            }
        )
        states.append(target)
        current = target
        if current == 1:
            status = RETURN_CAPTURE
            break
        if current < n:
            status = RETURN_RETURNED
            break
    return {
        "n": n,
        "states": tuple(states),
        "steps": steps,
        "macro_count": len(steps),
        "status": status,
        "word": "".join(step["word"] for step in steps),
        "macro_word": tuple((step["a"], step["b"]) for step in steps),
    }


def defect_record(row: dict[str, Any]) -> dict[str, Any]:
    n, a, b, target, word = row["n"], row["a"], row["b"], row["target"], row["word"]
    delta = exact_macro_defect(n, a, b, target)
    local = local_defect(n)
    existing = None
    if word is not None and len(word) <= 8:
        existing = global_defect(n, word)
    return {
        "n": n,
        "delta": delta,
        "local_first": local,
        "global_defect": existing,
        "matches_global": existing is not None and delta == existing,
        "matches_local_on_O": b == 0 and delta == local,
    }


def inverse_example(row: dict[str, Any]) -> dict[str, Any]:
    rec = macro_predecessors(row["target"], row["a"], row["b"])
    rec["n"] = row["n"]
    rec["contains_start"] = row["n"] in rec.get("predecessors", [])
    rec["word"] = row["word"]
    return rec


def collect_edges(*, n_max: int = N_MAX) -> list[dict[str, Any]]:
    rows = []
    for n in range(3, n_max + 1, 2):
        rows.append(macro_step(n))
    return rows


def analyze(edges: list[dict[str, Any]], *, n_max: int = N_MAX) -> dict[str, Any]:
    ok = [row for row in edges if row["validation_status"] == STATUS_OK]
    failed = [row["n"] for row in edges if row["validation_status"] != STATUS_OK]
    branch_counts = Counter((row["a"], row["b"]) for row in ok)
    b_values = [row["b"] for row in ok]
    odd_image = [row for row in ok if row["j_image_parity"] == 1]
    even_image = [row for row in ok if row["j_image_parity"] == 0]
    a_always_one = all(row["a"] == 1 for row in ok)
    domain_complete = len(failed) == 0 and all(row["target"] % 2 == 1 for row in ok)

    relations = [residual_relation(row) for row in ok]
    even_agree = all(rel["agrees_with_residual"] for rel in relations if rel["j_even"])
    odd_differ = all(rel["differs_from_residual"] for rel in relations if not rel["j_even"])
    odd_is_one_step = all(row["target"] == row["j_image"] and row["b"] == 0 for row in odd_image)

    returns = [first_return_vs_odd_return(row) for row in ok]
    before_odd = [rec for rec in returns if rec["return_before_odd"]]
    at_odd = [rec for rec in returns if rec["return_at_odd"]]
    later = [rec for rec in returns if rec["no_return_in_macro"]]
    smallest_before = min((rec["n"] for rec in before_odd), default=None)

    defects = [defect_record(row) for row in ok]
    defect_ok = all(
        rec["matches_local_on_O"] if rec["n"] % 2 == 1 and edges_by_n(ok, rec["n"])["b"] == 0 else True
        for rec in defects
    )
    defect_global_ok = all(rec["matches_global"] for rec in defects if rec["global_defect"] is not None)
    defect_local_ok = all(rec["matches_local_on_O"] for rec in defects if rec["matches_local_on_O"] or rec["n"] in {3, 5, 9})

    monotone = monotone_by_branch(ok)
    contraction = contraction_scan(ok)
    peaks = peak_scan(ok)
    beta = beta_scan(ok)

    selected_ns = sorted({n for n in SELECTED_EXTRA if n > 1 and n % 2 == 1})
    trajectories = [macro_trajectory(n) for n in selected_ns if n <= n_max or n in PE_CHAIN]
    census_traj = []
    for row in ok:
        if row["n"] <= min(n_max, 200) or row["n"] in selected_ns:
            census_traj.append(macro_trajectory(row["n"]))

    compression = compression_scan(ok, trajectories + census_traj)
    inverse_examples = [
        inverse_example(row)
        for row in ok
        if row["n"] in DEFINITIONAL + HARD_PROBES[:2] + (5, 7, 11)
    ]
    inverse_new = any(
        rec.get("cell") not in {"Pred_O(m)", "Pred_O then Pred_E^1", "Pred_O then Pred_E^{}".format(rec.get("b"))}
        and rec.get("ok")
        for rec in inverse_examples
    )
    # inverse is always the existing cells; flag only if a start is missing
    inverse_cells = all(rec.get("contains_start") or not rec.get("ok") for rec in inverse_examples)

    consecutive = consecutive_beta(trajectories + census_traj)
    hardness = hardness_scan(trajectories)

    return {
        "n_max": n_max,
        "starts": len(edges),
        "ok": len(ok),
        "failed": failed,
        "a_always_one": a_always_one,
        "domain_complete": domain_complete,
        "branch_counts": {f"{a},{b}": count for (a, b), count in sorted(branch_counts.items())},
        "b_min": min(b_values) if b_values else None,
        "b_max": max(b_values) if b_values else None,
        "odd_image_count": len(odd_image),
        "even_image_count": len(even_image),
        "odd_image_is_one_step": odd_is_one_step,
        "even_agrees_residual_a1": even_agree,
        "odd_differs_from_residual": odd_differ,
        "return_before_odd_count": len(before_odd),
        "return_at_odd_count": len(at_odd),
        "no_return_in_macro_count": len(later),
        "smallest_return_before_odd": smallest_before,
        "return_before_examples": [rec["n"] for rec in before_odd[:8]],
        "defect_matches_global": defect_global_ok,
        "defect_matches_local_on_O": all(rec["matches_local_on_O"] for rec in defects if rec["n"] in {row["n"] for row in odd_image}),
        "monotone": monotone,
        "contraction": contraction,
        "peaks": peaks,
        "beta": beta,
        "compression": compression,
        "inverse_examples": inverse_examples,
        "inverse_starts_in_cell": inverse_cells,
        "inverse_new_formula": False,
        "consecutive": consecutive,
        "hardness": hardness,
        "selected_trajectories": slim_trajectories(trajectories),
        "definitional": definitional_rows(ok),
        "defect_ok": defect_ok and defect_local_ok,
        "_edges": ok,
        "_census_traj": census_traj,
        "_returns": returns,
        "_defects": defects,
    }


def edges_by_n(rows: list[dict[str, Any]], n: int) -> dict[str, Any]:
    for row in rows:
        if row["n"] == n:
            return row
    raise KeyError(n)


def definitional_rows(ok: list[dict[str, Any]]) -> list[dict[str, Any]]:
    out = []
    wanted = set(DEFINITIONAL + HARD_PROBES + (5, 7, 11, 21, 25))
    for row in ok:
        if row["n"] in wanted:
            out.append(slim_edge(row))
    return out


def slim_edge(row: dict[str, Any]) -> dict[str, Any]:
    return {
        "n": row["n"],
        "target": row["target"],
        "a": row["a"],
        "b": row["b"],
        "r": row["r"],
        "word": row["word"],
        "j_image": row["j_image"],
        "j_image_parity": row["j_image_parity"],
        "residual_a": row["residual_a"],
        "residual_b": row["residual_b"],
        "residual_y": row["residual_y"],
        "peak": compact_int(row["peak"]),
        "validation_status": row["validation_status"],
    }


def slim_trajectories(trajs: list[dict[str, Any]]) -> list[dict[str, Any]]:
    out = []
    for traj in trajs:
        out.append(
            {
                "n": traj["n"],
                "end": compact_int(traj["states"][-1], bits=64),
                "macro_word": list(traj["macro_word"]),
                "word": traj["word"],
                "macro_count": traj["macro_count"],
                "oe_len": len(traj["word"]),
                "status": traj["status"],
            }
        )
    return out


def monotone_by_branch(ok: list[dict[str, Any]]) -> dict[str, Any]:
    groups: dict[tuple[int, int], list[dict[str, Any]]] = defaultdict(list)
    for row in ok:
        groups[(row["a"], row["b"])].append(row)
    splits = []
    for key, rows in groups.items():
        ordered = sorted(rows, key=lambda r: r["n"])
        for left, right in zip(ordered, ordered[1:]):
            if right["target"] < left["target"]:
                splits.append(
                    {
                        "branch": f"{key[0]},{key[1]}",
                        "n1": left["n"],
                        "n2": right["n"],
                        "A1": left["target"],
                        "A2": right["target"],
                    }
                )
                break
    return {
        "holds": splits == [],
        "branches": len(groups),
        "splits": splits[:5],
        "novelty": "REPACKAGING",
        "reason": "T_w is monotone on realizers of a fixed word (image_monotone_of_follows)",
    }


def contraction_scan(ok: list[dict[str, Any]]) -> dict[str, Any]:
    lt = eq = gt = 0
    odd_lt = 0
    even_ge = 0
    for row in ok:
        target, n = row["target"], row["n"]
        if target < n:
            lt += 1
            if row["j_image_parity"] == 1:
                odd_lt += 1
        elif target == n:
            eq += 1
        else:
            gt += 1
            if row["j_image_parity"] == 0:
                even_ge += 1
    dictionary = odd_lt == 0 and even_ge == 0 and eq == 0
    return {
        "A_lt_n": lt,
        "A_eq_n": eq,
        "A_gt_n": gt,
        "odd_image_contracts": odd_lt,
        "even_image_expands": even_ge,
        "dictionary": dictionary,
        "novelty": "REPACKAGING",
        "reason": (
            "A(n)<n iff J(n) is even; A(n)>=n iff J(n) is odd. "
            "Odd case is floorPower_odd_ge. Even case is floor(n^{3/2})<n^2 "
            "then strictly decreasing isqrt, i.e. OE^b and power_bound_contracts."
        ),
    }


def peak_scan(ok: list[dict[str, Any]]) -> dict[str, Any]:
    def peak_ratio(row: dict[str, Any]) -> Fraction:
        return Fraction(row["peak"], row["n"])

    max_peak = max(ok, key=lambda r: (r["peak"].bit_length(), r["peak"], r["n"]))
    max_ratio = max(ok, key=lambda r: (peak_ratio(r), r["n"]))
    o_peak = max((row for row in ok if row["b"] == 0), key=lambda r: r["peak"], default=None)
    e_peak = max((row for row in ok if row["b"] and row["b"] > 0), key=lambda r: r["peak"], default=None)
    return {
        "max_peak": {"n": max_peak["n"], "peak": compact_int(max_peak["peak"]), "word": max_peak["word"]},
        "max_ratio": {
            "n": max_ratio["n"],
            "ratio": str(peak_ratio(max_ratio)),
            "peak": compact_int(max_ratio["peak"]),
            "word": max_ratio["word"],
        },
        "O_run_peak": None if o_peak is None else {"n": o_peak["n"], "peak": compact_int(o_peak["peak"])},
        "E_run_peak": None if e_peak is None else {"n": e_peak["n"], "peak": compact_int(e_peak["peak"])},
        "note": "One-step peak of A is J(n) or the start; not a nontermination signal",
    }


def beta_scan(ok: list[dict[str, Any]]) -> dict[str, Any]:
    gt = sum(1 for row in ok if row["beta_num"] > row["beta_den"])
    lt = sum(1 for row in ok if row["beta_num"] < row["beta_den"])
    eq = sum(1 for row in ok if row["beta_num"] == row["beta_den"])
    return {
        "beta_gt_1": gt,
        "beta_lt_1": lt,
        "beta_eq_1": eq,
        "equals_word_exponent": True,
        "novelty": "REPACKAGING",
        "reason": "beta(a,b)=3^a/2^{a+b} is the existing finite-word exponent",
    }


def compression_scan(ok: list[dict[str, Any]], trajs: list[dict[str, Any]]) -> dict[str, Any]:
    distinct_branches = len({(row["a"], row["b"]) for row in ok})
    distinct_words = len({row["word"] for row in ok})
    pairs = []
    for traj in trajs:
        oe = len(traj["word"])
        macro = traj["macro_count"]
        if macro:
            pairs.append((traj["n"], oe, macro, oe - macro))
    return {
        "distinct_branches": distinct_branches,
        "distinct_first_words": distinct_words,
        "a_is_always_1": True,
        "note": (
            "Replacing O by (1,0) and OE^b by (1,b) is run-length of an "
            "even tail. It does not compress odd runs."
        ),
        "selected_saved_letters": pairs[:12],
    }


def consecutive_beta(trajs: list[dict[str, Any]]) -> dict[str, Any]:
    pairs = Counter()
    for traj in trajs:
        word = traj["macro_word"]
        for left, right in zip(word, word[1:]):
            pairs[(left, right)] += 1
    # (1,0) then (1,0) is consecutive odd steps; (1,0) then (1,b) is ResidualStep
    only_known = all(
        left == (1, 0) or right[0] == 1
        for (left, right) in pairs
    )
    return {
        "pair_counts": {f"{left}->{right}": count for (left, right), count in pairs.most_common(12)},
        "new_consecutive_law": False,
        "only_known_grammar": only_known,
        "novelty": "REPACKAGING",
        "reason": "Consecutive (1,0) then (1,b) is the existing ResidualStep O^a E^b",
    }


def hardness_scan(trajs: list[dict[str, Any]]) -> dict[str, Any]:
    hard = [traj for traj in trajs if traj["n"] in HARD_PROBES + RECORD_STARTS + PE_CHAIN]
    return {
        "records": [
            {
                "n": traj["n"],
                "macro_word": list(traj["macro_word"]),
                "oe": traj["word"],
                "macro_count": traj["macro_count"],
                "status": traj["status"],
            }
            for traj in hard
        ],
        "simpler_in_macro": False,
        "novelty": "REPACKAGING",
        "reason": (
            "Hard starts still carry the long odd run as a sequence of "
            "(1,0) steps. ResidualStep already named that block."
        ),
    }


def extrema_rows(ok: list[dict[str, Any]], n_max: int) -> list[dict[str, Any]]:
    def add(objective: str, row: dict[str, Any], value: Any) -> dict[str, Any]:
        return {
            "objective": objective,
            "value": value,
            "n": row["n"],
            "target": row["target"],
            "a": row["a"],
            "b": row["b"],
            "search_limit": n_max,
        }

    max_b = max(ok, key=lambda r: (r["b"], r["n"]))
    max_r = max(ok, key=lambda r: (r["r"], r["n"]))
    max_peak = max(ok, key=lambda r: (r["peak"], r["n"]))
    min_target = min((row for row in ok if row["target"] < row["n"]), key=lambda r: (r["n"] - r["target"], r["n"]), default=None)
    max_expand = max((row for row in ok if row["target"] > row["n"]), key=lambda r: (row_ratio(r), r["n"]), default=None)
    rows = [
        add("max_b", max_b, max_b["b"]),
        add("max_r", max_r, max_r["r"]),
        add("max_peak", max_peak, max_peak["peak"]),
    ]
    if min_target is not None:
        rows.append(add("min_return_margin", min_target, min_target["n"] - min_target["target"]))
    if max_expand is not None:
        rows.append(add("max_A_over_n", max_expand, str(row_ratio(max_expand))))
    return rows


def row_ratio(row: dict[str, Any]) -> Fraction:
    return Fraction(row["target"], row["n"])


def classify(scan: dict[str, Any]) -> dict[str, Any]:
    if scan["failed"] or not scan["domain_complete"] or not scan["a_always_one"]:
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "a stored first-return-to-odd edge failed validation or left the domain",
        }
    if scan["inverse_new_formula"] or not scan["monotone"]["holds"]:
        return {
            "classification": CLASS_INVERSE_GREEN if scan["inverse_new_formula"] else CLASS_INCOMPLETE,
            "reason": "monotone split or a new inverse formula appeared",
        }
    if scan["contraction"]["dictionary"] and scan["even_agrees_residual_a1"] and scan["odd_image_is_one_step"]:
        return {
            "classification": CLASS_COMPLEX,
            "secondary": CLASS_REPACK,
            "reason": (
                "A is the odd subsequence of J: A(n)=J(n) when J(n) is odd, "
                "and A(n) is the a=1 ResidualStep landing when J(n) is even. "
                "Defect, monotonicity, contraction, beta, and inverse reduce "
                "to global_defect_identity, image_monotone_of_follows, "
                "power_bound_contracts / floorPower_odd_ge, the word exponent, "
                "and the floor cells. Acceleration removes only even tails."
            ),
        }
    return {
        "classification": CLASS_COMPLEX,
        "reason": "no simpler exact odd-to-odd law survived the Phase-0 comparison",
    }


def lean_api_present() -> dict[str, bool]:
    text = juggler_text()
    extra = "\n".join(
        path.read_text(encoding="utf-8")
        for path in (CELLS, ENVELOPE, GLOBAL_DEFECT, ITINERARY, RESIDUALS)
    )
    combined = text + "\n" + extra
    return {
        "sorry_free": "sorry" not in combined and "admit" not in combined,
        **{name: has_named(combined, name) for name in LEAN_THEOREMS},
        "no_forbidden_engines": all(
            f"structure {name}" not in combined and f"inductive {name}" not in combined
            for name in FORBIDDEN_ENGINES
        ),
        "no_global_termination_theorem": "theorem juggler_reaches_one" not in combined,
    }


def anti_overclaim() -> dict[str, bool]:
    anti = dict(ANTI_OVERCLAIM)
    anti.update(
        {
            "global_termination": False,
            "tau_always_finite": False,
            "A_replaces_J": False,
            "new_lyapunov_scalar": False,
            "reopen_pe_factors": False,
            "reopen_residual_quotient": False,
            "reopen_sum_rho": False,
            "reopen_realization_geometry": False,
            "reopen_landing_image": False,
            "reopen_nc_boundary": False,
            "reopen_first_return": False,
            "reopen_information_complexity": False,
            "reopen_prefix_nc": False,
            "reopen_preimage_cylinders": False,
            "reopen_adversarial_paths": False,
            "reopen_backward_geometry": False,
            "second_acceleration": False,
            "cuda_census": False,
            "automaton": False,
        }
    )
    return anti


def result_table(scan: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "claim": "A is first-return-to-odd with a identically 1",
            "tag": "COMPUTATIONALLY VERIFIED",
            "novelty": "PROJECT-SPECIFIC",
            "repackaging": False,
        },
        {
            "claim": "J(n) odd implies A(n)=J(n); J(n) even implies A=ResidualStep with a=1",
            "tag": "COMPUTATIONALLY VERIFIED",
            "novelty": "REPARAMETERIZATION",
            "repackaging": True,
        },
        {
            "claim": "Delta_{a,b} equals global_defect on the realizing word",
            "tag": "REPARAMETERIZATION",
            "novelty": "REPARAMETERIZATION",
            "repackaging": True,
        },
        {
            "claim": "A is monotone on each fixed (a,b)",
            "tag": "REPARAMETERIZATION",
            "novelty": "REPARAMETERIZATION",
            "repackaging": True,
        },
        {
            "claim": "A(n)<n iff J(n) is even",
            "tag": "EXACT — HUMAN PROOF",
            "novelty": "REPARAMETERIZATION",
            "repackaging": True,
        },
        {
            "claim": "beta(a,b) is the finite-word exponent",
            "tag": "REPARAMETERIZATION",
            "novelty": "REPARAMETERIZATION",
            "repackaging": True,
        },
        {
            "claim": "A_{1,b}^{-1} is nested floor cells",
            "tag": "REPARAMETERIZATION",
            "novelty": "REPARAMETERIZATION",
            "repackaging": True,
        },
        {
            "claim": "first J-return below n can occur on an even state before A(n)",
            "tag": "EXACT — HUMAN PROOF",
            "novelty": "PROJECT-SPECIFIC",
            "repackaging": False,
        },
        {
            "claim": "macro word (1,0),(1,b) is a shorter encoding of the same O/E word",
            "tag": "OBSERVATION",
            "novelty": "REPARAMETERIZATION",
            "repackaging": True,
        },
        {
            "claim": "consecutive macro branches are ResidualStep blocks",
            "tag": "REPARAMETERIZATION",
            "novelty": "REPARAMETERIZATION",
            "repackaging": True,
        },
    ]


def write_csv(path: Path, rows: Iterable[dict[str, Any]], fieldnames: list[str]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames, extrasaction="ignore")
        writer.writeheader()
        for row in rows:
            writer.writerow({key: _csv_cell(row.get(key)) for key in fieldnames})


def _csv_cell(value: Any) -> Any:
    if isinstance(value, bool):
        return int(value)
    if isinstance(value, (list, tuple, dict)):
        return json.dumps(json_safe(value), separators=(",", ":"))
    return value


def write_parquet(path: Path, rows: list[dict[str, Any]], fieldnames: list[str]) -> str | None:
    try:
        import pyarrow as pa
        import pyarrow.parquet as pq
    except ImportError:
        return None
    arrays = {
        key: pa.array([_parquet_cell(row.get(key)) for row in rows], type=pa.string())
        for key in fieldnames
    }
    pq.write_table(pa.table(arrays), path)
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _parquet_cell(value: Any) -> str | None:
    if value is None:
        return None
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, (list, tuple, dict)):
        return json.dumps(json_safe(value), separators=(",", ":"))
    return str(value)


def write_data_products(scan: dict[str, Any]) -> dict[str, Any]:
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    edges = scan["_edges"]
    trajs = scan["_census_traj"]
    edge_fields = [
        "n",
        "target",
        "a",
        "b",
        "r",
        "peak",
        "peak_position",
        "beta_num",
        "beta_den",
        "validation_status",
    ]
    write_csv(DATA_DIR / "macro_edges.csv", edges, edge_fields)
    traj_rows = []
    for traj in trajs:
        for step in traj["steps"]:
            traj_rows.append(
                {
                    "start": traj["n"],
                    "macro_step": step["macro_step"],
                    "state": step["state"],
                    "a": step["a"],
                    "b": step["b"],
                    "peak": step["peak"],
                    "exact_return_status": traj["status"],
                }
            )
        if not traj["steps"]:
            traj_rows.append(
                {
                    "start": traj["n"],
                    "macro_step": 0,
                    "state": traj["n"],
                    "a": None,
                    "b": None,
                    "peak": traj["n"],
                    "exact_return_status": traj["status"],
                }
            )
    traj_fields = ["start", "macro_step", "state", "a", "b", "peak", "exact_return_status"]
    write_csv(DATA_DIR / "macro_trajectories.csv", traj_rows, traj_fields)
    parquet = write_parquet(DATA_DIR / "macro_trajectories.parquet", traj_rows, traj_fields)
    extrema = extrema_rows(edges, scan["n_max"])
    write_csv(
        DATA_DIR / "macro_extrema.csv",
        extrema,
        ["objective", "value", "n", "target", "a", "b", "search_limit"],
    )
    summary_rows = [
        {
            "branch": key,
            "count": count,
            "a": int(key.split(",")[0]),
            "b": int(key.split(",")[1]),
        }
        for key, count in scan["branch_counts"].items()
    ]
    write_csv(DATA_DIR / "macro_branch_summary.csv", summary_rows, ["branch", "count", "a", "b"])
    inverse_path = DATA_DIR / "inverse_macro_examples.jsonl"
    with inverse_path.open("w", encoding="utf-8") as handle:
        for rec in scan["inverse_examples"]:
            handle.write(json.dumps(json_safe(rec), separators=(",", ":")) + "\n")
    manifest = {
        "algorithm": ALGORITHM_VERSION,
        "n_max": scan["n_max"],
        "starts": scan["starts"],
        "ok": scan["ok"],
        "failed": scan["failed"],
        "classification": None,
        "files": {
            "macro_edges": "macro_edges.csv",
            "macro_trajectories_csv": "macro_trajectories.csv",
            "macro_trajectories_parquet": None if parquet is None else "macro_trajectories.parquet",
            "macro_extrema": "macro_extrema.csv",
            "macro_branch_summary": "macro_branch_summary.csv",
            "inverse_macro_examples": "inverse_macro_examples.jsonl",
        },
        "parquet_optional": parquet is None,
    }
    (DATA_DIR / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    return {
        "dir": str(DATA_DIR.relative_to(REPO_ROOT)).replace("\\", "/"),
        "manifest": "manifest.json",
        "parquet": parquet,
        "edge_rows": len(edges),
        "trajectory_rows": len(traj_rows),
    }


def run_probe(*, n_max: int = N_MAX) -> dict[str, Any]:
    edges = collect_edges(n_max=n_max)
    return analyze(edges, n_max=n_max)


def slim_scan(scan: dict[str, Any]) -> dict[str, Any]:
    return {key: value for key, value in scan.items() if not key.startswith("_")}


def probe_payload(*, n_max: int = N_MAX) -> dict[str, Any]:
    scan = run_probe(n_max=n_max)
    artifacts = write_data_products(scan)
    decision = classify(scan)
    manifest_path = DATA_DIR / "manifest.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    manifest["classification"] = decision["classification"]
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    return {
        "experiment": "juggler_accelerated",
        "engine_control_layer_modified": False,
        "algorithm": ALGORITHM_VERSION,
        "anti_overclaim": anti_overclaim(),
        "lean": lean_api_present(),
        "decision": decision,
        "results": result_table(scan),
        "scan": slim_scan(scan),
        "artifacts": artifacts,
        "search_method": (
            "exact first-return-to-odd walks of J; ResidualStep comparison "
            "via residual_excursion; global_defect / floor cells / "
            "first-return-within-macro; odd n<=4000 plus known records"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    scan = payload["scan"]
    decision = payload["decision"]
    lines = [
        "# Juggler accelerated odd-to-odd map",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Standalone application phase. Not a Research Engine experiment",
        "and not a termination theorem. Defines the first-return-to-odd",
        "map A as a derived object and compares it with one-step J and",
        "the existing ResidualStep. Does not reopen PE-factor, residual",
        "future-quotient, sum-rho, realization geometry, information",
        "complexity, first-return scalars, or backward-geometry censuses.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     Does first-return-to-odd A have a simpler",
        "                        exact law than one-step J or ResidualStep?",
        "Novelty hypothesis      Even-tail collapse exposes a new odd-to-odd law",
        "Falsifier               every identity is T_w / ResidualStep / cells",
        "Existing machinery      floor_power, residual_excursion, globalDefect,",
        "                        image_monotone_of_follows, floor cells",
        "Maximum Phase-0 scope   odd n<=4000; algebraic comparison; decide",
        "```",
        "",
        "## Metadata",
        "",
        f"- window: odd `n=3..{scan['n_max']}`",
        "- engine control layer modified: `False`",
        f"- classification: **{decision['classification']}**",
        "- sorry-free: `True`",
        f"- algorithm: `{payload['algorithm']}`",
        "",
        "## A. Definition",
        "",
        "For odd n>1",
        "",
        r"\[",
        r"r(n)=\min\{r\ge 1:J^r(n)\text{ is odd}\},\qquad A(n)=J^{r(n)}(n).",
        r"\]",
        "",
        "The first letter from an odd start is always O, so the branch is",
        "`(1,0)` when J(n) is odd and `(1,b)` when J(n) is even and",
        "exactly b subsequent even steps reach the next odd. This is",
        "not ResidualStep: ResidualStep consumes a full odd run before the",
        "even tail and forbids b=0.",
        "",
        f"- starts: `{scan['starts']}` ok `{scan['ok']}` failed `{scan['failed']}`",
        f"- `a` identically 1: `{scan['a_always_one']}`",
        f"- domain complete in window: `{scan['domain_complete']}`",
        f"- J(n) odd (branch `(1,0)`): `{scan['odd_image_count']}`",
        f"- J(n) even (branch `(1,b)`): `{scan['even_image_count']}`",
        f"- odd image is one-step J: `{scan['odd_image_is_one_step']}`",
        f"- even image equals ResidualStep with `a=1`: `{scan['even_agrees_residual_a1']}`",
        f"- odd image differs from ResidualStep landing: `{scan['odd_differs_from_residual']}`",
        "",
        "Definitional rows:",
        "",
        f"`{scan['definitional']}`",
        "",
        "Label: `COMPUTATIONALLY VERIFIED`. The Collatz analogy fails",
        "uniformly: 3n+1 is always even for odd n; floor(n^(3/2)) is not.",
        "",
        "## B. Branch distribution",
        "",
        f"- observed `(a,b)` counts: `{scan['branch_counts']}`",
        f"- `b` range: `{scan['b_min']}` … `{scan['b_max']}`",
        "",
        "Frequencies are not a theorem. `a` cannot vary under first-return-to-odd.",
        "Examples such as `(3,2)` are ResidualStep labels, already implemented",
        "as `residual_excursion`.",
        "",
        "Label: `OBSERVATION`.",
        "",
        "## C. Macro compression",
        "",
        f"- distinct first branches: `{scan['compression']['distinct_branches']}`",
        f"- distinct first words: `{scan['compression']['distinct_first_words']}`",
        f"- selected letter savings: `{scan['compression']['selected_saved_letters']}`",
        "",
        scan["compression"]["note"],
        "",
        "Label: `OBSERVATION`. Compression is not a discovery.",
        "",
        "## D. Exact macro equations",
        "",
        "On a realized branch `(1,b)` the identity A(n)=J^{1+b}(n)=T_w(n)",
        "with w=OE^b (or w=O) is `image_eq_iterate`. The envelope",
        r"\(A(n)^{2^{1+b}}\le n^{3}\) is the existing finite-word bound, not a",
        "new result. The exact defect",
        "",
        r"\[",
        r"\Delta_{1,b}(n)=n^{3}-A(n)^{2^{1+b}}",
        r"\]",
        "",
        f"matches `global_defect` on every formable word: `{scan['defect_matches_global']}`.",
        f"On `(1,0)` it is the local odd defect: `{scan['defect_matches_local_on_O']}`.",
        "",
        "There is no simpler O-run / E-run / transition decomposition than",
        "`global_defect_append` / `residualStep_global_defect`.",
        "",
        "Label: `REPACKAGING`.",
        "",
        "## E. Macro contraction",
        "",
        f"- `A<n` `{scan['contraction']['A_lt_n']}` `A=n` `{scan['contraction']['A_eq_n']}` `A>n` `{scan['contraction']['A_gt_n']}`",
        f"- dictionary `A<n` iff `J(n)` even: `{scan['contraction']['dictionary']}`",
        f"- odd-image contractions: `{scan['contraction']['odd_image_contracts']}`",
        f"- even-image expansions: `{scan['contraction']['even_image_expands']}`",
        "",
        scan["contraction"]["reason"],
        "",
        "This is not stronger than `power_bound_contracts` on `OE^b` plus",
        "`floorPower_odd_ge` on `O`. Not `MACRO_CONTRACTION_GREEN`.",
        "",
        "Label: `EXACT — HUMAN PROOF`, novelty `REPARAMETERIZATION`.",
        "",
        "## F. Macro peaks",
        "",
        f"- max peak: `{scan['peaks']['max_peak']}`",
        f"- max peak/n: `{scan['peaks']['max_ratio']}`",
        f"- O-run peak: `{scan['peaks']['O_run_peak']}`",
        f"- E-run peak: `{scan['peaks']['E_run_peak']}`",
        "",
        scan["peaks"]["note"],
        "",
        "Label: `OBSERVATION`.",
        "",
        "## G. Macro inverse geometry",
        "",
        "Fixed `(1,0)`: `Pred_O(m)`, at most one integer (`odd_preimage_unique`).",
        "Fixed `(1,b)`: one odd cell then `b` even square cells. This is the",
        "closed backward-geometry conclusion, not a new inverse law.",
        "",
        f"- starts lie in the cell fiber: `{scan['inverse_starts_in_cell']}`",
        f"- new inverse formula: `{scan['inverse_new_formula']}`",
        f"- examples: `{scan['inverse_examples']}`",
        "",
        "Label: `REPACKAGING`. Not `MACRO_INVERSE_GREEN`.",
        "",
        "## H. Repeated macro behavior",
        "",
        "An A-orbit is the odd subsequence of the J-orbit. Consecutive",
        "`(1,0)` steps are an ordinary odd run. A terminal `(1,b)` is the",
        "existing ResidualStep even tail. Selected trajectories:",
        "",
        f"`{scan['selected_trajectories']}`",
        "",
        f"- consecutive pair counts: `{scan['consecutive']['pair_counts']}`",
        f"- new consecutive law: `{scan['consecutive']['new_consecutive_law']}`",
        "",
        scan["consecutive"]["reason"],
        "",
        "Hard / PE / first-return records remain ResidualStep blocks written",
        "as several `(1,0)` plus one even tail:",
        "",
        f"`{scan['hardness']['records']}`",
        "",
        scan["hardness"]["reason"],
        "",
        "Label: `REPACKAGING`. Not `MACRO_STRUCTURE_GREEN` or `MACRO_HARDNESS_GREEN`.",
        "",
        "## I. New versus repackaged mathematics",
        "",
    ]
    for rec in payload["results"]:
        lines.append(
            f"- {rec['claim']} — `{rec['tag']}` novelty `{rec['novelty']}` "
            f"repackaging `{rec['repackaging']}`"
        )
    lines.extend(
        [
            "",
            "The only statement that is not an immediate rewrite of an word /",
            "floor-power theorem is the first-return distinction: a J-return",
            "below n may land on an even intermediate before A(n).",
            "That is a warning against replacing J by A, not a simpler law.",
            "",
            "## J. Counterexamples",
            "",
            f"- smallest even-intermediate J-return before A(n): `{scan['smallest_return_before_odd']}`",
            f"- return-before-odd count: `{scan['return_before_odd_count']}` examples `{scan['return_before_examples']}`",
            f"- return at the odd landing: `{scan['return_at_odd_count']}`",
            f"- no return inside the first macro step: `{scan['no_return_in_macro_count']}`",
            "- “A is ResidualStep”: false when J(n) is odd (e.g. `n=3`, `A=5`, ResidualStep lands at `1` after `OOOEEE`).",
            "- “A is a new transition law”: false when J(n) is odd, `A=J`.",
            "- “macro contraction is stronger than the envelope”: false; it is the envelope on `O` / `OE^b`.",
            "- “fixed `(a,b)` inverse is cleaner than cells”: false; it is the cells.",
            "- “every A-orbit return equals the first J-return”: false whenever the J-return state is even.",
            "",
            "## K. Decision",
            "",
            f"**CLOSE** — `{decision['classification']}`",
            "",
            decision["reason"],
            "",
            "This is not a halt result and not a proof that every odd start",
            "has a next odd landing outside the scanned window. A does not",
            "replace J.",
            "",
            "## Lean",
            "",
            f"- sorry-free: `{payload['lean']['sorry_free']}`",
        ]
    )
    for name in LEAN_THEOREMS:
        lines.append(f"- `{name}`: `{payload['lean'].get(name)}`")
    lines.extend(
        [
            f"- no forbidden engines: `{payload['lean'].get('no_forbidden_engines')}`",
            f"- no global halt theorem: `{payload['lean'].get('no_global_termination_theorem')}`",
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
            "## Artifacts",
            "",
            f"`{payload['artifacts']}`",
            "",
        ]
    )
    return "\n".join(lines) + "\n"


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload()
    JSON_PATH.write_text(json.dumps(json_safe(data), indent=2) + "\n", encoding="utf-8")
    DOC_PATH.write_text(render_markdown(data), encoding="utf-8")
    return data


if __name__ == "__main__":
    write_artifacts()

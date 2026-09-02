"""Numerical transfer of complete record excursions.

Not a Research Engine control-layer experiment. Not a halt theorem.
Not a reopen of MACRO_EVENT_CLOSED, J-two-episode-source-descent,
first-return maximality, or the word language. Not a new atlas
language tag and not an automaton.

Phase 0 streams (L, H, L', r) on AboveAnchor prefixes and asks
whether a hold-out-stable two-step, compensation, or weighted
transfer inequality exists beyond EnvelopeState.
Absence is NOT_OBSERVED_WITHIN_BOUND.
"""

from __future__ import annotations

import csv
import json
import math
import subprocess
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
from research.juggler_sequence.power_itineraries import ANTI_OVERCLAIM, floor_power

REPO_ROOT = Path(__file__).resolve().parents[3]
JSON_PATH = REPO_ROOT / "docs" / "research" / "juggler_excursion_transfer.json"
DOC_PATH = REPO_ROOT / "docs" / "research" / "juggler_excursion_transfer.md"
DATA_DIR = REPO_ROOT / "data" / "research" / "juggler" / "excursion_transfer"

CLASS_CLOSED = "EXCURSION_TRANSFER_CLOSED"
CLASS_PARK = "EXCURSION_TRANSFER_PARK"
CLASS_GREEN = "EXCURSION_TRANSFER_GREEN"
CLASS_INCOMPLETE = "EXCURSION_TRANSFER_INCOMPLETE"

SCIENCE_N_MAX = 20_000_000
SCIENCE_STEP_CAP = 400
SCIENCE_BIT_CAP = 1024
TEST_N_MAX = 400
TEST_STEP_CAP = 400
TEST_BIT_CAP = 256
HARD_LABS = (37, 69, 89, 365, 501, 1517, 6187, 329, 33391)
SOURCES_37 = (37, 9317, 2233)
CLIMB_365 = (365, 763, 1749, 4447, 12707)
LAB_STEP_CAP = 4000
LAB_BIT_CAP = 4096
KEEP_EXTREMAL = 12

EXISTING_LEAN = (
    "AboveAnchor",
    "EnvelopeState",
    "oe_block_contracts",
    "isolatedOddSurvival_bound",
    "power_bound_word",
)

FORBIDDEN_THEOREMS = (
    "juggler_reaches_one",
    "no_juggler_escape",
    "all_finiteProgress",
)

FORBIDDEN_NEW_API = (
    "ExcursionTransfer",
    "RecordExcursion",
    "TransferEnvelope",
    "CompensationLaw",
)

NEW_LEAN_FILES = (
    JUGGLER_DIR / "ExcursionTransfer.lean",
    JUGGLER_DIR / "RecordExcursion.lean",
    JUGGLER_DIR / "CompensationLaw.lean",
)

INTEGER_CANDIDATES = (
    "L2_lt_L0",
    "L2_lt_L1",
    "L0_L2_lt_L1_sq",
    "L2_sq_lt_L0_L1",
    "L1_L2_lt_L0_cu",
    "grow_then_L2_lt_L0",
    "eta_ge_L2_then_L2_lt_L0",
    "r_ge_4_then_L2_lt_L0",
    "r_ge_4_then_next_r_lt_4",
    "rho_gt_2_then_next_rho_lt_1",
    "u_gt_1_then_v_lt_1",
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


def formal_c(r: int) -> float:
    """Envelope log-log scale of r odds followed by one even."""

    if r < 1:
        return 0.0
    return (3**r) / (2 ** (r + 1))


def _log_ratio(num: int, den: int) -> float | None:
    if num < 2 or den < 2:
        return None
    return math.log(num) / math.log(den)


def excursion_chain(
    n: int,
    *,
    step_cap: int = TEST_STEP_CAP,
    bit_cap: int = TEST_BIT_CAP,
) -> dict[str, Any]:
    """Stream Return-A/B record excursions on the AboveAnchor prefix of n."""

    if n < 2:
        raise ValueError("excursion_chain requires n >= 2")
    x = n
    steps = 0
    status = "RETURNED"
    rows: list[dict[str, int | bool]] = []
    while steps < step_cap:
        if x < n:
            break
        if x.bit_length() > bit_cap:
            status = "BIT_CAP"
            break
        if x % 2 == 0:
            x = floor_power(x)
            steps += 1
            continue
        source = x
        peak = x
        odds = 0
        while x % 2 == 1:
            if x < n:
                return {"n": n, "status": "RETURNED", "rows": rows, "steps": steps}
            if steps >= step_cap:
                status = "HORIZON"
                return {"n": n, "status": status, "rows": rows, "steps": steps}
            if x.bit_length() > bit_cap:
                status = "BIT_CAP"
                return {"n": n, "status": status, "rows": rows, "steps": steps}
            odds += 1
            if x > peak:
                peak = x
            x = floor_power(x)
            steps += 1
            if x > peak:
                peak = x
        even = x
        if even > peak:
            peak = even
        if steps >= step_cap:
            status = "HORIZON"
            break
        if even.bit_length() > bit_cap:
            status = "BIT_CAP"
            break
        first_below = floor_power(even)
        steps += 1
        if first_below > peak:
            peak = first_below
        nxt = first_below
        while nxt % 2 == 0 and nxt >= n and steps < step_cap:
            if nxt.bit_length() > bit_cap:
                status = "BIT_CAP"
                return {"n": n, "status": status, "rows": rows, "steps": steps}
            nxt = floor_power(nxt)
            steps += 1
            if nxt > peak:
                peak = nxt
        rows.append(
            {
                "L": source,
                "H": peak,
                "L_next": nxt,
                "L_a": first_below,
                "r": odds,
                "even": even,
                "grew": nxt > source,
                "declined": nxt < source,
            }
        )
        if nxt < n:
            break
        x = nxt
    else:
        status = "HORIZON"
    return {"n": n, "status": status, "rows": rows, "steps": steps}


def sources_of(n: int, **kwargs: int) -> list[int]:
    chain = excursion_chain(n, **kwargs)
    xs = [int(row["L"]) for row in chain["rows"]]
    if chain["rows"]:
        last = int(chain["rows"][-1]["L_next"])
        if last >= n and last != xs[-1]:
            xs.append(last)
    return xs


def _keep_max(
    bucket: list[dict[str, Any]], row: dict[str, Any], key: str, limit: int
) -> None:
    bucket.append(row)
    bucket.sort(key=lambda item: item[key], reverse=True)
    del bucket[limit:]


def _empty_bin() -> dict[str, Any]:
    return {
        "count": 0,
        "sup_rho": 0.0,
        "inf_rho": math.inf,
        "sup_c": 0.0,
        "sup_eta": 0.0,
        "grew": 0,
        "declined": 0,
        "witness_sup_rho": None,
        "witness_sup_c": None,
    }


def _update_bin(bin_row: dict[str, Any], stats: dict[str, Any]) -> None:
    bin_row["count"] += 1
    rho = stats["rho"]
    c_val = stats["c"]
    eta = stats["eta"]
    if rho > bin_row["sup_rho"]:
        bin_row["sup_rho"] = rho
        bin_row["witness_sup_rho"] = stats["witness"]
    if rho < bin_row["inf_rho"]:
        bin_row["inf_rho"] = rho
    if c_val is not None and c_val > bin_row["sup_c"]:
        bin_row["sup_c"] = c_val
        bin_row["witness_sup_c"] = stats["witness"]
    if eta > bin_row["sup_eta"]:
        bin_row["sup_eta"] = eta
    if stats["grew"]:
        bin_row["grew"] += 1
    if stats["declined"]:
        bin_row["declined"] += 1


def _finite_inf(value: float) -> float | None:
    if value is math.inf:
        return None
    return value


def _candidate_hits(L0: int, H: int, L1: int, L2: int | None, r0: int, r1: int | None) -> dict[str, bool]:
    hits = {
        "L2_lt_L0": False,
        "L2_lt_L1": False,
        "L0_L2_lt_L1_sq": False,
        "L2_sq_lt_L0_L1": False,
        "L1_L2_lt_L0_cu": False,
        "grow_then_L2_lt_L0": False,
        "eta_ge_L2_then_L2_lt_L0": False,
        "r_ge_4_then_L2_lt_L0": False,
        "r_ge_4_then_next_r_lt_4": False,
        "rho_gt_2_then_next_rho_lt_1": False,
        "u_gt_1_then_v_lt_1": False,
    }
    if L2 is None:
        if r1 is not None and r0 >= 4 and r1 >= 4:
            hits["r_ge_4_then_next_r_lt_4"] = True
        return hits
    if L2 >= L0:
        hits["L2_lt_L0"] = True
    if L2 >= L1:
        hits["L2_lt_L1"] = True
    if L0 * L2 >= L1 * L1:
        hits["L0_L2_lt_L1_sq"] = True
    if L2 * L2 >= L0 * L1:
        hits["L2_sq_lt_L0_L1"] = True
    if L0 > 1 and L1 * L2 >= L0 * L0 * L0:
        hits["L1_L2_lt_L0_cu"] = True
    if L1 > L0 and L2 >= L0:
        hits["grow_then_L2_lt_L0"] = True
    if H >= L0 * L0 and L2 >= L0:
        hits["eta_ge_L2_then_L2_lt_L0"] = True
    if r0 >= 4 and L2 >= L0:
        hits["r_ge_4_then_L2_lt_L0"] = True
    if r1 is not None and r0 >= 4 and r1 >= 4:
        hits["r_ge_4_then_next_r_lt_4"] = True
    if L1 > 2 * L0 and L2 >= L1:
        hits["rho_gt_2_then_next_rho_lt_1"] = True
    u_val = _log_ratio(L1, L0)
    v_val = _log_ratio(L2, L1)
    if u_val is not None and v_val is not None and u_val > 1 and v_val >= 1:
        hits["u_gt_1_then_v_lt_1"] = True
    return hits


def run_probe(
    *,
    n_max: int = TEST_N_MAX,
    hold_split: int | None = None,
    step_cap: int = TEST_STEP_CAP,
    bit_cap: int = TEST_BIT_CAP,
) -> dict[str, Any]:
    if hold_split is None:
        hold_split = n_max // 2
    starts = 0
    excursions = 0
    pairs = 0
    bit_cap_n = 0
    horizon_n = 0
    exact_source_repeat = 0
    return_a_differs = 0
    extra_evens = 0
    grew = 0
    declined = 0
    growth_growth = 0
    candidate_ce: dict[str, dict[str, Any] | None] = {
        name: None for name in INTEGER_CANDIDATES
    }
    candidate_fail_count = {name: 0 for name in INTEGER_CANDIDATES}
    scale_bins: dict[int, dict[str, Any]] = {}
    r_bins: dict[int, dict[str, Any]] = {}
    two_step_bins: dict[int, dict[str, Any]] = {}
    train = {
        "excursions": 0,
        "pairs": 0,
        "sup_c": 0.0,
        "sup_c2": 0.0,
        "sup_rho": 0.0,
        "sup_product": 0.0,
        "sup_u": 0.0,
        "sup_v_given_u_gt_1": 0.0,
    }
    hold = {
        "excursions": 0,
        "pairs": 0,
        "broke_c": None,
        "broke_c2": None,
        "broke_rho": None,
        "broke_product": None,
        "broke_v_given_u": None,
    }
    extremal_c: list[dict[str, Any]] = []
    extremal_c2: list[dict[str, Any]] = []
    extremal_rho: list[dict[str, Any]] = []
    extremal_eta: list[dict[str, Any]] = []
    near_cycles: list[dict[str, Any]] = []
    max_r = 0

    def consume(n: int, chain: dict[str, Any], *, scored: bool) -> None:
        nonlocal starts, excursions, pairs, bit_cap_n, horizon_n
        nonlocal return_a_differs, extra_evens, grew, declined
        nonlocal growth_growth, exact_source_repeat, max_r
        starts += 1
        if chain["status"] == "BIT_CAP":
            bit_cap_n += 1
        elif chain["status"] == "HORIZON":
            horizon_n += 1
        rows = chain["rows"]
        train_n = n <= hold_split
        seen_L: set[int] = set()
        for idx, row in enumerate(rows):
            L0 = int(row["L"])
            H = int(row["H"])
            L1 = int(row["L_next"])
            r0 = int(row["r"])
            L_a = int(row["L_a"])
            even = int(row["even"])
            if L0 in seen_L:
                exact_source_repeat += 1
                if len(near_cycles) < KEEP_EXTREMAL:
                    near_cycles.append(
                        {"n": n, "L": L0, "kind": "exact_source_repeat"}
                    )
            seen_L.add(L0)
            if L1 == L0 and L1 >= n:
                exact_source_repeat += 1
                if len(near_cycles) < KEEP_EXTREMAL:
                    near_cycles.append({"n": n, "L": L0, "kind": "L_next_eq_L"})
            if L_a != L1:
                return_a_differs += 1
            if even != H and L_a != L1:
                extra_evens += 1
            max_r = max(max_r, r0)
            rho = L1 / L0 if L0 else 0.0
            eta = H / L0 if L0 else 0.0
            c_val = _log_ratio(L1, L0)
            a_val = _log_ratio(H, L0)
            witness = {
                "n": n,
                "L": L0,
                "H": H,
                "L_next": L1,
                "r": r0,
                "rho": rho,
                "c": c_val,
                "eta": eta,
            }
            excursions += 1
            if row["grew"]:
                grew += 1
            if row["declined"]:
                declined += 1
            scale_key = int(math.log10(L0)) if L0 >= 10 else 0
            r_bin = r_bins.setdefault(r0, _empty_bin())
            s_bin = scale_bins.setdefault(scale_key, _empty_bin())
            stats = {
                "rho": rho,
                "c": c_val,
                "eta": eta,
                "grew": bool(row["grew"]),
                "declined": bool(row["declined"]),
                "witness": witness,
            }
            _update_bin(r_bin, stats)
            _update_bin(s_bin, stats)
            if c_val is not None:
                _keep_max(
                    extremal_c,
                    {**witness, "score": c_val},
                    "score",
                    KEEP_EXTREMAL,
                )
            _keep_max(
                extremal_rho, {**witness, "score": rho}, "score", KEEP_EXTREMAL
            )
            _keep_max(
                extremal_eta, {**witness, "score": eta}, "score", KEEP_EXTREMAL
            )
            L2 = int(rows[idx + 1]["L_next"]) if idx + 1 < len(rows) else None
            r1 = int(rows[idx + 1]["r"]) if idx + 1 < len(rows) else None
            hits = _candidate_hits(L0, H, L1, L2, r0, r1)
            if scored:
                for name, failed in hits.items():
                    if failed:
                        candidate_fail_count[name] += 1
                        if candidate_ce[name] is None:
                            candidate_ce[name] = {
                                "n": n,
                                "L0": L0,
                                "H": H,
                                "L1": L1,
                                "L2": L2,
                                "r0": r0,
                                "r1": r1,
                            }
            if L2 is None:
                if scored:
                    if train_n:
                        train["excursions"] += 1
                        if c_val is not None and c_val > train["sup_c"]:
                            train["sup_c"] = c_val
                        if rho > train["sup_rho"]:
                            train["sup_rho"] = rho
                    else:
                        hold["excursions"] += 1
                        if c_val is not None and c_val > train["sup_c"] + 1e-12:
                            if hold["broke_c"] is None:
                                hold["broke_c"] = witness
                        if rho > train["sup_rho"] + 1e-12 and hold["broke_rho"] is None:
                            hold["broke_rho"] = witness
                continue
            pairs += 1
            c2 = _log_ratio(L2, L0)
            u_val = _log_ratio(L1, L0)
            v_val = _log_ratio(L2, L1)
            product = (L1 / L0) * (L2 / L1) if L1 else 0.0
            two = {
                "n": n,
                "L0": L0,
                "L1": L1,
                "L2": L2,
                "H": H,
                "r0": r0,
                "r1": r1,
                "c2": c2,
                "u": u_val,
                "v": v_val,
                "product": product,
            }
            if L1 > L0 and L2 > L1:
                growth_growth += 1
            if c2 is not None:
                _keep_max(
                    extremal_c2, {**two, "score": c2}, "score", KEEP_EXTREMAL
                )
            t_bin = two_step_bins.setdefault(scale_key, _empty_bin())
            t_stats = {
                "rho": product,
                "c": c2,
                "eta": eta,
                "grew": L2 > L0,
                "declined": L2 < L0,
                "witness": two,
            }
            _update_bin(t_bin, t_stats)
            if not scored:
                continue
            if train_n:
                train["excursions"] += 1
                train["pairs"] += 1
                if c_val is not None and c_val > train["sup_c"]:
                    train["sup_c"] = c_val
                if c2 is not None and c2 > train["sup_c2"]:
                    train["sup_c2"] = c2
                if rho > train["sup_rho"]:
                    train["sup_rho"] = rho
                if product > train["sup_product"]:
                    train["sup_product"] = product
                if u_val is not None and u_val > train["sup_u"]:
                    train["sup_u"] = u_val
                if (
                    u_val is not None
                    and v_val is not None
                    and u_val > 1
                    and v_val > train["sup_v_given_u_gt_1"]
                ):
                    train["sup_v_given_u_gt_1"] = v_val
            else:
                hold["excursions"] += 1
                hold["pairs"] += 1
                if c_val is not None and c_val > train["sup_c"] + 1e-12:
                    if hold["broke_c"] is None:
                        hold["broke_c"] = witness
                if c2 is not None and c2 > train["sup_c2"] + 1e-12:
                    if hold["broke_c2"] is None:
                        hold["broke_c2"] = two
                if rho > train["sup_rho"] + 1e-12 and hold["broke_rho"] is None:
                    hold["broke_rho"] = witness
                if (
                    product > train["sup_product"] + 1e-12
                    and hold["broke_product"] is None
                ):
                    hold["broke_product"] = two
                if (
                    u_val is not None
                    and v_val is not None
                    and u_val > 1
                    and v_val > train["sup_v_given_u_gt_1"] + 1e-12
                    and hold["broke_v_given_u"] is None
                ):
                    hold["broke_v_given_u"] = two

    for n in range(3, n_max + 1, 2):
        consume(
            n,
            excursion_chain(n, step_cap=step_cap, bit_cap=bit_cap),
            scored=True,
        )
    lab_detail = []
    for n in HARD_LABS:
        kwargs = {"step_cap": LAB_STEP_CAP, "bit_cap": LAB_BIT_CAP}
        chain = excursion_chain(n, **kwargs)
        if n > n_max:
            consume(n, chain, scored=False)
        xs = sources_of(n, **kwargs)
        triples = []
        for row in chain["rows"]:
            triples.append(
                {
                    "L": row["L"],
                    "H": row["H"],
                    "L_next": row["L_next"],
                    "L_a": row["L_a"],
                    "r": row["r"],
                    "grew": row["grew"],
                }
            )
        lab_detail.append(
            {
                "n": n,
                "status": chain["status"],
                "sources": xs,
                "excursions": triples,
            }
        )

    r_compare = []
    envelope_dominated = True
    for r, bin_row in sorted(r_bins.items()):
        predicted = formal_c(int(r))
        actual = bin_row["sup_c"]
        slack = predicted - actual
        if actual > predicted + 1e-6:
            envelope_dominated = False
        r_compare.append(
            {
                "r": r,
                "count": bin_row["count"],
                "sup_c": actual,
                "formal_c": predicted,
                "slack": slack,
                "sup_rho": bin_row["sup_rho"],
                "witness": bin_row["witness_sup_c"],
            }
        )

    scale_out = []
    for key, bin_row in sorted(scale_bins.items()):
        scale_out.append(
            {
                "log10_L": key,
                "count": bin_row["count"],
                "sup_rho": bin_row["sup_rho"],
                "inf_rho": _finite_inf(bin_row["inf_rho"]),
                "sup_c": bin_row["sup_c"],
                "sup_eta": bin_row["sup_eta"],
                "grew": bin_row["grew"],
                "declined": bin_row["declined"],
                "witness": bin_row["witness_sup_c"],
            }
        )
    two_out = []
    for key, bin_row in sorted(two_step_bins.items()):
        two_out.append(
            {
                "log10_L": key,
                "count": bin_row["count"],
                "sup_product": bin_row["sup_rho"],
                "sup_c2": bin_row["sup_c"],
                "grew": bin_row["grew"],
                "declined": bin_row["declined"],
                "witness": bin_row["witness_sup_c"],
            }
        )

    holdout_stable = all(
        hold[name] is None
        for name in (
            "broke_c",
            "broke_c2",
            "broke_rho",
            "broke_product",
            "broke_v_given_u",
        )
    )
    all_integer_fail = all(
        candidate_ce[name] is not None for name in INTEGER_CANDIDATES
    )
    xs37 = next(lab["sources"] for lab in lab_detail if lab["n"] == 37)
    xs365 = next(lab["sources"] for lab in lab_detail if lab["n"] == 365)
    return_b_is_q = xs37[:3] == list(SOURCES_37)
    two_step_37_grows = 2233 > 37
    climb_365 = xs365[:5] == list(CLIMB_365)
    first_37 = next(lab["excursions"] for lab in lab_detail if lab["n"] == 37)
    a_b_agree_37_first = bool(first_37) and int(first_37[0]["L_a"]) == int(
        first_37[0]["L_next"]
    )
    a_b_differ_later_37 = any(
        int(row["L_a"]) != int(row["L_next"]) for row in first_37[1:]
    )

    return {
        "n_max": n_max,
        "hold_split": hold_split,
        "step_cap": step_cap,
        "bit_cap": bit_cap,
        "starts": starts,
        "excursions": excursions,
        "pairs": pairs,
        "bit_cap_n": bit_cap_n,
        "horizon_n": horizon_n,
        "grew": grew,
        "declined": declined,
        "growth_growth": growth_growth,
        "max_r": max_r,
        "return_a_differs": return_a_differs,
        "extra_evens": extra_evens,
        "exact_source_repeat": exact_source_repeat,
        "return_b_is_q_on_37": return_b_is_q,
        "return_a_b_agree_37_first": a_b_agree_37_first,
        "return_a_b_differ_later_37": a_b_differ_later_37,
        "two_step_37_grows": two_step_37_grows,
        "climb_365": climb_365,
        "sources_37": xs37[:6],
        "sources_365": xs365[:6],
        "train": train,
        "hold": hold,
        "holdout_stable": holdout_stable,
        "envelope_dominated": envelope_dominated,
        "all_integer_candidates_fail": all_integer_fail,
        "candidate_ce": candidate_ce,
        "candidate_fail_count": candidate_fail_count,
        "r_compare": r_compare,
        "scale_bins": scale_out,
        "two_step_bins": two_out,
        "extremal_c": extremal_c,
        "extremal_c2": extremal_c2,
        "extremal_rho": extremal_rho,
        "extremal_eta": extremal_eta,
        "near_cycles": near_cycles,
        "labs": lab_detail,
        "git": git_commit(),
        "letter_chain": False,
        "itinerary_language_reopen": False,
        "macro_event_reopen": False,
        "source_descent_reopen": False,
        "halt_theorem": False,
        "excursion_transfer_lean": False,
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
        "no_atlas_lang": "LANG_EXCURSION" not in combined,
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
        or scan["macro_event_reopen"]
        or scan["source_descent_reopen"]
        or scan["halt_theorem"]
        or scan["excursion_transfer_lean"]
        or not scan["return_b_is_q_on_37"]
        or not scan["two_step_37_grows"]
        or not scan["climb_365"]
    ):
        return {
            "classification": CLASS_INCOMPLETE,
            "reason": "out-of-scope claim or lab chain mismatch",
        }

    integer_all_fail = scan["all_integer_candidates_fail"]
    growth_free = scan["growth_growth"] > 0
    envelope = scan["envelope_dominated"]
    no_cycle = scan["exact_source_repeat"] == 0
    if (
        integer_all_fail
        and growth_free
        and envelope
        and no_cycle
        and not scan["source_descent_reopen"]
    ):
        return {
            "classification": CLASS_CLOSED,
            "reason": (
                "Return B is the Q-source chain; every tested one-step, "
                "two-step, compensation, and weighted inequality has a "
                "counterexample; growth can follow growth; r-bin envelopes "
                "stay under the formal 3^r/2^{r+1} scale; no exact source "
                "recurrence"
            ),
        }
    if integer_all_fail and growth_free and no_cycle:
        return {
            "classification": CLASS_PARK,
            "reason": (
                "no hold-out-stable exact inequality survived, but the "
                "r-bin envelope is not a clean formal-scale match"
            ),
        }
    return {
        "classification": CLASS_GREEN,
        "reason": (
            "a transfer inequality or recurrence survived the laboratories "
            "and the integer candidate battery"
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
            "global_non_realizability": False,
            "A_w_empty_from_window": False,
            "density_theorem": False,
            "two_episode_descent_theorem": False,
            "compensation_theorem": False,
            "excursion_transfer_lean": False,
            "itinerary_language_reopen": False,
            "macro_event_reopen": False,
            "source_descent_reopen": False,
            "search_horizon_is_L": False,
        }
    )
    return {
        "experiment": "juggler_excursion_transfer",
        "engine_control_layer_modified": False,
        "anti_overclaim": anti,
        "scan": scan,
        "lean": lean,
        "decision": decision,
        "search_method": (
            "streamed Return-B record excursions on odd starts; "
            f"n<={n_max}, hold-out {scan['hold_split']}; labs {list(HARD_LABS)}"
        ),
    }


def render_markdown(payload: dict[str, Any]) -> str:
    decision = payload["decision"]
    scan = payload["scan"]
    lean = payload["lean"]
    lines = [
        "# Juggler long-excursion transfer",
        "",
        f"Status: **{decision['classification']}**",
        "",
        "Numerical (L, H, L') transfer of complete record excursions.",
        "Not a halt theorem. Absence is NOT_OBSERVED_WITHIN_BOUND.",
        "",
        "## Branch budget",
        "",
        "```text",
        "Mathematical target     hold-out-stable transfer / compensation law",
        "Novelty hypothesis      the peak H constrains the next source",
        "Maximum Phase-0 scope   streamed (L,H,L',r); hold-out by start n",
        "```",
        "",
        "## Metadata",
        "",
        f"- classification: **{decision['classification']}**",
        f"- n_max: `{scan['n_max']}` hold_split: `{scan['hold_split']}`",
        f"- starts: `{scan['starts']}` excursions: `{scan['excursions']}` "
        f"pairs: `{scan['pairs']}`",
        f"- bit_cap starts: `{scan['bit_cap_n']}` horizon: `{scan['horizon_n']}`",
        f"- grew / declined / growth-growth: `{scan['grew']}` / "
        f"`{scan['declined']}` / `{scan['growth_growth']}`",
        f"- max r: `{scan['max_r']}` Return A differs: `{scan['return_a_differs']}`",
        f"- exact source repeat: `{scan['exact_source_repeat']}`",
        f"- Return B is Q on 37: `{scan['return_b_is_q_on_37']}`",
        f"- envelope dominated: `{scan['envelope_dominated']}`",
        f"- hold-out stable: `{scan['holdout_stable']}`",
        f"- all integer candidates fail: `{scan['all_integer_candidates_fail']}`",
        "",
        decision["reason"] + ".",
        "",
        "## Laboratories",
        "",
        f"- 37 sources: `{scan['sources_37']}`",
        f"- 365 sources: `{scan['sources_365']}`",
        "",
    ]
    for lab in scan["labs"]:
        lines.append(
            f"- `{lab['n']}`: status=`{lab['status']}` "
            f"sources=`{lab['sources'][:8]}` "
            f"excursions=`{len(lab['excursions'])}`"
        )
    lines.extend(
        [
            "",
            "## r-bin versus formal scale",
            "",
        ]
    )
    for row in scan["r_compare"]:
        lines.append(
            f"- r=`{row['r']}` n=`{row['count']}` sup_c=`{row['sup_c']:.6f}` "
            f"formal=`{row['formal_c']:.6f}` slack=`{row['slack']:.6f}`"
        )
    lines.extend(
        [
            "",
            "## Scale bins",
            "",
        ]
    )
    for row in scan["scale_bins"]:
        lines.append(
            f"- 10^{row['log10_L']}: count=`{row['count']}` "
            f"sup_rho=`{row['sup_rho']:.6g}` sup_c=`{row['sup_c']:.6f}` "
            f"grew=`{row['grew']}`"
        )
    lines.extend(
        [
            "",
            "## Integer candidates (first counterexample)",
            "",
        ]
    )
    for name in INTEGER_CANDIDATES:
        ce = scan["candidate_ce"][name]
        count = scan["candidate_fail_count"][name]
        lines.append(f"- `{name}`: fails=`{count}` ce=`{ce}`")
    lines.extend(
        [
            "",
            "## Hold-out",
            "",
            f"- train: `{scan['train']}`",
            f"- hold breaks: `{ {k: v for k, v in scan['hold'].items() if k.startswith('broke')} }`",
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


def _write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    if not rows:
        path.write_text("", encoding="utf-8")
        return
    fieldnames: list[str] = []
    for row in rows:
        for key in row:
            if key not in fieldnames:
                fieldnames.append(key)
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames, extrasaction="ignore")
        writer.writeheader()
        for row in rows:
            flat = {}
            for key, value in row.items():
                if isinstance(value, (dict, list)):
                    flat[key] = json.dumps(value, separators=(",", ":"))
                else:
                    flat[key] = value
            writer.writerow(flat)


def write_data_artifacts(payload: dict[str, Any]) -> None:
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    scan = payload["scan"]
    extremals = []
    for kind, rows in (
        ("c", scan["extremal_c"]),
        ("c2", scan["extremal_c2"]),
        ("rho", scan["extremal_rho"]),
        ("eta", scan["extremal_eta"]),
    ):
        for row in rows:
            extremals.append({"kind": kind, **row})
    _write_csv(DATA_DIR / "extremal_rows.csv", extremals)
    _write_csv(DATA_DIR / "transfer_bins.csv", scan["scale_bins"])
    hard_rows = []
    for lab in scan["labs"]:
        for idx, row in enumerate(lab["excursions"]):
            hard_rows.append({"n": lab["n"], "i": idx, **row})
    _write_csv(DATA_DIR / "hard_trajectories.csv", hard_rows)
    _write_csv(DATA_DIR / "near_cycles.csv", scan["near_cycles"])
    candidates = {
        "classification": payload["decision"]["classification"],
        "reason": payload["decision"]["reason"],
        "holdout_stable": scan["holdout_stable"],
        "envelope_dominated": scan["envelope_dominated"],
        "all_integer_candidates_fail": scan["all_integer_candidates_fail"],
        "candidate_ce": scan["candidate_ce"],
        "candidate_fail_count": scan["candidate_fail_count"],
        "claim": CLAIM_NOT_OBSERVED,
    }
    (DATA_DIR / "candidate_relations.json").write_text(
        json.dumps(candidates, indent=2) + "\n", encoding="utf-8"
    )
    (DATA_DIR / "excursions.bin").write_bytes(
        json.dumps(
            {
                "note": "compact extremals only; full trajectories are not stored",
                "extremal_c": scan["extremal_c"][:8],
                "extremal_c2": scan["extremal_c2"][:8],
                "labs": [
                    {"n": lab["n"], "sources": lab["sources"][:8]}
                    for lab in scan["labs"]
                ],
            },
            separators=(",", ":"),
        ).encode("utf-8")
    )
    summary = {
        "classification": payload["decision"]["classification"],
        "reason": payload["decision"]["reason"],
        "n_max": scan["n_max"],
        "starts": scan["starts"],
        "excursions": scan["excursions"],
        "pairs": scan["pairs"],
        "growth_growth": scan["growth_growth"],
        "envelope_dominated": scan["envelope_dominated"],
        "holdout_stable": scan["holdout_stable"],
        "claim": CLAIM_NOT_OBSERVED,
        "git": scan["git"],
    }
    (DATA_DIR / "summary.json").write_text(
        json.dumps(summary, indent=2) + "\n", encoding="utf-8"
    )
    (DATA_DIR / "README.md").write_text(
        "# Juggler record-excursion transfer\n\n"
        "Bounded (L, H, L') census. Absence is NOT_OBSERVED_WITHIN_BOUND.\n\n"
        "Regenerate with `python -m research.juggler_sequence.excursion_transfer`.\n",
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
    print(
        f"starts={scan['starts']} excursions={scan['excursions']} "
        f"pairs={scan['pairs']} growth_growth={scan['growth_growth']}"
    )
    print(f"37 {scan['sources_37']}")
    print(f"365 {scan['sources_365']}")


if __name__ == "__main__":
    main()

"""Scale-induced near-tightness. Not a termination theorem.

Local remainders satisfy ``ρ < 2T+1``, so ``η = ρ/T^2`` decays with
``T``. For a fixed word, ``1+q`` is a weighted product of ``1+η``
factors. A large-``λ`` predecessor enters only by making the next
start large. This module does not claim an infinite expanding chain.
"""

from __future__ import annotations

from math import expm1, log
from typing import Any

from research.juggler_sequence.expansion_slack import NEAR_TIGHT
from research.juggler_sequence.global_defect import (
    follows_itinerary,
    image_after,
    odd_count,
)
from research.juggler_sequence.lean_paths import has_named, juggler_text
from research.juggler_sequence.normalized_defect import (
    bits_ok,
    eta_pair,
    odd_even_word,
    slack_den,
    slack_num,
)
from research.juggler_sequence.power_itineraries import floor_power
from research.juggler_sequence.progress_coverage import is_odd_odd
from research.juggler_sequence.residual_chain import residual_excursion
from research.juggler_sequence.two_block_residual import (
    classify_step,
    odd_odd_starts,
)

N_MAX = 2000

LEAN_THEOREMS = (
    "even_remainder_bound",
    "odd_remainder_bound",
    "normalized_remainder_upper",
    "one_plus_eta_lt_succ_sq",
    "local_eta_scale",
    "even_eta_le_two_over_T",
    "odd_eta_le_two_over_T",
    "ooe_eta_product",
    "ooe_one_plus_slack_lt_succ_ratio",
    "block_growth_from_q",
    "large_lambda_successor_q_bound",
)

OOE_PRED_START = 329
OOE_EXPONENT = 9 / 8


def q_exact(n: int, word: str) -> float:
    num, den = slack_num(n, word), slack_den(n, word)
    return (num - den) / den


def q_log(n: int, word: str) -> float:
    end = image_after(n, word)
    log1p = (3 ** odd_count(word)) * log(n) - (2 ** len(word)) * log(end)
    return expm1(log1p)


def eta_bound(t: int) -> float | None:
    if t <= 0:
        return None
    return 2 / t + 1 / (t * t)


def etas_along(n: int, word: str) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    current = n
    for letter in word:
        rho, t2 = eta_pair(current)
        t = floor_power(current)
        eta = (rho / t2) if t2 else None
        weight = 3 if letter == "O" else 1
        rows.append(
            {
                "x": current,
                "letter": letter,
                "T": t,
                "rho": rho,
                "eta": eta,
                "eta_bound": eta_bound(t),
                "weight_letter": weight,
            }
        )
        current = floor_power(current)
    return rows


def ooe_weighted_etas(n: int) -> tuple[float, float, float] | None:
    path = etas_along(n, "OOE")
    if any(row["eta"] is None for row in path):
        return None
    return (3 * path[0]["eta"], 2 * path[1]["eta"], 4 * path[2]["eta"])


def ooe_scale_census(*, n_max: int = N_MAX) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    last_even_dom = 0
    for n in range(3, n_max + 1, 2):
        if not is_odd_odd(n) or not follows_itinerary(n, "OOE"):
            continue
        if not bits_ok(n, 9) or not bits_ok(image_after(n, "OOE"), 8):
            continue
        q = q_exact(n, "OOE")
        if q < 0:
            continue
        weights = ooe_weighted_etas(n)
        if weights is None:
            continue
        w0, w1, w2 = weights
        if w2 >= w0 and w2 >= w1:
            last_even_dom += 1
        rows.append(
            {
                "n": n,
                "q": q,
                "q_over_scale": q / (n ** (-OOE_EXPONENT)),
                "w0": w0,
                "w1": w1,
                "w2": w2,
            }
        )
    large = [row for row in rows if row["n"] >= 200 and row["q"] > 0]
    ratios = [row["q_over_scale"] for row in large]
    return {
        "n_max": n_max,
        "checked": len(rows),
        "last_even_dominant": last_even_dom,
        "last_even_frac": (last_even_dom / len(rows)) if rows else None,
        "median_q_over_scale": (
            sorted(ratios)[len(ratios) // 2] if ratios else None
        ),
        "min_q_over_scale": min(ratios) if ratios else None,
        "max_q_over_scale": max(ratios) if ratios else None,
    }


def near_tight_prediction() -> dict[str, Any]:
    raw = residual_excursion(OOE_PRED_START)
    assert raw is not None
    first = classify_step(OOE_PRED_START, raw)
    y = first["y"]
    q = q_exact(y, "OOE")
    scale = y ** (-OOE_EXPONENT)
    weights = ooe_weighted_etas(y)
    return {
        "x": OOE_PRED_START,
        "u": first["word"],
        "lam_u": (3 ** first["a"]) / (2 ** (first["a"] + first["b"])),
        "y": y,
        "v": "OOE",
        "q": q,
        "y_scale": scale,
        "q_over_scale": q / scale,
        "weights": weights,
        "exact_positive": exact_q_positive(y, "OOE"),
        "mixed": True,
    }


def exact_q_positive(n: int, word: str) -> bool:
    return slack_num(n, word) > slack_den(n, word)


def pe_pair_census(*, n_max: int = N_MAX) -> dict[str, Any]:
    pairs: list[dict[str, Any]] = []
    for n in odd_odd_starts(n_max):
        raw = residual_excursion(n)
        if raw is None:
            continue
        first = classify_step(n, raw)
        if not (first["persistent"] and first["expanding"]):
            continue
        y = first["y"]
        raw2 = residual_excursion(y)
        if raw2 is None:
            continue
        second = classify_step(y, raw2)
        if not second["expanding"]:
            continue
        word = odd_even_word(second["a"], second["b"])
        if not follows_itinerary(y, word):
            continue
        q2 = q_log(y, word)
        if q2 <= 0:
            continue
        lam = (3 ** first["a"]) / (2 ** (first["a"] + first["b"]))
        pairs.append(
            {
                "x": n,
                "y": y,
                "u": first["word"],
                "v": word,
                "lam": lam,
                "q2": q2,
            }
        )
    ooe = [row for row in pairs if row["v"] == "OOE"]
    ooe_ratios = [row["q2"] / (row["y"] ** (-OOE_EXPONENT)) for row in ooe]
    large = [row for row in pairs if row["y"] > 10**6]
    return {
        "pairs": len(pairs),
        "ooe_sequels": len(ooe),
        "ooe_q_over_y_scale_min": min(ooe_ratios) if ooe_ratios else None,
        "ooe_q_over_y_scale_max": max(ooe_ratios) if ooe_ratios else None,
        "large_y_pairs": len(large),
        "large_y_max_q2": max((row["q2"] for row in large), default=None),
        "largest_lam_ooe": max(ooe, key=lambda row: row["lam"]) if ooe else None,
    }


def eta_window(*, n_max: int = N_MAX) -> dict[str, Any]:
    fail = 0
    checked = 0
    max_eta = None
    zeros = 0
    for n in range(1, n_max + 1):
        rho, t2 = eta_pair(n)
        t = floor_power(n)
        if t == 0:
            continue
        checked += 1
        eta = rho / t2
        bound = eta_bound(t)
        if bound is not None and eta >= bound:
            fail += 1
        if eta == 0:
            zeros += 1
        if max_eta is None or eta > max_eta:
            max_eta = eta
    return {
        "checked": checked,
        "bound_fail": fail,
        "tight": zeros,
        "max_eta": max_eta,
    }


def lean_api_present() -> dict[str, bool]:
    text = juggler_text()
    return {
        "sorry_free": "sorry" not in text and "admit" not in text,
        **{name: has_named(text, name) for name in LEAN_THEOREMS},
    }

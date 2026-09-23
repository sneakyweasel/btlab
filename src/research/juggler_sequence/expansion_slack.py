"""Weighted slack budget on residual chains. Not a termination theorem.

Records the log-free block multiplier ``λ = 3^a / 2^{a+b}`` and the
logarithmic slack tax ``c = λ log x - log y`` along persistent residual
chains. The exact identities are a change of coordinates for ``1+q``.
The census asks whether the weighted budget constrains expanding-block
runs independently of the endpoint comparison.
"""

from __future__ import annotations

from collections import Counter
from math import log
from typing import Any

from research.juggler_sequence.lean_registry import has_named, juggler_text
from research.juggler_sequence.progress_coverage import is_odd_odd
from research.juggler_sequence.residual_chain import residual_excursion
from research.juggler_sequence.two_block_residual import (
    classify_step,
    odd_odd_starts,
)

N_MAX = 4000
CHAIN_CAP = 24

LEAN_THEOREMS = (
    "blockMultiplier",
    "expansionMargin",
    "blockLogSlack",
    "blockSlackTax",
    "weightedSlack",
    "normalizedSlackBudget",
    "blockMultiplier_mul",
    "block_power_identity",
    "block_log_growth",
    "weighted_slack_concat",
    "weighted_slack_cocycle",
    "normalized_budget_identity",
    "block_growth_compat",
    "four_block_pe_1999",
    "four_consecutive_persistent_expanding_exists",
)

FOUR_BLOCK = {
    "x": 1999,
    "words": ("OOE", "OOOOEE", "OOE", "OOE"),
    "xs": (1999, 5169, 50093, 193753, 887471),
}

FIVE_BLOCK = {
    "x": 2183,
    "words": ("OOE", "OOOOE", "OOOOOOOOE", "OOOE", "OOOOOOOE"),
}

NEAR_TIGHT = {
    "x": 180370579261640036336071806107777,
    "word": "OOE",
    "y": 1941719144218166368455510841464890645,
}


def block_lambda(a: int, b: int) -> float:
    return (3**a) / (2 ** (a + b))


def block_log_slack(x: int, y: int, a: int, b: int) -> float:
    """``c = λ log x - log y``. Numerically ``log T = λ log n - c``."""
    return block_lambda(a, b) * log(x) - log(y)


def exact_slack_positive(x: int, y: int, a: int, b: int) -> bool:
    """``x^{3^a} > y^{2^{a+b}}``, i.e. ``q > 0``, without logs."""
    return x ** (3**a) > y ** (2 ** (a + b))


def classify_budget_step(x: int, step: dict[str, Any]) -> dict[str, Any]:
    row = classify_step(x, step)
    a, b, y = row["a"], row["b"], row["y"]
    lam = block_lambda(a, b)
    c = block_log_slack(x, y, a, b)
    mu = lam - 1.0
    row["lam"] = lam
    row["c"] = c
    row["mu"] = mu
    row["c_over_mu"] = (c / mu) if mu > 0 else None
    row["c_over_logx"] = c / log(x) if x > 1 else None
    return row


def walk_pe_run(x: int, *, cap: int = CHAIN_CAP) -> list[dict[str, Any]]:
    run: list[dict[str, Any]] = []
    current = x
    seen: set[int] = set()
    for _ in range(cap):
        if current in seen or current <= 1:
            break
        seen.add(current)
        raw = residual_excursion(current)
        if raw is None:
            break
        row = classify_budget_step(current, raw)
        if not (row["persistent"] and row["expanding"]):
            break
        run.append(row)
        current = row["y"]
    return run


def accumulate_budget(run: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """Exact affine cocycle in logs: ``Λ``, ``C``, ``B = C/Λ``."""
    lam_prod = 1.0
    weighted = 0.0
    y0 = log(run[0]["x"]) if run else None
    rows: list[dict[str, Any]] = []
    for index, block in enumerate(run):
        weighted = weighted * block["lam"] + block["c"]
        lam_prod *= block["lam"]
        budget = weighted / lam_prod
        predicted = lam_prod * (y0 - budget)
        actual = log(block["y"])
        taut = y0 * (1.0 - 1.0 / lam_prod) if y0 is not None else None
        rows.append(
            {
                "i": index,
                "word": block["word"],
                "x": block["x"],
                "y": block["y"],
                "lam": block["lam"],
                "c": block["c"],
                "c_over_mu": block["c_over_mu"],
                "Lambda": lam_prod,
                "C": weighted,
                "B": budget,
                "pred": predicted,
                "actual": actual,
                "err": abs(predicted - actual),
                "taut_B": taut,
                "B_over_taut": (budget / taut) if taut else None,
                "B_over_y0": (budget / y0) if y0 else None,
            }
        )
    return rows


def identity_holds(x: int, a: int, b: int, y: int, *, tol: float = 1e-12) -> bool:
    """Check ``log y = λ log x - c`` to float tolerance."""
    return abs(log(y) - (block_lambda(a, b) * log(x) - block_log_slack(x, y, a, b))) <= tol


def expansion_slack_census(
    *, n_max: int = N_MAX, chain_cap: int = CHAIN_CAP
) -> dict[str, Any]:
    starts = odd_odd_starts(n_max)
    seen: set[int] = set()
    queue = list(starts)
    extra_landings = 0
    run_len_hist: Counter[int] = Counter()
    word_counts: Counter[str] = Counter()
    pe_runs = 0
    pe_blocks = 0
    max_run = 0
    max_run_start = None
    min_c_over_mu = None
    min_c_over_mu_row = None
    min_B_over_taut = None
    min_B_over_taut_row = None
    max_identity_err = 0.0
    long_runs: list[dict[str, Any]] = []
    c_over_mu_by_scale = {"small": [], "mid": [], "big": []}

    while queue:
        x = queue.pop()
        if x in seen or x <= 1:
            continue
        seen.add(x)
        run = walk_pe_run(x, cap=chain_cap)
        if not run:
            continue
        pe_runs += 1
        run_len_hist[len(run)] += 1
        acc = accumulate_budget(run)
        last = acc[-1]
        if last["err"] > max_identity_err:
            max_identity_err = last["err"]
        if last["B_over_taut"] is not None and (
            min_B_over_taut is None or last["B_over_taut"] < min_B_over_taut
        ):
            min_B_over_taut = last["B_over_taut"]
            min_B_over_taut_row = {
                "x": run[0]["x"],
                "len": len(run),
                "B": last["B"],
                "taut": last["taut_B"],
                "ratio": last["B_over_taut"],
                "words": [block["word"] for block in run],
            }
        if len(run) > max_run:
            max_run = len(run)
            max_run_start = run[0]["x"]
        if len(run) >= 3:
            long_runs.append(
                {
                    "x": run[0]["x"],
                    "len": len(run),
                    "words": [block["word"] for block in run],
                    "B": last["B"],
                    "B_over_taut": last["B_over_taut"],
                    "Lambda": last["Lambda"],
                }
            )
        for block in run:
            pe_blocks += 1
            word_counts[block["word"]] += 1
            ratio = block["c_over_mu"]
            if ratio is not None and (
                min_c_over_mu is None or ratio < min_c_over_mu
            ):
                min_c_over_mu = ratio
                min_c_over_mu_row = {
                    "x": block["x"],
                    "y": block["y"],
                    "word": block["word"],
                    "lam": block["lam"],
                    "c": block["c"],
                    "c_over_mu": ratio,
                }
            if ratio is not None:
                if block["x"] < 1000:
                    c_over_mu_by_scale["small"].append(ratio)
                elif block["x"] < 10000:
                    c_over_mu_by_scale["mid"].append(ratio)
                else:
                    c_over_mu_by_scale["big"].append(ratio)
        landing = run[-1]["y"]
        if landing not in seen and landing >= 3 and is_odd_odd(landing):
            if landing > n_max:
                extra_landings += 1
            queue.append(landing)

    long_runs.sort(key=lambda row: (-row["len"], row["x"]))
    scale_mins = {
        name: (min(vals) if vals else None)
        for name, vals in c_over_mu_by_scale.items()
    }
    return {
        "n_max": n_max,
        "visited": len(seen),
        "extra_landings": extra_landings,
        "pe_runs": pe_runs,
        "pe_blocks": pe_blocks,
        "run_len_hist": dict(sorted(run_len_hist.items())),
        "word_counts": dict(word_counts.most_common(12)),
        "max_run": max_run,
        "max_run_start": max_run_start,
        "n_runs_ge4": sum(1 for row in long_runs if row["len"] >= 4),
        "n_runs_ge5": sum(1 for row in long_runs if row["len"] >= 5),
        "min_c_over_mu": min_c_over_mu,
        "min_c_over_mu_row": min_c_over_mu_row,
        "min_B_over_taut": min_B_over_taut,
        "min_B_over_taut_row": min_B_over_taut_row,
        "max_identity_err": max_identity_err,
        "scale_min_c_over_mu": scale_mins,
        "long_runs": long_runs[:8],
    }


def lean_api_present() -> dict[str, bool]:
    text = juggler_text()
    return {
        "sorry_free": "sorry" not in text and "admit" not in text,
        **{name: has_named(text, name) for name in LEAN_THEOREMS},
    }

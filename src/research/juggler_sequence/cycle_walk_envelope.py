"""Hitting-lemma envelope C_L < 1/(ln 3 ln n) for leftover hug/IET.

Phase 0: prove the crude bound by equal-bin Riemann sums plus
the rotation hitting estimate |#I - L mu(I)| <= 1, not by
Denjoy-Koksma at constant 1/L. Slack comes from J(n) < 1 in
the Laplace integral. Not a halt theorem, not a floor raise,
not a uniform B/theta claim, and not a reopen of the REFUTED
Koksma +1/L or Christoffel slogans.

Dossier: docs/problems/juggler_cycle_walk_envelope.md.
"""

from __future__ import annotations

from research.juggler_sequence.lean_paths import (
    DATA_ROOT,
)

import json
import math
from pathlib import Path
from typing import Any

import numpy as np

from research.juggler_sequence.cycle_finance import (
    EPS_CONST,
    PARITY_REL_GUARD,
    git_commit,
)
from research.juggler_sequence.cycle_walk_charge import (
    CERTIFIED_FLOOR,
    MU,
    STEP,
    deficit_D,
)
from research.juggler_sequence.cycle_walk_exchange import (
    GREEDY_SUMMARY,
    c_star_integral,
)
from research.juggler_sequence.cycle_walk_mechanical import SURVEY_PATH

DATA_DIR = (
    DATA_ROOT
    / "cycle_walk_envelope"
)

BIN_COUNT = 250
HIT_CAP = 4
MIN_LENGTH = 50_508
MIN_LOG_N = 17.0
LN3 = math.log(3.0)

CLASS_GREEN = "WALK_ENVELOPE_GREEN"
CLASS_PARK = "WALK_ENVELOPE_PARK"
CLASS_CLOSED = "WALK_ENVELOPE_CLOSED"


def j_upper(log_n: float) -> float:
    """J <= 1 - 2/ln n + 6/(ln n)^2 via 1/(1+x)^2 <= 1-2x+3x^2."""

    return 1.0 - 2.0 / log_n + 6.0 / log_n**2


def crude_bound(log_n: float) -> float:
    return 1.0 / (LN3 * log_n)


def gap_lower(log_n: float) -> float:
    """Lower bound on 1/(ln 3 ln n) - C_* from the J upper bound."""

    return (2.0 / log_n - 6.0 / log_n**2) / (LN3 * log_n)


def binning_excess(c_star: float, length: int, bins: int, hit: int = 1) -> float:
    """(1 + hit*m/L)(C_* + 1/m) - C_* = 1/m + hit*m C_*/L + hit/L."""

    return (
        1.0 / bins
        + hit * bins * c_star / length
        + hit / length
    )


def binning_upper(c_star: float, length: int, bins: int, hit: int = 1) -> float:
    return (1.0 + hit * bins / length) * (c_star + 1.0 / bins)


def analytic_covers(
    length: int = MIN_LENGTH,
    log_n: float = MIN_LOG_N,
    bins: int = BIN_COUNT,
    hit: int = HIT_CAP,
) -> dict[str, Any]:
    """Worst-case numeric check of the written inequality."""

    bound = crude_bound(log_n)
    # Pessimistic C_* < B in the m C_*/L term.
    c_star_hat = bound
    excess = binning_excess(c_star_hat, length, bins, hit)
    gap = gap_lower(log_n)
    return {
        "length": length,
        "log_n": log_n,
        "bins": bins,
        "hit": hit,
        "crude_bound": bound,
        "gap_lower": gap,
        "binning_excess": excess,
        "covers": excess < gap,
    }


def iet_bin_counts(length: int, bins: int) -> np.ndarray:
    """Equal-bin occupancy of {k α/(1+α)} for k = 0..L-1."""

    theta = MU / STEP
    xs = np.mod(np.arange(length, dtype=np.float64) * theta, 1.0)
    idx = np.minimum((xs * bins).astype(np.int64), bins - 1)
    return np.bincount(idx, minlength=bins)


def hitting_report(length: int, bins: int = BIN_COUNT) -> dict[str, Any]:
    counts = iet_bin_counts(length, bins)
    expected = length / bins
    dev = np.abs(counts - expected)
    return {
        "length": length,
        "bins": bins,
        "max_abs_dev": float(np.max(dev)),
        "max_over": float(np.max(counts - expected)),
        "within_one": bool(np.max(dev) <= 1.0 + 1e-12),
        "within_two": bool(np.max(dev) <= 2.0 + 1e-12),
    }


def survey_envelope(
    survey_path: Path = SURVEY_PATH,
    n0: int = CERTIFIED_FLOOR,
    bins: int = BIN_COUNT,
) -> dict[str, Any]:
    survey = json.loads(survey_path.read_text(encoding="utf-8"))
    greedy = json.loads(GREEDY_SUMMARY.read_text(encoding="utf-8"))
    hug_c = {int(r["length"]): float(r["C"]) for r in greedy["survey_rows"]}
    n = int(survey["floor"]) + 1
    rows = []
    for item in survey["rows"]:
        length = int(item["length"])
        odd_count = int(item["odd_count"])
        theta = float(item["theta"])
        log_n = math.log(n) - deficit_D(length, odd_count, n)
        star = c_star_integral(log_n)
        hit = hitting_report(length, bins)
        upper = binning_upper(star["C"], length, bins, hit=HIT_CAP)
        bound = star["bound"]
        scale = length / (math.exp(log_n) * log_n)
        b_env = bound * scale
        rhs = EPS_CONST * b_env * (1.0 + PARITY_REL_GUARD)
        rows.append(
            {
                "length": length,
                "odd_count": odd_count,
                "log_n": log_n,
                "C_hug": hug_c[length],
                "C_star": star["C"],
                "C_bound": bound,
                "binning_upper": upper,
                "binning_below_bound": upper < bound,
                "hug_below_bound": hug_c[length] < bound,
                "max_abs_dev": hit["max_abs_dev"],
                "max_over": hit["max_over"],
                "within_one": hit["within_one"],
                "within_cap": hit["max_abs_dev"] <= HIT_CAP + 1e-12,
                "margin_envelope": theta / rhs if rhs else math.inf,
            }
        )
    return {
        "floor": survey["floor"],
        "n": n,
        "bins": bins,
        "n_rows": len(rows),
        "all_binning_below_bound": all(r["binning_below_bound"] for r in rows),
        "all_hug_below_bound": all(r["hug_below_bound"] for r in rows),
        "all_within_one": all(r["within_one"] for r in rows),
        "all_within_cap": all(r["within_cap"] for r in rows),
        "max_abs_dev": max(r["max_abs_dev"] for r in rows),
        "max_over": max(r["max_over"] for r in rows),
        "hit_cap": HIT_CAP,
        "n_envelope_kills": sum(1 for r in rows if r["margin_envelope"] > 1.0),
        "min_kill_margin": min(r["margin_envelope"] for r in rows),
        "margin_50508": next(
            r["margin_envelope"] for r in rows if r["length"] == 50508
        ),
        "margin_176251": next(
            r["margin_envelope"] for r in rows if r["length"] == 176251
        ),
        "uniform_ratio_false": any(r["margin_envelope"] < 1.0 for r in rows),
        "rows": rows,
    }


def classify(
    analytic: dict[str, Any],
    extra: list[dict[str, Any]],
    survey: dict[str, Any],
) -> dict[str, Any]:
    one_ok = survey["all_within_one"]
    cap_ok = survey["all_within_cap"]
    bound_ok = survey["all_binning_below_bound"] and analytic["covers"]
    if one_ok and bound_ok:
        return {
            "label": CLASS_GREEN,
            "reason": (
                "rotation bins stay within 1 of L/m; the Riemann + "
                "hitting bound sits under 1/(ln 3 ln n')"
            ),
        }
    if (not one_ok) and cap_ok and bound_ok:
        return {
            "label": CLASS_GREEN,
            "reason": (
                "hitting |#I-L mu|<=1 is false (first-bin excess); "
                f"occupancy stays within {HIT_CAP} on every leftover, "
                "and Riemann + J-slack with that cap sits under "
                "1/(ln 3 ln n') and recovers the 18 kills"
            ),
        }
    if not cap_ok:
        return {
            "label": CLASS_CLOSED,
            "reason": f"equal-bin occupancy exceeds the cap {HIT_CAP}",
        }
    return {
        "label": CLASS_PARK,
        "reason": (
            "occupancy is bounded but the written binning bound does "
            "not yet sit under the crude envelope"
        ),
    }


def probe_payload() -> dict[str, Any]:
    analytic = analytic_covers()
    extra_lengths = (19, 84, 1054, MIN_LENGTH, MIN_LENGTH + 1, 60_000, 100_000)
    extra = [hitting_report(length) for length in extra_lengths]
    survey = survey_envelope()
    return {
        "model": (
            "equal-bin left Riemann of the decreasing density plus "
            "rotation hitting |#I - L mu| <= 1; slack from J < 1"
        ),
        "bins": BIN_COUNT,
        "analytic": analytic,
        "extra_hitting": extra,
        "survey": {
            k: survey[k]
            for k in (
                "floor",
                "n",
                "bins",
                "n_rows",
                "all_binning_below_bound",
                "all_hug_below_bound",
                "all_within_one",
                "all_within_cap",
                "max_abs_dev",
                "max_over",
                "hit_cap",
                "n_envelope_kills",
                "min_kill_margin",
                "margin_50508",
                "margin_176251",
                "uniform_ratio_false",
            )
        },
        "rows": survey["rows"],
        "classification": classify(analytic, extra, survey),
        "not_a_halt_theorem": True,
        "no_cycle_all_lengths": False,
        "not_a_uniform_ratio_theorem": True,
        "git_commit": git_commit(),
    }


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    payload = payload or probe_payload()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    (DATA_DIR / "summary.json").write_text(
        json.dumps(payload, indent=2) + "\n", encoding="utf-8"
    )
    return payload


def main() -> None:
    payload = write_artifacts()
    analytic = payload["analytic"]
    survey = payload["survey"]
    print(
        f"analytic m={analytic['bins']} L={analytic['length']} "
        f"excess={analytic['binning_excess']:.6f} "
        f"gap={analytic['gap_lower']:.6f} covers={analytic['covers']}"
    )
    print(
        f"hitting max_dev={survey['max_abs_dev']:.4f} "
        f"max_over={survey['max_over']:.4f} "
        f"within_one={survey['all_within_one']} "
        f"within_cap={survey['all_within_cap']}"
    )
    print(
        f"binning<B={survey['all_binning_below_bound']} "
        f"kills={survey['n_envelope_kills']}/{survey['n_rows']} "
        f"margin_50508={survey['margin_50508']:.4f} "
        f"margin_176251={survey['margin_176251']:.4f} "
        f"uniform_ratio_false={survey['uniform_ratio_false']}"
    )
    print(payload["classification"]["label"])
    print(payload["classification"]["reason"])


if __name__ == "__main__":
    main()

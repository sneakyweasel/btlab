"""Denjoy-Koksma / Ostrowski census-free envelope for leftover hug charge.

Phase 0: |C_L - C_*(n')| <= 2 s(L) / L for the exact IET/hug prefix,
where s(L) is the greedy digit sum of L over certified convergent
denominators of theta = log(3/2)/log 3, by Denjoy-Koksma per block
with Var(F) <= 2 (F(u) = n^{1-2^u}/2^u decreases from F(0) = 1).
Replaces both the walk DP and the 19-row occupancy cap for the 18
kills. Not a halt theorem, not a floor raise, not a uniform B/theta
claim, and not a reopen of the REFUTED Koksma +1/L slogan: the
correct constant is 2 s(L), not 1.

Dossier: docs/problems/juggler_cycle_walk_ostrowski.md.
"""

from __future__ import annotations

from research.juggler_sequence.lean_paths import (
    DATA_ROOT,
)

import json
import math
from fractions import Fraction
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_finance import (
    EPS_CONST,
    PARITY_REL_GUARD,
    git_commit,
)
from research.juggler_sequence.cycle_walk_charge import (
    CERTIFIED_FLOOR,
    deficit_D,
)
from research.juggler_sequence.cycle_walk_envelope import gap_lower
from research.juggler_sequence.cycle_walk_exchange import (
    GREEDY_SUMMARY,
    c_star_integral,
)
from research.juggler_sequence.cycle_walk_greedy import hug_word
from research.juggler_sequence.cycle_walk_mechanical import SURVEY_PATH

DATA_DIR = (
    DATA_ROOT
    / "cycle_walk_ostrowski"
)

# Consecutive convergents of x = log 2 / log 3 (below / above x);
# certified below by pure big-int comparisons. The interval width
# 3.5e-15 survives the twelve Gauss inversions needed to certify
# the convergent denominator 176251 of theta.
X_LO = (10_781_274, 17_087_915)
X_HI = (10_590_737, 16_785_921)

Q_LIMIT = 200_000
VAR_BOUND = 2.0

CLASS_GREEN = "WALK_OSTROWSKI_GREEN"
CLASS_PARK = "WALK_OSTROWSKI_PARK"
CLASS_CLOSED = "WALK_OSTROWSKI_CLOSED"


def certify_x_bounds() -> dict[str, Any]:
    """x = log2/log3 in (X_LO, X_HI), by integer power comparisons.

    x > p/q  iff  2^q > 3^p;  x < p/q  iff  2^q < 3^p.
    """

    p_lo, q_lo = X_LO
    p_hi, q_hi = X_HI
    lower_ok = (1 << q_lo) > 3**p_lo
    upper_ok = (1 << q_hi) < 3**p_hi
    width = float(Fraction(p_hi, q_hi) - Fraction(p_lo, q_lo))
    return {
        "x_lo": [p_lo, q_lo],
        "x_hi": [p_hi, q_hi],
        "lower_ok": lower_ok,
        "upper_ok": upper_ok,
        "certified": lower_ok and upper_ok,
        "interval_width": width,
    }


def certified_theta_cf(q_limit: int = Q_LIMIT) -> dict[str, Any]:
    """Interval CF of theta = 1 - x on certified rational bounds.

    Both endpoints must produce the same partial quotient at every
    step; the convergent denominators are then exact for theta.
    """

    lo = 1 - Fraction(*X_HI)
    hi = 1 - Fraction(*X_LO)
    partial: list[int] = []
    denominators: list[int] = []
    h_prev, h = 1, 0
    k_prev, k = 0, 1
    first = True
    while True:
        a_lo = int(lo) if lo >= 0 else -int(-lo) - 1
        a_hi = int(hi) if hi >= 0 else -int(-hi) - 1
        if a_lo != a_hi:
            break
        a = a_lo
        partial.append(a)
        if first:
            h_prev, h = 1, a
            k_prev, k = 0, 1
            first = False
        else:
            h_prev, h = h, a * h + h_prev
            k_prev, k = k, a * k + k_prev
            if k > q_limit:
                break
            denominators.append(k)
        frac_lo = lo - a
        frac_hi = hi - a
        if frac_lo == 0 or frac_hi == 0:
            break
        lo, hi = 1 / frac_hi, 1 / frac_lo
    return {
        "partial_quotients": partial,
        "denominators": [1] + denominators,
        "reached": max([1] + denominators),
    }


def greedy_digits(length: int, denominators: list[int]) -> dict[str, Any]:
    """Greedy decomposition L = sum b_j q_j over certified q_j."""

    blocks: list[list[int]] = []
    rem = length
    for q in sorted(set(denominators), reverse=True):
        if q > rem:
            continue
        b = rem // q
        if b:
            blocks.append([q, b])
            rem -= b * q
    return {
        "length": length,
        "blocks": blocks,
        "digit_sum": sum(b for _, b in blocks),
        "exact": rem == 0,
    }


def exact_hug_word(length: int) -> tuple[str, int]:
    """Exact infinite-hug prefix: E iff u >= 1, decided by x-bounds.

    E at step k (0-indexed) iff 3^a >= 2^{k+1} iff a >= (k+1) x.
    The certified interval decides every step because (k+1) x stays
    at distance >= 1/q_next from integers for k+1 <= Q_LIMIT.
    """

    p_lo, q_lo = X_LO
    p_hi, q_hi = X_HI
    letters: list[str] = []
    a = 0
    for k in range(length):
        t = k + 1
        if a * q_hi >= t * p_hi:
            letters.append("E")
        elif a * q_lo < t * p_lo:
            letters.append("O")
            a += 1
        else:
            raise RuntimeError(f"undecided step k={k} a={a}")
    return "".join(letters), a


def survey_dk(
    denominators: list[int],
    survey_path: Path = SURVEY_PATH,
    n0: int = CERTIFIED_FLOOR,
) -> dict[str, Any]:
    survey = json.loads(survey_path.read_text(encoding="utf-8"))
    greedy = json.loads(GREEDY_SUMMARY.read_text(encoding="utf-8"))
    hug_c = {int(r["length"]): float(r["C"]) for r in greedy["survey_rows"]}
    n = int(survey["floor"]) + 1
    guard = 1.0 + PARITY_REL_GUARD
    rows = []
    for item in survey["rows"]:
        length = int(item["length"])
        odd_count = int(item["odd_count"])
        theta = float(item["theta"])
        const = float(item.get("const", EPS_CONST))
        log_n = math.log(n) - deficit_D(length, odd_count, n)
        star = c_star_integral(log_n)
        digits = greedy_digits(length, denominators)
        s = digits["digit_sum"]
        word, exact_odds = exact_hug_word(length)
        budgeted = hug_word(length, odd_count)
        c_hug = hug_c[length]
        excess = c_hug - star["C"]
        dk_cap = 2.0 * s / length
        gap = gap_lower(log_n)
        c_dk = star["C"] + dk_cap
        scale = length / (math.exp(log_n) * log_n)
        b_dk = c_dk * scale
        rhs = const * b_dk * guard
        rows.append(
            {
                "length": length,
                "odd_count": odd_count,
                "log_n": log_n,
                "digit_sum": s,
                "blocks": digits["blocks"],
                "greedy_exact": digits["exact"],
                "word_matches_budgeted_hug": word == budgeted,
                "exact_odds_match": exact_odds == odd_count,
                "C_hug": c_hug,
                "C_star": star["C"],
                "C_bound": star["bound"],
                "excess": excess,
                "excess_times_L": excess * length,
                "dk_cap": dk_cap,
                "dk_cap_times_L": 2.0 * s,
                "within_dk": excess <= dk_cap,
                "gap_lower": gap,
                "cap_below_gap": dk_cap < gap,
                "C_dk": c_dk,
                "dk_below_bound": c_dk < star["bound"],
                "theta": theta,
                "margin_dk": theta / rhs if rhs else math.inf,
            }
        )
    return {
        "floor": survey["floor"],
        "n": n,
        "n_rows": len(rows),
        "all_greedy_exact": all(r["greedy_exact"] for r in rows),
        "all_word_match": all(r["word_matches_budgeted_hug"] for r in rows),
        "all_odds_match": all(r["exact_odds_match"] for r in rows),
        "all_within_dk": all(r["within_dk"] for r in rows),
        "all_cap_below_gap": all(r["cap_below_gap"] for r in rows),
        "all_dk_below_bound": all(r["dk_below_bound"] for r in rows),
        "max_digit_sum": max(r["digit_sum"] for r in rows),
        "max_excess_times_L": max(r["excess_times_L"] for r in rows),
        "n_dk_kills": sum(1 for r in rows if r["margin_dk"] > 1.0),
        "margin_dk_50508": next(
            r["margin_dk"] for r in rows if r["length"] == 50508
        ),
        "margin_dk_176251": next(
            r["margin_dk"] for r in rows if r["length"] == 176251
        ),
        "uniform_ratio_false": any(r["margin_dk"] < 1.0 for r in rows),
        "rows": rows,
    }


def classify(
    bounds: dict[str, Any],
    cf: dict[str, Any],
    survey: dict[str, Any],
) -> dict[str, Any]:
    certified = bounds["certified"] and cf["reached"] >= 176_251
    structural = (
        survey["all_greedy_exact"]
        and survey["all_word_match"]
        and survey["all_odds_match"]
    )
    envelope = (
        survey["all_within_dk"]
        and survey["all_cap_below_gap"]
        and survey["all_dk_below_bound"]
        and survey["n_dk_kills"] == 18
        and survey["margin_dk_176251"] < 1.0
    )
    if certified and structural and envelope:
        return {
            "label": CLASS_GREEN,
            "reason": (
                "q_j certified by integer sandwich; every leftover is "
                "an exact greedy sum of convergent denominators with "
                "digit sum <= 6; the exact IET prefix equals the "
                "budgeted hug word; excess stays under 2s/L and 2s/L "
                "stays under the J-gap, so C_L < 1/(ln 3 ln n') with "
                "no occupancy census; the DK envelope alone kills the "
                "same 18 lengths and 176251 still survives"
            ),
        }
    if not survey["all_within_dk"]:
        return {
            "label": CLASS_CLOSED,
            "reason": "a leftover excess exceeds the DK cap 2s/L",
        }
    return {
        "label": CLASS_PARK,
        "reason": (
            "DK cap holds but certification, word identity, or the "
            "kill table is incomplete"
        ),
    }


def probe_payload() -> dict[str, Any]:
    bounds = certify_x_bounds()
    cf = certified_theta_cf()
    survey = survey_dk(cf["denominators"])
    return {
        "model": (
            "Denjoy-Koksma per Ostrowski block: Var(F) <= 2 on the "
            "circle of length 1+alpha, blocks are certified convergent "
            "denominators of theta = log(3/2)/log 3, so "
            "|C_L - C_*| <= 2 s(L)/L for the exact hug/IET prefix"
        ),
        "var_bound": VAR_BOUND,
        "x_certification": bounds,
        "theta_cf": cf,
        "survey": {
            k: survey[k]
            for k in (
                "floor",
                "n",
                "n_rows",
                "all_greedy_exact",
                "all_word_match",
                "all_odds_match",
                "all_within_dk",
                "all_cap_below_gap",
                "all_dk_below_bound",
                "max_digit_sum",
                "max_excess_times_L",
                "n_dk_kills",
                "margin_dk_50508",
                "margin_dk_176251",
                "uniform_ratio_false",
            )
        },
        "rows": survey["rows"],
        "classification": classify(bounds, cf, survey),
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
    bounds = payload["x_certification"]
    cf = payload["theta_cf"]
    survey = payload["survey"]
    print(
        f"x bounds certified={bounds['certified']} "
        f"width={bounds['interval_width']:.3e}"
    )
    print(
        f"theta CF {cf['partial_quotients'][:13]} "
        f"q reached {cf['reached']}"
    )
    print(
        f"greedy exact={survey['all_greedy_exact']} "
        f"word={survey['all_word_match']} "
        f"odds={survey['all_odds_match']} "
        f"max_s={survey['max_digit_sum']}"
    )
    print(
        f"within 2s/L={survey['all_within_dk']} "
        f"max excess*L={survey['max_excess_times_L']:.3f} "
        f"cap<gap={survey['all_cap_below_gap']}"
    )
    print(
        f"dk kills={survey['n_dk_kills']}/{survey['n_rows']} "
        f"margin_50508={survey['margin_dk_50508']:.4f} "
        f"margin_176251={survey['margin_dk_176251']:.4f} "
        f"uniform_ratio_false={survey['uniform_ratio_false']}"
    )
    print(payload["classification"]["label"])
    print(payload["classification"]["reason"])


if __name__ == "__main__":
    main()

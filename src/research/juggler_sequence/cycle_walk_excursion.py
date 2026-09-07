"""Near-return structure of the walk-charge DP maximizer.

Phase 0: reconstruct a maximizer of the existing lattice DP, split it
into primitive near-returns to the band [0, 1), and test whether those
blocks are semi-convergents of alpha = log2(3/2). The committed survey
supplies the charge-per-letter table. Not a halt theorem, not a floor
raise, not a uniform B/theta claim, and not a reopen of the closed
Christoffel leftover-cell slogan.

Dossier: docs/problems/juggler_cycle_walk_excursion.md.
"""

from __future__ import annotations

from research.juggler_sequence.lean_paths import (
    DATA_ROOT,
)

import json
import math
from collections import Counter
from pathlib import Path
from typing import Any

import numpy as np

from research.juggler_sequence.cycle_christoffel import christoffel_word
from research.juggler_sequence.cycle_finance import (
    PARITY_REL_GUARD,
    git_commit,
    o_min_and_theta,
)
from research.juggler_sequence.cycle_walk_charge import (
    MU,
    STEP,
    U_TOL,
    charge_row,
)

DATA_DIR = (
    DATA_ROOT
    / "cycle_walk_excursion"
)
SURVEY_PATH = (
    DATA_ROOT
    / "cycle_walk_charge"
    / "survey.json"
)

CENSUS_L_MAX = 24
CF_PROBE_LENGTHS = (19, 84, 1054)
NAMED_TYPES = ((2, 1), (5, 3), (12, 7), (29, 17), (41, 24), (53, 31))
LATTICE_GENERATORS = ((665, 389), (16266, 9515))
BAND_HI = 1.0
BAND_TOL = 1e-12
RECONSTRUCT_N = 1000
SEMI_MAX_ODD = 20_000

CLASS_GREEN = "WALK_EXCURSION_GREEN"
CLASS_PARK = "WALK_EXCURSION_PARK"
CLASS_CLOSED = "WALK_EXCURSION_CLOSED"


def continued_fraction_terms(x: float, max_terms: int = 40) -> list[int]:
    terms: list[int] = []
    for _ in range(max_terms):
        integer = int(math.floor(x))
        terms.append(integer)
        frac = x - integer
        if frac < 1e-18:
            break
        x = 1.0 / frac
    return terms


def semi_convergents_alpha(
    max_odd: int = SEMI_MAX_ODD,
    *,
    alpha: float = MU,
) -> list[tuple[int, int]]:
    """Semi-convergents of alpha as (odd, even) = (q, p) for p/q.

    Exact 0-returns are impossible (3^a = 2^k), so these are the
    legal near-return types of the exponent walk.
    """

    terms = continued_fraction_terms(alpha)
    p_prev2, q_prev2 = 0, 1
    p_prev1, q_prev1 = 1, 0
    pairs: list[tuple[int, int]] = []
    seen: set[tuple[int, int]] = set()
    for coeff in terms:
        for k in range(1, coeff + 1):
            numer = k * p_prev1 + p_prev2
            denom = k * q_prev1 + q_prev2
            if denom <= 0 or denom > max_odd:
                continue
            pair = (denom, numer)
            if pair not in seen and numer >= 0:
                seen.add(pair)
                pairs.append(pair)
        p_new = coeff * p_prev1 + p_prev2
        q_new = coeff * q_prev1 + q_prev2
        p_prev2, q_prev2 = p_prev1, q_prev1
        p_prev1, q_prev1 = p_new, q_new
        if q_new > max_odd:
            break
    for extra in NAMED_TYPES + LATTICE_GENERATORS:
        if extra not in seen and extra[0] <= max_odd:
            seen.add(extra)
            pairs.append(extra)
    return pairs


def alpha_type_set(max_odd: int = SEMI_MAX_ODD) -> set[tuple[int, int]]:
    return set(semi_convergents_alpha(max_odd))


def in_valley_band(u: float) -> bool:
    return u >= -U_TOL and u < BAND_HI - BAND_TOL


def reconstruct_maximizer(
    length: int,
    odd_count: int,
    n: int,
    *,
    eta: float = 0.0,
    log_n: float | None = None,
) -> dict[str, Any]:
    """One maximizer of the walk DP, with predecessor traceback.

    Ties prefer an even letter. Memory is one bit per (k, a). Does
    not touch the certified walk_budget table.
    """

    even_count = length - odd_count
    neg = -math.inf
    values = np.full(odd_count + 1, neg)
    values[0] = float(charge_row(np.zeros(1), n, eta, log_n=log_n)[0])
    a_axis = np.arange(odd_count + 1, dtype=np.float64)
    came_from_odd = np.zeros((length, odd_count + 1), dtype=np.bool_)
    for k in range(1, length + 1):
        stay = values
        step_up = np.full_like(values, neg)
        step_up[1:] = values[:-1]
        chose_odd = step_up > stay
        values = np.where(chose_odd, step_up, stay)
        u = STEP * a_axis - k
        feasible = (
            (u >= -U_TOL)
            & (a_axis <= min(odd_count, k))
            & (k - a_axis <= even_count)
        )
        values = np.where(feasible, values, neg)
        came_from_odd[k - 1] = chose_odd & feasible
        if k < length:
            values = values + np.where(
                feasible,
                charge_row(np.maximum(u, 0.0), n, eta, log_n=log_n),
                0.0,
            )
    best = float(values[odd_count])
    if not math.isfinite(best):
        return {
            "length": length,
            "odd_count": odd_count,
            "n": n,
            "feasible": False,
            "walk_sum": best,
            "word": "",
            "surplus_u": STEP * odd_count - length,
        }
    letters: list[str] = []
    a = odd_count
    for k in range(length, 0, -1):
        if came_from_odd[k - 1, a]:
            letters.append("O")
            a -= 1
        else:
            letters.append("E")
    if a != 0:
        raise RuntimeError(
            f"traceback did not return to a=0 at L={length} o={odd_count}"
        )
    word = "".join(reversed(letters))
    return {
        "length": length,
        "odd_count": odd_count,
        "even_count": even_count,
        "n": n,
        "feasible": True,
        "walk_sum": best,
        "word": word,
        "surplus_u": STEP * odd_count - length,
    }


def replay_charge(
    word: str,
    n: int,
    *,
    eta: float = 0.0,
    log_n: float | None = None,
) -> float:
    """Charge of a concrete word; same accounting as walk_budget."""

    if not word:
        return -math.inf
    total = float(charge_row(np.zeros(1), n, eta, log_n=log_n)[0])
    u = 0.0
    for i, letter in enumerate(word):
        u += MU if letter == "O" else -1.0
        if u < -U_TOL:
            return -math.inf
        if i + 1 < len(word):
            total += float(
                charge_row(np.array([max(u, 0.0)]), n, eta, log_n=log_n)[0]
            )
    return total


def segment_near_returns(word: str) -> list[dict[str, Any]]:
    """Split at first descents back into the band [0, 1)."""

    if not word:
        return []
    blocks: list[dict[str, Any]] = []
    u = 0.0
    in_band = True
    start = 0
    odds = 0
    evens = 0
    for i, letter in enumerate(word):
        if letter == "O":
            u += MU
            odds += 1
        else:
            u -= 1.0
            evens += 1
        now_in = in_valley_band(u)
        if in_band and not now_in:
            in_band = False
        elif (not in_band) and now_in:
            blocks.append(
                {
                    "word": word[start : i + 1],
                    "odd_count": odds,
                    "even_count": evens,
                    "landing_u": u,
                    "closed": True,
                }
            )
            start = i + 1
            odds = 0
            evens = 0
            in_band = True
    if start < len(word):
        blocks.append(
            {
                "word": word[start:],
                "odd_count": odds,
                "even_count": evens,
                "landing_u": u,
                "closed": False,
            }
        )
    return blocks


def annotate_blocks(
    blocks: list[dict[str, Any]],
    types: set[tuple[int, int]],
) -> list[dict[str, Any]]:
    rows = []
    for block in blocks:
        pair = (block["odd_count"], block["even_count"])
        row = dict(block)
        row["type"] = pair
        row["is_semi_convergent"] = pair in types
        rows.append(row)
    return rows


def type_histogram(blocks: list[dict[str, Any]]) -> dict[str, int]:
    counts: Counter[str] = Counter()
    for block in blocks:
        counts[f"{block['odd_count']},{block['even_count']}"] += 1
    return dict(sorted(counts.items()))


def analyze_word(
    word: str,
    *,
    types: set[tuple[int, int]] | None = None,
) -> dict[str, Any]:
    types = types or alpha_type_set()
    blocks = annotate_blocks(segment_near_returns(word), types)
    leftovers = [b["landing_u"] for b in blocks if b["closed"]]
    non_cf = [
        b["type"] for b in blocks if b["closed"] and not b["is_semi_convergent"]
    ]
    return {
        "word": word,
        "blocks": blocks,
        "n_blocks": len(blocks),
        "n_closed": sum(1 for b in blocks if b["closed"]),
        "type_histogram": type_histogram(blocks),
        "non_cf_types": sorted(set(non_cf)),
        "all_closed_cf": not non_cf,
        "max_leftover_u": max(leftovers) if leftovers else None,
        "mean_leftover_u": (
            float(sum(leftovers) / len(leftovers)) if leftovers else None
        ),
        "open_tail": next((b["type"] for b in blocks if not b["closed"]), None),
    }


def census_small(
    l_max: int = CENSUS_L_MAX,
    n: int = RECONSTRUCT_N,
    *,
    types: set[tuple[int, int]] | None = None,
) -> dict[str, Any]:
    types = types or alpha_type_set()
    rows = []
    non_cf_witnesses = []
    for length in range(1, l_max + 1):
        for odd_count in range(0, length + 1):
            if STEP * odd_count - length < -U_TOL:
                continue
            rec = reconstruct_maximizer(length, odd_count, n)
            if not rec["feasible"]:
                continue
            analysis = analyze_word(rec["word"], types=types)
            row = {
                "length": length,
                "odd_count": odd_count,
                "walk_sum": rec["walk_sum"],
                "all_closed_cf": analysis["all_closed_cf"],
                "type_histogram": analysis["type_histogram"],
                "non_cf_types": analysis["non_cf_types"],
                "open_tail": analysis["open_tail"],
            }
            rows.append(row)
            if analysis["non_cf_types"]:
                non_cf_witnesses.append(
                    {
                        **row,
                        "word": rec["word"],
                    }
                )
    return {
        "l_max": l_max,
        "n": n,
        "n_feasible": len(rows),
        "n_all_cf": sum(1 for r in rows if r["all_closed_cf"]),
        "n_non_cf": len(non_cf_witnesses),
        "non_cf_witnesses": non_cf_witnesses[:20],
        "rows": rows,
    }


def reconstruct_cf_lengths(
    lengths: tuple[int, ...] = CF_PROBE_LENGTHS,
    n: int = RECONSTRUCT_N,
    *,
    types: set[tuple[int, int]] | None = None,
) -> list[dict[str, Any]]:
    types = types or alpha_type_set()
    reports = []
    for length in lengths:
        odd_count, _theta = o_min_and_theta(length)
        rec = reconstruct_maximizer(length, odd_count, n)
        analysis = analyze_word(rec["word"], types=types)
        mechanical = christoffel_word(length, odd_count)
        reports.append(
            {
                "length": length,
                "odd_count": odd_count,
                "feasible": rec["feasible"],
                "walk_sum": rec["walk_sum"],
                "word_prefix": rec["word"][:80],
                "word_suffix": rec["word"][-40:] if rec["word"] else "",
                "equals_christoffel": rec["word"] == mechanical,
                "n_blocks": analysis["n_blocks"],
                "n_closed": analysis["n_closed"],
                "type_histogram": analysis["type_histogram"],
                "all_closed_cf": analysis["all_closed_cf"],
                "non_cf_types": analysis["non_cf_types"],
                "max_leftover_u": analysis["max_leftover_u"],
                "mean_leftover_u": analysis["mean_leftover_u"],
                "open_tail": analysis["open_tail"],
            }
        )
    return reports


def survey_charge_density(
    survey_path: Path = SURVEY_PATH,
) -> dict[str, Any]:
    """Read-only B/L table from the committed walk-charge survey."""

    survey = json.loads(survey_path.read_text(encoding="utf-8"))
    n = int(survey["floor"]) + 1
    log_n = math.log(n)
    rows = []
    for item in survey["rows"]:
        rhs = float(item["walk_rhs_certified"])
        const = float(item["const"])
        budget = rhs / (const * (1.0 + PARITY_REL_GUARD))
        length = int(item["length"])
        rows.append(
            {
                "length": length,
                "odd_count": item["odd_count"],
                "theta": item["theta"],
                "kill_margin": item["kill_margin"],
                "B": budget,
                "B_over_L": budget / length,
                "C": budget * n * log_n / length,
                "theta_over_L": item["theta"] / length,
            }
        )
    densities = [r["B_over_L"] for r in rows]
    constants = [r["C"] for r in rows]
    median = sorted(densities)[len(densities) // 2]
    spread = (max(densities) - min(densities)) / median if median else math.inf
    return {
        "floor": survey["floor"],
        "n": n,
        "n_rows": len(rows),
        "B_over_L_min": min(densities),
        "B_over_L_max": max(densities),
        "B_over_L_median": median,
        "relative_spread": spread,
        "C_min": min(constants),
        "C_max": max(constants),
        "C_median": sorted(constants)[len(constants) // 2],
        "rows": rows,
        "uniform_ratio_false": any(r["kill_margin"] < 1.0 for r in rows),
    }


def classify(
    census: dict[str, Any],
    cf_reports: list[dict[str, Any]],
    density: dict[str, Any],
) -> dict[str, Any]:
    all_cf = census["n_non_cf"] == 0 and all(
        r["all_closed_cf"] for r in cf_reports
    )
    mechanical = all(r.get("equals_christoffel") for r in cf_reports)
    density_ok = density["relative_spread"] < 1e-2
    if all_cf and density_ok:
        extra = (
            "; the leftover maximizers are the Christoffel words of slope o/L"
            if mechanical
            else ""
        )
        return {
            "label": CLASS_GREEN,
            "reason": (
                "every reconstructed maximizer through L=24 and at "
                "CF lengths 19, 84, 1054 splits into semi-convergents "
                "of alpha, and the committed survey has constant B/L"
                + extra
            ),
        }
    if census["n_non_cf"] > 0:
        return {
            "label": CLASS_CLOSED,
            "reason": (
                "a feasible maximizer used a primitive near-return "
                f"outside the semi-convergents of alpha: "
                f"{census['non_cf_witnesses'][0]}"
            ),
        }
    return {
        "label": CLASS_PARK,
        "reason": (
            "CF lengths or charge-per-letter are only partially "
            "explained; carry produced an unclassified family"
        ),
    }


def probe_payload() -> dict[str, Any]:
    types = alpha_type_set()
    census = census_small(types=types)
    cf_reports = reconstruct_cf_lengths(types=types)
    density = survey_charge_density()
    return {
        "model": (
            "walk-DP maximizer reconstructed by predecessor traceback; "
            "primitive blocks are first returns to the band [0, 1); "
            "types tested against semi-convergents of log2(3/2)"
        ),
        "named_types_present": all(pair in types for pair in NAMED_TYPES),
        "lattice_generators_present": all(
            pair in types for pair in LATTICE_GENERATORS
        ),
        "semi_convergent_count": len(types),
        "named_types": [list(pair) for pair in NAMED_TYPES],
        "census": {
            "l_max": census["l_max"],
            "n_feasible": census["n_feasible"],
            "n_all_cf": census["n_all_cf"],
            "n_non_cf": census["n_non_cf"],
            "non_cf_witnesses": census["non_cf_witnesses"],
        },
        "cf_lengths": cf_reports,
        "charge_density": {
            k: density[k]
            for k in (
                "floor",
                "n",
                "n_rows",
                "B_over_L_min",
                "B_over_L_max",
                "B_over_L_median",
                "relative_spread",
                "C_min",
                "C_max",
                "C_median",
                "uniform_ratio_false",
            )
        },
        "density_rows": density["rows"],
        "classification": classify(census, cf_reports, density),
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
    label = payload["classification"]["label"]
    census = payload["census"]
    density = payload["charge_density"]
    print(
        f"census L<={census['l_max']}: "
        f"{census['n_all_cf']}/{census['n_feasible']} CF, "
        f"non-cf={census['n_non_cf']}"
    )
    for row in payload["cf_lengths"]:
        print(
            f"L={row['length']} o={row['odd_count']} "
            f"blocks={row['n_closed']}/{row['n_blocks']} "
            f"cf={row['all_closed_cf']} "
            f"types={row['type_histogram']}"
        )
    print(
        f"B/L spread={density['relative_spread']:.4e} "
        f"C_median={density['C_median']:.5f} "
        f"uniform_ratio_false={density['uniform_ratio_false']}"
    )
    print(label)
    print(payload["classification"]["reason"])


if __name__ == "__main__":
    main()

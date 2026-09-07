"""Christoffel prefix-dominance and mechanical-limit charge.

Phase 0: among admissible u>=0 walks with fixed (L,o), does the
ceiling Christoffel word prefix-minimize a_k (hence u_k)? And does
leftover B/L at the certified floor match the long mechanical word
of slope 1/(1+log2(3/2))? Not a halt theorem, not a floor raise,
not a uniform B/theta claim, and not a reopen of the closed
Christoffel leftover-cell slogan.

Dossier: docs/problems/juggler_cycle_walk_mechanical.md.
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

from research.juggler_sequence.cycle_christoffel import christoffel_word
from research.juggler_sequence.cycle_finance import (
    PARITY_REL_GUARD,
    git_commit,
    o_min_and_theta,
)
from research.juggler_sequence.cycle_walk_charge import (
    CERTIFIED_FLOOR,
    MU,
    STEP,
    TARGET_LENGTH,
    U_TOL,
    charge_row,
    deficit_D,
)
from research.juggler_sequence.cycle_walk_excursion import replay_charge

DATA_DIR = (
    DATA_ROOT
    / "cycle_walk_mechanical"
)
SURVEY_PATH = (
    DATA_ROOT
    / "cycle_walk_charge"
    / "survey.json"
)

CENSUS_L_MAX = 24
CF_PROBE_LENGTHS = (19, 84, 1054)
MECHANICAL_PREFIX = 100_000
RHO = 1.0 / STEP  # log2 / log3 = 1 / (1 + log2(3/2))
SURVEY_REL_TOL = 1e-9
C_SPREAD_TOL = 2.5e-3

CLASS_GREEN = "WALK_MECHANICAL_GREEN"
CLASS_PARK = "WALK_MECHANICAL_PARK"
CLASS_CLOSED = "WALK_MECHANICAL_CLOSED"


def christoffel_prefix_odds(length: int, odd_count: int, step: int) -> int:
    """a_k = ceil(k * o / L) for the ceiling Christoffel word."""

    if step <= 0:
        return 0
    return math.ceil(step * odd_count / length)


def reachable_completable(
    length: int,
    odd_count: int,
) -> tuple[list[set[int]], list[set[int]]]:
    """Forward-reachable and backward-completable odd-counts at each k."""

    even_count = length - odd_count
    reachable: list[set[int]] = [set() for _ in range(length + 1)]
    reachable[0].add(0)
    for k in range(length):
        for odds in reachable[k]:
            evens = k - odds
            if STEP * odds - k < -U_TOL:
                continue
            if odds < odd_count and evens <= even_count:
                nxt = odds + 1
                if STEP * nxt - (k + 1) >= -U_TOL:
                    reachable[k + 1].add(nxt)
            if evens < even_count and odds <= odd_count:
                if STEP * odds - (k + 1) >= -U_TOL:
                    reachable[k + 1].add(odds)

    completable: list[set[int]] = [set() for _ in range(length + 1)]
    completable[length].add(odd_count)
    for k in range(length - 1, -1, -1):
        for odds in range(odd_count + 1):
            evens = k - odds
            if evens < 0 or evens > even_count:
                continue
            if STEP * odds - k < -U_TOL:
                continue
            can_o = (
                odds < odd_count
                and (odds + 1) in completable[k + 1]
                and STEP * (odds + 1) - (k + 1) >= -U_TOL
            )
            can_e = (
                evens < even_count
                and odds in completable[k + 1]
                and STEP * odds - (k + 1) >= -U_TOL
            )
            if can_o or can_e:
                completable[k].add(odds)
    return reachable, completable


def prefix_min_odds(length: int, odd_count: int) -> list[int | None]:
    """Least odd-count at each k among admissible completions."""

    reachable, completable = reachable_completable(length, odd_count)
    mins: list[int | None] = []
    for k in range(length + 1):
        live = reachable[k] & completable[k]
        mins.append(min(live) if live else None)
    return mins


def prefix_dominance_holds(length: int, odd_count: int) -> dict[str, Any]:
    mins = prefix_min_odds(length, odd_count)
    mismatches = []
    for k, observed in enumerate(mins):
        expected = christoffel_prefix_odds(length, odd_count, k)
        if observed is None or observed != expected:
            mismatches.append(
                {"k": k, "min_a": observed, "christoffel_a": expected}
            )
    return {
        "length": length,
        "odd_count": odd_count,
        "holds": not mismatches,
        "n_mismatches": len(mismatches),
        "mismatches": mismatches[:8],
    }


def greedy_word(length: int, odd_count: int) -> str:
    """Take E at the first legal completable time."""

    even_count = length - odd_count
    _reachable, completable = reachable_completable(length, odd_count)
    letters: list[str] = []
    odds = 0
    for k in range(length):
        evens = k - odds
        can_e = (
            evens < even_count
            and odds in completable[k + 1]
            and STEP * odds - (k + 1) >= -U_TOL
        )
        can_o = (
            odds < odd_count
            and (odds + 1) in completable[k + 1]
            and STEP * (odds + 1) - (k + 1) >= -U_TOL
        )
        if can_e:
            letters.append("E")
        elif can_o:
            letters.append("O")
            odds += 1
        else:
            raise RuntimeError(
                f"greedy stuck at k={k} a={odds} L={length} o={odd_count}"
            )
    return "".join(letters)


def christoffel_charge(
    length: int,
    odd_count: int,
    n: int,
    *,
    eta: float = 0.0,
    log_n: float | None = None,
) -> float:
    """Walk charge of the ceiling Christoffel word, streamed."""

    total = float(charge_row(np.zeros(1), n, eta, log_n=log_n)[0])
    odds = 0
    for k in range(1, length + 1):
        bit = math.ceil(k * odd_count / length) - math.ceil(
            (k - 1) * odd_count / length
        )
        odds += int(bit)
        if k < length:
            height = STEP * odds - k
            total += float(
                charge_row(
                    np.array([max(height, 0.0)]), n, eta, log_n=log_n
                )[0]
            )
    return total


def charge_density(budget: float, length: int, log_n: float) -> float:
    """B / (L / (n ln n)) at the base n = exp(log_n)."""

    return budget * math.exp(log_n) * log_n / length


def census_small(l_max: int = CENSUS_L_MAX) -> dict[str, Any]:
    rows = []
    dominance_fail = []
    greedy_fail = []
    for length in range(1, l_max + 1):
        for odd_count in range(0, length + 1):
            if STEP * odd_count - length < -U_TOL:
                continue
            _reachable, completable = reachable_completable(length, odd_count)
            if 0 not in completable[0]:
                continue
            dom = prefix_dominance_holds(length, odd_count)
            greedy = greedy_word(length, odd_count)
            mechanical = christoffel_word(length, odd_count)
            row = {
                "length": length,
                "odd_count": odd_count,
                "prefix_min": dom["holds"],
                "greedy_equals_christoffel": greedy == mechanical,
            }
            rows.append(row)
            if not dom["holds"]:
                dominance_fail.append({**row, "mismatches": dom["mismatches"]})
            if greedy != mechanical:
                greedy_fail.append(
                    {
                        **row,
                        "greedy_prefix": greedy[:40],
                        "christoffel_prefix": mechanical[:40],
                    }
                )
    ok_pairs = [
        [r["length"], r["odd_count"]]
        for r in rows
        if r["prefix_min"] and r["greedy_equals_christoffel"]
    ]
    return {
        "l_max": l_max,
        "n_feasible": len(rows),
        "n_prefix_min": sum(1 for r in rows if r["prefix_min"]),
        "n_greedy_match": sum(
            1 for r in rows if r["greedy_equals_christoffel"]
        ),
        "prefix_ok_pairs": ok_pairs,
        "dominance_failures": dominance_fail[:12],
        "greedy_failures": greedy_fail[:12],
        "counterexample_4_3": {
            "christoffel": christoffel_word(4, 3),
            "greedy": greedy_word(4, 3),
            "prefix_min": prefix_dominance_holds(4, 3),
        },
    }


def cf_length_checks(
    lengths: tuple[int, ...] = CF_PROBE_LENGTHS,
) -> list[dict[str, Any]]:
    rows = []
    for length in lengths:
        odd_count, _theta = o_min_and_theta(length)
        greedy = greedy_word(length, odd_count)
        mechanical = christoffel_word(length, odd_count)
        dom = prefix_dominance_holds(length, odd_count)
        rows.append(
            {
                "length": length,
                "odd_count": odd_count,
                "prefix_min": dom["holds"],
                "greedy_equals_christoffel": greedy == mechanical,
                "n_mismatches": dom["n_mismatches"],
            }
        )
    return rows


def certified_log_n(
    length: int = TARGET_LENGTH,
    n0: int = CERTIFIED_FLOOR,
) -> dict[str, Any]:
    odd_count, _theta = o_min_and_theta(length)
    n = n0 + 1
    deficit = deficit_D(length, odd_count, n)
    return {
        "length": length,
        "odd_count": odd_count,
        "n": n,
        "deficit_D": deficit,
        "log_n": math.log(n) - deficit,
    }


def survey_christoffel_compare(
    survey_path: Path = SURVEY_PATH,
    n0: int = CERTIFIED_FLOOR,
) -> dict[str, Any]:
    survey = json.loads(survey_path.read_text(encoding="utf-8"))
    n = int(survey["floor"]) + 1
    rows = []
    for item in survey["rows"]:
        length = int(item["length"])
        odd_count = int(item["odd_count"])
        const = float(item["const"])
        survey_b = float(item["walk_rhs_certified"]) / (
            const * (1.0 + PARITY_REL_GUARD)
        )
        deficit = deficit_D(length, odd_count, n)
        log_n = math.log(n) - deficit
        chr_b = christoffel_charge(length, odd_count, n, log_n=log_n)
        rel = abs(chr_b - survey_b) / survey_b if survey_b else math.inf
        theta = float(item["theta"])
        rhs = const * chr_b * (1.0 + PARITY_REL_GUARD)
        rows.append(
            {
                "length": length,
                "odd_count": odd_count,
                "theta": theta,
                "survey_B": survey_b,
                "christoffel_B": chr_b,
                "relative_mismatch": rel,
                "C": charge_density(chr_b, length, log_n),
                "B_over_theta": chr_b / theta if theta else math.inf,
                "kill_margin": theta / rhs if rhs else math.inf,
            }
        )
    mismatches = [r["relative_mismatch"] for r in rows]
    return {
        "floor": survey["floor"],
        "n": n,
        "n_rows": len(rows),
        "max_relative_mismatch": max(mismatches),
        "all_match": max(mismatches) < SURVEY_REL_TOL,
        "uniform_ratio_false": any(r["kill_margin"] < 1.0 for r in rows),
        "rows": rows,
    }


def mechanical_average(
    prefix: int = MECHANICAL_PREFIX,
    n: int = CERTIFIED_FLOOR + 1,
    *,
    log_n: float,
) -> dict[str, Any]:
    """Ceiling-Beatty stream of slope rho = 1/(1+alpha)."""

    total = float(charge_row(np.zeros(1), n, 0.0, log_n=log_n)[0])
    odds = 0
    band_hits = 0
    u_sum = 0.0
    u_min = 0.0
    u_max = 0.0
    for k in range(1, prefix + 1):
        bit = math.ceil(k * RHO) - math.ceil((k - 1) * RHO)
        odds += int(bit)
        height = STEP * odds - k
        if height < u_min:
            u_min = height
        if height > u_max:
            u_max = height
        if 0.0 <= height < 1.0:
            band_hits += 1
        u_sum += height
        if k < prefix:
            total += float(
                charge_row(np.array([max(height, 0.0)]), n, 0.0, log_n=log_n)[0]
            )
    return {
        "prefix": prefix,
        "rho": RHO,
        "B": total,
        "C": charge_density(total, prefix, log_n),
        "mean_u": u_sum / prefix,
        "min_u": u_min,
        "max_u": u_max,
        "band_fraction": band_hits / prefix,
        "odd_fraction": odds / prefix,
    }


def classify(
    census: dict[str, Any],
    cf_rows: list[dict[str, Any]],
    survey: dict[str, Any],
    mechanical: dict[str, Any],
) -> dict[str, Any]:
    prefix_ok = (
        census["n_prefix_min"] == census["n_feasible"]
        and all(r["prefix_min"] for r in cf_rows)
    )
    greedy_ok = (
        census["n_greedy_match"] == census["n_feasible"]
        and all(r["greedy_equals_christoffel"] for r in cf_rows)
    )
    survey_ok = survey["all_match"]
    leftover_c = [r["C"] for r in survey["rows"]]
    mech_c = mechanical["C"]
    c_rel = max(abs(c - mech_c) / mech_c for c in leftover_c)
    c_ok = c_rel < C_SPREAD_TOL
    if prefix_ok and greedy_ok and survey_ok and c_ok:
        return {
            "label": CLASS_GREEN,
            "reason": (
                "ceiling Christoffel prefix-minimizes a_k on L<=24 and "
                "at 19,84,1054; greedy E equals that word; survey B "
                "matches Christoffel charge; leftover C agrees with "
                "the mechanical average"
            ),
            "c_relative_spread_vs_mechanical": c_rel,
        }
    if survey_ok and not prefix_ok:
        return {
            "label": CLASS_PARK,
            "reason": (
                "Christoffel matches survey B (sum-optimal) but is not "
                "pointwise prefix-minimal"
            ),
            "c_relative_spread_vs_mechanical": c_rel,
        }
    if not survey_ok:
        exact = [
            r["length"]
            for r in survey["rows"]
            if r["relative_mismatch"] == 0.0
        ]
        return {
            "label": CLASS_CLOSED,
            "reason": (
                "greedy hugging undercuts ceiling Christoffel off the "
                "critical slope: prefix-min fails at (4,3) (OOEO vs OOOE), "
                "and survey B exceeds Christoffel charge by up to "
                f"{survey['max_relative_mismatch']:.4e} on family offsets; "
                f"exact match only on seed multiples {exact}"
            ),
            "c_relative_spread_vs_mechanical": c_rel,
            "exact_survey_lengths": exact,
        }
    return {
        "label": CLASS_PARK,
        "reason": (
            "prefix/greedy/survey checks split, or leftover C is not "
            "yet the mechanical average"
        ),
        "c_relative_spread_vs_mechanical": c_rel,
    }


def probe_payload() -> dict[str, Any]:
    base = certified_log_n()
    census = census_small()
    cf_rows = cf_length_checks()
    survey = survey_christoffel_compare()
    mechanical = mechanical_average(log_n=base["log_n"], n=base["n"])
    return {
        "model": (
            "ceiling Christoffel / greedy-E prefix-min among u>=0 walks; "
            "mechanical limit is the ceiling-Beatty stream of slope "
            "1/(1+log2(3/2)); charge at the reduced base n e^{-D}"
        ),
        "certified_base": base,
        "census": {
            "l_max": census["l_max"],
            "n_feasible": census["n_feasible"],
            "n_prefix_min": census["n_prefix_min"],
            "n_greedy_match": census["n_greedy_match"],
            "prefix_ok_pairs": census["prefix_ok_pairs"],
            "counterexample_4_3": census["counterexample_4_3"],
            "dominance_failures": census["dominance_failures"],
            "greedy_failures": census["greedy_failures"],
        },
        "cf_lengths": cf_rows,
        "survey_compare": {
            k: survey[k]
            for k in (
                "floor",
                "n",
                "n_rows",
                "max_relative_mismatch",
                "all_match",
                "uniform_ratio_false",
            )
        },
        "survey_rows": survey["rows"],
        "mechanical": mechanical,
        "classification": classify(census, cf_rows, survey, mechanical),
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
    census = payload["census"]
    survey = payload["survey_compare"]
    mechanical = payload["mechanical"]
    print(
        f"census L<={census['l_max']}: "
        f"prefix-min {census['n_prefix_min']}/{census['n_feasible']}, "
        f"greedy {census['n_greedy_match']}/{census['n_feasible']}"
    )
    for row in payload["cf_lengths"]:
        print(
            f"L={row['length']} prefix_min={row['prefix_min']} "
            f"greedy={row['greedy_equals_christoffel']}"
        )
    print(
        f"survey match={survey['all_match']} "
        f"max_rel={survey['max_relative_mismatch']:.3e} "
        f"uniform_ratio_false={survey['uniform_ratio_false']}"
    )
    print(
        f"mechanical C={mechanical['C']:.6f} "
        f"band={mechanical['band_fraction']:.4f} "
        f"u in [{mechanical['min_u']:.4f},{mechanical['max_u']:.4f}]"
    )
    print(payload["classification"]["label"])
    print(payload["classification"]["reason"])


if __name__ == "__main__":
    main()

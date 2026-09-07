"""Greedy E-when-legal as the walk-charge prefix-minimizer.

Phase 0: among admissible u>=0 walks with fixed (L,o), does taking
E at the first legal time stay on the pointwise min-a_k path, and
does that word's charge equal the certified survey DP? Not a halt
theorem, not a floor raise, not a uniform B/theta claim, and not a
reopen of the REFUTED Christoffel prefix-dominance slogan.

Dossier: docs/problems/juggler_cycle_walk_greedy.md.
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
    PARITY_REL_GUARD,
    git_commit,
    o_min_and_theta,
)
from research.juggler_sequence.cycle_walk_charge import (
    CERTIFIED_FLOOR,
    MU,
    STEP,
    U_TOL,
    charge_row,
    deficit_D,
)
from research.juggler_sequence.cycle_walk_mechanical import (
    CENSUS_L_MAX,
    CF_PROBE_LENGTHS,
    SURVEY_PATH,
    certified_log_n,
    charge_density,
    greedy_word,
    mechanical_average,
    prefix_min_odds,
    reachable_completable,
)

DATA_DIR = (
    DATA_ROOT
    / "cycle_walk_greedy"
)

SURVEY_REL_TOL = 1e-9
C_SPREAD_TOL = 2.5e-3

CLASS_GREEN = "WALK_GREEDY_GREEN"
CLASS_PARK = "WALK_GREEDY_PARK"
CLASS_CLOSED = "WALK_GREEDY_CLOSED"


def hug_word(length: int, odd_count: int) -> str:
    """Take E iff u>=1 and an even remains. No completability table.

    On feasible pairs (nonnegative terminal surplus) this cannot
    strand: when only evens remain, u = surplus + e_left >= e_left.
    """

    o_left = odd_count
    e_left = length - odd_count
    height = 0.0
    letters: list[str] = []
    for _ in range(length):
        if e_left > 0 and height >= 1.0 - U_TOL:
            height -= 1.0
            e_left -= 1
            letters.append("E")
        elif o_left > 0:
            height += MU
            o_left -= 1
            letters.append("O")
        else:
            raise RuntimeError(
                f"hug stranded L={length} o={odd_count} o_left={o_left} "
                f"e_left={e_left} u={height}"
            )
    return "".join(letters)


def hug_prefix_odds(length: int, odd_count: int) -> list[int]:
    """Odd-count after each prefix of the hug word, including a_0=0."""

    word = hug_word(length, odd_count)
    odds = [0]
    count = 0
    for letter in word:
        if letter == "O":
            count += 1
        odds.append(count)
    return odds


def hug_charge(
    length: int,
    odd_count: int,
    n: int,
    *,
    eta: float = 0.0,
    log_n: float | None = None,
) -> float:
    """Walk charge of the hug word, streamed in O(L)."""

    total = float(charge_row(np.zeros(1), n, eta, log_n=log_n)[0])
    o_left = odd_count
    e_left = length - odd_count
    height = 0.0
    for k in range(length):
        if e_left > 0 and height >= 1.0 - U_TOL:
            height -= 1.0
            e_left -= 1
        elif o_left > 0:
            height += MU
            o_left -= 1
        else:
            return -math.inf
        if k + 1 < length:
            total += float(
                charge_row(
                    np.array([max(height, 0.0)]), n, eta, log_n=log_n
                )[0]
            )
    return total


def census_small(l_max: int = CENSUS_L_MAX) -> dict[str, Any]:
    rows = []
    prefix_fail = []
    table_fail = []
    for length in range(1, l_max + 1):
        for odd_count in range(0, length + 1):
            if STEP * odd_count - length < -U_TOL:
                continue
            _reachable, completable = reachable_completable(length, odd_count)
            if 0 not in completable[0]:
                continue
            mins = prefix_min_odds(length, odd_count)
            hugged = hug_prefix_odds(length, odd_count)
            table = greedy_word(length, odd_count)
            simple = hug_word(length, odd_count)
            on_min = mins == hugged
            table_match = table == simple
            row = {
                "length": length,
                "odd_count": odd_count,
                "hug_is_prefix_min": on_min,
                "hug_equals_table_greedy": table_match,
            }
            rows.append(row)
            if not on_min:
                prefix_fail.append(
                    {
                        **row,
                        "min_a": mins,
                        "hug_a": hugged,
                    }
                )
            if not table_match:
                table_fail.append(
                    {
                        **row,
                        "hug": simple[:40],
                        "table": table[:40],
                    }
                )
    return {
        "l_max": l_max,
        "n_feasible": len(rows),
        "n_prefix_min": sum(1 for r in rows if r["hug_is_prefix_min"]),
        "n_table_match": sum(
            1 for r in rows if r["hug_equals_table_greedy"]
        ),
        "prefix_failures": prefix_fail[:12],
        "table_failures": table_fail[:12],
    }


def cf_length_checks(
    lengths: tuple[int, ...] = CF_PROBE_LENGTHS,
) -> list[dict[str, Any]]:
    rows = []
    for length in lengths:
        odd_count, _theta = o_min_and_theta(length)
        mins = prefix_min_odds(length, odd_count)
        hugged = hug_prefix_odds(length, odd_count)
        rows.append(
            {
                "length": length,
                "odd_count": odd_count,
                "hug_is_prefix_min": mins == hugged,
                "hug_equals_table_greedy": (
                    hug_word(length, odd_count)
                    == greedy_word(length, odd_count)
                ),
            }
        )
    return rows


def survey_hug_compare(
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
        hug_b = hug_charge(length, odd_count, n, log_n=log_n)
        rel = abs(hug_b - survey_b) / survey_b if survey_b else math.inf
        theta = float(item["theta"])
        rhs = const * hug_b * (1.0 + PARITY_REL_GUARD)
        rows.append(
            {
                "length": length,
                "odd_count": odd_count,
                "theta": theta,
                "survey_B": survey_b,
                "hug_B": hug_b,
                "relative_mismatch": rel,
                "C": charge_density(hug_b, length, log_n),
                "B_over_theta": hug_b / theta if theta else math.inf,
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


def classify(
    census: dict[str, Any],
    cf_rows: list[dict[str, Any]],
    survey: dict[str, Any],
    mechanical: dict[str, Any],
) -> dict[str, Any]:
    prefix_ok = (
        census["n_prefix_min"] == census["n_feasible"]
        and all(r["hug_is_prefix_min"] for r in cf_rows)
    )
    table_ok = (
        census["n_table_match"] == census["n_feasible"]
        and all(r["hug_equals_table_greedy"] for r in cf_rows)
    )
    survey_ok = survey["all_match"]
    leftover_c = [r["C"] for r in survey["rows"]]
    mech_c = mechanical["C"]
    c_rel = max(abs(c - mech_c) / mech_c for c in leftover_c)
    c_ok = c_rel < C_SPREAD_TOL
    if prefix_ok and table_ok and survey_ok and c_ok:
        return {
            "label": CLASS_GREEN,
            "reason": (
                "hug E-when-legal stays on the prefix-min a_k path "
                "for every feasible pair through L=24 and at 19,84,"
                "1054; its charge equals the certified survey DP; "
                "leftover C agrees with the mechanical average"
            ),
            "c_relative_spread_vs_mechanical": c_rel,
        }
    if prefix_ok and not survey_ok:
        return {
            "label": CLASS_PARK,
            "reason": (
                "hug is prefix-minimal on the census but its charge "
                "disagrees with the certified survey B"
            ),
            "c_relative_spread_vs_mechanical": c_rel,
        }
    if not prefix_ok:
        return {
            "label": CLASS_CLOSED,
            "reason": (
                "hug E-when-legal left the prefix-min path on a "
                "feasible pair"
            ),
            "c_relative_spread_vs_mechanical": c_rel,
        }
    return {
        "label": CLASS_PARK,
        "reason": (
            "prefix-min holds and survey matches, but leftover C "
            "is not yet the mechanical average"
        ),
        "c_relative_spread_vs_mechanical": c_rel,
    }


def probe_payload() -> dict[str, Any]:
    base = certified_log_n()
    census = census_small()
    cf_rows = cf_length_checks()
    survey = survey_hug_compare()
    mechanical = mechanical_average(log_n=base["log_n"], n=base["n"])
    return {
        "model": (
            "hug word: E iff u>=1 and evens remain; compared to the "
            "prefix-min a_k DP and to certified survey B at n e^{-D}"
        ),
        "certified_base": base,
        "census": {
            "l_max": census["l_max"],
            "n_feasible": census["n_feasible"],
            "n_prefix_min": census["n_prefix_min"],
            "n_table_match": census["n_table_match"],
            "prefix_failures": census["prefix_failures"],
            "table_failures": census["table_failures"],
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
        f"table {census['n_table_match']}/{census['n_feasible']}"
    )
    for row in payload["cf_lengths"]:
        print(
            f"L={row['length']} prefix_min={row['hug_is_prefix_min']} "
            f"table={row['hug_equals_table_greedy']}"
        )
    print(
        f"survey match={survey['all_match']} "
        f"max_rel={survey['max_relative_mismatch']:.3e} "
        f"uniform_ratio_false={survey['uniform_ratio_false']}"
    )
    print(
        f"mechanical C={mechanical['C']:.6f} "
        f"spread={payload['classification'].get('c_relative_spread_vs_mechanical')}"
    )
    print(payload["classification"]["label"])
    print(payload["classification"]["reason"])


if __name__ == "__main__":
    main()

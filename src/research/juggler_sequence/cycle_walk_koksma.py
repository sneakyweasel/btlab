"""Koksma / +1/L envelope for leftover hug charge.

Phase 0: does leftover hug C_L stay under C_*(n') + 1/L
(Denjoy-Koksma with Var(f)<1), or under the crude bound
1/(ln 3 ln n'), tightly enough to make the 18 kills DP-free?
Not a halt theorem, not a floor raise, not a uniform B/theta
claim, and not a reopen of the REFUTED Christoffel slogans.

Dossier: docs/problems/juggler_cycle_walk_koksma.md.
"""

from __future__ import annotations

from research.juggler_sequence.lean_paths import (
    DATA_ROOT,
)

import json
import math
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_finance import git_commit
from research.juggler_sequence.cycle_walk_charge import (
    CERTIFIED_FLOOR,
    STEP,
    deficit_D,
)
from research.juggler_sequence.cycle_walk_exchange import (
    GREEDY_SUMMARY,
    c_star_integral,
    rotation_average,
)
from research.juggler_sequence.cycle_walk_mechanical import SURVEY_PATH

DATA_DIR = (
    DATA_ROOT
    / "cycle_walk_koksma"
)

SEED_LENGTHS = (50508, 101016, 151524, 176251)
PLUS_ONE_TOL = 1e-12

CLASS_GREEN = "WALK_KOKSMA_GREEN"
CLASS_PARK = "WALK_KOKSMA_PARK"
CLASS_CLOSED = "WALK_KOKSMA_CLOSED"


def survey_koksma(
    survey_path: Path = SURVEY_PATH,
    n0: int = CERTIFIED_FLOOR,
) -> dict[str, Any]:
    survey = json.loads(survey_path.read_text(encoding="utf-8"))
    greedy = json.loads(GREEDY_SUMMARY.read_text(encoding="utf-8"))
    hug_c = {int(r["length"]): float(r["C"]) for r in greedy["survey_rows"]}
    n = int(survey["floor"]) + 1
    rows = []
    for item in survey["rows"]:
        length = int(item["length"])
        odd_count = int(item["odd_count"])
        log_n = math.log(n) - deficit_D(length, odd_count, n)
        star = c_star_integral(log_n)
        iet = rotation_average(length, n, log_n=log_n)
        c_hug = hug_c[length]
        surplus = STEP * odd_count - length
        inv_l = 1.0 / length
        excess_hug = c_hug - star["C"]
        excess_iet = iet["C"] - star["C"]
        rows.append(
            {
                "length": length,
                "odd_count": odd_count,
                "seed": length in SEED_LENGTHS,
                "log_n": log_n,
                "C_hug": c_hug,
                "C_iet": iet["C"],
                "C_star": star["C"],
                "C_bound": star["bound"],
                "surplus": surplus,
                "excess_hug": excess_hug,
                "excess_iet": excess_iet,
                "excess_hug_times_L": excess_hug * length,
                "excess_iet_times_L": excess_iet * length,
                "plus_1_over_L_hug": excess_hug <= inv_l + PLUS_ONE_TOL,
                "plus_1_over_L_iet": excess_iet <= inv_l + PLUS_ONE_TOL,
                "plus_half_over_L_hug": excess_hug
                <= 0.5 * inv_l + PLUS_ONE_TOL,
                "em_surplus_hug": excess_hug
                <= 0.5 * inv_l + surplus * inv_l + PLUS_ONE_TOL,
                "hug_below_bound": c_hug < star["bound"],
                "iet_minus_hug": iet["C"] - c_hug,
            }
        )
    hug_xl = [r["excess_hug_times_L"] for r in rows]
    iet_xl = [r["excess_iet_times_L"] for r in rows]
    return {
        "floor": survey["floor"],
        "n": n,
        "n_rows": len(rows),
        "n_plus1_hug": sum(1 for r in rows if r["plus_1_over_L_hug"]),
        "n_plus1_iet": sum(1 for r in rows if r["plus_1_over_L_iet"]),
        "n_plus_half_hug": sum(1 for r in rows if r["plus_half_over_L_hug"]),
        "n_em_surplus": sum(1 for r in rows if r["em_surplus_hug"]),
        "n_below_bound": sum(1 for r in rows if r["hug_below_bound"]),
        "max_excess_hug_times_L": max(hug_xl),
        "max_excess_iet_times_L": max(iet_xl),
        "max_seed_excess_hug_times_L": max(
            r["excess_hug_times_L"] for r in rows if r["seed"]
        ),
        "max_offset_excess_hug_times_L": max(
            r["excess_hug_times_L"] for r in rows if not r["seed"]
        ),
        "plus1_hug_failures": [
            r["length"] for r in rows if not r["plus_1_over_L_hug"]
        ],
        "plus1_iet_failures": [
            r["length"] for r in rows if not r["plus_1_over_L_iet"]
        ],
        "rows": rows,
    }


def classify(report: dict[str, Any]) -> dict[str, Any]:
    plus1 = report["n_plus1_hug"] == report["n_rows"]
    iet_plus1 = report["n_plus1_iet"] == report["n_rows"]
    salvage = report["n_em_surplus"] == report["n_rows"]
    crude = report["n_below_bound"] == report["n_rows"]
    if plus1 and crude:
        return {
            "label": CLASS_GREEN,
            "reason": (
                "C_hug <= C_* + 1/L on every leftover; Denjoy-Koksma "
                "with Var(f)<1 applies and the 18 kills are DP-free "
                "under that envelope"
            ),
        }
    if not plus1:
        return {
            "label": CLASS_CLOSED,
            "reason": (
                "C_hug <= C_* + 1/L fails on leftover offsets "
                f"{report['plus1_hug_failures']}; "
                f"max (C_hug-C_*)L = "
                f"{report['max_excess_hug_times_L']:.3f} "
                f"(seeds {report['max_seed_excess_hug_times_L']:.3f}, "
                f"IET max {report['max_excess_iet_times_L']:.3f}); "
                "the Koksma slogan is false and the crude bound was "
                "already a 19-row observation of walk-exchange"
            ),
            "iet_plus1": iet_plus1,
            "em_surplus": salvage,
            "crude": crude,
        }
    return {
        "label": CLASS_PARK,
        "reason": "plus 1/L holds but a usable kill envelope is not closed",
        "iet_plus1": iet_plus1,
        "em_surplus": salvage,
        "crude": crude,
    }


def probe_payload() -> dict[str, Any]:
    report = survey_koksma()
    return {
        "model": (
            "Koksma / Denjoy-Koksma test: leftover hug and IET-prefix "
            "C versus C_* + 1/L and the Euler-Maclaurin + surplus trial"
        ),
        "survey": {
            k: report[k]
            for k in (
                "floor",
                "n",
                "n_rows",
                "n_plus1_hug",
                "n_plus1_iet",
                "n_plus_half_hug",
                "n_em_surplus",
                "n_below_bound",
                "max_excess_hug_times_L",
                "max_excess_iet_times_L",
                "max_seed_excess_hug_times_L",
                "max_offset_excess_hug_times_L",
                "plus1_hug_failures",
                "plus1_iet_failures",
            )
        },
        "rows": report["rows"],
        "classification": classify(report),
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
    survey = payload["survey"]
    print(
        f"plus1 hug={survey['n_plus1_hug']}/{survey['n_rows']} "
        f"iet={survey['n_plus1_iet']}/{survey['n_rows']} "
        f"half={survey['n_plus_half_hug']} "
        f"em+surplus={survey['n_em_surplus']} "
        f"crude={survey['n_below_bound']}"
    )
    print(
        f"max (C-C*)L hug={survey['max_excess_hug_times_L']:.3f} "
        f"iet={survey['max_excess_iet_times_L']:.3f} "
        f"seed={survey['max_seed_excess_hug_times_L']:.3f} "
        f"offset={survey['max_offset_excess_hug_times_L']:.3f}"
    )
    print(f"plus1 hug fail {survey['plus1_hug_failures']}")
    print(f"plus1 iet fail {survey['plus1_iet_failures']}")
    print(payload["classification"]["label"])
    print(payload["classification"]["reason"])


if __name__ == "__main__":
    main()

"""Affine n-gap diagnostic: readings of the merge surviving sentence.

The Paper A x Paper B merge left an n-dependent lower bound on
|3^o - 2^L| along F1/F2/F3. This Phase 0 classifies every reading
of that sentence against Baker dominance and the existing CycleMin
identities. It is not a leftover-killer, not a Baker-constant
reimport, not a floor raise, and not a fan-minimum successor.

Dossier: docs/problems/juggler_cycle_affine_n_gap.md.
"""

from __future__ import annotations

from research.juggler_sequence.lean_paths import (
    DATA_ROOT,
)

import json
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_finance import git_commit, o_min_and_theta
from research.juggler_sequence.cycle_gap_baker import n_max_from_theta
from research.juggler_sequence.cycle_inhomogeneous_log import lambda_from_theta

DATA_DIR = (
    DATA_ROOT
    / "cycle_affine_n_gap"
)
COMPETITION_SUMMARY = (
    DATA_DIR.parent / "cycle_walk_competition" / "summary.json"
)

LSTAR, OSTAR = 25781, 16266
LSTEP, OSTEP = 1054, 665

NINETEEN_GAP = 3**12 - 2**19  # 7153
NINETEEN_O = 12
WEAKENING = 0.999

CLASS_CLOSED = "AFFINE_N_GAP_CLOSED"
CLASS_NEW_FORM = "AFFINE_N_GAP_NEW_FORM"

SEEDS: tuple[dict[str, Any], ...] = (
    {"length": 19, "family": "dominance_lock", "a": None, "b": None},
    {"length": 25781, "family": "F1", "a": 1, "b": 0},
    {"length": 50508, "family": "F2", "a": 2, "b": -1},
    {"length": 76289, "family": "F3", "a": 3, "b": -1},
    {"length": 478245, "family": "fanA_k1", "a": None, "b": None},
)


def lattice_point(a: int, b: int) -> tuple[int, int]:
    return a * LSTAR + b * LSTEP, a * OSTAR + b * OSTEP


def identity_table() -> list[dict[str, Any]]:
    """Cycle-forced identities that could involve n or the gap G."""

    return [
        {
            "id": "cycleMin_finance",
            "formula": "n log n * G <= L * 3^o",
            "uses_n": True,
            "kind": "upper_bound_on_G",
            "tag": "REPARAMETERIZATION",
            "note": (
                "the n-dependent bound in contrapositive; an upper "
                "bound on G, not a lower bound"
            ),
        },
        {
            "id": "global_defect_identity",
            "formula": "n^{3^o} = T_w(n)^{2^L} + Delta_w(n)",
            "uses_n": True,
            "kind": "return_identity",
            "tag": "REPARAMETERIZATION",
            "note": "the global defect; on a return it becomes G log n",
        },
        {
            "id": "image_eq_start_defectRatio",
            "formula": "log R = G log n on a return",
            "uses_n": True,
            "kind": "return_identity",
            "tag": "REPARAMETERIZATION",
            "note": "the only exact n-log form; not a lower bound on G",
        },
        {
            "id": "exponent_budget",
            "formula": "sum (a_i log 3 - (a_i+r_i) log 2) = Lambda",
            "uses_n": False,
            "kind": "homogeneous_two_log",
            "tag": "REPARAMETERIZATION",
            "note": "no n; Lambda = o log 3 - L log 2",
        },
        {
            "id": "inhomogeneous_p_plus_lambda",
            "formula": "|p + Lambda| >= 1 - |Lambda| for p != 0",
            "uses_n": False,
            "kind": "integer_shift",
            "tag": "REFUTED",
            "note": "juggler_inhomogeneous_ww_beats_finance; not log n",
        },
        {
            "id": "height_position_finance",
            "formula": "stronger upper bounds on theta from valley heights",
            "uses_n": True,
            "kind": "upper_bound_on_theta",
            "tag": "REPARAMETERIZATION",
            "note": "explored; still an upper bound, not a gap lower bound",
        },
    ]


def reading_table() -> list[dict[str, Any]]:
    return [
        {
            "id": "R1",
            "title": "universal linear-forms lower bound on G",
            "status": "REFUTED",
            "discharge": "juggler_cycle_gap_baker; Baker dominance",
        },
        {
            "id": "R2",
            "title": "finance contrapositive (n_max from exact theta)",
            "status": "KNOWN",
            "discharge": "cycleMin_finance; floor campaigns PARK",
        },
        {
            "id": "R3",
            "title": "new cycle-forced form using log n, not G log n",
            "status": "REPARAMETERIZATION",
            "discharge": "identity table: every n-form is finance or G log n",
        },
        {
            "id": "R4",
            "title": "defect-sum n-power L/n^{1+delta}",
            "status": "REPARAMETERIZATION",
            "discharge": "walk-charge structure; program terminal",
        },
        {
            "id": "R5",
            "title": "lattice binary recurrence |A alpha^b - B beta^b|",
            "status": "REFUTED",
            "discharge": (
                "cannot beat exact theta at a known point; uniform "
                "family bounds are the imported Wu-Wang/Rhin shape"
            ),
        },
    ]


def dominance_nineteen() -> dict[str, Any]:
    """Any correct delta <= G produces n_max at least as large."""

    pow3 = 3**NINETEEN_O
    theta = NINETEEN_GAP / pow3
    weaker_theta = (NINETEEN_GAP - 1) / pow3
    half_theta = (NINETEEN_GAP // 2) / pow3
    exact_n_max = n_max_from_theta(19, theta)
    weaker_n_max = n_max_from_theta(19, weaker_theta)
    half_n_max = n_max_from_theta(19, half_theta)
    return {
        "length": 19,
        "odd_count": NINETEEN_O,
        "gap": NINETEEN_GAP,
        "theta": theta,
        "n_max_exact": exact_n_max,
        "weaker_gap": NINETEEN_GAP - 1,
        "n_max_weaker": weaker_n_max,
        "half_gap": NINETEEN_GAP // 2,
        "n_max_half": half_n_max,
        "dominance_holds": weaker_n_max >= exact_n_max
        and half_n_max >= exact_n_max,
        "half_gap_strictly_worse": half_n_max > exact_n_max,
        "theta_depends_only_on_L_o": True,
    }


def seed_row(
    spec: dict[str, Any],
    stored: dict[int, dict[str, Any]],
) -> dict[str, Any]:
    length = int(spec["length"])
    if length in stored:
        odd = int(stored[length]["odd_count"])
        theta = float(stored[length]["theta"])
        n_star = stored[length].get("n_star")
        source = "cycle_walk_competition"
    else:
        odd, theta = o_min_and_theta(length)
        n_star = None
        source = "o_min_and_theta"
    a, b = spec["a"], spec["b"]
    lattice_ok = True
    if a is not None and b is not None:
        L, o = lattice_point(int(a), int(b))
        lattice_ok = L == length and o == odd
    n_max = n_max_from_theta(length, theta)
    weaker_n_max = n_max_from_theta(length, theta * WEAKENING)
    lam = lambda_from_theta(theta)
    return {
        "length": length,
        "odd_count": odd,
        "family": spec["family"],
        "a": a,
        "b": b,
        "theta": theta,
        "lambda": lam,
        "n_max_exact": n_max,
        "n_max_weaker_theta": weaker_n_max,
        "dominance_holds": weaker_n_max >= n_max,
        "theta_depends_only_on_L_o": True,
        "lattice_matches": lattice_ok,
        "n_star_competition": n_star,
        "theta_source": source,
    }


def classify(
    identities: list[dict[str, Any]],
    readings: list[dict[str, Any]],
    rows: list[dict[str, Any]],
    nineteen: dict[str, Any],
) -> dict[str, Any]:
    closed_tags = {"REPARAMETERIZATION", "KNOWN", "REFUTED"}
    identities_closed = all(i["tag"] in closed_tags for i in identities)
    no_new_form = not any(i["tag"] == "NEW" for i in identities)
    readings_closed = all(r["status"] in closed_tags for r in readings)
    dominance_ok = (
        nineteen["dominance_holds"]
        and nineteen["half_gap_strictly_worse"]
        and all(r["dominance_holds"] for r in rows)
    )
    lattice_ok = all(r["lattice_matches"] for r in rows)
    theta_ok = all(r["theta_depends_only_on_L_o"] for r in rows)
    if (
        identities_closed
        and no_new_form
        and readings_closed
        and dominance_ok
        and lattice_ok
        and theta_ok
    ):
        return {
            "label": CLASS_CLOSED,
            "decision": "CLOSE",
            "reason": (
                "every reading of the merge n-dependent gap is "
                "KNOWN, REPARAMETERIZATION, or already REFUTED; "
                "Baker dominance holds on L=19 and the affine "
                "seeds; no cycle-forced form uses log n except "
                "G log n / finance"
            ),
            "identities_closed": True,
            "no_new_form": True,
            "readings_closed": True,
            "dominance_holds": True,
            "lattice_matches": True,
        }
    return {
        "label": CLASS_NEW_FORM,
        "decision": "PROMOTE",
        "reason": "a reading or identity escaped the closed list",
        "identities_closed": identities_closed,
        "no_new_form": no_new_form,
        "readings_closed": readings_closed,
        "dominance_holds": dominance_ok,
        "lattice_matches": lattice_ok,
    }


def probe_payload() -> dict[str, Any]:
    stored_rows = json.loads(COMPETITION_SUMMARY.read_text(encoding="utf-8"))[
        "rows"
    ]
    stored = {int(r["length"]): r for r in stored_rows}
    identities = identity_table()
    readings = reading_table()
    nineteen = dominance_nineteen()
    rows = [seed_row(spec, stored) for spec in SEEDS]
    return {
        "model": (
            "Does any reading of an n-dependent lower bound on "
            "|3^o-2^L| along F1/F2/F3 escape Baker dominance, "
            "or does a cycle-forced form use log n without being "
            "G log n?"
        ),
        "lattice": {
            "v_star": [LSTAR, OSTAR],
            "v_step": [LSTEP, OSTEP],
            "unimodular": LSTAR * OSTEP - LSTEP * OSTAR,
            "F1": list(lattice_point(1, 0)),
            "F2": list(lattice_point(2, -1)),
            "F3": list(lattice_point(3, -1)),
        },
        "identities": identities,
        "readings": readings,
        "dominance_nineteen": nineteen,
        "seeds": rows,
        "classification": classify(identities, readings, rows, nineteen),
        "not_a_halt_theorem": True,
        "no_cycle_all_lengths": False,
        "no_new_period_bound": True,
        "no_baker_reopen": True,
        "no_floor_raise": True,
        "no_paper_a_edit": True,
        "no_fan_minimum_successor": True,
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
    d19 = payload["dominance_nineteen"]
    print(
        f"L=19 G={d19['gap']} n_max={d19['n_max_exact']} "
        f"weaker={d19['n_max_weaker']} "
        f"dominance={d19['dominance_holds']}"
    )
    for row in payload["seeds"]:
        print(
            f"L={row['length']} {row['family']} o={row['odd_count']} "
            f"theta={row['theta']:.6e} n_max={row['n_max_exact']} "
            f"dominance={row['dominance_holds']} "
            f"lattice={row['lattice_matches']}"
        )
    print(payload["classification"]["label"])
    print(payload["classification"]["reason"])


if __name__ == "__main__":
    main()

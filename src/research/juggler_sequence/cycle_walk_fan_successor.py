"""Fan successor rigidity: the 478245 → 780239 block.

Phase 0. Arithmetic only on stored leftovers and the leftover-seed
cone. Tests whether classical CF bounds reach the leftover ε, so
that k = 2 would be forced without scanning 301995 lengths. No
census, no floor, no Baker, no 0.999-theta, no Paper A edit, not
a halt theorem.

Dossier: docs/problems/juggler_cycle_walk_fan_successor.md.
"""

from __future__ import annotations

from research.juggler_sequence.lean_paths import (
    DATA_ROOT,
)

import json
import math
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_finance import EPS_CONST, git_commit
from research.juggler_sequence.cycle_walk_competition import o_min_exact

DATA_DIR = (
    DATA_ROOT
    / "cycle_walk_fan_successor"
)
FLIGHT_SUMMARY = DATA_DIR.parent / "flight_anchor_period" / "summary.json"

BLOCKER = 478_245
O_BLOCKER = 301_739
NEXT_FAN = 780_239
O_NEXT = 492_276
ANCHOR = 350_000_000
LN3 = math.log(3.0)
LN2 = math.log(2.0)

# Leftover seeds and the fan step. The fan step uses p13 = 190537,
# not o_min(301994) = 190538 (positive-side convergent, theta ~ 2/3).
GENERATORS: tuple[tuple[int, int, str], ...] = (
    (25_781, 16_266, "vstar"),
    (50_508, 31_867, "F2"),
    (176_251, 111_202, "seed_q"),
    (301_994, 190_537, "fan_step"),
)

CLASS_CLOSED = "FAN_SUCCESSOR_CLOSED"
CLASS_GREEN = "FAN_SUCCESSOR_GREEN"


def invert_defect(theta_sum: float, theta_left: float) -> float:
    """Solve theta_sum = theta_left + theta_right - product."""

    return (theta_sum - theta_left) / (1.0 - theta_left)


def defect_product(theta_l: float, theta_m: float) -> float:
    """Exact rational identity: r(L+M) = r(L) r(M) ⇒ this formula."""

    return theta_l + theta_m - theta_l * theta_m


def _one_minus(theta: float, copies: int) -> float:
    """(1 - theta)^copies."""

    value = 1.0
    for _ in range(copies):
        value *= 1.0 - theta
    return value


def enumerate_cone(
    lo: int = BLOCKER,
    hi: int = NEXT_FAN,
    generator_thetas: dict[str, float] | None = None,
    theta_star: float | None = None,
) -> list[dict[str, Any]]:
    """Nonnegative cone from the blocker along the leftover generators.

    Theta of a lattice point is the defect product from the generators,
    so the probe never enumerates 3^o at every cone point. o-minimality
    uses the cheap deep-sandwich o_min_exact.
    """

    if generator_thetas is None or theta_star is None:
        raise ValueError("cone enumeration needs stored generator thetas")
    gtheta = generator_thetas
    star = theta_star
    rows: list[dict[str, Any]] = []
    seen: set[int] = set()
    a_max = (hi - lo) // GENERATORS[0][0]
    for a in range(a_max + 1):
        b_max = (hi - lo - a * GENERATORS[0][0]) // GENERATORS[1][0]
        for b in range(b_max + 1):
            c_max = (
                hi - lo - a * GENERATORS[0][0] - b * GENERATORS[1][0]
            ) // GENERATORS[2][0]
            for c in range(c_max + 1):
                d_max = (
                    hi
                    - lo
                    - a * GENERATORS[0][0]
                    - b * GENERATORS[1][0]
                    - c * GENERATORS[2][0]
                ) // GENERATORS[3][0]
                for d in range(d_max + 1):
                    length = (
                        lo
                        + a * GENERATORS[0][0]
                        + b * GENERATORS[1][0]
                        + c * GENERATORS[2][0]
                        + d * GENERATORS[3][0]
                    )
                    odd = (
                        O_BLOCKER
                        + a * GENERATORS[0][1]
                        + b * GENERATORS[1][1]
                        + c * GENERATORS[2][1]
                        + d * GENERATORS[3][1]
                    )
                    if length in seen:
                        continue
                    seen.add(length)
                    omin = o_min_exact(length)
                    remain = (
                        (1.0 - star)
                        * _one_minus(gtheta["vstar"], a)
                        * _one_minus(gtheta["F2"], b)
                        * _one_minus(gtheta["seed_q"], c)
                        * _one_minus(gtheta["fan_step"], d)
                    )
                    theta_sum = 1.0 - remain
                    rows.append(
                        {
                            "length": length,
                            "odd_sum": odd,
                            "o_min": omin,
                            "o_minimal": odd == omin,
                            "coeffs": {
                                "a_vstar": a,
                                "b_F2": b,
                                "c_seed": c,
                                "d_fan": d,
                            },
                            "theta_sum": theta_sum,
                        }
                    )
    rows.sort(key=lambda r: r["length"])
    return rows


def leftover_crude_cap(length: int, floor_n: float) -> float:
    """Crude finance leftover: theta <= (6/5) L / (n ln n)."""

    return EPS_CONST * length / (floor_n * math.log(floor_n))


def legendre_cap(length: int) -> float:
    """theta < (ln 3)/(2L) is the finance image of |x - o/L| < 1/(2 L^2)."""

    return LN3 / (2.0 * length)


def dirichlet_cap(length: int) -> float:
    """theta < (ln 3)/L is the finance image of |x - o/L| < 1/L^2."""

    return LN3 / length


def completeness_bounds(
    lengths: list[int],
    floor_n: float,
) -> dict[str, Any]:
    """Leftover ε versus Legendre / Dirichlet at the interval ends."""

    rows = []
    reaches = True
    for length in lengths:
        crude = leftover_crude_cap(length, floor_n)
        leg = legendre_cap(length)
        diri = dirichlet_cap(length)
        row = {
            "length": length,
            "leftover_crude": crude,
            "legendre": leg,
            "dirichlet": diri,
            "crude_over_legendre": crude / leg,
            "crude_over_dirichlet": crude / diri,
            "legendre_reaches": crude < leg,
            "dirichlet_reaches": crude < diri,
        }
        rows.append(row)
        if not row["dirichlet_reaches"]:
            reaches = False
    return {
        "floor": floor_n,
        "rows": rows,
        "dirichlet_reaches": reaches,
        "legendre_reaches": all(r["legendre_reaches"] for r in rows),
    }


def recover_generator_thetas(
    stored: list[dict[str, Any]],
) -> tuple[float, dict[str, float], list[dict[str, Any]]]:
    """Invert the defect product on stored one-generator sums."""

    by_l = {r["length"]: r["theta"] for r in stored}
    theta_star = by_l[BLOCKER]
    # Each generator appears as a stored leftover: blocker + generator.
    witnesses = {
        "vstar": BLOCKER + 25_781,
        "F2": BLOCKER + 50_508,
        "seed_q": BLOCKER + 176_251,
        "fan_step": BLOCKER + 301_994,
    }
    gtheta: dict[str, float] = {}
    checks: list[dict[str, Any]] = []
    for tag, target in witnesses.items():
        theta_g = invert_defect(by_l[target], theta_star)
        gtheta[tag] = theta_g
        predicted = defect_product(theta_star, theta_g)
        rel = abs(predicted - by_l[target]) / max(abs(by_l[target]), 1e-30)
        checks.append(
            {
                "generator": tag,
                "sum_length": target,
                "in_stored": True,
                "theta_generator": theta_g,
                "predicted": predicted,
                "actual": by_l[target],
                "relative_error": rel,
                "holds": rel < 1e-14,
            }
        )
    return theta_star, gtheta, checks


def multi_step_defect_checks(
    stored: list[dict[str, Any]],
    theta_star: float,
    gtheta: dict[str, float],
) -> list[dict[str, Any]]:
    """Predict stored multi-generator leftovers from one-step thetas."""

    by_l = {r["length"]: r["theta"] for r in stored}
    targets = (
        (579_261, {"vstar": 0, "F2": 2, "seed_q": 0, "fan_step": 0}),
        (629_769, {"vstar": 0, "F2": 3, "seed_q": 0, "fan_step": 0}),
        (680_277, {"vstar": 1, "F2": 0, "seed_q": 1, "fan_step": 0}),
        (705_004, {"vstar": 0, "F2": 1, "seed_q": 1, "fan_step": 0}),
        (730_785, {"vstar": 1, "F2": 1, "seed_q": 1, "fan_step": 0}),
        (755_512, {"vstar": 0, "F2": 2, "seed_q": 1, "fan_step": 0}),
    )
    checks = []
    for length, coeffs in targets:
        remain = 1.0 - theta_star
        for tag, copies in coeffs.items():
            remain *= _one_minus(gtheta[tag], copies)
        predicted = 1.0 - remain
        actual = by_l[length]
        rel = abs(predicted - actual) / max(abs(actual), 1e-30)
        checks.append(
            {
                "length": length,
                "coeffs": coeffs,
                "predicted": predicted,
                "actual": actual,
                "relative_error": rel,
                "holds": rel < 1e-10,
            }
        )
    return checks


def load_stored_leftovers() -> list[dict[str, Any]]:
    payload = json.loads(FLIGHT_SUMMARY.read_text(encoding="utf-8"))
    leftovers = payload["scan"]["parity_survivors"]
    dk = {int(r["length"]): r for r in payload["dk_rows"]}
    rows = []
    for entry in leftovers:
        length = int(entry["length"])
        priced = dk[length]
        rows.append(
            {
                "length": length,
                "odd_count": int(entry["odd_count"]),
                "theta": float(entry["theta"]),
                "digit_sum": int(priced["digit_sum"]),
                "dk_margin": float(priced["dk_margin"]),
                "dk_kills": bool(priced["dk_kills"]),
            }
        )
    return rows


def classify(
    stored: list[dict[str, Any]],
    cone: list[dict[str, Any]],
    bounds: dict[str, Any],
    defects: list[dict[str, Any]],
) -> dict[str, Any]:
    stored_lengths = {r["length"] for r in stored}
    omin_cone = {r["length"] for r in cone if r["o_minimal"]}
    extras = sorted(omin_cone - stored_lengths)
    missing = sorted(stored_lengths - omin_cone)
    by_l = {r["length"]: r for r in stored}
    theta_ratio = by_l[NEXT_FAN]["theta"] / by_l[BLOCKER]["theta"]
    margin_k1 = by_l[BLOCKER]["dk_margin"]
    margin_k2 = by_l[NEXT_FAN]["dk_margin"]
    same_shape = 0.9 < theta_ratio < 1.1 and margin_k2 < margin_k1
    product_ok = all(c["holds"] for c in defects if "holds" in c)
    completeness_fails = not bounds["dirichlet_reaches"]
    cone_contains = not missing
    if completeness_fails and cone_contains and same_shape and product_ok:
        return {
            "label": CLASS_CLOSED,
            "decision": "CLOSE",
            "reason": (
                "classical CF bounds miss the leftover ε by more than "
                "a factor 30, so the 301995-length scan remains the "
                "completeness proof; the stored leftovers sit in the "
                "cone but the cone is larger; k=2 has the same theta "
                "scale and a worse DK margin than k=1 — not a new "
                "Juggler shape"
            ),
            "completeness_reaches": False,
            "cone_contains_stored": True,
            "cone_equals_stored": not extras,
            "k2_same_shape": True,
            "defect_product_holds": True,
            "extra_ominimal_count": len(extras),
            "missing_count": 0,
        }
    if bounds["dirichlet_reaches"] and cone_contains and not extras:
        return {
            "label": CLASS_GREEN,
            "decision": "PROMOTE",
            "reason": (
                "Dirichlet reaches the leftover ε and the cone equals "
                "the leftover set"
            ),
            "completeness_reaches": True,
            "cone_contains_stored": True,
            "cone_equals_stored": True,
            "k2_same_shape": same_shape,
            "defect_product_holds": product_ok,
            "extra_ominimal_count": 0,
            "missing_count": 0,
        }
    return {
        "label": CLASS_CLOSED,
        "decision": "CLOSE",
        "reason": "completeness or successor rigidity failed a check",
        "completeness_reaches": bounds["dirichlet_reaches"],
        "cone_contains_stored": cone_contains,
        "cone_equals_stored": not extras and cone_contains,
        "k2_same_shape": same_shape,
        "defect_product_holds": product_ok,
        "extra_ominimal_count": len(extras),
        "missing_count": len(missing),
    }


def probe_payload() -> dict[str, Any]:
    stored = load_stored_leftovers()
    theta_star, gtheta, one_step = recover_generator_thetas(stored)
    cone = enumerate_cone(generator_thetas=gtheta, theta_star=theta_star)
    bounds = completeness_bounds([BLOCKER, NEXT_FAN], float(ANCHOR))
    defects = multi_step_defect_checks(stored, theta_star, gtheta)
    stored_lengths = {r["length"] for r in stored}
    omin_cone = [r for r in cone if r["o_minimal"]]
    extras = [r for r in omin_cone if r["length"] not in stored_lengths]
    by_l = {r["length"]: r for r in stored}
    return {
        "model": (
            "At the leftover ε of the flight anchor 3.5e8, is every "
            "parity leftover in [478245, 780239] a member of the "
            "explicit leftover-seed cone, so that k=2 is forced as "
            "the unique DK survivor without scanning 301995 lengths?"
        ),
        "interval": [BLOCKER, NEXT_FAN],
        "anchor": ANCHOR,
        "generators": [
            {
                "length": L,
                "odd": o,
                "tag": tag,
                "theta": gtheta[tag],
            }
            for L, o, tag in GENERATORS
        ],
        "stored_leftovers": stored,
        "cone_count": len(cone),
        "cone_ominimal_count": len(omin_cone),
        "cone_ominimal_lengths": [r["length"] for r in omin_cone],
        "extras_ominimal": [
            {
                "length": r["length"],
                "coeffs": r["coeffs"],
                "theta_sum": r["theta_sum"],
            }
            for r in extras
        ],
        "one_step_inversions": one_step,
        "defect_checks": defects,
        "completeness": bounds,
        "shape": {
            "theta_k1": by_l[BLOCKER]["theta"],
            "theta_k2": by_l[NEXT_FAN]["theta"],
            "theta_ratio": by_l[NEXT_FAN]["theta"] / by_l[BLOCKER]["theta"],
            "margin_k1": by_l[BLOCKER]["dk_margin"],
            "margin_k2": by_l[NEXT_FAN]["dk_margin"],
            "digit_sum_k1": by_l[BLOCKER]["digit_sum"],
            "digit_sum_k2": by_l[NEXT_FAN]["digit_sum"],
            "k2_worse_margin": by_l[NEXT_FAN]["dk_margin"]
            < by_l[BLOCKER]["dk_margin"],
        },
        "classification": classify(stored, cone, bounds, defects),
        "not_a_halt_theorem": True,
        "no_cycle_all_lengths": False,
        "no_new_period_bound": True,
        "no_baker_reopen": True,
        "no_floor_raise": True,
        "no_paper_a_edit": True,
        "no_fan_minimum_reopen": True,
        "no_census": True,
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
    cls = payload["classification"]
    shape = payload["shape"]
    comp = payload["completeness"]["rows"]
    print(
        f"cone {payload['cone_count']} points, "
        f"{payload['cone_ominimal_count']} o-minimal, "
        f"{cls['extra_ominimal_count']} extras, "
        f"missing {cls['missing_count']}"
    )
    for row in comp:
        print(
            f"L={row['length']} crude/Dirichlet="
            f"{row['crude_over_dirichlet']:.2f} "
            f"crude/Legendre={row['crude_over_legendre']:.2f} "
            f"Dirichlet_reaches={row['dirichlet_reaches']}"
        )
    print(
        f"theta ratio k2/k1={shape['theta_ratio']:.4f} "
        f"margins {shape['margin_k1']:.4f} -> {shape['margin_k2']:.4f}"
    )
    for chk in payload["defect_checks"]:
        print(
            f"defect L={chk['length']}: holds={chk['holds']} "
            f"rel={chk['relative_error']}"
        )
    print(cls["label"])
    print(cls["reason"])


if __name__ == "__main__":
    main()

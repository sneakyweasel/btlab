"""Floor-defect / congruence accumulation after exponent cancellation.

Phase 0 only: each seam is an exact remainder cell. Composing them
around a cycle leaves a residual after the main 3^o versus 2^L
powers cancel. This module records that the residual is the global
defect, that the cyclic remainder sum is an identity, that cycle-
scale defects are free residues, and that cell positions are
unrestricted. Floors on a genuine return are cycleMin_finance.

Not a finance leftover-killer, not a floor raise, not a new modulus
census, not a halt theorem, and not a claim that every positive
integer reaches 1.

Dossier: docs/problems/juggler_cycle_defect_congruence.md.
"""

from __future__ import annotations

import json
from typing import Any

from research.juggler_sequence.cycle_finance import DATA_DIR, PUBLISHED_FLOOR
from research.juggler_sequence.cycle_gap_baker import exact_gap
from research.juggler_sequence.cycle_mod_closure import MODULI, defect_width_collapses
from research.juggler_sequence.cycle_remainder_finance import cell_record
from research.juggler_sequence.cycle_rounding import path_identity
from research.juggler_sequence.global_defect import (
    envelope_slack,
    follows_itinerary,
    global_defect,
    image_after,
    local_defect,
    odd_count,
)
from research.juggler_sequence.power_itineraries import floor_power

CONGRUENCE_DIR = DATA_DIR / "defect_congruence"
START = PUBLISHED_FLOOR + 1

CLASS_CLOSED = "DEFECT_CONGRUENCE_CLOSED"
CLASS_GREEN = "DEFECT_CONGRUENCE_GREEN"
CLASS_PARK = "DEFECT_CONGRUENCE_PARK"

NEAR_TOP_WITNESS = 1_016_445
DEMO_START = 365
DEMO_WORD = "OOE"
PEAK_ODD = 13
RESIDUE_LO = 13
RESIDUE_HI = 400
RESIDUE_MODULI = (3, 8, 9, 16)
LEFTOVER_LENGTHS = (19, 84)

ARCHIVED = (
    "global_defect_identity",
    "global_defect_append",
    "image_eq_start_defectRatio",
    "cycle_remainder_balance",
    "cycle_not_localsTight",
    "peak_diophantine_slack",
    "cycleMin_finance",
    "cycle_itinerary_formally_expanding",
)


def seam_cell(v: int) -> dict[str, Any]:
    """Exact remainder cell of one Juggler step."""

    if v < 1:
        raise ValueError("seam_cell requires v >= 1")
    odd = v % 2 == 1
    power = v * v * v if odd else v
    image = floor_power(v)
    lo = image * image
    hi = (image + 1) * (image + 1)
    rho = power - lo
    return {
        "v": v,
        "odd": odd,
        "image": image,
        "lo": lo,
        "hi": hi,
        "rho": rho,
        "holds": lo <= power < hi,
        "rho_eq_local": rho == local_defect(v),
    }


def composed_residual(n: int, word: str) -> dict[str, Any]:
    """Weighted composition of the seam remainders is the global defect."""

    if not follows_itinerary(n, word):
        raise ValueError(f"{n} does not follow {word}")
    delta = global_defect(n, word)
    slack = envelope_slack(n, word)
    end = image_after(n, word)
    odds = odd_count(word)
    length = len(word)
    return {
        "n": n,
        "word": word,
        "end": end,
        "o": odds,
        "L": length,
        "delta": delta,
        "slack": slack,
        "identity": delta == slack,
        "cycle_formula_if_return": end == n,
        "would_be_cycle_residual": (
            n ** (3**odds) - n ** (2**length) if end == n else None
        ),
    }


def peak_pair_slack(x: int) -> dict[str, Any]:
    """One-even peak pair: x^3 - p^4 = 2 ε p^2 + ε^2 + δ."""

    if x < 1 or x % 2 == 0:
        raise ValueError("peak_pair_slack requires an odd start")
    peak = floor_power(x)
    if peak % 2 == 1:
        raise ValueError("peak_pair_slack requires an even image")
    landing = floor_power(peak)
    delta = x**3 - peak * peak
    eps = peak - landing * landing
    slack = x**3 - landing**4
    compose = 2 * eps * landing * landing + eps * eps + delta
    return {
        "x": x,
        "peak": peak,
        "landing": landing,
        "delta": delta,
        "eps": eps,
        "slack": slack,
        "compose": compose,
        "is_envelope_slack": slack == compose,
    }


def cyclic_balance_identity(states: list[int]) -> dict[str, Any]:
    """Path remainder sum equals the odd/even gaps plus start^2 - end^2."""

    rec = path_identity(states)
    correction = states[0] ** 2 - states[-1] ** 2
    return {
        "start": states[0],
        "end": states[-1],
        "length": len(states) - 1,
        "rho_sum": rec["rho_sum"],
        "even_gaps": rec["even_gaps"],
        "odd_gaps": rec["odd_gaps"],
        "closure_correction": rec["closure_correction"],
        "balance_off_cycle": rec["balance_off_cycle"],
        "is_identity": rec["balance_off_cycle"] == correction,
        "would_vanish_on_a_cycle": correction == 0,
    }


def residue_occupancy(
    *,
    lo: int = RESIDUE_LO,
    hi: int = RESIDUE_HI,
    word: str = DEMO_WORD,
) -> dict[str, Any]:
    """Local first-step remainders occupy several residues, not one class."""

    occupied: dict[int, set[int]] = {m: set() for m in RESIDUE_MODULI}
    checked = 0
    for n in range(lo, hi):
        if n % 2 == 0 or not follows_itinerary(n, word):
            continue
        checked += 1
        rho = local_defect(n)
        for m in RESIDUE_MODULI:
            occupied[m].add(rho % m)
    counts = {str(m): len(occupied[m]) for m in RESIDUE_MODULI}
    return {
        "lo": lo,
        "hi": hi,
        "word": word,
        "checked": checked,
        "occupied_counts": counts,
        "occupied": {str(m): sorted(occupied[m]) for m in RESIDUE_MODULI},
        "single_class": all(count == 1 for count in counts.values()),
    }


def cycle_scale_defects_free() -> dict[str, Any]:
    """At CycleMin scale 2Y+1 > m, so δ,η are free residues."""

    rows = [
        {
            "m": m,
            "collapses": defect_width_collapses(m, START),
            "width": 2 * START + 1,
        }
        for m in MODULI
    ]
    return {
        "y_min": START,
        "width": 2 * START + 1,
        "moduli": rows,
        "any_collapse": any(row["collapses"] for row in rows),
    }


def leftover_residuals() -> list[dict[str, Any]]:
    """After cancellation the leftover is the exact finance gap, not a modulus."""

    rows: list[dict[str, Any]] = []
    for length in LEFTOVER_LENGTHS:
        gap = exact_gap(length)
        rows.append(
            {
                **gap,
                "cycle_residual": "n^{2^L} (n^{3^o - 2^L} - 1)",
                "is_congruence": False,
                "is_finance_gap": True,
                "formally_expanding": 2**length < 3 ** gap["o"],
            }
        )
    return rows


def classify(payload: dict[str, Any]) -> dict[str, Any]:
    composed = payload["composed"]
    peak = payload["peak_pair"]
    balance = payload["balance"]
    residues = payload["residues"]
    free = payload["cycle_scale"]
    leftovers = payload["leftovers"]
    near = payload["near_top"]
    identity = bool(composed["identity"])
    slack_id = bool(peak["is_envelope_slack"])
    balance_id = bool(balance["is_identity"])
    not_cycle = composed["cycle_formula_if_return"] is False
    multi = not bool(residues["single_class"])
    no_collapse = not bool(free["any_collapse"])
    finance_gaps = all(row["is_finance_gap"] for row in leftovers)
    near_top = bool(near["pos"] > 0.99)
    new_cong = False
    if (
        identity
        and slack_id
        and balance_id
        and not_cycle
        and multi
        and no_collapse
        and finance_gaps
        and near_top
        and not new_cong
    ):
        classification = CLASS_CLOSED
        decision = "CLOSE"
        reason = (
            "composed seams are global_defect_identity; a return "
            "leaves n^{3^o}-n^{2^L}, which is finance; cyclic "
            "balance is an identity; cycle-scale defects are free "
            "residues; cell positions are unrestricted"
        )
    elif new_cong:
        classification = CLASS_GREEN
        decision = "PROMOTE"
        reason = (
            "a congruence or fractional-part obstruction appears "
            "that is not the global defect, cyclic balance, "
            "mod-closure freeness, or cycleMin_finance"
        )
    else:
        classification = CLASS_PARK
        decision = "PARK"
        reason = "the defect-congruence census is mixed and does not decide"
    return {
        "classification": classification,
        "decision": decision,
        "reason": reason,
        "composed_is_global_defect": identity,
        "peak_pair_is_envelope_slack": slack_id,
        "balance_is_identity": balance_id,
        "residues_not_a_single_class": multi,
        "cycle_scale_defects_free": no_collapse,
        "leftover_is_finance_gap": finance_gaps,
        "cell_positions_unrestricted": near_top,
        "new_congruence": new_cong,
        "leftover_killer": False,
        "reopens_finance": False,
        "reopens_mod_closure": False,
        "halt_theorem": False,
        "raise_n0": False,
        "paper_a_edit": False,
        "archived": list(ARCHIVED),
    }


def probe_payload() -> dict[str, Any]:
    states = [DEMO_START]
    current = DEMO_START
    for _ in DEMO_WORD:
        current = floor_power(current)
        states.append(current)
    payload = {
        "bound": "defect_congruence",
        "published_floor": PUBLISHED_FLOOR,
        "seams": {
            "odd": seam_cell(PEAK_ODD),
            "even": seam_cell(floor_power(PEAK_ODD)),
        },
        "composed": composed_residual(DEMO_START, DEMO_WORD),
        "peak_pair": peak_pair_slack(PEAK_ODD),
        "balance": cyclic_balance_identity(states),
        "residues": residue_occupancy(),
        "cycle_scale": cycle_scale_defects_free(),
        "near_top": cell_record(NEAR_TOP_WITNESS),
        "leftovers": leftover_residuals(),
        "note": (
            "after the main 3^o / 2^L powers cancel, the residual "
            "is Delta = n^{3^o}-n^{2^L} on a cycle; that size is "
            "cycleMin_finance, not a new congruence"
        ),
    }
    payload["decision"] = classify(payload)
    return payload


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload()
    CONGRUENCE_DIR.mkdir(parents=True, exist_ok=True)
    path = CONGRUENCE_DIR / "summary.json"
    path.write_text(json.dumps(data, indent=2, allow_nan=False) + "\n", encoding="utf-8")
    return data


def main() -> None:
    payload = write_artifacts()
    decision = payload["decision"]
    print(decision["classification"])
    print(decision["reason"])
    print(
        json.dumps(
            {
                "composed": payload["composed"],
                "peak_pair": payload["peak_pair"],
                "residues": payload["residues"]["occupied_counts"],
                "decision": decision,
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()

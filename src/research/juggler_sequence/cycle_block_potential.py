"""Strict block potential as a Lyapunov rewrite of the exponent budget.

Phase 0 only: the candidates Φ = log n and Φ = log log n are strictly
increasing on integers ≥ 3, so Φ(J^{block}(n)) < Φ(n) is exactly
T < n. CycleMin-legal first blocks have valley ≥ n. Contracting
blocks already decrease by power_bound_contracts. The floor-strict
scale L(T) < ρ L(n) is power_bound_word_strict. A first-E event
decreases every increasing Φ and does not forbid return.

This is Attack #1 written as a Lyapunov problem, not a reopen of
the exponent budget, finance, or compensated contraction. Not a
halt theorem, and not a claim that every positive integer reaches 1.

Dossier: docs/problems/juggler_cycle_block_potential.md.
"""

from __future__ import annotations

import json
from typing import Any

from research.juggler_sequence.cycle_e_block import (
    cyclemin_shaped_block,
    first_oe_block,
)
from research.juggler_sequence.cycle_exponent_budget import rho
from research.juggler_sequence.cycle_finance import DATA_DIR, PUBLISHED_FLOOR
from research.juggler_sequence.power_itineraries import floor_power

POTENTIAL_DIR = DATA_DIR / "block_potential"
START = PUBLISHED_FLOOR + 1

CLASS_CLOSED = "BLOCK_POTENTIAL_CLOSED"
CLASS_GREEN = "BLOCK_POTENTIAL_GREEN"
CLASS_PARK = "BLOCK_POTENTIAL_PARK"

CONTRACTING_WITNESS = 25
EXPANDING_WITNESS = 115
REALIZED_LO = 13
REALIZED_HI = 2001

ARCHIVED = (
    "power_bound_word",
    "power_bound_word_strict",
    "power_bound_contracts",
    "cycle_itinerary_formally_expanding",
    "cycleMin_finance",
    "global_defect_identity",
)

CANONICAL_EVENTS = ("block_landing", "first_e", "peak")


def log_descent_sign(start: int, image: int) -> int:
    """Sign of log(image) − log(start). Integer verdict: image vs start."""

    if start < 1 or image < 1:
        raise ValueError("log_descent_sign requires positive integers")
    if image < start:
        return -1
    if image > start:
        return 1
    return 0


def loglog_descent_sign(start: int, image: int) -> int:
    """Sign of log log(image) − log log(start) on the domain ≥ 3.

    log and log log are strictly increasing there, so the sign
    agrees with log_descent_sign.
    """

    if start < 3 or image < 3:
        raise ValueError("loglog_descent_sign requires arguments >= 3")
    return log_descent_sign(start, image)


def monotone_candidates_agree(start: int, image: int) -> bool:
    return log_descent_sign(start, image) == loglog_descent_sign(start, image)


def first_e_decreases(peak: int) -> bool:
    """The first even letter of a block drops every increasing Φ."""

    if peak < 2 or peak % 2 == 1:
        raise ValueError("first_e_decreases requires an even peak >= 2")
    return floor_power(peak) < peak


def envelope_holds(start: int, image: int, a: int, r: int) -> bool:
    """Integer form of L(image) ≤ ρ L(start): image^{2^{a+r}} ≤ start^{3^a}."""

    if start < 1 or image < 1 or a < 0 or r < 0 or a + r < 1:
        raise ValueError("envelope_holds requires a nonempty realized block")
    return image ** (1 << (a + r)) <= start ** (3**a)


def envelope_strict(start: int, image: int, a: int, r: int) -> bool:
    """Mixed-word form: L(image) < ρ L(start)."""

    if start < 1 or image < 1 or a < 1 or r < 1:
        raise ValueError("envelope_strict requires a mixed O^a E^r block")
    return image ** (1 << (a + r)) < start ** (3**a)


def block_record(n: int) -> dict[str, Any]:
    rec = first_oe_block(n)
    a0, r = rec["a0"], rec["r"]
    start, peak, valley = rec["n"], rec["peak"], rec["valley"]
    mixed = a0 >= 1 and r >= 1
    shaped = cyclemin_shaped_block(rec)
    landing_sign = log_descent_sign(start, valley) if valley >= 1 else 0
    return {
        "n": start,
        "a0": a0,
        "r": r,
        "peak": peak,
        "valley": valley,
        "rho": str(rho(a0, r)) if mixed else None,
        "rho_ge_one": mixed and rho(a0, r) >= 1,
        "cyclemin_shaped": shaped,
        "landing_sign": landing_sign,
        "log_decreases": landing_sign < 0,
        "loglog_decreases": (
            loglog_descent_sign(start, valley) < 0
            if start >= 3 and valley >= 3
            else None
        ),
        "monotone_agree": (
            monotone_candidates_agree(start, valley)
            if start >= 3 and valley >= 3
            else None
        ),
        "first_e_decreases": first_e_decreases(peak) if peak >= 2 and peak % 2 == 0 else False,
        "peak_increases": peak > start,
        "envelope_holds": envelope_holds(start, valley, a0, r) if mixed else None,
        "envelope_strict": envelope_strict(start, valley, a0, r) if mixed else None,
    }


def first_block_census(*, lo: int = REALIZED_LO, hi: int = REALIZED_HI) -> dict[str, Any]:
    n_oo = 0
    n_contract = 0
    n_expand = 0
    n_shaped = 0
    n_shaped_expand = 0
    n_shaped_equal = 0
    n_shaped_contract = 0
    n_first_e = 0
    n_monotone = 0
    n_monotone_checked = 0
    for n in range(lo if lo % 2 else lo + 1, hi, 2):
        rec = first_oe_block(n)
        if rec["a0"] < 2 or rec["r"] < 1:
            continue
        n_oo += 1
        if rec["valley"] < n:
            n_contract += 1
        elif rec["valley"] > n:
            n_expand += 1
        if rec["peak"] >= 2 and rec["peak"] % 2 == 0 and first_e_decreases(rec["peak"]):
            n_first_e += 1
        if n >= 3 and rec["valley"] >= 3:
            n_monotone_checked += 1
            if monotone_candidates_agree(n, rec["valley"]):
                n_monotone += 1
        if cyclemin_shaped_block(rec):
            n_shaped += 1
            if rec["valley"] > n:
                n_shaped_expand += 1
            elif rec["valley"] == n:
                n_shaped_equal += 1
            else:
                n_shaped_contract += 1
    return {
        "lo": lo,
        "hi": hi,
        "n_oo_launches": n_oo,
        "n_contract": n_contract,
        "n_expand": n_expand,
        "n_cyclemin_shaped": n_shaped,
        "n_shaped_expand": n_shaped_expand,
        "n_shaped_equal": n_shaped_equal,
        "n_shaped_contract": n_shaped_contract,
        "n_first_e_decreases": n_first_e,
        "first_e_always": n_first_e == n_oo,
        "monotone_agree": n_monotone == n_monotone_checked and n_monotone_checked > 0,
        "n_monotone_checked": n_monotone_checked,
        "cyclemin_legal_never_decreases_L": n_shaped_contract == 0,
    }


def classify(payload: dict[str, Any]) -> dict[str, Any]:
    census = payload["census"]
    contracting = payload["contracting"]
    expanding = payload["expanding"]
    monotone = bool(census["monotone_agree"])
    no_shaped_drop = bool(census["cyclemin_legal_never_decreases_L"])
    first_e = bool(census["first_e_always"])
    contract_drops = bool(contracting["log_decreases"]) and contracting["rho_ge_one"] is False
    expand_rises = bool(expanding["cyclemin_shaped"]) and not expanding["log_decreases"]
    envelope = bool(contracting["envelope_strict"]) and bool(expanding["envelope_strict"])
    tautology = True
    if monotone and no_shaped_drop and first_e and contract_drops and expand_rises and envelope:
        classification = CLASS_CLOSED
        decision = "CLOSE"
        reason = (
            "log n and log log n are monotone, so a block Lyapunov is "
            "T < n; CycleMin-legal first blocks never drop L (valley >= n); "
            "115 --O^5 E^2--> 8165 increases L; 25 --OOOEE--> 15 is "
            "power_bound_contracts; L(T) < rho L(n) is the mixed envelope; "
            "first E always decreases and does not kill a cycle; a "
            "state-only Φ cannot telescope around a closed orbit"
        )
    elif not monotone or not no_shaped_drop:
        classification = CLASS_GREEN
        decision = "PROMOTE"
        reason = (
            "a logarithmic candidate decreases on a CycleMin-legal "
            "block for a reason that is not T < n"
        )
    else:
        classification = CLASS_PARK
        decision = "PARK"
        reason = "the block-potential census is mixed and does not decide"
    return {
        "classification": classification,
        "decision": decision,
        "reason": reason,
        "monotone_candidates_agree": monotone,
        "cyclemin_legal_never_decreases_L": no_shaped_drop,
        "first_e_always_decreases": first_e,
        "contracting_is_power_bound_contracts": contract_drops,
        "expanding_increases_L": expand_rises,
        "strict_scale_is_mixed_envelope": envelope,
        "state_only_phi_cannot_telescope": tautology,
        "new_phi": False,
        "leftover_killer": False,
        "reopens_finance": False,
        "reopens_exponent_budget": False,
        "halt_theorem": False,
        "raise_n0": False,
        "paper_a_edit": False,
        "archived": list(ARCHIVED),
    }


def probe_payload() -> dict[str, Any]:
    contracting = block_record(CONTRACTING_WITNESS)
    expanding = block_record(EXPANDING_WITNESS)
    census = first_block_census()
    payload = {
        "bound": "block_potential",
        "published_floor": PUBLISHED_FLOOR,
        "canonical_events": list(CANONICAL_EVENTS),
        "note": (
            "On integers >= 3, log and log log have the same descent "
            "sign as n itself. CycleMin-legal first blocks satisfy "
            "valley >= n, so no increasing Φ can drop. The first E "
            "drops every increasing Φ and does not forbid return. "
            "L(T) < rho L(n) is power_bound_word_strict."
        ),
        "contracting": contracting,
        "expanding": expanding,
        "census": census,
        "identities": {
            "log_sign_is_image_vs_start": True,
            "loglog_sign_is_image_vs_start": True,
            "cyclemin_legal_means_valley_ge_n": True,
            "strict_scale_is_mixed_envelope": True,
            "cycle_telescoping_forbids_state_only_lyapunov": True,
        },
    }
    payload["decision"] = classify(payload)
    return payload


def write_artifacts(payload: dict[str, Any] | None = None) -> dict[str, Any]:
    data = payload if payload is not None else probe_payload()
    POTENTIAL_DIR.mkdir(parents=True, exist_ok=True)
    path = POTENTIAL_DIR / "summary.json"
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
                "contracting": {
                    "n": payload["contracting"]["n"],
                    "valley": payload["contracting"]["valley"],
                    "rho": payload["contracting"]["rho"],
                },
                "expanding": {
                    "n": payload["expanding"]["n"],
                    "valley": payload["expanding"]["valley"],
                    "rho": payload["expanding"]["rho"],
                    "cyclemin_shaped": payload["expanding"]["cyclemin_shaped"],
                },
                "census": payload["census"],
                "decision": decision,
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()

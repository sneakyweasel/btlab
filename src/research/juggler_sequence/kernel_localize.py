"""Phase-0: does Paper B Theorem 5.3 localize to OOOEE / OOEOE even-block fibers?

Not a Paper B edit, not a retag of ``J-kernel-cancellation``, not a
re-derivation of the forty Step 3--5 estimates, and not a halt theorem.
Fate note §7.4 assessed localization at the OOEEE length
``Y = P^{23/32}`` with leftovers at most ``P^{7/16}``.  This module
checks the printed leftovers against the intervals the OOOEE / OOEOE
productions actually use, and against Lemma 3.9's printed trivial bound.
"""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path
from typing import Any

from research.juggler_sequence.cycle_finance import git_commit

DATA_DIR = Path(__file__).resolve().parents[3] / "data" / "research" / "juggler" / "kernel_localize"

# J^5 along OOOEE / OOEOE is n^{27/32}. The even-block fiber
# I(m') = [m'^{32/27}, (m'+1)^{32/27}) at P = m'^{32/27} has length
# ≍ P^{5/32}.  §7.4 copied the OOEEE length P^{23/32} instead.
Y_FIBER = Fraction(5, 32)
Y_ASSESSED = Fraction(23, 32)  # OOEEE / fate note §7.4
Y_TRIPLE = Fraction(1, 2)  # Theorem 4.11 threshold
SAVING = Fraction(1, 24)  # T2 target is Y P^{-1/24}

# Printed leftovers of Theorem 5.3 / Lemma 3.9.
LEMMA39 = Fraction(89, 96)  # |Ω_V| ≤ C(E) P^{89/96} on a dyadic block
PASSENGER = Fraction(7, 16)
END_CELL = Fraction(3, 8)
MAJORANT_TAIL = Fraction(1, 4)

# Freeze-window length T = P^{1/2}/(2 h_1) ≥ (1/2) P^{23/48}.
T_MIN = Fraction(1, 2) - Fraction(1, 48)  # 23/48
# Gap-cell length ≥ P^{1/2}/h ≥ P^{11/24} at h ≤ P^{1/24}.
CELL_MIN = Fraction(1, 2) - Fraction(1, 24)  # 11/24

# V-retune on the §7.4 interval Y = P^{23/32}:
# |Ω| ≤ C P σ^{1/2} ≤ Y P^{-1/24} forces σ ≤ P^{-31/48}.
# N_I V^{-1/2} ≤ Y P^{-1/24} with N_I ≤ P^{25/96} and
# V ≥ σ P^{-5/8} forces σ ≥ P^{-5/24}.
SIGMA_MAX_ASSESSED = Fraction(-31, 48)
SIGMA_MIN_PIECES = Fraction(-5, 24)


def target_exponent(y_exp: Fraction) -> Fraction:
    """Exponent of ``Y P^{-1/24}``."""
    return y_exp - SAVING


def effective_measure_leftover(y_exp: Fraction) -> Fraction:
    """Lemma 3.9 on ``I`` of length ``Y = P^{y_exp}``: ``min(Y, P^{89/96})``."""
    return min(y_exp, LEMMA39)


def exceeds_target(leftover_exp: Fraction, y_exp: Fraction) -> bool:
    return leftover_exp > target_exponent(y_exp)


def leftover_inventory() -> list[dict[str, Any]]:
    """Printed leftovers, classified. Window totals that scale with ``Y``
    are recorded as the ``+1`` end-window leftover, not the full-block sum.
    """
    return [
        {
            "id": "lemma39_trivial",
            "step": "5b",
            "kind": "measure",
            "printed_exponent": float(LEMMA39),
            "printed_as": "89/96",
            "note": "min(Y, P^{89/96}); does not shrink below Y",
        },
        {
            "id": "pure_passenger",
            "step": "3/5",
            "kind": "absolute",
            "printed_exponent": float(PASSENGER),
            "printed_as": "7/16",
            "note": "Kusmin--Landau / passenger end cell",
        },
        {
            "id": "end_cell",
            "step": "3a",
            "kind": "window_plus_one",
            "printed_exponent": float(END_CELL),
            "printed_as": "3/8",
            "note": "one leftover freeze/collision window",
        },
        {
            "id": "majorant_tail",
            "step": "3",
            "kind": "absolute",
            "printed_exponent": float(MAJORANT_TAIL),
            "printed_as": "1/4",
            "note": "Vaaler / majorant end cells",
        },
    ]


def evaluate_at(y_exp: Fraction, label: str) -> dict[str, Any]:
    tgt = target_exponent(y_exp)
    measure = effective_measure_leftover(y_exp)
    rows = []
    any_hit = False
    for item in leftover_inventory():
        if item["kind"] == "measure":
            leftover = measure
        else:
            leftover = Fraction(item["printed_as"])
        hit = leftover > tgt
        any_hit = any_hit or hit
        rows.append(
            {
                **item,
                "effective_exponent": float(leftover),
                "target_exponent": float(tgt),
                "exceeds_target": hit,
            }
        )
    return {
        "label": label,
        "y_exponent": float(y_exp),
        "y_as": str(y_exp),
        "target_exponent": float(tgt),
        "target_as": str(tgt),
        "fiber_shorter_than_gap_cell": y_exp < CELL_MIN,
        "fiber_shorter_than_freeze_window": y_exp < T_MIN,
        "below_triple_threshold": y_exp < Y_TRIPLE,
        "leftovers": rows,
        "falsifier_fires": any_hit,
    }


def v_retune_assessed() -> dict[str, Any]:
    """Retuning V on the §7.4 interval cannot close both constraints."""
    gap = SIGMA_MIN_PIECES - SIGMA_MAX_ASSESSED  # -5/24 - (-31/48) = 21/48
    return {
        "interval": "Y = P^{23/32}",
        "sigma_max_for_sublevel": str(SIGMA_MAX_ASSESSED),
        "sigma_min_for_piece_boundaries": str(SIGMA_MIN_PIECES),
        "gap_exponent": str(gap),
        "constraints_compatible": SIGMA_MIN_PIECES <= SIGMA_MAX_ASSESSED,
        "y_needed_for_printed_omega": str(LEMMA39 + SAVING),  # 31/32
    }


def y_needed_for_passenger() -> str:
    """Smallest Y-exponent at which P^{7/16} ≤ Y P^{-1/24}."""
    return str(PASSENGER + SAVING)  # 23/48


def summary() -> dict[str, Any]:
    fiber = evaluate_at(Y_FIBER, "OOOEE_OOEOE_even_block_fiber")
    assessed = evaluate_at(Y_ASSESSED, "section_7_4_OOEEE_length")
    retune = v_retune_assessed()
    return {
        "git_commit": git_commit(),
        "anti": {
            "halt_theorem": False,
            "paper_a_modified": False,
            "paper_b_modified": False,
            "kernel_retagged": False,
            "forty_estimates_rederived": False,
        },
        "scales": {
            "y_fiber": str(Y_FIBER),
            "y_assessed": str(Y_ASSESSED),
            "y_triple_threshold": str(Y_TRIPLE),
            "saving": str(SAVING),
            "lemma39": str(LEMMA39),
            "t_min": str(T_MIN),
            "cell_min": str(CELL_MIN),
            "y_needed_for_passenger": y_needed_for_passenger(),
            "y_needed_for_printed_omega": str(LEMMA39 + SAVING),
        },
        "fiber": fiber,
        "assessed": assessed,
        "v_retune": retune,
        "classification": {
            "true_fiber_is_p_5_32": True,
            "section_7_4_used_wrong_y": True,
            "lemma39_exceeds_assessed_target": assessed["falsifier_fires"],
            "lemma39_exceeds_fiber_target": fiber["falsifier_fires"],
            "fiber_below_triple_threshold": fiber["below_triple_threshold"],
            "fiber_inside_one_gap_cell": fiber["fiber_shorter_than_gap_cell"],
            "v_retune_impossible_at_assessed_y": not retune["constraints_compatible"],
            "free_term_untouched": True,
            "decision": "CLOSE",
        },
    }


def main() -> None:
    result = summary()
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    out = DATA_DIR / "summary.json"
    out.write_text(json.dumps(result, indent=2), encoding="utf-8")
    print(json.dumps(result, indent=2))
    print(out)


if __name__ == "__main__":
    main()

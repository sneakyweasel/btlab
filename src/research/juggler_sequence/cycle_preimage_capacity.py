"""Three fixed controls of exact support holes and B-preimage multiplicity.

The witness graph is open. Counts use closed formulas; no source interval,
parameter class, fibre, retained set, or matching is enumerated.
"""
from __future__ import annotations

import json
from math import isqrt

from research.juggler_sequence.cycle_return_seam import (
    FIXED_PARAMETERS,
    family as return_seam_family,
)
from research.juggler_sequence.lean_paths import DATA_ROOT


def collision_pair(v: int, j: int) -> dict:
    """Check one symbolically selected pair from the proved two-parameter ray."""
    if v < 3 or v % 2 != 1 or j < 1 or j % 2 != 1 or 2*j >= v:
        raise ValueError("odd v>=3 and odd 1<=j<v/2 required")
    x, H, y = v**4+2*j, v**6+3*v*v*j, v**3
    o_lower = 3*v**4*j*j+8*j**3
    o_upper = 2*v**6+6*v*v*j+1-3*v**4*j*j-8*j**3
    e_lower = 3*v*v*j
    e_upper = 2*v**3+1-3*v*v*j
    assert x**3-H*H == o_lower > 0
    assert (H+1)**2-x**3 == o_upper > 0
    assert H-y*y == e_lower > 0
    assert (y+1)**2-H == e_upper > 0
    assert x % 2 == y % 2 == 1 and H % 2 == 0
    assert isqrt(x**3) == H and isqrt(H) == y
    return {"v": v, "j": j, "source": x, "intermediate": H, "target": y,
            "O_lower_margin": o_lower, "O_upper_margin": o_upper,
            "E_lower_margin": e_lower, "E_upper_margin": e_upper,
            "actual_guards": True}


def control(u: int) -> dict:
    base = return_seam_family(u)
    r, m, M, t, w = (base[k] for k in ("r", "minimum", "maximum", "t", "w"))
    v_low, v_high = r*r+2, 2*r*r-1
    pairs = []
    for v in (v_low, v_high):
        j_bound = (v-1)//2
        j_high = j_bound if j_bound % 2 else j_bound-1
        for j in (1, j_high):
            row = collision_pair(v, j)
            x, H, y = (row[k] for k in ("source", "intermediate", "target"))
            assert base["b_high"] < x < t < H < M
            assert m < y < w and H > m*m
            row["inside_both_face_domains"] = True
            row["interior_above_retained_interval"] = True
            pairs.append(row)
    assert len({(row["v"], row["j"]) for row in pairs}) == 4

    support_numerator = r*r-1
    singleton_numerator = r*r+3
    raw_numerator = 3*r**4-2*r*r-1
    assert support_numerator % 2 == singleton_numerator % 4 == raw_numerator % 16 == 0
    support_count = support_numerator//2
    singleton_lower = singleton_numerator//4
    source_count = raw_numerator//16
    assert support_count % 2 == 0
    assert source_count == support_count*singleton_lower+(support_count//2)*(support_count//2-1)

    # The exact power target has one prescribed A-preimage, with a bad E guard.
    a_source, a_first, a_second, a_target = r**8, r**12, r**18, r**9
    assert m < a_source < base["a"] and base["z"] < a_target < t
    assert isqrt(a_source**3) == a_first
    assert isqrt(a_first**3) == a_second and isqrt(a_second) == a_target
    assert a_source % 2 == a_first % 2 == a_second % 2 == a_target % 2 == 1
    # For x<a_source, A(x)<=x^(9/8)<a_target. For x>=a_source+1,
    # these exact lower cells imply A(x)>=a_target+1 by monotonicity.
    first_upper_source_margin = (a_source+1)**3-(r**12+r**4)**2
    second_lower_margin = (r**12+r**4)**3-(r**18+r**10)**2
    final_lower_margin = r**18+r**10-(a_target+1)**2
    assert first_upper_source_margin > 0 and second_lower_margin > 0 and final_lower_margin > 0
    assert (a_source-1)**9 < a_target**8
    return {
        "u": u, "r": r, "minimum": m, "maximum": M,
        "a": base["a"], "b_low": base["b_low"], "b_high": base["b_high"],
        "t": t, "w": w, "z": base["z"],
        "selected_pairs": pairs,
        "target_interval": {"lower": v_low**3, "upper": v_high**3},
        "closed_form_counts": {
            "exhibited_supported_targets": support_count,
            "exhibited_sources": source_count,
            "singleton_supported_targets": 1,
            "singleton_preimages_lower_bound": singleton_lower,
            "complete_interval_support_asserted": False,
            "all_preimages_counted": False,
        },
        "A_support_hole": {
            "target": a_target, "unique_prescribed_source": a_source,
            "first_O_output": a_first, "second_O_output": a_second,
            "prescribed_A_output": a_target, "actual_final_E_guard": False,
            "exact_guarded_support": 0,
            # Hex preserves this certificate beyond Python's decimal JSON limit.
            "left_ideal_power_upper_hex": hex(a_target**8-(a_source-1)**9),
            "right_first_lower_margin": first_upper_source_margin,
            "right_second_lower_margin": second_lower_margin,
            "right_final_lower_margin": final_lower_margin,
            "target_in_retained_set_asserted": False,
        },
        "all_inherited_checks": all(base["checks"].values()),
        "full_matching_asserted": False,
        "periodic_orbit_asserted": False,
    }


def report() -> dict:
    return {
        "decision": "CLOSE",
        "scope": "ordinary raw-preimage Hall counts add no global deficit; exact support still requires common-set closure",
        "fixed_parameters": list(FIXED_PARAMETERS),
        "selected_pairs_per_parameter": 4,
        "counts_by_formula_only": True,
        "controls": [control(u) for u in FIXED_PARAMETERS],
        "source_search": False, "orbit_search": False, "rank_search": False,
        "residue_search": False, "fibre_enumeration": False,
        "new_local_prefix": False, "new_period_or_height_bound": False,
        "strict_shared_support_deficit": False,
        "full_matching_asserted": False, "no_cycle_proved": False,
        "new_lean_or_paper_claim": False,
        "proof_owner": "docs/problems/juggler_cycle_preimage_capacity.md",
        "proof_status": "AI-assisted written proof with exact fixed controls; not Lean or independent human review",
    }


def main() -> None:
    data = report()
    destination = DATA_ROOT/"cycle_preimage_capacity/summary.json"
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(data, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({"decision": data["decision"],
                      "fixed_parameters": data["fixed_parameters"],
                      "selected_B_pairs": sum(len(row["selected_pairs"]) for row in data["controls"]),
                      "A_support_holes": len(data["controls"]),
                      "new_period_or_height_bound": False}, indent=2))


if __name__ == "__main__":
    main()

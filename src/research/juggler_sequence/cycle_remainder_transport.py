"""Exact remainder repair and bounded fates of six existing OOE-family starts."""
from __future__ import annotations

import json
from math import isqrt

from research.juggler_sequence.lean_paths import DATA_ROOT
from research.juggler_sequence.cycle_cubic_induction import (
    trace_word, parity_guard, square_cell_carry,
)

PARAMETERS = (3, 5, 11, 101, 10**6+1, 10**20+1)
MAX_STEPS, MAX_BITS = 500, 16384


def corrected_suffix(x: int, R: int, z: int) -> dict:
    """Use an already certified first-square remainder and validate its endpoint.

    Contract: B=x^3-R is a positive square and R is its true square-cell
    remainder. Initialization/certification belongs to the caller.
    """
    X, B = x**3, x**3-R
    if R < 0 or B < 9 or R*R > 4*B or z < 2:
        raise ValueError("invalid certified-record bounds")
    if not z**8 <= B**3 < (z+1)**8:
        raise ValueError("candidate endpoint fails its exact cell")
    K = 2*X-3*R
    assert K > 0
    q = (isqrt(K*K*X)-2*z**4) // (4*z*z)
    h = min(q+1, 2*z)
    assert h >= 0
    ceiling = z*z+h
    kappa = next(j for j in range(4) if (ceiling-j)**4 <= B**3)
    v = ceiling-kappa
    assert v**4 <= B**3 < (v+1)**4
    return {"x": x, "R": R, "B": B, "z": z, "K": K, "q": q, "h": h,
            "kappa": kappa, "recovered_v": v,
            "odd_endpoint_ooe_guard": bool(x % 2 and z % 2 and R % 2 == 0 and v % 2 == 0)}


def corrected_record(x: int) -> dict:
    """Initialize the exact remainder, then audit the different recovery formula."""
    u = isqrt(x**3)
    R = x**3-u*u
    v = isqrt(u**3)
    z = isqrt(v)
    row = corrected_suffix(x, R, z)
    d = (u**3-z**4) // (2*z*z)
    assert row["recovered_v"] == v and d-row["q"] in (0, 1)
    expected_guard = parity_guard([x, u, v, z], "OOE") and bool(z % 2)
    assert row["odd_endpoint_ooe_guard"] == expected_guard
    row.update({"actual_u": u, "actual_v": v, "true_quotient": d,
                "corrected_quotient_error": d-row["q"]})
    return row


def guard_ooeoe(x: int, y: int, R: int) -> bool:
    """Finite-depth exact guard; this is not a uniform arbitrary-word algorithm."""
    if x < 3 or x % 2 != 1 or y < 1 or y % 2 != 1:
        return False
    H = isqrt(isqrt(isqrt(x**9)))
    z = H if H % 2 else H-1
    B = x**3-R
    if z < 2 or not z**8 <= B**3 < (z+1)**8:
        return False
    prefix = corrected_suffix(x, R, z)
    if not prefix["odd_endpoint_ooe_guard"] or not y**4 <= z**3 < (y+1)**4:
        return False
    suffix = square_cell_carry(z**3, y)
    return suffix["u"] % 2 == 0


def family_chain_bound(r: int) -> int:
    if r < 3 or r % 2 != 1:
        raise ValueError("odd r >= 3 required")
    a = ((r-1) & -(r-1)).bit_length()-1
    return max(0, (a-2)//2)


def exact_family_trace(r: int) -> dict:
    """Bounded orbit of one specified parameter; capped output is never escape."""
    start = r**8+8
    if start.bit_length() > MAX_BITS:
        raise ValueError("initial state exceeds the fixed bit cap")
    x, states, seen = start, [start], {start: 0}
    maximum, maximum_step, first_below = start, 0, None
    status, extra = "step_cap", {}
    for step in range(1, MAX_STEPS+1):
        y = isqrt(x**3 if x % 2 else x)
        if y.bit_length() > MAX_BITS:
            status = "bit_cap"
            extra = {"next_step": step, "next_value_bits": y.bit_length()}
            break
        states.append(y)
        if y > maximum:
            maximum, maximum_step = y, step
        if y < start and first_below is None:
            first_below = step
        if y == 1:
            status = "reached_one"
            break
        if y in seen:
            status = "cycle_detected"
            extra = {"cycle_start_step": seen[y], "cycle_period": step-seen[y]}
            break
        seen[y] = step
        x = y
    terminal = r**9+9*r-1
    candidate = isqrt(isqrt(isqrt(terminal-8)))
    prefix = [start, r**12+12*r**4, r**18+18*r**10+54*r*r-1, terminal]
    assert states[:4] == prefix[:min(4, len(states))]
    reentry = candidate >= 3 and candidate % 2 == 1 and candidate**8+8 == terminal
    return {"r": r, "start": start, "status": status, "steps_recorded": len(states)-1,
            "first_below_start_step": first_below, "maximum_step": maximum_step,
            "maximum_bits": maximum.bit_length(), "maximum_hex": hex(maximum),
            "maximum_decimal_digits": len(str(maximum)), "final_bits": states[-1].bit_length(),
            "terminal_ooe_reenters_family": reentry,
            "immediate_reentry_excluded_by_mod48": r % 48 != 1,
            "consecutive_family_transition_bound": family_chain_bound(r),
            "states_hex": [hex(n) for n in states], **extra}


def report() -> dict:
    sources = list(range(3, 129)) + [r**8+8 for r in PARAMETERS]
    repairs = [corrected_record(x) for x in sources]
    extensions = []
    for x in list(range(3, 129, 2))+[201, 263]:
        states = trace_word(x, "OOEOE")
        y = states[-1]
        R = x**3-isqrt(x**3)**2
        result = guard_ooeoe(x, y, R)
        expected = parity_guard(states, "OOEOE") and bool(y % 2)
        assert result == expected
        extensions.append({"x": x, "y": y, "guard_valid": result})
    fates = [exact_family_trace(r) for r in PARAMETERS]
    return {"scope": {"family_parameters": list(PARAMETERS), "max_steps": MAX_STEPS,
                       "max_state_bits": MAX_BITS, "caps_enlarged": False,
                       "repair_small_source_range": [3, 128], "repair_instances": len(repairs),
                       "ooeoe_guard_instances": len(extensions), "cycle_census": False},
            "arithmetic": "Exact integers; orbit states are lossless hexadecimal integers",
            "corrected_quotient_controls": repairs, "ooeoe_controls": extensions,
            "family_fates": fates, "universal_family_termination_proved": False,
            "escaping_orbit_proved": False, "uniform_word_guard_closure_proved": False}


if __name__ == "__main__":
    data = report()
    out = DATA_ROOT / "cycle_remainder_transport" / "summary.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(data, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({"scope": data["scope"], "family_fates": [
        {k: r[k] for k in ("r", "status", "steps_recorded", "maximum_decimal_digits")}
        for r in data["family_fates"]]}, indent=2))

"""Bounded exact controls for Euclidean induction; never searches for cycles."""
from __future__ import annotations

from math import gcd, isqrt
import json

from research.juggler_sequence.lean_paths import DATA_ROOT
from research.juggler_sequence.cycle_cubic_band import (
    ABSOLUTE_CELL_THRESHOLD_CYCLES,
    certify_cycle,
)

WORDS = ("O", "OE", "OOE", "OOEOE", "OOEOOEOE",
         "OOE" + "OOEOOEOE", "OOE" + "OOEOOEOE" * 2)


def trace_word(x: int, word: str) -> list[int]:
    """Execute prescribed branches, independently of their parity guards."""
    states = [x]
    for letter in word:
        if letter not in "OE":
            raise ValueError("unknown branch")
        x = isqrt(x**3 if letter == "O" else x)
        states.append(x)
    return states


def parity_guard(states: list[int], word: str) -> bool:
    return all(bool(x % 2) == (w == "O") for x, w in zip(states[:-1], word))


def rank_induction(a: int, b: int) -> list[dict]:
    """Check each symbolic stage against literal original first returns."""
    if a <= 0 or b <= 0:
        raise ValueError("positive branch lengths required")
    original_a, original_b, length = a, b, a+b
    A, B = "O", "E"
    stages = []
    while True:
        n = a+b
        covered = []
        towers = []
        for base in range(n):
            word = A if base < a else B
            i, actual_word, tower = base, "", []
            while True:
                tower.append(i)
                actual_word += "O" if i < original_a else "E"
                i = (i+original_b) % length
                if i < n:
                    break
            assert actual_word == word
            assert i == (base+b) % n
            covered.extend(tower)
            towers.append({"base": base, "word": word, "ranks": tower, "image": i})
        assert sorted(covered) == list(range(length))
        assert a*len(A)+b*len(B) == length
        assert a*A.count("O")+b*B.count("O") == original_a
        assert a*A.count("E")+b*B.count("E") == original_b
        stages.append({"a": a, "b": b, "A": A, "B": B, "towers": towers})
        if a == 0 or b == 0:
            assert n == gcd(original_a, original_b)
            break
        if a >= b:
            a, B = a-b, A+B
        else:
            b, A = b-a, A+B
    return stages


def source_controls() -> list[dict]:
    """Recheck exactly the original 3..65535 sample, with integer powers."""
    records = []
    for word in WORDS:
        numerator, denominator = 3**word.count("O"), 2**len(word)
        valid, cubic, failures = 0, 0, []
        for x in range(3, 65536, 2):
            states = [x]
            y = x
            for letter in word:
                if bool(y % 2) != (letter == "O"):
                    break
                y = isqrt(y**3 if letter == "O" else y)
                states.append(y)
            if len(states) != len(word)+1 or not y % 2:
                continue
            valid += 1
            if max(states) >= min(states)**3:
                continue
            cubic += 1
            # For an odd y, this pair is precisely odd_floor(x^(num/den))=y.
            power = x**numerator
            assert y**denominator <= power
            if power >= (y+2)**denominator:
                failures.append({"x": x, "y": y, "states": states})
        records.append({"word": word, "numerator": numerator, "denominator": denominator,
                        "odd_sources_checked": 32767, "parity_valid_odd_endpoints": valid,
                        "also_cubic_height": cubic, "projection_failures": failures})
    return records


def report() -> dict:
    for a in range(1, 33):
        for b in range(1, 33):
            rank_induction(a, b)
    cycles = []
    for threshold, cyclic in ABSOLUTE_CELL_THRESHOLD_CYCLES:
        certificate = certify_cycle(threshold, list(cyclic))
        values = sorted(cyclic)
        odd = certificate["odd_branch_count"]
        stages = rank_induction(odd, len(values)-odd)
        mismatches = sum(bool(x % 2) != (i < odd) for i, x in enumerate(values))
        for stage in stages:
            failed_guards, tested_sources = 0, 0
            for tower in stage["towers"]:
                trace = trace_word(values[tower["base"]], tower["word"])
                assert trace == [values[i] for i in tower["ranks"]] + [values[tower["image"]]]
                failed_guards += sum(bool(x % 2) != (w == "O")
                                     for x, w in zip(trace[:-1], tower["word"]))
                tested_sources += len(tower["word"])
            assert failed_guards == mismatches and tested_sources == len(values)
        cycles.append({"threshold": threshold, "minimum": values[0], "period": len(values),
                       "stages": len(stages), "parity_mismatches_at_every_stage": mismatches,
                       "terminal_word": stages[-1]["towers"][0]["word"],
                       "actual_juggler_cycle": False})
    guards = []
    for s in (3, 5, 101):
        states, b = trace_word(s**4, "OE"), s**3
        assert states == [s**4, s**6, s**3]
        assert b <= states[0] < b*b == states[1] < b**3
        assert states[-1] == b and all(x % 2 for x in states)
        assert not parity_guard(states, "OE")
        guards.append({"s": s, "threshold": b, "states": states,
                       "odd_endpoints": True, "hidden_even_guard": False})
    return {"scope": {"odd_source_range": [3, 65535], "words": list(WORDS),
                       "rank_branch_length_range": [1, 32], "rank_pairs": 1024,
                       "archived_threshold_cycles": 7, "cycle_search": False},
            "arithmetic": "Exact integers throughout; no numerical roots or logarithms",
            "sources": source_controls(), "archived_cycles": cycles,
            "hidden_guard_examples": guards,
            "uniform_endpoint_closure_proved": False,
            "uniform_parity_closure_proved": False, "no_cycle_proved": False}


def square_cell_carry(N: int, y: int) -> dict:
    """Recover sqrt(N) within its exact double-square endpoint cell."""
    if y < 1 or not y**4 <= N < (y+1)**4:
        raise ValueError("positive y and its exact fourth-power cell required")
    d = (N-y**4) // (2*y*y)
    h = min(d, 2*y)
    # The theorem bounds the correction before these comparisons are made.
    if (y*y+h)**2 <= N:
        kappa = 0
    elif (y*y+h-1)**2 <= N:
        kappa = 1
    else:
        kappa = 2
    c = h-kappa
    u = y*y+c
    assert 0 <= c <= 2*y and u*u <= N < (u+1)**2
    return {"N": N, "y": y, "d": d, "h": h, "kappa": kappa, "c": c, "u": u}


def valid_ooe_carry_family(r: int) -> dict:
    """Exact controls for the proved infinite family; no orbit search."""
    if r < 3 or r % 2 != 1:
        raise ValueError("odd r >= 3 required")
    b, x = r**8, r**8+8
    u = r**12+12*r**4
    v = r**18+18*r**10+54*r*r-1
    z = r**9+9*r-1
    states = [x, u, v, z]
    assert trace_word(x, "OOE") == states and parity_guard(states, "OOE")
    assert z % 2 == 1
    assert b <= x < b*b and b <= u < b*b
    assert b*b <= v < b**3 and b <= z < b*b
    assert max(states) < min(states)**3
    exact = square_cell_carry(u**3, z)
    assert exact["u"] == v and exact["c"] == 2*z-27*r*r
    # floor((sqrt(x^9)-A)/B) = (isqrt(x^9)-A)//B for integer A,B>0.
    D = (isqrt(x**9)-z**4) // (2*z*z)
    assert D-exact["d"] in (36*r*r, 36*r*r+1)
    H = min(D, 2*z)
    assert H == 2*z and H-exact["c"] == 27*r*r
    # This is exact output compression despite the growing internal quotient gap.
    assert (z+1)**8 < x**9 < (z+2)**8
    # The substituted radicand is outside the original unit endpoint cell.
    assert isqrt(x**9) >= (z+1)**4
    return {"r": r, "threshold": b, "states": states, "word": "OOE",
            "source_parities_valid": True, "cubic_height": True,
            "first_square_remainder": x**3-u*u, "true_oe_carry": exact,
            "substituted_quotient": D, "quotient_difference": D-exact["d"],
            "quotient_difference_base": 36*r*r,
            "quotient_difference_extra_bit": D-exact["d"]-36*r*r,
            "clipped_substitute": H, "clipped_offset_error": H-exact["c"],
            "ordinary_power_endpoint": z+1, "odd_power_endpoint": z,
            "substitution_preserves_unit_endpoint_cell": False,
            "closed_cycle": False}


def guard_carry_report() -> dict:
    """Boundary controls for the normal form and literal infinite-family instances."""
    cells, corrections = 0, set()
    for y in range(1, 33):
        for c in range(2*y+1):
            u = y*y+c
            for epsilon in sorted({0, 1, 2*u-1, 2*u}):
                N = u*u+epsilon
                result = square_cell_carry(N, y)
                assert result["u"] == isqrt(N) == u
                assert result["c"] == c
                corrections.add(result["kappa"])
                cells += 1
    sharp = square_cell_carry(93**3, 29)
    assert trace_word(93, "OE") == [93, 896, 29]
    assert sharp["kappa"] == 2
    family = [valid_ooe_carry_family(r) for r in (3, 5, 11, 101, 10**6+1, 10**20+1)]
    fibers = []
    for s in (3, 5, 11, 101):
        count = 2*s//3+1
        guards = []
        for j in range(count):
            x, y = s**4+2*j, s**3
            states = trace_word(x, "OE")
            assert states == [x, s**6+3*s*s*j, y]
            guard = parity_guard(states, "OE")
            assert guard == bool(j % 2) == (x % 4 == 3)
            guards.append(guard)
        fibers.append({"s": s, "endpoint": s**3, "sources_checked": count,
                       "guard_sequence": guards, "valid_iff_source_mod4_is3": True})
    return {
        "scope": {"endpoint_range_for_boundary_controls": [1, 32],
                  "square_cell_boundary_instances": cells,
                  "boundary_offsets": "0,1,2u-1,2u, deduplicated",
                  "family_parameters": [row["r"] for row in family],
                  "cube_fiber_parameters": [row["s"] for row in fibers],
                  "cycle_search": False, "source_scan_enlarged": False},
        "arithmetic": "Exact integers throughout",
        "normal_form_corrections_seen": sorted(corrections),
        "sharp_valid_oe_block": {"states": [93, 896, 29], "carry": sharp},
        "valid_ooe_family": family, "cube_fiber_controls": fibers,
        "uniform_bounded_additive_substitution_refuted": True,
        "general_arithmetic_parity_closure_refuted": False, "no_cycle_proved": False}


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--guard-carries", action="store_true",
                        help="verify only exact parity-carry and substitution controls")
    args = parser.parse_args()
    data = guard_carry_report() if args.guard_carries else report()
    out = DATA_ROOT / "cycle_cubic_induction" / ("guard_carries.json" if args.guard_carries else "controls.json")
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(data, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({"scope": data["scope"], "sources": data.get("sources", []),
                      "no_cycle_proved": data["no_cycle_proved"]}, indent=2))

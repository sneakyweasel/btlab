"""Exact direction-change replay on archived cycles; no cycle or source search."""
from __future__ import annotations

import argparse
from fractions import Fraction
import json
from math import isqrt
from pathlib import Path

from research.juggler_sequence.lean_paths import DATA_ROOT
from research.juggler_sequence.cycle_cubic_band import ABSOLUTE_CELL_THRESHOLD_CYCLES
from research.juggler_sequence.cycle_cubic_induction import rank_induction, trace_word
from research.juggler_sequence.cycle_periodic_carries import (
    ceiling_record as previous_ceiling_record,
    cube_root_floor,
    periodic_record,
)

MINIMUM = 2**24
CEILING_MINIMA = (214358889, 10828567056280809)
RETURN_WORDS = {"O": "OOE", "E": "OE"}


def expand_return_word(word: str) -> str:
    """The abstract O/E symbols name the initial OOE/OE returns."""
    return "".join(RETURN_WORDS[letter] for letter in word)


def exact_cells(states: list[int], word: str) -> list[dict]:
    if len(states) != len(word)+1 or any(letter not in "OE" for letter in word):
        raise ValueError("one source for every original branch letter required")
    cells = []
    for x, y, letter in zip(states, states[1:], word):
        radicand = x**3 if letter == "O" else x
        remainder = radicand-y*y
        assert 0 <= remainder <= 2*y
        assert y*y <= radicand < (y+1)**2
        cells.append({"source": x, "branch": letter, "image": y,
                      "square_remainder": remainder,
                      "wrong_parity": bool(x % 2) != (letter == "O")})
    return cells


def archived_cycle_record(threshold: int, cyclic: tuple[int, ...]) -> dict:
    """Replay first returns inside the given literal cycle, never extend it."""
    original = periodic_record(threshold, cyclic)
    values = sorted(cyclic)
    rank = {x: i for i, x in enumerate(values)}
    position = {x: i for i, x in enumerate(cyclic)}
    period = len(cyclic)
    minimum = min(cyclic)
    baseline_word = "".join("O" if x < minimum**2 else "E" for x in cyclic)
    baseline = exact_cells(list(cyclic)+[cyclic[0]], baseline_word)
    by_source = sorted(baseline, key=lambda cell: cell["source"])
    mismatch_sources = sorted(cell["source"] for cell in baseline if cell["wrong_parity"])
    bases = original["retained_bases"]
    initial_a, initial_b = original["OOE_count"], original["OE_count"]
    result = {
        "threshold": threshold, "normalized_threshold": minimum,
        "minimum": minimum, "maximum": max(cyclic), "period": period,
        "retained_bases": bases, "OOE_count": initial_a, "OE_count": initial_b,
        "original_cells": by_source, "wrong_parity_sources": mismatch_sources,
        "parity_mismatches_at_every_stage": len(mismatch_sources),
        "actual_juggler_cycle": original["actual_juggler_cycle"],
        "large_minimum_theorem_applies": minimum >= MINIMUM and not mismatch_sources,
    }
    assert len(mismatch_sources) == original["parity_mismatches"]
    assert not result["actual_juggler_cycle"]
    if initial_a == 0 or initial_b == 0:
        assert len(bases) == 1 and initial_b == 0
        result.update({"rank_induction_excluded": True,
                       "exclusion_reason": "singleton retained section with no OE branch",
                       "stages": [], "transitions": [],
                       "terminal_extra_seam_edge": False})
        return result

    stages = []
    for raw in rank_induction(initial_a, initial_b):
        a, b = raw["a"], raw["b"]
        retained = bases[:a+b]
        retained_set = set(retained)
        covered_cells = []
        towers = []
        for tower in raw["towers"]:
            word = expand_return_word(tower["word"])
            x = bases[tower["base"]]
            trace = trace_word(x, word)
            # Independent reference: positions on the supplied literal cycle.
            expected = [cyclic[(position[x]+j) % period] for j in range(len(word)+1)]
            assert len(word) <= period and trace == expected
            macro_trace = [x]
            macro_word = ""
            for i, letter in zip(tower["ranks"], tower["word"]):
                block = original["returns"][i]
                assert block["base"] == macro_trace[-1]
                assert block["word"] == RETURN_WORDS[letter]
                macro_trace.extend(block["states"][1:])
                macro_word += block["word"]
            assert macro_word == word and macro_trace == trace
            assert trace[-1] == bases[tower["image"]]
            assert trace[0] in retained_set and trace[-1] in retained_set
            assert all(x not in retained_set for x in trace[1:-1])
            cells = exact_cells(trace, word)
            covered_cells.extend(cells)
            towers.append({"base_rank": tower["base"], "base": trace[0],
                           "image_rank": tower["image"], "image": trace[-1],
                           "abstract_word": tower["word"], "word": word,
                           "states": trace, "cells": cells})
        assert sorted(covered_cells, key=lambda cell: cell["source"]) == by_source
        assert sum(cell["wrong_parity"] for cell in covered_cells) == len(mismatch_sources)
        seam = None
        if a > 0 and b > 0:
            w, z = bases[b-1], bases[b]
            assert towers[0]["image"] == z and towers[-1]["image"] == w
            seam = {"w": w, "z": z, "gap": z-w}
        stages.append({"a": a, "b": b,
                       "A": expand_return_word(raw["A"]),
                       "B": expand_return_word(raw["B"]),
                       "retained_bases": retained, "seam": seam, "towers": towers,
                       "original_cells_preserved": period,
                       "wrong_parity_sources": mismatch_sources})

    transitions = []
    for old, new in zip(stages, stages[1:]):
        a, b = old["a"], old["b"]
        seam = old["seam"]
        assert seam is not None
        if a == b:
            assert new["a"] == 0 and new["b"] == b and new["seam"] is None
            assert all(tower["base"] == tower["image"] for tower in new["towers"])
            assert seam["w"] in new["retained_bases"]
            assert seam["z"] not in new["retained_bases"]
            transitions.append({"direction": "terminal", "old_seam": seam,
                                "new_seam": None, "upper_seam_point_removed": True,
                                "extra_seam_transfer": False})
        elif a > b:
            assert (new["a"], new["b"]) == (a-b, b)
            assert new["seam"] == seam
            assert trace_word(new["retained_bases"][-1], old["A"])[-1] == old["retained_bases"][-1]
            transitions.append({"direction": "left", "old_seam": seam,
                                "new_seam": new["seam"], "same_two_values": True})
        else:
            assert (new["a"], new["b"]) == (a, b-a)
            assert new["retained_bases"][-1] == seam["w"]
            lower = trace_word(seam["w"], old["B"])
            upper = trace_word(seam["z"], old["B"])
            assert [lower[-1], upper[-1]] == [new["seam"]["w"], new["seam"]["z"]]
            # Each common-letter prefix is an adjacent pair in the full cycle.
            assert all(rank[y] == rank[x]+1 for x, y in zip(lower, upper))
            transitions.append({"direction": "right", "old_seam": seam,
                                "new_seam": new["seam"], "transfer_word": old["B"],
                                "adjacent_intermediate_pairs": [list(pair) for pair in zip(lower, upper)]})
    assert stages[-1]["seam"] is None and len(stages[-1]["retained_bases"]) == 1
    assert transitions[-1]["direction"] == "terminal"
    result.update({"rank_induction_excluded": False, "stages": stages,
                   "transitions": transitions, "terminal_extra_seam_edge": False})
    return result


def least_even_seam_gap(m: int) -> int:
    """Least even G>=6 above the proved strict rational-power lower bound."""
    if m < MINIMUM:
        raise ValueError("minimum at least 2^24 required")
    rhs = 26240**128*m**13
    def allowed(half: int) -> bool:
        return (59049*(2*half))**128 > rhs
    low, high = 2, 3
    while not allowed(high):
        low, high = high, 2*high
    while low+1 < high:
        middle = (low+high)//2
        if allowed(middle):
            high = middle
        else:
            low = middle
    gap = 2*high
    assert gap >= 6 and allowed(high)
    assert gap == 6 or not allowed(high-1)
    return gap


def ceiling_record(m: int) -> dict:
    """Evaluate a conditional necessary ceiling, without generating an orbit."""
    if m < MINIMUM or m % 2 == 0:
        raise ValueError("odd minimum at least 2^24 required")
    G = least_even_seam_gap(m)
    H = isqrt(isqrt(isqrt(m**9)))
    z = H if H % 2 else H-1
    assert z**8 <= m**9 < (z+2)**8 and z-G > 0
    squared_seam = ((z-G)*(z-G+2))**2
    root = cube_root_floor(squared_seam-2)
    T = root if root % 2 else root-1
    assert T**3+2 <= squared_seam < (T+2)**3+2
    cap = (T+1)**2-2
    gap = m**3-cap
    previous = previous_ceiling_record(m)["new_maximum_ceiling"]
    assert cap < previous and gap > 0
    assert (2*gap)**128 > m**253
    return {"minimum": m, "least_even_seam_gap": G, "odd_projected_return": z,
            "seam_squared_product": squared_seam, "max_retained_odd_base": T,
            "new_maximum_ceiling": cap, "previous_periodic_ceiling": previous,
            "ceiling_improvement": previous-cap, "cube_gap": gap,
            "gap_bound_certificate": "(59049*G)^128 > 26240^128*m^13",
            "smooth_strip_integer_certificate": "(2*cube_gap)^128 > minimum^253",
            "periodicity": "not asserted; conditional bound evaluation only"}


def rational_constant_record() -> dict:
    """Exact rational checks supporting, but not replacing, the written proof."""
    alpha, beta = Fraction(9, 8), Fraction(3, 4)
    word = "OOEOOEOE"
    prefixes, product = [], Fraction(1)
    for letter in word:
        product *= Fraction(3, 2) if letter == "O" else Fraction(1, 2)
        prefixes.append(product)
    gamma = product
    tails = [gamma/prefix for prefix in prefixes[:-1]]
    assert tails == list(map(lambda pair: Fraction(*pair),
                            ((81, 128), (27, 64), (27, 32), (9, 16), (3, 8), (3, 4), (1, 2))))
    powers = [(24*(1-q)).numerator//(24*(1-q)).denominator for q in tails]
    majorants = [q/2**k for q, k in zip(tails, powers)]
    tail_sum = sum(majorants, Fraction(0))
    assert tail_sum == Fraction(63121, 524288) < Fraction(1, 8)
    assert Fraction(39, 32) > Fraction(6, 5) and 2**16 > 3**10
    assert gamma/Fraction(9, 4) == Fraction(27, 64)
    coefficient_exponent = 1+beta*(1+alpha+alpha**2)
    assert coefficient_exponent == Fraction(907, 256) < 4
    assert Fraction(7, 8)**4 > Fraction(1, 2)
    assert 15*(alpha**3*beta-1) > 1
    assert alpha*gamma**2 == Fraction(531441, 524288)
    assert alpha*gamma**3 == Fraction(129140163, 134217728) < 1
    assert 24*(alpha*gamma**2-1) > Fraction(1, 4)
    assert Fraction(9, 8)**4 < 2
    kappa = Fraction(27, 64)
    numerator = 2-Fraction(9, 8)*(1+kappa)
    gap_coefficient = numerator/gamma**2
    assert numerator == Fraction(205, 512)
    assert gap_coefficient == Fraction(26240, 59049)
    assert Fraction(5, 6)*gap_coefficient == Fraction(65600, 177147) > Fraction(1, 3)
    assert 2*(1-gamma) == Fraction(13, 128)
    assert Fraction(3, 2)+Fraction(3, 8)+Fraction(13, 128) == Fraction(253, 128)
    return {"word": word, "ideal_exponent": str(gamma),
            "proper_prefix_tail_exponents": list(map(str, tails)),
            "dyadic_majorants": list(map(str, majorants)), "tail_sum": str(tail_sum),
            "error_bound": "9/8", "derivative_majorant": str(kappa),
            "A3B_coefficient_exponent": str(coefficient_exponent),
            "two_transfer_gap_coefficient": str(gap_coefficient),
            "height_strip_exponent": "253/128", "height_strip_coefficient": "1/2",
            "role": "exact constants in the written argument; not a Lean proof"}


def report() -> dict:
    records = [archived_cycle_record(b, cycle) for b, cycle in ABSOLUTE_CELL_THRESHOLD_CYCLES]
    assert len(records) == 7
    return {
        "scope": {"archived_threshold_cycles": 7, "induction_cycles": 5,
                  "singleton_sections_excluded": 2,
                  "ceiling_minima": list(CEILING_MINIMA), "ceiling_evaluations": 2,
                  "cycle_search": False, "source_census": False,
                  "rank_pair_scan": False, "trajectory_extension": False,
                  "descent_floor_increase": False},
        "arithmetic": "Exact integer cells and rational constants; no numerical roots or logarithms",
        "constant_checks": rational_constant_record(), "archived_cycles": records,
        "conditional_ceilings": [ceiling_record(m) for m in CEILING_MINIMA],
        "written_bound": "If a Juggler cycle has m>=2^24 and M<m^3, then M<m^3-(1/2)*m^(253/128)",
        "proof_status": "written mathematical proof; this probe provides bounded controls only",
        "new_theorem_formalized_in_lean": False,
        "uniform_gap_propagation_proved": False, "universal_wrong_parity_proved": False,
        "tall_cycles_excluded": False, "new_period_bound": False, "no_cycle_proved": False,
    }


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=DATA_ROOT / "cycle_direction_change/summary.json")
    args = parser.parse_args(argv)
    data = report()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(data, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({"scope": data["scope"], "conditional_ceilings": data["conditional_ceilings"],
                      "no_cycle_proved": False}, indent=2))


if __name__ == "__main__":
    main()

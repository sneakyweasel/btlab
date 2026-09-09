"""Fixed-word constants and seven archived return replays; no orbit search."""
from __future__ import annotations

import argparse
from fractions import Fraction
import json
from math import isqrt
from pathlib import Path

from research.juggler_sequence.lean_paths import DATA_ROOT
from research.juggler_sequence.cycle_cubic_band import ABSOLUTE_CELL_THRESHOLD_CYCLES
from research.juggler_sequence.cycle_periodic_carries import cube_root_floor
from research.juggler_sequence import cycle_direction_change as direction

MINIMUM = 2**128
CEILING_MINIMUM = MINIMUM+1
A = "OOE"
C = A*2+"OE"
D = A+C*2
W = D*3+C
V = D*4+C
WORDS = {"A": A, "C": C, "D": D, "W": W, "V": V}


def exponent(word: str) -> Fraction:
    if any(letter not in "OE" for letter in word):
        raise ValueError("original O/E letters required")
    return Fraction(3**word.count("O"), 2**len(word))


def prefix_exponents(word: str) -> list[Fraction]:
    values, current = [], Fraction(1)
    for letter in word:
        if letter not in "OE":
            raise ValueError("original O/E letters required")
        current *= Fraction(3, 2) if letter == "O" else Fraction(1, 2)
        values.append(current)
    return values


def fixed_word_constants() -> dict:
    records = {}
    for name, word in WORDS.items():
        prefixes = prefix_exponents(word)
        assert prefixes[-1] == exponent(word)
        records[name] = {"word": word, "length": len(word), "odd_count": word.count("O"),
                         "ideal_exponent": str(prefixes[-1]),
                         "nonempty_prefix_exponents": list(map(str, prefixes)),
                         "minimum_proper_prefix_exponent": str(min(prefixes[:-1]))}
    gamma, delta, rho, epsilon = map(exponent, (C, D, W, V))
    assert gamma == Fraction(243, 256) and delta == Fraction(531441, 524288)
    assert (len(W), W.count("O")) == (65, 41)
    assert (len(V), V.count("O")) == (84, 53)
    assert rho == Fraction(3**41, 2**65) < 1
    assert epsilon == Fraction(3**53, 2**84) > 1+Fraction(1, 512)
    assert min(prefix_exponents(D)[:-1]) > delta > 1
    assert min(prefix_exponents(C)[:-1]) > 1
    assert min(prefix_exponents(W)[:-1]) == delta
    assert min(prefix_exponents(V)[:-1]) == delta > epsilon
    tails = [rho/prefix for prefix in prefix_exponents(W)[:-1]]
    assert len(tails) == 64 and all(0 < tail < 1 for tail in tails)
    powers = [(128*(1-tail)).numerator//(128*(1-tail)).denominator for tail in tails]
    majorants = [tail/2**power for tail, power in zip(tails, powers)]
    total = sum(majorants, Fraction(0))
    assert total == Fraction(277910493483851358096413315698577150111783, 2**140)
    assert total < Fraction(1, 5)
    assert 128*(1-rho) > Fraction(10, 7) and 2**10*3**7 > 8**7
    assert 128*(1-gamma) == Fraction(13, 2) > 6 and gamma < 1
    assert 128*(epsilon-1) > Fraction(1, 4)
    assert Fraction(9, 8)**4 < 2 and MINIMUM > 8*84
    numerator = 2-Fraction(6, 5)-Fraction(3, 8)*Fraction(9, 8)*(1+Fraction(1, 64))
    assert numerator == Fraction(7609, 20480)
    C0 = numerator/(gamma**2*rho)
    sigma = Fraction(13, 128)+1-rho
    theta = Fraction(15, 8)+sigma
    assert C0 > Fraction(2, 5) and Fraction(7, 64) < sigma < Fraction(1, 8)
    assert theta == Fraction(381, 128)-rho and Fraction(127, 64) < theta < 2
    assert Fraction(7, 8)*Fraction(2, 5) > Fraction(1, 3)
    assert Fraction(3, 2)+Fraction(3, 8)+Fraction(7, 64) == Fraction(127, 64)
    return {"words": records, "minimum_scale_exponent": 128,
            "W_proper_tail_exponents": list(map(str, tails)),
            "W_dyadic_majorants": list(map(str, majorants)), "W_tail_sum": str(total),
            "W_error_bound": "6/5", "W_derivative_majorant": "3/8",
            "C_error_bound": "9/8", "C_derivative_majorant": "1/64",
            "three_transfer_numerator": str(numerator), "sharp_gap_coefficient_C0": str(C0),
            "sharp_gap_exponent_sigma": str(sigma),
            "sharp_written_height_exponent_theta": str(theta),
            "clean_gap_coefficient": "2/5", "clean_gap_exponent": "7/64",
            "clean_height_strip_coefficient": "1/2", "clean_height_strip_exponent": "127/64",
            "role": "exact constants supporting the written proof, not a uniform or Lean certificate"}


def follow_archived(start: int, word: str, cells: dict[int, dict]) -> list[int]:
    """Read at most one lap of existing edges, never compute a new trajectory."""
    if len(word) > len(cells):
        raise ValueError("at most one archived lap required")
    trace = [start]
    for letter in word:
        edge = cells[trace[-1]]
        assert edge["branch"] == letter
        trace.append(edge["image"])
    return trace


def archived_record(threshold: int, cyclic: tuple[int, ...]) -> dict:
    replay = direction.archived_cycle_record(threshold, cyclic)
    cells = {cell["source"]: cell for cell in replay["original_cells"]}
    total = Fraction(3**sum(cell["branch"] == "O" for cell in cells.values()), 2**len(cells))
    assert total > 1
    result = {"threshold": threshold, "minimum": replay["minimum"], "period": replay["period"],
              "original_cells": replay["original_cells"],
              "wrong_parity_sources": replay["wrong_parity_sources"],
              "actual_juggler_cycle": replay["actual_juggler_cycle"],
              "rank_induction_excluded": replay["rank_induction_excluded"],
              "all_original_cells_and_mismatches_replayed": True,
              "total_ideal_exponent": str(total), "off_domain_lower_guard_asserted": False}
    assert result["wrong_parity_sources"] and not result["actual_juggler_cycle"]
    if replay["rank_induction_excluded"]:
        result.update({"stages": [], "terminal": None,
                       "exclusion_reason": replay["exclusion_reason"]})
        return result
    P, Q = "O", "OE"
    stages = []
    last = None
    for stage in replay["stages"]:
        a, b, U, upper = (stage[key] for key in ("a", "b", "A", "B"))
        lower_exp, upper_exp = exponent(U), exponent(upper)
        assert lower_exp**a*upper_exp**b == total
        record = {"a": a, "b": b, "lower_word": U, "upper_word": upper,
                  "lower_exponent": str(lower_exp), "upper_exponent": str(upper_exp),
                  "weighted_ideal_exponent": str(total)}
        if a > 0 and b > 0:
            assert U+upper == P+"OE"+Q and upper+U == P+"EO"+Q
            record.update({"common_prefix_P": P, "common_suffix_Q": Q})
            last = (stage, P, Q)
            if a > b:
                P = U+P
            elif b > a:
                Q = Q+upper
        stages.append(record)
    assert last is not None
    terminal_stage, P, Q = last
    assert terminal_stage["a"] == terminal_stage["b"] == 1
    m, v = terminal_stage["retained_bases"]
    U, upper = terminal_stage["A"], terminal_stage["B"]
    assert follow_archived(m, U, cells)[-1] == v
    assert follow_archived(v, upper, cells)[-1] == m
    assert follow_archived(m, U+upper, cells)[-1] == m
    assert follow_archived(v, upper+U, cells)[-1] == v
    low_prefix = follow_archived(m, P, cells)
    high_prefix = follow_archived(v, P, cells)
    p, h = low_prefix[-1], high_prefix[-1]
    ordered = sorted(cells)
    rank = {x: i for i, x in enumerate(ordered)}
    assert all(rank[y] == rank[x]+1 for x, y in zip(low_prefix, high_prefix))
    assert p == max(x for x, cell in cells.items() if cell["branch"] == "O")
    assert h == min(x for x, cell in cells.items() if cell["branch"] == "E")
    M = max(cells)
    t, q = cells[M]["image"], cells[m]["image"]
    low_mixed = follow_archived(p, "OE", cells)
    high_mixed = follow_archived(h, "EO", cells)
    assert low_mixed == [p, M, t] and high_mixed == [h, m, q]
    low_suffix = follow_archived(t, Q, cells)
    high_suffix = follow_archived(q, Q, cells)
    assert low_suffix[-1] == m and high_suffix[-1] == v
    assert exponent(P)*Fraction(3, 4)*exponent(Q) == total
    mixed_guards = all(not cells[x]["wrong_parity"] for x in (p, M, h, m))
    if mixed_guards:
        assert q-t < h-p
    result.update({"stages": stages,
                   "terminal": {"states": [m, v], "lower_word": U, "upper_word": upper,
                                "common_prefix_P": P, "common_suffix_Q": Q,
                                "prefix_traces": [low_prefix, high_prefix],
                                "mixed_traces": [low_mixed, high_mixed],
                                "suffix_traces": [low_suffix, high_suffix],
                                "mixed_source_gap": h-p, "mixed_image_gap": q-t,
                                "mixed_actual_parity_hypotheses": mixed_guards,
                                "terminal_section_size": 1, "extra_seam_transfer": False,
                                "off_domain_lower_guard_asserted": False}})
    return result


def least_even_gap(m: int) -> int:
    if m < MINIMUM:
        raise ValueError("minimum at least 2^128 required")
    rhs = 2**64*m**7
    def allowed(half: int) -> bool:
        return (10*half)**64 > rhs
    low, high = 3, 4
    while not allowed(high):
        low, high = high, 2*high
    while low+1 < high:
        middle = (low+high)//2
        if allowed(middle):
            high = middle
        else:
            low = middle
    G = 2*high
    assert G >= 8 and (5*G)**64 > rhs
    assert G == 8 or (5*(G-2))**64 <= rhs
    return G


def ceiling_record(m: int) -> dict:
    if m < MINIMUM or m % 2 == 0:
        raise ValueError("odd minimum at least 2^128 required")
    G = least_even_gap(m)
    H = isqrt(isqrt(isqrt(m**9)))
    z = H if H % 2 else H-1
    assert z**8 <= m**9 < (z+2)**8 and z-G > 0
    squared_seam = ((z-G)*(z-G+2))**2
    root = cube_root_floor(squared_seam-2)
    T = root if root % 2 else root-1
    assert T**3+2 <= squared_seam < (T+2)**3+2
    cap = (T+1)**2-2
    previous = direction.ceiling_record(m)["new_maximum_ceiling"]
    gap = m**3-cap
    assert cap < previous and gap > 0 and (2*gap)**64 > m**127
    return {"minimum": m, "least_even_gap": G, "odd_projected_return": z,
            "seam_squared_product": squared_seam, "max_retained_odd_base": T,
            "new_maximum_ceiling": cap, "previous_direction_change_ceiling": previous,
            "ceiling_improvement": previous-cap, "cube_gap": gap,
            "gap_certificate": "(5*G)^64 > 2^64*minimum^7",
            "clean_strip_certificate": "(2*cube_gap)^64 > minimum^127",
            "sharp_rational_power_evaluated": False,
            "periodicity": "not asserted; one conditional bound evaluation only"}


def report() -> dict:
    return {"scope": {"fixed_words": list(WORDS), "W_tail_terms": 64,
                      "minimum_scale_exponent": 128, "archived_threshold_cycles": 7,
                      "singleton_sections_excluded": 2, "ceiling_evaluations": 1,
                      "ceiling_minima": [CEILING_MINIMUM], "cycle_search": False,
                      "source_census": False, "rank_pair_scan": False,
                      "trajectory_extension": False, "descent_floor_increase": False},
            "arithmetic": "Exact fractions, integer cells and power comparisons only",
            "constant_checks": fixed_word_constants(),
            "archived_cycles": [archived_record(b, cycle) for b, cycle in ABSOLUTE_CELL_THRESHOLD_CYCLES],
            "conditional_ceiling": ceiling_record(CEILING_MINIMUM),
            "written_bound": "If a Juggler cycle has m>=2^128 and M<m^3, then M<m^3-(1/2)*m^(127/64)",
            "proof_status": "written mathematical proof; bounded controls do not replace it",
            "uniform_fixed_minimum_certificate": False,
            "new_theorem_formalized_in_lean": False, "uniform_gap_propagation_proved": False,
            "universal_wrong_parity_proved": False, "tall_cycles_excluded": False,
            "new_period_bound": False, "no_cycle_proved": False}


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DATA_ROOT / "cycle_later_returns/summary.json")
    args = parser.parse_args(argv)
    data = report()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(data, indent=2)+"\n", encoding="utf-8")
    print(json.dumps({"scope": data["scope"], "conditional_ceiling": data["conditional_ceiling"],
                      "no_cycle_proved": False}, indent=2))


if __name__ == "__main__":
    main()

"""Check finite inverse budgets against independent forward integer enumeration."""

from fractions import Fraction as Q
from itertools import combinations

import pytest

from research.collatz.fibre_height_budget import budget_coefficient, diagnostic, error_bound


@pytest.mark.parametrize("sign,target", [(1, 1), (1, 7), (-1, 1), (-1, 47)])
def test_conditioned_compositions_select_exactly_two_ternary_cells(sign, target):
    # Enumerate global affine offsets independently of the inverse recurrence.
    # The source-unit guard removes one of the three lifts modulo 3**(depth+1).
    for depth in range(1, 5):
        modulus = 3 ** (depth + 1)
        cells = {(sign * target + t * 3**depth) % modulus for t in (1, 2)}
        for total in range(depth, 11):
            count = 0
            for cuts in combinations(range(1, total), depth - 1):
                boundaries = (0, *cuts, total)
                word = tuple(b - a for a, b in zip(boundaries, boundaries[1:]))
                offset, prefix = 0, 0
                for exponent in word:
                    offset = 3 * offset + 2**prefix
                    prefix += exponent
                residue = offset * pow(2**total, -1, modulus) % modulus
                selected = residue in cells

                # Separately reconstruct the actual positive odd predecessors.
                n = target
                actual = True
                for exponent in reversed(word):
                    numerator = 2**exponent * n - sign
                    if numerator % 3:
                        actual = False
                        break
                    n = numerator // 3
                    assert n > 0 and n % 2 == 1
                actual = actual and n % 3 != 0
                assert selected == actual
                count += selected

            exact_layer = (budget_coefficient(target, depth, total, sign)
                           - budget_coefficient(target, depth, total - 1, sign))
            assert exact_layer == Q(3**depth * count, 2**total)


@pytest.mark.parametrize("sign,target", [(1, 1), (1, 7), (-1, 1), (-1, 47)])
def test_budget_equals_forward_enumeration_with_source_height_control(sign, target):
    # This independently enumerates actual sources. It does not call the
    # inverse-child evaluator or its recurrence to determine the answer.
    for budget in (0, 4, 8):
        masses = [Q(0) for _ in range(4)]
        for source in range(1, target * 2**budget + 1, 2):
            if source % 3 == 0:
                continue
            n, total = source, 0
            for depth in range(4):
                if n == target and total <= budget:
                    masses[depth] += Q(3**depth, 2**total)
                n = 3 * n + sign
                while n % 2 == 0:
                    total += 1
                    n //= 2
        for depth, expected in enumerate(masses):
            assert budget_coefficient(target, depth, budget, sign) == expected


def test_complete_residue_operator_encloses_each_finite_budget():
    rows = diagnostic()
    assert len(rows) == 8
    for row in rows:
        difference = Q(row["complete"]) - Q(row["retained"])
        assert 0 <= difference <= Q(row["uniform_allowance"])


def test_eight_step_budget_has_summable_uniform_error():
    ratio = Q(19683, 32768)
    assert 0 < ratio < 1
    for depth in range(12):
        assert error_bound(depth, 8 * depth) == ratio**depth
    assert 1 / (1 - ratio) == Q(32768, 13085)


def test_total_budget_is_spent_across_all_steps_and_sterile_sources_are_removed():
    assert budget_coefficient(1, 2, 1) == 0
    assert budget_coefficient(3, 0, 0) == 0
    assert budget_coefficient(3, 3, 24, -1) == 0
    with pytest.raises(ValueError):
        budget_coefficient(2, 2, 16)

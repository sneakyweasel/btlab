"""Finite total-exponent approximations to complete signed inverse coefficients.

The uniform error theorem is in Problems.Collatz.FibreHeightBudget. This
small exact evaluator supplies controls, not evidence for series divergence.
"""

from fractions import Fraction
from functools import cache


def budget_coefficient(target: int, depth: int, total_halvings: int, sign: int = 1) -> Fraction:
    """Sum 3**depth/2**K over unit ancestors with total halving exponent K <= budget."""
    if sign not in (-1, 1):
        raise ValueError("sign must be -1 or 1")
    if target < 1 or target % 2 == 0:
        raise ValueError("target must be positive and odd")
    if depth < 0 or total_halvings < 0:
        raise ValueError("depth and total_halvings must be nonnegative")

    @cache
    def visit(m: int, d: int, budget: int) -> Fraction:
        if d == 0:
            return Fraction(m % 3 != 0)
        if budget < d or m % 3 == 0:
            return Fraction()
        result = Fraction()
        for k in range(1, budget - d + 2):
            numerator = 2**k * m - sign
            if numerator % 3 == 0:
                result += Fraction(3, 2**k) * visit(numerator // 3, d - 1, budget - k)
        return result

    return visit(target, depth, total_halvings)


def error_bound(depth: int, total_halvings: int) -> Fraction:
    """Uniform geometric-moment allowance; it need not be sharp at small budgets."""
    if depth < 0 or total_halvings < 0:
        raise ValueError("depth and total_halvings must be nonnegative")
    return 6**depth * Fraction(3, 4)**total_halvings


def diagnostic() -> list[dict]:
    """Compare with independently computed complete residue coefficients at three depths."""
    from research.collatz.fibre_mass import residue_transfer

    rows = []
    for sign, target in ((1, 7), (-1, 47)):
        table = (Fraction(0), Fraction(1), Fraction(1))
        for depth in range(4):
            budget = 8 * depth
            retained = budget_coefficient(target, depth, budget, sign)
            full = table[target % len(table)]
            allowance = error_bound(depth, budget)
            assert 0 <= full - retained <= allowance
            rows.append({
                "sign": sign, "target": target, "depth": depth,
                "total_halvings": budget, "complete": str(full),
                "retained": str(retained), "omitted": str(full - retained),
                "uniform_allowance": str(allowance),
                "source_height_bound": target * 2**budget,
            })
            if depth < 3:
                table = residue_transfer(table, sign)
    return rows


if __name__ == "__main__":
    import json

    print(json.dumps(diagnostic(), indent=2))

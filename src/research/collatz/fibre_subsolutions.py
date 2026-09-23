"""Exact capped lower/upper iterations at four fixed subcritical rates.

The upper iteration starts at the unit cap, so it bounds every feasible
periodic weight, not merely the chosen lower certificate. No limiting
rate or fixed-root divergence is inferred from these finite brackets.
"""

from fractions import Fraction
import json
from pathlib import Path

from research.collatz.fibre_critical_minorants import integer_rows, verify


SCALE = 10**12
ITERATION_LIMIT = 2000
GAP_TOLERANCE = 1000
RATES = {1: Fraction(1, 4), 2: Fraction(1, 2),
         3: Fraction(2, 3), 4: Fraction(3, 4)}
SEEDS = Path('data/research/collatz/fibre_critical_minorants.json')
DESTINATION = Path('data/research/collatz/fibre_subsolutions.json')


def capped_step(weights, level, rate, denominator, sparse_rows, *, upward):
    """Round the capped minimum of all refined inverse rows on an integer grid."""
    size = 3**level
    image = [SCALE if a % 3 else 0 for a in range(size)]
    divisor = denominator * rate.numerator
    for target, row in sparse_rows:
        numerator = rate.denominator * sum(c * weights[a] for a, c in row)
        rounded = (numerator + (divisor - 1 if upward else 0)) // divisor
        image[target % size] = min(image[target % size], rounded)
    return image


def bracket(seed):
    """Bracket the greatest subsolution using only exact integer operations."""
    level, sign = seed['level'], seed['sign']
    rate = RATES[level]
    denominator, rows = integer_rows(level, sign)
    sparse_rows = [(target, [(a, c) for a, c in enumerate(row) if c])
                   for target, row in rows]
    seed_max = max(seed['weights'])
    assert SCALE % seed_max == 0
    lower = [w * (SCALE // seed_max) for w in seed['weights']]
    initial = lower.copy()
    assert verify(level, sign, lower, rate)[0]
    upper = [SCALE if a % 3 else 0 for a in range(3**level)]
    for iteration in range(1, ITERATION_LIMIT + 1):
        next_lower = capped_step(lower, level, rate, denominator, sparse_rows, upward=False)
        next_upper = capped_step(upper, level, rate, denominator, sparse_rows, upward=True)
        assert all(l <= nl <= nu <= u for l, nl, nu, u in
                   zip(lower, next_lower, next_upper, upper))
        lower, upper = next_lower, next_upper
        if max(u - l for l, u in zip(lower, upper)) <= GAP_TOLERANCE:
            break
    passed, slack = verify(level, sign, lower, rate)
    assert passed
    root = 7 if sign == 1 else 47
    position = root % (3**level)
    gap = max(u - l for l, u in zip(lower, upper))
    return {
        'level': level, 'sign': sign, 'rate': str(rate), 'scale': SCALE,
        'iterations': iteration, 'converged_to_tolerance': gap <= GAP_TOLERANCE,
        'maximum_gap': gap, 'initial_lower': initial, 'lower': lower, 'upper': upper,
        'minimum_integer_slack': str(slack), 'exact_rows_checked': len(rows),
        'fixed_root': {
            'root': root,
            'initial_over_deficit': str(Fraction(initial[position], SCALE) / (1-rate)),
            'lower_over_deficit': str(Fraction(lower[position], SCALE) / (1-rate)),
            'upper_over_deficit': str(Fraction(upper[position], SCALE) / (1-rate)),
        },
    }


def report():
    seeds = json.loads(SEEDS.read_text(encoding='utf-8'))['certificates']
    return {
        'scope': 'Both signs, levels 1..4, one fixed rational rate per level; no asymptotic conclusion.',
        'iteration_limit': ITERATION_LIMIT, 'gap_tolerance': GAP_TOLERANCE,
        'upper_bound_basis': 'Replay the rounded decreasing iteration from the unit cap.',
        'certificates': [bracket(seed) for seed in seeds],
    }


if __name__ == '__main__':
    result = report()
    DESTINATION.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    for item in result['certificates']:
        print({key: item[key] for key in
               ('sign', 'level', 'rate', 'iterations', 'maximum_gap', 'fixed_root')})

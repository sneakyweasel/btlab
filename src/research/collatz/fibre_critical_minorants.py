"""Small exact subcritical certificates for the complete signed inverse operator.

Floating iteration proposes periodic weights. Integer arithmetic checks every
refined residue and every exponent through an exact geometric period. No
critical limit or fixed-root divergence is inferred from these finite records.
"""

from fractions import Fraction
import json
from pathlib import Path

import numpy as np


def integer_rows(level: int, sign: int):
    """Return the exact common denominator and all unit-target numerator rows."""
    if level not in range(1, 5) or sign not in (-1, 1):
        raise ValueError('the bounded audit covers signs +/-1 and levels 1..4')
    size = 3**level
    period = 2*size
    denominator = 2**period - 1
    rows = []
    for target in range(3*size):
        if target % 3 == 0:
            continue
        row = [0]*size
        residue = target
        for exponent in range(1, period + 1):
            residue = 2*residue % (3*size)
            if (residue - sign) % 3 == 0:
                child = ((residue - sign)//3) % size
                row[child] += 3 * 2**(period - exponent)
        rows.append((target, row))
    return denominator, rows


def verify(level: int, sign: int, weights: list[int], rate: Fraction):
    """Check L h >= rate*h at every refined target, with exact integer slack."""
    size = 3**level
    if len(weights) != size or not 0 < rate < 1:
        return False, None
    if any(not isinstance(w, int) or (w <= 0 if a % 3 else w != 0)
           for a, w in enumerate(weights)):
        return False, None
    denominator, rows = integer_rows(level, sign)
    slacks = [rate.denominator*sum(c*w for c, w in zip(row, weights))
              - rate.numerator*denominator*weights[target % size]
              for target, row in rows]
    return min(slacks) >= 0, min(slacks)


def certificate(level: int, sign: int):
    """Propose a weight, then round downward only the exactly checked rate."""
    denominator, rows = integer_rows(level, sign)
    size = 3**level
    units = [a for a in range(size) if a % 3]
    matrix = np.array([[float(Fraction(row[a], denominator)) for a in units]
                       for _, row in rows])
    positions = [[j for j, (target, _) in enumerate(rows) if target % size == a]
                 for a in units]
    v = np.ones(len(units))
    for iteration in range(20000):
        image = matrix @ v
        lower = np.array([min(image[j] for j in lifts) for lifts in positions])
        candidate = lower / max(lower)
        updated = (v + candidate)/2
        if max(abs(updated - v)) < 1e-13:
            v = updated
            break
        v = updated
    else:
        raise RuntimeError('candidate iteration exceeded its fixed budget')
    weights = [0]*size
    for a, value in zip(units, v):
        weights[a] = max(1, round(float(value)*10**9))
    exact_rate = min(Fraction(sum(c*w for c, w in zip(row, weights)),
                              denominator*weights[target % size])
                     for target, row in rows)
    rate = Fraction((exact_rate.numerator*10**9)//exact_rate.denominator, 10**9)
    passed, slack = verify(level, sign, weights, rate)
    assert passed
    leading = Fraction(min(weights[a] for a in units), max(weights))
    root = 7 if sign == 1 else 47
    root_leading = Fraction(weights[root % size], max(weights))
    return {
        'level': level, 'sign': sign, 'weights': weights,
        'rate': str(rate), 'leading_constant': str(leading),
        'leading_over_deficit': str(leading/(1-rate)),
        'minimum_integer_slack': str(slack), 'candidate_iterations': iteration + 1,
        'exact_rows_checked': len(rows),
        'fixed_root': {'root': root, 'leading_constant': str(root_leading),
                       'leading_over_deficit': str(root_leading/(1-rate))},
    }


def report():
    return {
        'scope': 'Exact finite certificates only; no limiting rate or divergence is proved.',
        'normalization': 'max(h)=1, h=0 on multiples of three; C_d(a)>=A*rate^d on units',
        'certificates': [certificate(level, sign) for sign in (1, -1)
                         for level in range(1, 5)],
    }


if __name__ == '__main__':
    result = report()
    destination = Path('data/research/collatz/fibre_critical_minorants.json')
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    for item in result['certificates']:
        print({key: item[key] for key in
               ('sign', 'level', 'rate', 'leading_constant', 'leading_over_deficit')})

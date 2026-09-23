"""Exact controls for geometric blocks of complete signed inverse generations.

The all-depth normalization obstruction is proved in Lean. This probe checks
the construction only at lengths 1..4; it performs no larger residue search.
"""

from fractions import Fraction as Q
import json
from pathlib import Path

from research.collatz.fibre_mass import residue_transfer


def block(sign: int, length: int):
    """Construct a rational block rate from its exact complete unit minimum."""
    if sign not in (-1, 1) or length not in range(1, 5):
        raise ValueError('the bounded control covers signs +/-1 and lengths 1..4')
    tables = [(Q(0), Q(1), Q(1))]
    for _ in range(length):
        tables.append(residue_transfer(tables[-1], sign))
    minimum = min(w for a, w in enumerate(tables[-1]) if a % 3)
    # Exact binary search, not a floating approximation to the nth root.
    scale, low, high = 10**9, 0, 10**9
    while low + 1 < high:
        middle = (low + high)//2
        if Q(middle, scale)**length <= minimum:
            low = middle
        else:
            high = middle
    rate = Q(low, scale)
    weights = tuple(sum(rate**(length-1-k)*tables[k][a % len(tables[k])]
                        for k in range(length)) for a in range(3**length))
    return rate, minimum, weights, tables


def record(sign: int, length: int):
    rate, minimum, weights, tables = block(sign, length)
    transferred = residue_transfer(weights, sign)
    for a, value in enumerate(transferred):
        remainder = tables[-1][a] - rate**length*(1 if a % 3 else 0)
        assert value - rate*weights[a % len(weights)] == remainder >= 0
    assert minimum <= Q(3, 4)
    assert 4*length*(1-rate) >= 1
    assert max(weights) >= Q(3, 2)**(length-1)
    root = 7 if sign == 1 else 47
    anchor = weights[root % len(weights)]/max(weights)
    return {'sign': sign, 'length': length, 'root': root,
            'block_minimum': str(minimum), 'rate': str(rate),
            'normalizer': str(max(weights)), 'root_weight': str(anchor),
            'root_weight_over_deficit': str(anchor/(1-rate))}


def report():
    return {'scope': 'Exact controls at lengths 1..4; the asymptotic obstruction is a separate Lean proof.',
            'blocks': [record(sign, n) for sign in (1, -1) for n in range(1, 5)]}


if __name__ == '__main__':
    result = report()
    destination = Path('data/research/collatz/fibre_block_weights.json')
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    for item in result['blocks']:
        print({'sign': item['sign'], 'length': item['length'],
               'rate': float(Q(item['rate'])),
               'root_weight_over_deficit': float(Q(item['root_weight_over_deficit']))})

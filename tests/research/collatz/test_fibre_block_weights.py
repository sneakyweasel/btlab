"""Exact block identities and independent actual-endpoint controls."""

from fractions import Fraction as Q
import json
from pathlib import Path

import pytest

from research.collatz.fibre_block_weights import block, record
from research.collatz.fibre_mass import transfer_iterate


REPORT = Path(__file__).resolve().parents[3] / 'data/research/collatz/fibre_block_weights.json'


@pytest.mark.parametrize('sign', [1, -1])
@pytest.mark.parametrize('length', [1, 2, 3, 4])
def test_block_identity_floor_and_normalization(sign, length):
    saved = json.loads(REPORT.read_text(encoding='utf-8'))['blocks']
    expected = next(r for r in saved if r['sign'] == sign and r['length'] == length)
    assert record(sign, length) == expected
    rate, minimum, weights, tables = block(sign, length)
    # Independent first-digit marginal: its exact mean is 2/3.
    low_class = 1 if sign == 1 else 2
    values = [w for a, w in enumerate(tables[-1]) if a % 3 == low_class]
    assert sum(values)/len(values) == Q(2, 3)
    assert rate**length <= minimum <= Q(2, 3)
    assert all(0 <= w/max(weights) <= 1 for w in weights)
    # The fully enumerated maximum must cover the one-halving residue.
    assert max(weights) >= weights[(-sign) % len(weights)] >= Q(3, 2)**(length-1)


def endpoints(root, depth, budget, sign):
    """Enumerate actual integer words; never combine repeated endpoints."""
    if depth == 0:
        return [(root, 0, Q(1))]
    result = []
    for exponent in range(1, budget + 1):
        numerator = 2**exponent*root-sign
        if numerator % 3 == 0:
            child = numerator//3
            for source, spent, coefficient in endpoints(child, depth-1, budget-exponent, sign):
                result.append((source, spent+exponent, Q(3, 2**exponent)*coefficient))
    return result


@pytest.mark.parametrize('sign,root', [(1, 7), (-1, 47)])
@pytest.mark.parametrize('depth', [1, 2, 3])
def test_budget_counts_distinct_actual_endpoints_and_has_geometric_tail(sign, root, depth):
    words = endpoints(root, depth, 8*depth, sign)
    sources = [n for n, _, _ in words]
    assert len(sources) == len(set(sources))
    for source, spent, coefficient in words:
        assert 1 <= source <= root*2**(8*depth) and source % 2 == 1
        x, actual_spent, affine_product = source, 0, Q(1)
        for _ in range(depth):
            affine_product *= 1 + Q(sign, 3*x)
            x = 3*x + sign
            while x % 2 == 0:
                x //= 2
                actual_spent += 1
        assert x == root and actual_spent == spent
        assert coefficient == Q(3**depth, 2**spent)
        assert coefficient*source*affine_product == root
        if sign == 1:
            assert coefficient <= Q(root, source)
    retained = sum(c for n, _, c in words if n % 3)
    complete = transfer_iterate((0, 1, 1), depth, sign)
    assert retained <= complete[root % len(complete)]
    assert complete[root % len(complete)] <= retained + Q(19683, 32768)**depth


def test_negative_fixed_point_retains_the_excluded_exponential_peak():
    for depth in range(1, 4):
        table = transfer_iterate((0, 1, 1), depth, -1)
        assert table[1] >= Q(3, 2)**depth

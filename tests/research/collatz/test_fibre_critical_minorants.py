"""Independent full-exponent checks of the small subcritical certificates."""

from fractions import Fraction as Q
import json
from pathlib import Path

import pytest

from research.collatz.fibre_critical_minorants import verify


REPORT = Path(__file__).resolve().parents[3] / 'data/research/collatz/fibre_critical_minorants.json'


def actual_transfer(target, weights, sign):
    """Use ordinary integer predecessors, then sum the infinite geometric period."""
    size = len(weights)
    period = 2*size
    assert pow(2, period, 3*size) == 1
    assert target > 0 and target % 2 == 1 and target % 3 != 0
    total = Q(0)
    for exponent in range(1, period + 1):
        raw = 2**exponent * target - sign
        if raw % 3 == 0:
            source = raw // 3
            assert source > 0 and source % 2 == 1
            total += Q(3, 2**exponent)*weights[source % size]
    return total/(1-Q(1, 2**period))


@pytest.mark.parametrize('sign', [1, -1])
@pytest.mark.parametrize('level', [1, 2, 3, 4])
def test_each_certificate_covers_all_refined_residues_and_all_exponents(sign, level):
    records = json.loads(REPORT.read_text(encoding='utf-8'))['certificates']
    record = next(c for c in records if c['sign'] == sign and c['level'] == level)
    weights, rate = record['weights'], Q(record['rate'])
    size = 3**level
    minimum, maximum = min(w for w in weights if w), max(weights)
    assert Q(record['leading_constant']) == Q(minimum, maximum)
    assert Q(record['leading_over_deficit']) == Q(minimum, maximum)/(1-rate)
    root = record['fixed_root']['root']
    root_leading = Q(weights[root % size], maximum)
    assert root_leading == Q(record['fixed_root']['leading_constant'])
    assert root_leading/(1-rate) == Q(record['fixed_root']['leading_over_deficit'])
    ratios = []
    for residue in range(3*size):
        if residue % 3 == 0:
            continue
        target = residue if residue % 2 else residue + 3*size
        value = actual_transfer(target, weights, sign)
        ratios.append(value/weights[target % size])
        assert value >= rate*weights[target % size]
    assert len(ratios) == record['exact_rows_checked'] == 2*size
    passed, slack = verify(level, sign, weights, rate)
    assert passed and str(slack) == record['minimum_integer_slack']
    # A strictly stronger rate than the actual worst row must be rejected.
    assert not verify(level, sign, weights, (1+min(ratios))/2)[0]


@pytest.mark.parametrize('sign,weights', [(1, [0, 1, 2]), (-1, [0, 2, 1])])
def test_first_level_has_the_exact_two_sevenths_certificate(sign, weights):
    assert verify(1, sign, weights, Q(2, 7)) == (True, 0)
    assert not verify(1, sign, weights, Q(13, 45))[0]
    wrong_support = [1, *weights[1:]]
    assert not verify(1, sign, wrong_support, Q(2, 7))[0]

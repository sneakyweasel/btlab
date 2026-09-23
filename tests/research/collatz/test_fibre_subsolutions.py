"""Independent exact replay of the lower and universal upper brackets."""

from fractions import Fraction as Q
import json
from pathlib import Path

import pytest

from research.collatz.fibre_critical_minorants import verify


REPORT = Path(__file__).resolve().parents[3] / 'data/research/collatz/fibre_subsolutions.json'


def ordinary_rows(level, sign):
    """Build rows from ordinary positive odd predecessors, independently of modular doubling."""
    size, period = 3**level, 2*3**level
    denominator = 2**period - 1
    rows = {a: [] for a in range(size) if a % 3}
    for residue in range(3*size):
        if not residue % 3:
            continue
        target = residue if residue % 2 else residue + 3*size
        coefficients = {}
        for e in range(1, period + 1):
            raw = 2**e * target - sign
            if raw % 3:
                continue
            child = raw // 3
            assert child > 0 and child % 2 == 1
            assert (2**(e+period)*target-sign)//3 % size == child % size
            a = child % size
            coefficients[a] = coefficients.get(a, 0) + 3*2**(period-e)
        rows[residue % size].append(coefficients)
    assert all(len(lifts) == 3 for lifts in rows.values())
    return denominator, rows


@pytest.mark.parametrize('sign', [1, -1])
@pytest.mark.parametrize('level', [1, 2, 3, 4])
def test_saved_bounds_cover_the_greatest_weight_by_exact_cap_replay(sign, level):
    report = json.loads(REPORT.read_text(encoding='utf-8'))
    record = next(c for c in report['certificates'] if c['sign'] == sign and c['level'] == level)
    scale, rate = record['scale'], Q(record['rate'])
    denominator, rows = ordinary_rows(level, sign)
    lower = record['initial_lower']
    upper = [scale if a % 3 else 0 for a in range(3**level)]
    assert verify(level, sign, lower, rate)[0]
    divisor = denominator * rate.numerator
    assert 1 <= record['iterations'] <= report['iteration_limit'] == 2000
    for _ in range(record['iterations']):
        new_lower, new_upper = [0]*len(lower), [0]*len(upper)
        for a, lifts in rows.items():
            lo = min(sum(c*lower[b] for b, c in row.items()) for row in lifts)
            hi = min(sum(c*upper[b] for b, c in row.items()) for row in lifts)
            new_lower[a] = min(scale, rate.denominator*lo // divisor)
            new_upper[a] = min(scale, -(-rate.denominator*hi // divisor))
        assert all(l <= nl <= nu <= u for l, nl, nu, u in
                   zip(lower, new_lower, new_upper, upper))
        lower, upper = new_lower, new_upper
    assert lower == record['lower'] and upper == record['upper']
    # Recheck feasibility directly with the independently constructed rows.
    slacks = [rate.denominator*sum(c*lower[b] for b, c in row.items())
              - divisor*lower[a] for a, lifts in rows.items() for row in lifts]
    assert min(slacks) >= 0
    assert str(min(slacks)) == record['minimum_integer_slack']
    gap = max(u-l for l, u in zip(lower, upper))
    assert gap == record['maximum_gap'] <= report['gap_tolerance']
    assert record['converged_to_tolerance']
    root = record['fixed_root']['root'] % len(lower)
    for key, vector in [('initial', record['initial_lower']), ('lower', lower), ('upper', upper)]:
        assert Q(vector[root], scale)/(1-rate) == Q(record['fixed_root'][key+'_over_deficit'])
    # A feasible lower table alone would not justify an upper claim: zero is
    # always another fixed point, so upper bounds must replay from the cap.
    assert max(upper) == scale and min(lower[a] for a in rows) > 0


@pytest.mark.parametrize('sign,root_class', [(1, 1), (-1, 2)])
def test_first_level_brackets_the_closed_form_solution(sign, root_class):
    records = json.loads(REPORT.read_text(encoding='utf-8'))['certificates']
    record = next(c for c in records if c['sign'] == sign and c['level'] == 1)
    # At q=1/4 the active small coordinate is 4/5; the other is capped at 1.
    exact = [Q(0), Q(1), Q(1)]
    exact[root_class] = Q(4, 5)
    denominator, rows = ordinary_rows(1, sign)
    for a, lifts in rows.items():
        image = min(sum(c*exact[b] for b, c in row.items()) / denominator for row in lifts)
        assert exact[a] == min(Q(1), 4*image)
        assert Q(record['lower'][a], record['scale']) <= exact[a]
        assert exact[a] <= Q(record['upper'][a], record['scale'])

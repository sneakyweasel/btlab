"""Independent integer-branch controls for the bounded stopping obstruction."""

from fractions import Fraction as Q

import pytest

from research.collatz.fibre_mass import residue_transfer, syracuse


@pytest.mark.parametrize("sign,root", [(1, 7), (-1, 47)])
def test_optimal_two_step_deficit_at_actual_nonperiodic_targets(sign, root):
    base = (Q(0), Q(1), Q(1))
    first = residue_transfer(base, sign)
    envelope = tuple(max(base[a % 3], v) for a, v in enumerate(first))
    continuation = residue_transfer(envelope, sign)
    exact = Q(437756, 1835001)
    assert continuation[root % 27] == exact < 1

    # Independently enumerate actual integer children. At each child the
    # policy chooses between stopping and its complete one-step coefficient.
    # Both possible rewards are <= 2, so the omitted exponent tail is <= 6/2^K.
    cutoff = 40
    lower = Q(0)
    for k in range(1, cutoff + 1):
        numerator = 2**k * root - sign
        if numerator % 3 == 0:
            child = numerator // 3
            assert syracuse(child, sign) == root
            reward = max(Q(child % 3 != 0), first[child % 9])
            lower += Q(3, 2**k) * reward
    assert lower <= exact <= lower + Q(6, 2**cutoff)

    # A repeated state certifies eventual periodicity; the target itself is
    # absent from that later cycle, so the example is nonperiodic.
    seen = set()
    n = root
    while n not in seen:
        seen.add(n)
        n = syracuse(n, sign)
    assert n != root


@pytest.mark.parametrize("sign,root", [(1, 1), (-1, 2)])
def test_branch_adaptation_strictly_improves_on_choosing_one_depth(sign, root):
    base = (Q(0), Q(1), Q(1))
    first = residue_transfer(base, sign)
    second = residue_transfer(first, sign)
    envelope = tuple(max(base[a % 3], v) for a, v in enumerate(first))
    adaptive = residue_transfer(envelope, sign)
    assert adaptive[root] > max(first[root % 9], second[root])


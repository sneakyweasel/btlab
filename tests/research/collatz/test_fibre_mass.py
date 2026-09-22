"""Actual-map checks and independent finite residue/series checks."""

from fractions import Fraction as Q

import pytest

from research.collatz.fibre_mass import (
    actual_mass_bounds, fibre, residue_transfer, sibling, syracuse,
    transfer_iterate,
)


@pytest.mark.parametrize("sign", [1, -1])
def test_fibres_against_independent_forward_enumeration(sign):
    observed = {}
    for n in range(1, 20001, 2):
        m = 3*n + sign
        while m % 2 == 0:
            m //= 2
        observed.setdefault(m, []).append(n)
    for m in range(1, 301, 2):
        expected = [n for n in fibre(m, 10, sign) if n <= 20000]
        assert observed.get(m, []) == expected


@pytest.mark.parametrize("sign", [1, -1])
def test_siblings_merge_and_cover_each_ternary_residue(sign):
    for n in range(1, 102, 2):
        x = n
        residues = []
        for j in range(3**4):
            assert x == sibling(n, j, sign)
            assert syracuse(x, sign) == syracuse(n, sign)
            residues.append(x % (3**4))
            x = 4*x + sign
        assert sorted(residues) == list(range(3**4))
        assert x % (3**4) == n % (3**4)


def test_exact_fertile_table_and_tao_depth_two_distribution():
    assert residue_transfer((0, 1, 1)) == tuple(
        Q(n, 21) for n in (0, 20, 40, 0, 17, 10, 0, 5, 34)
    )
    # Tao Lemma 1.12: 3*P(Syrac mod 3)=(0,1,2); after another
    # step the density is 9*(0,8,16,0,11,4,0,2,22)/63.
    assert residue_transfer((0, 1, 2)) == tuple(
        Q(n, 7) for n in (0, 8, 16, 0, 11, 4, 0, 2, 22)
    )


@pytest.mark.parametrize("sign", [1, -1])
@pytest.mark.parametrize("size", [3, 9, 27])
def test_mean_conservation_fixed_residue_and_deficient_row(sign, size):
    h = tuple(Q(1+(17*i+3) % 29) if i % 3 else Q(0) for i in range(size))
    output = residue_transfer(h, sign)
    assert sum(output) == 3*sum(h)
    assert output[(-sign) % len(output)] >= Q(3, 2)*h[(-sign) % size]
    assert any(output[a] < h[a % size] for a in range(len(output)) if a % 3)
    # Sign reflection is an exact identity of this homogeneous operator.
    reflected = tuple(h[(-i) % size] for i in range(size))
    other = residue_transfer(reflected, -sign)
    assert all(output[i] == other[(-i) % len(output)] for i in range(len(output)))


@pytest.mark.parametrize("sign", [1, -1])
def test_fixed_depth_grouping_still_has_a_deficient_row(sign):
    h = (Q(0), Q(7), Q(13))
    for d in range(1, 4):
        output = transfer_iterate(h, d, sign)
        assert sum(output) == 3**d * sum(h)
        assert output[(-sign) % len(output)] >= Q(3, 2)**d*h[(-sign) % 3]
        assert any(output[a] < h[a % 3] for a in range(len(output)) if a % 3)


@pytest.mark.parametrize("sign", [1, -1])
def test_integer_masses_respect_tail_bounds_and_homogeneous_error(sign):
    h = (Q(0), Q(2), Q(3), Q(0), Q(5), Q(7), Q(0), Q(11), Q(13))
    output = residue_transfer(h, sign)
    for m in range(1, 150, 2):
        if m % 3 == 0:
            continue
        lo, hi = actual_mass_bounds(m, h, 20, sign)
        fine_lo, fine_hi = actual_mass_bounds(m, h, 60, sign)
        assert lo <= fine_lo <= fine_hi <= hi
        model = output[m % len(output)]
        error = max(h) / (m-Q(1, 2))
        assert m*fine_lo >= model-error
        assert m*fine_hi <= model+error
        if sign == 1:
            assert m*fine_hi > model
        else:
            assert m*fine_lo < model


def test_actual_poor_fibre_does_not_disappear_at_large_targets():
    # These are genuine odd unit targets, not just formal residue labels.
    for m in (7, 25, 97, 1000000015):
        assert m % 9 == 7
        _, upper = actual_mass_bounds(m, (0, 1, 1), 40)
        assert m*upper < Q(1, 3)


def test_input_boundaries():
    assert fibre(3, 5) == ()
    assert fibre(5, 0) == ()
    for weights in ((1, 1, 1), (0, 1), (0, -1, 2)):
        with pytest.raises(ValueError):
            residue_transfer(weights)


def test_first_hit_generations_and_the_affine_mass_lower_bound():
    # 7 is nonperiodic: its forward orbit reaches 1 without returning to 7.
    n, seen = 7, set()
    while n not in seen:
        seen.add(n)
        n = syracuse(n)
    assert n == 1
    generation, earlier = {7: Q(1)}, set()
    for depth in range(4):
        assert not earlier.intersection(generation)
        earlier.update(generation)
        for n, coefficient in generation.items():
            assert Q(1, n) >= coefficient/7
            actual = n
            for _ in range(depth):
                actual = syracuse(actual)
            assert actual == 7
        following = {}
        for m, coefficient in generation.items():
            for k in range(1, 10):
                numerator = 2**k*m-1
                if numerator % 3:
                    continue
                child = numerator//3
                if child % 3:
                    assert child not in following
                    following[child] = coefficient*Q(3, 2**k)
        generation = following
    assert 1 in fibre(1, 3)  # A periodic root does not give disjoint generations.


@pytest.mark.parametrize("sign", [1, -1])
def test_fixed_depth_affine_error_on_actual_paths(sign):
    root = 101
    generation = {root: Q(1)}
    for depth in range(1, 4):
        following = {}
        for m, coefficient in generation.items():
            for k in range(1, 7):
                numerator = 2**k*m-sign
                if numerator % 3 == 0 and (numerator//3) % 3:
                    child = numerator//3
                    assert child not in following
                    following[child] = coefficient*Q(3, 2**k)
        bound = Q(3, 2)**depth-1
        for child, coefficient in following.items():
            assert abs(Q(root, child)-coefficient) <= coefficient*bound/(root-bound)
        generation = following

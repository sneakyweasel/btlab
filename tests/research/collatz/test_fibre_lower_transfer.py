"""Exact actual-predecessor and full-table controls for local lower transport."""

from fractions import Fraction as Q

import pytest

from research.collatz.fibre_mass import residue_transfer, syracuse


def coarse_tables(sign, last_depth):
    """The complete coarse recurrence starts with the signed mod-three row."""
    tables = [(Q(1),), (Q(0), Q(1), Q(2)) if sign == 1
              else (Q(0), Q(2), Q(1))]
    while len(tables) <= last_depth:
        tables.append(residue_transfer(tables[-1], sign))
    return tables


def coefficient(table, target):
    return table[target % len(table)]


@pytest.mark.parametrize("sign", [1, -1])
def test_one_actual_fibre_covers_every_ternary_class_with_bounded_exponent(sign):
    tables = coarse_tables(sign, 4)
    for r in range(4):
        modulus = 3**r
        cap = 2*modulus
        cost = Q(3, 2**cap)
        for residue in range(3*modulus):
            if residue % 3 == 0:
                continue
            target = residue if residue % 2 else residue + 3*modulus
            seen = []
            for exponent in range(1, cap + 1):
                raw = 2**exponent * target - sign
                if raw % 3:
                    continue
                source = raw // 3
                assert source >= 1 and source % 2 == 1
                assert syracuse(source, sign) == target
                numerator = 3*source + sign
                assert (numerator & -numerator).bit_length() - 1 == exponent
                seen.append(source % modulus)
                weight = Q(3, 2**exponent)
                assert cost <= weight
                # The SAME ordinary predecessor works at each later depth.
                for depth in range(4):
                    local = coefficient(tables[depth], source)
                    global_next = coefficient(tables[depth + 1], target)
                    assert cost*local <= weight*local <= global_next
            assert sorted(seen) == list(range(modulus))


@pytest.mark.parametrize("sign", [1, -1])
def test_uniform_local_block_lower_bounds_transport_to_every_unit_root(sign):
    tables = coarse_tables(sign, 4)
    for r in range(1, 4):
        modulus = 3**r
        cost = Q(3, 2**(2*modulus))
        for depths in ((0, 1), (1, 2), (2, 3)):
            source_period = max(modulus, *(len(tables[d]) for d in depths))
            target_period = max(len(tables[d + 1]) for d in depths)
            global_min = min(
                sum(coefficient(tables[d + 1], a) for d in depths)
                for a in range(target_period) if a % 3
            )
            for b in range(modulus):
                if b % 3 == 0:
                    continue
                local_min = min(
                    sum(coefficient(tables[d], m) for d in depths)
                    for m in range(b, source_period, modulus)
                )
                assert cost*local_min <= global_min


@pytest.mark.parametrize("sign", [1, -1])
def test_unit_hypothesis_and_positive_transport_loss_are_necessary(sign):
    assert all((2**e * 3 - sign) % 3 for e in range(1, 20))
    tables = coarse_tables(sign, 2)
    favorable_class = 2 if sign == 1 else 1
    local_lower = tables[1][favorable_class]
    global_next = min(value for a, value in enumerate(tables[2]) if a % 3)
    assert global_next < local_lower

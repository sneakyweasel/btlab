"""Independent actual-word controls for transported signed coefficient peaks."""

from fractions import Fraction as Q

import pytest

from research.collatz.fibre_mass import syracuse, transfer_iterate


@pytest.mark.parametrize("sign", [1, -1])
def test_transported_peak_words_realize_every_small_unit_neighborhood(sign):
    tables = [transfer_iterate((0, 1, 1), depth, sign) for depth in range(1, 4)]
    for r in range(3):
        coarse_modulus = 3 ** (r + 1)
        for a in range(coarse_modulus):
            if a % 3 == 0:
                continue
            k = next(k for k in range(2 * 3**r)
                     if (2**k * a + sign) % coarse_modulus == 0)
            for d in range(r, 3):
                modulus = 3 ** (d + 2)
                peak = -sign * pow(2**k, -1, modulus) % modulus
                assert peak % coarse_modulus == a
                # Select an ordinary positive odd representative, then reconstruct
                # the claimed word and independently verify every forward valuation.
                target = peak if peak % 2 else peak + modulus
                child = target
                for exponent in (k + 1, *([1] * d)):
                    parent = child
                    numerator = 2**exponent * parent - sign
                    assert numerator % 3 == 0
                    child = numerator // 3
                    assert child > 0 and child % 2 == 1
                    assert syracuse(child, sign) == parent
                    assert (3 * child + sign) // parent == 2**exponent
                assert child % 3 != 0
                word_weight = Q(3, 2 ** (k + 1)) * Q(3, 2)**d
                assert tables[d][peak] >= word_weight


@pytest.mark.parametrize("sign", [1, -1])
def test_local_average_stays_bounded_despite_transported_peaks(sign):
    # Exact complete tables check the averaging allowance used in the written
    # Harnack obstruction; the all-depth peak theorem is proved separately in Lean.
    for depth in range(1, 4):
        table = transfer_iterate((0, 1, 1), depth, sign)
        assert sum(table) == 2 * 3**depth
        for r in range(depth + 1):
            modulus = 3 ** (r + 1)
            for a in range(modulus):
                if a % 3:
                    cell = table[a::modulus]
                    assert Q(sum(cell), len(cell)) <= 2 * 3**r

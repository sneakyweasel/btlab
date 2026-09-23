"""Finite residue checks for the logical counterexample, not an orbit experiment."""

from fractions import Fraction as Q

import pytest

from research.collatz.fibre_mixing import cylinder_density, diagnostic
from research.collatz.fibre_mass import residue_transfer


@pytest.mark.parametrize("root", [1, 7, 17, 47])
def test_residue_refinement_conserves_mass_and_bounds_every_cell(root):
    for level in range(1, 5):
        for syracuse in (False, True):
            table = [cylinder_density(root, a, level, syracuse=syracuse)
                     for a in range(3**level)]
            assert sum(table) == (3**level if syracuse else 2 * 3 ** (level - 1))
            for a, value in enumerate(table):
                assert (value > 0) == (a % 3 != 0)
                assert value <= (Q(8, 3) if syracuse else Q(4, 3))
                children = [cylinder_density(root, a + j * 3**level, level + 1,
                                             syracuse=syracuse) for j in range(3)]
                assert sum(children) == 3 * value
                # Check two refinement levels directly, beyond local coherence.
                for j in range(9):
                    refined = cylinder_density(root, a + j * 3**level, level + 2,
                                               syracuse=syracuse)
                    assert abs(refined - value) <= Q(2 if syracuse else 1, 3 ** (level - 1))


def test_prescribed_integer_series_and_initial_normalizations():
    for root in (7, 47):
        assert [cylinder_density(root, a, 1) for a in range(3)] == [0, 1, 1]
        assert [cylinder_density(root, a, 1, syracuse=True) for a in range(3)] == [0, 1, 2]
        for depth in range(1, 12):
            terms = [cylinder_density(root, root % 3**level, level)
                     for level in range(1, depth + 1)]
            assert sum(terms) == Q(3, 2) * (1 - Q(1, 3**depth))
            assert cylinder_density(root, root % 3**depth, depth, syracuse=True) == (
                root % 3 * Q(1, 3 ** (depth - 1)))


def test_actual_operator_does_not_satisfy_the_artificial_bound():
    for row in diagnostic()["actual_spikes"]:
        assert Q(row["coefficient"]) == Q(34, 21) > Q(row["model_upper_bound"])
    # The actual unit-weight iterates are not Tao's coherent density sequence.
    unit_next = residue_transfer((0, 1, 1))
    assert [sum(unit_next[a::3]) / 3 for a in range(3)] == [0, Q(2, 3), Q(4, 3)]
    # Starting with the actual Syracuse density gives the correct coarse row.
    syracuse_next = residue_transfer((0, 1, 2))
    assert [sum(syracuse_next[a::3]) / 3 for a in range(3)] == [0, 1, 2]


def test_domain_rejects_nonunit_roots_and_nonresidues():
    for args in ((0, 0, 1), (3, 0, 1), (7, 3, 1), (7, -1, 1), (7, 0, 0)):
        with pytest.raises(ValueError):
            cylinder_density(*args)

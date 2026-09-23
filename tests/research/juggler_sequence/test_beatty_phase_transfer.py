"""Independent finite checks of the proposed limiting profile's ingredients."""

import math

import pytest

from research.juggler_sequence.beatty_phase_transfer import (
    ALPHA, B, BETA, Q, atoms, check_spitzer_coefficients, cumulative_head,
)
from research.juggler_sequence.jump_spectrum import survivor_counts


@pytest.fixture(scope="module")
def counts():
    return survivor_counts(512)


def test_spitzer_recursion_against_independent_binomial_tails(counts):
    check_spitzer_coefficients(counts, 256)
    corrupted = counts.copy()
    corrupted[73] += 1
    with pytest.raises(AssertionError, match="73"):
        check_spitzer_coefficients(corrupted, 128)


def test_entropy_and_centered_walk_normalizations_agree(counts):
    for atom in atoms(counts):
        entropy = math.exp(math.log(atom.count) - atom.order*math.log(B)
                           - atom.phase*math.log(Q))
        assert atom.weight == pytest.approx(entropy, rel=2e-12)
        m, delta = atom.depth - 1, atom.phase
        assert (m / ALPHA) % 1 == pytest.approx(1-delta/ALPHA, abs=6e-14)
        assert ((m+1) / ALPHA) % 1 == pytest.approx((1-delta)/ALPHA, abs=6e-14)


def test_first_jump_is_beta_and_all_finite_weights_are_positive(counts):
    rows = atoms(counts)
    assert rows[0].count == 1
    assert rows[0].weight == pytest.approx(BETA, abs=2e-16)
    assert all(row.weight > 0 for row in rows)


def test_cdf_uses_the_left_trace_at_an_atom(counts):
    rows = atoms(counts)
    location = rows[0].phase
    left, right = cumulative_head(rows, [location, math.nextafter(location, math.inf)])
    assert right-left == pytest.approx(BETA, abs=1e-15)
    values = cumulative_head(rows, [k/100 for k in range(101)])
    assert values == sorted(values)
    assert values[0] == 1

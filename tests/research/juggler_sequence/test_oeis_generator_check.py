"""Independent count comparisons and regressions for the two OEIS discrepancies."""

from __future__ import annotations

from math import comb

import pytest

from research.juggler_sequence.certificate_increment import survivor_counts
from research.juggler_sequence.oeis_generator_check import (
    STORED_GENERATOR,
    carrying_length,
    certificate_from_generator,
    comparison_report,
    generator_boundary,
    generator_coefficients,
)


def test_boundary_has_exact_defining_power_inequalities() -> None:
    for n in range(1, 257):
        c = generator_boundary(n)
        assert 3**c < 1 << (c + n)
        assert 3**(c + 1) > 1 << (c + n + 1)


def test_published_upper_limit_fails_at_first_nontrivial_order() -> None:
    coefficients = generator_coefficients(3)
    assert carrying_length(1) - 2 - 2 == -2
    assert certificate_from_generator(2, coefficients, published_upper_limit=True) == 0
    # The unique order-two certificate is OOEE: 3, 9, 9, 9 versus 2, 4, 8, 16.
    assert [3**o >= 2**d for d, o in enumerate((1, 2, 2, 2), start=1)] == [
        True, True, True, False,
    ]
    assert certificate_from_generator(2, coefficients) == 1


def test_exact_recurrence_and_stored_table_first_disagree_at_21() -> None:
    exact = generator_coefficients(26)
    assert exact[:21] == STORED_GENERATOR[:21]
    assert exact[21] == -517564939540550
    assert STORED_GENERATOR[21] == -517564939540551
    assert [k for k in range(27) if exact[k] != STORED_GENERATOR[k]] == list(range(21, 27))


def test_repaired_transform_matches_prefix_dp_and_reconstructs_survivors() -> None:
    report = comparison_report(256)
    assert report["certificate_orders_checked"] == [1, 256]
    assert report["survivor_depths_checked"] == [0, 406]
    assert report["repaired_transform_mismatches"] == []
    assert report["reconstructed_survivor_mismatches"] == []
    assert report["stored_generator_transform_first_mismatch"]["order"] == 37


def test_dp_inversion_independently_recovers_generator_coefficients() -> None:
    """Recover G from integer path counts, without the OEIS G recurrence."""
    _, minimal = survivor_counts(carrying_length(100))
    recovered = [1, 0]
    for order in range(2, 101):
        length = carrying_length(order - 1)
        last = length - order
        if last == len(recovered):
            # At the first occurrence of 'last', its coefficient is binom(r,r)=1.
            known = sum(recovered[k] * comb(length - k - 2, order - 2)
                        for k in range(last))
            recovered.append(minimal[carrying_length(order)] - known)
    assert len(recovered) > 50
    assert tuple(recovered) == generator_coefficients(len(recovered) - 1)


@pytest.mark.parametrize("function,value", [
    (carrying_length, -1), (generator_boundary, 0), (generator_coefficients, -1),
    (comparison_report, 1),
])
def test_invalid_domains_are_rejected(function, value) -> None:
    with pytest.raises(ValueError):
        function(value)

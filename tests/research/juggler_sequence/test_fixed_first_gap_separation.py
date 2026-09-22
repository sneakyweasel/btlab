"""Exact controls for the written fixed-first-gap separation inequality.

These finite checks do not replace the uniform calculus proof in the
predecessor-transfer dossier. Both nested floors are evaluated as integers.
"""

from math import isqrt

import pytest


@pytest.mark.parametrize("scale", [256, 4096, 65536])
def test_second_gap_separates_on_each_actual_first_gap_branch(scale: int):
    comparisons = 0
    nonadjacent = 0
    for half_shift in (1, 2, 7, scale // 8, scale // 2):
        previous: dict[int, tuple[int, int]] = {}
        for n in range(scale + 1, 2 * scale, 2):
            m = isqrt(n**3)
            shifted_m = isqrt((n + 2 * half_shift) ** 3)
            first_gap = shifted_m - m
            second_gap = isqrt(shifted_m**3) - isqrt(m**3)
            if first_gap in previous:
                old_n, old_gap = previous[first_gap]
                delta = second_gap - old_gap
                distance = n - old_n
                assert delta >= 3
                # Exact fourth-power version of delta + 2 > h*d*P^(1/4)/2.
                assert (2 * (delta + 2)) ** 4 > half_shift**4 * distance**4 * scale
                comparisons += 1
                nonadjacent += distance > 2
            previous[first_gap] = (n, second_gap)
    assert comparisons > scale // 2
    assert nonadjacent > 0

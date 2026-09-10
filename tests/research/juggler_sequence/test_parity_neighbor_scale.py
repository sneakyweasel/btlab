"""Exact finite checks for first-image parity locality and its sharp scale.

These fixtures are not the asymptotic proof and give no growing-depth
all-odd count or termination assertion. The added finite block checks
verify scoped assignments, not their asymptotic existence.
"""

from __future__ import annotations

import math


PRIME_C = (37, 101, 1009, 10007)


def _ceil_fourth_root(n: int) -> int:
    return math.isqrt(math.isqrt(n - 1)) + 1


def test_integer_ceiling_fourth_root() -> None:
    for n in (*range(1, 258), 4096, 4097, 65536, 65537, 10**12 + 1):
        root = _ceil_fourth_root(n)
        assert (root - 1) ** 4 < n <= root**4


def test_both_first_image_parities_occur_within_the_upper_radius() -> None:
    centers = []
    for c in PRIME_C:
        size = (math.isqrt(4 * c) + 1) // 2
        centers.append(4 * c**2 + 2 * ((size - 1) // 2) + 1)
    starts = [*range(4097, 4198, 2), 65537, 10**6 + 1, 10**8 + 1, 10**12 + 1, *centers]
    for n in starts:
        assert n >= 4096 and n % 2 == 1
        length = _ceil_fourth_root(n)
        assert 36 * length**2 < n
        assert 8 * length <= n
        parities = {math.isqrt((n + 2 * j) ** 3) % 2 for j in range(4 * length + 1)}
        assert parities == {0, 1}


def test_prime_centered_lower_clusters_have_exact_odd_nonsquare_images() -> None:
    for c in PRIME_C:
        assert c >= 37 and c % 2 == 1
        assert all(c % divisor for divisor in range(2, math.isqrt(c) + 1))
        size = (math.isqrt(4 * c) + 1) // 2
        offsets = range(1, 2 * size, 2)
        assert (2 * size - 1) ** 2 <= 4 * c < (2 * size + 1) ** 2
        for offset in offsets:
            n, m = 4 * c**2 + offset, 8 * c**3 + 3 * c * offset
            assert offset**2 <= 4 * c
            assert n % 2 == m % 2 == 1
            assert math.isqrt(n) ** 2 != n and math.isqrt(m) ** 2 != m
            assert m % c == 0 and m % (c * c) != 0
            defect = n**3 - m**2
            assert defect == offset**2 * (3 * c**2 + offset)
            assert 0 < defect < 2 * m + 1
            assert math.isqrt(n**3) == m


def test_central_sources_have_no_opposite_image_inside_the_lower_radius() -> None:
    for c in PRIME_C:
        size = (math.isqrt(4 * c) + 1) // 2
        center = 4 * c**2 + 2 * ((size - 1) // 2) + 1
        cluster_first, cluster_last = 4 * c**2 + 1, 4 * c**2 + 2 * size - 1
        outside_left, outside_right = cluster_first - 2, cluster_last + 2
        assert min(center - outside_left, outside_right - center) >= size
        assert (4 * size) ** 4 >= center
        for source in range(center - size + 1, center + size):
            if source % 2 == 1:
                assert cluster_first <= source <= cluster_last
                assert math.isqrt(source**3) % 2 == 1


def test_target_neighbor_window_is_isolated_from_other_odd_source_images() -> None:
    """Finite gap fixtures: target availability does not supply an odd pullback."""

    for n in (65537, 66053, 10**6 + 1, 10**8 + 1, 10**12 + 1):
        assert n >= 65536 and n % 2 == 1
        m = math.isqrt(n**3)
        length = _ceil_fourth_root(m)
        radius = 8 * length
        left_image, right_image = math.isqrt((n - 2) ** 3), math.isqrt((n + 2) ** 3)
        assert m - left_image > radius and right_image - m > radius
        if n == 66053:
            assert m % 2 == 1
            assert math.isqrt(n) ** 2 != n and math.isqrt(m) ** 2 != m
            target = next(
                m + 2 * j for j in range(1, 4 * length + 1)
                if math.isqrt((m + 2 * j) ** 3) % 2 != math.isqrt(m**3) % 2
            )
            assert target % 2 == 1 and target - m <= radius
            # Strict monotonicity leaves no odd-source image between these neighbors.
            assert m < target < right_image



def test_fixed_block_pairing_preserves_prefix_and_has_capacity_two() -> None:
    """Twelve literal controls; the small radius at t=2,3,4 is not a theorem."""

    def word(n: int, length: int) -> tuple[int, ...]:
        result = []
        for _ in range(length):
            result.append(n % 2)
            n = math.isqrt(n**3 if n % 2 else n)
        return tuple(result)

    for y in (2**20, 2**28, 2**36):
        size = 32 * _ceil_fourth_root(y)
        sources = list(range(y + 1, y + 2 * size, 2))
        assert len(sources) == size and sources[-1] <= 2 * y
        words = {n: word(n, 5) for n in sources}
        for depth in (1, 2, 3, 4):
            continuers = [
                n for n in sources if words[n][:depth + 1] == (1,) * (depth + 1)
            ]
            exits = [
                n for n in sources if words[n][:depth + 1] == (1,) * depth + (0,)
            ]
            if depth == 4:
                expected = {2**20: (59, 63), 2**28: (218, 256), 2**36: (932, 983)}
                assert (len(continuers), len(exits)) == expected[y]
            assert len(continuers) <= 2 * len(exits)
            if depth == 1:
                assert 3 * size <= 8 * len(exits) <= 5 * size
            capacity: dict[int, int] = {}
            for i, n in enumerate(continuers):
                target = exits[i // 2]
                assert n != target
                assert words[n][:depth] == words[target][:depth] == (1,) * depth
                assert words[n][depth] == 1 and words[target][depth] == 0
                assert abs(n - target) < 2 * size
                capacity[target] = capacity.get(target, 0) + 1
            assert max(capacity.values(), default=0) <= 2

"""Finite regressions for the absorbed-cylinder obstruction to H(C,A).

These checks exercise exact small integer instances and the elementary
geometric-product arithmetic used by the human proof.  They are not a
finite verification of the asymptotic OEE estimate or of its consequence
for arbitrarily deep cylinders.
"""

from __future__ import annotations

from fractions import Fraction
from math import isqrt
import re

from research.juggler_sequence.lean_paths import REPO_ROOT


def test_proof_sources_have_no_escaped_control_character_damage() -> None:
    for relative in (
        "docs/problems/juggler_absorbed_cylinder.md",
        "docs/theory/juggler_tao_reduction_note.md",
        "docs/theory/juggler_fate_almost_all_note.md",
    ):
        source = (REPO_ROOT / relative).read_bytes()
        # A literal LaTeX macro such as \rm must not become a lone CR.
        assert re.search(rb"\r(?!\n)|[\x00-\x08\x0b\x0c\x0e-\x1f]", source) is None


def juggler(n: int) -> int:
    return isqrt(n) if n % 2 == 0 else isqrt(n**3)


def iterate(n: int, steps: int) -> int:
    for _ in range(steps):
        n = juggler(n)
    return n


def word(n: int, depth: int) -> str:
    letters = []
    for _ in range(depth):
        letters.append("O" if n % 2 else "E")
        n = juggler(n)
    return "".join(letters)


def ceil_nth_root(value: int, degree: int) -> int:
    """Least nonnegative r such that r**degree >= value."""
    if value == 0:
        return 0
    lo, hi = 0, 1
    while hi**degree < value:
        hi *= 2
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if mid**degree < value:
            lo = mid
        else:
            hi = mid
    return hi


def even_preimages(parent: int) -> list[int]:
    """Even n with floor(sqrt(n)) = parent."""
    return [
        n
        for n in range(parent * parent, (parent + 1) ** 2)
        if n % 2 == 0
    ]


def even_tree(seed: int, depth: int) -> list[int]:
    level = [seed]
    for _ in range(depth):
        level = [child for parent in level for child in even_preimages(parent)]
    return level


def oee_fiber(target: int) -> list[int]:
    """Odd OEE starts whose third iterate is target, using exact endpoints."""
    lo = ceil_nth_root(target**8, 3)
    hi = ceil_nth_root((target + 1) ** 8, 3)
    return [
        n
        for n in range(lo, hi)
        if n % 2 == 1 and word(n, 3) == "OEE" and iterate(n, 3) == target
    ]


def harmonic_mass(values: list[int]) -> Fraction:
    return sum((Fraction(1, n) for n in values), start=Fraction())


def test_even_preimage_cell_and_harmonic_lower_bound() -> None:
    for parent in (4, 16, 18, 20, 22, 24):
        children = even_preimages(parent)
        assert children == list(
            range(parent * parent, parent * parent + 2 * parent + 1, 2)
        )
        assert len(children) == parent + 1
        assert all(isqrt(child) == parent for child in children)
        assert harmonic_mass(children) >= (
            Fraction(1, parent) * (1 - Fraction(2, parent))
        )


def test_small_even_trees_are_exact_and_land_at_four() -> None:
    seed = 4
    for depth in range(3):
        level = even_tree(seed, depth)
        assert len(level) == len(set(level))
        assert all(x % 2 == 0 for x in level)
        assert all(iterate(x, depth) == seed for x in level)
        for x in level:
            states = [iterate(x, j) for j in range(depth)]
            assert all(state % 2 == 0 for state in states)
            assert seed ** (2**depth) <= x < (seed + 1) ** (2**depth)
        assert harmonic_mass(level) >= Fraction(1, 12)


def test_geometric_product_constant_is_uniform_in_depth() -> None:
    product = Fraction(1)
    for j in range(9):
        product *= 1 - Fraction(2, 4 ** (2**j))
        assert product >= Fraction(1, 3)

    # Product inequality: prod(1-x_j) >= 1-sum(x_j), followed by
    # {2^j : j >= 0} subset {1,2,3,...}.
    geometric_sum = sum(
        (Fraction(2, 4**r) for r in range(1, 80)), start=Fraction()
    )
    assert geometric_sum < Fraction(2, 3)
    assert Fraction(1, 4) * (1 - Fraction(2, 3)) == Fraction(1, 12)


def test_oee_fibers_land_exactly_and_have_the_fixture_mass_margin() -> None:
    for target in even_tree(4, 1):
        starts = oee_fiber(target)
        assert starts
        assert all(n % 2 == 1 for n in starts)
        assert all(word(n, 3) == "OEE" for n in starts)
        assert all(iterate(n, 3) == target for n in starts)
        assert harmonic_mass(starts) >= Fraction(1, 6 * target)


def test_absorbed_fixture_has_one_long_cylinder_and_reaches_one() -> None:
    seed = 4
    for depth in (0, 1):
        starts = [
            n
            for leaf in even_tree(seed, depth)
            for n in oee_fiber(leaf)
        ]
        absorption_time = depth + 5
        common_prefix = "O" + "E" * (depth + 4)
        assert starts
        assert all(word(n, absorption_time) == common_prefix for n in starts)
        assert all(iterate(n, absorption_time) == 1 for n in starts)

        blocks: dict[int, list[int]] = {}
        for n in starts:
            # Integer n belongs to (2^r, 2^(r+1)] for this exact r.
            r = (n - 1).bit_length() - 1
            blocks.setdefault(r, []).append(n)
        assert len(blocks) <= 3 * 2**depth
        assert max(harmonic_mass(block) for block in blocks.values()) >= (
            harmonic_mass(starts) / (3 * 2**depth)
        )


def test_endpoint_inequality_and_entire_prefix_cylinder_absorb() -> None:
    # This is the exact integer form of
    # (1/4) log(5) + (3/32) log(2) < log(2).
    assert 5**8 < 2**29

    for depth in (0, 1):
        constructed = [
            n
            for leaf in even_tree(4, depth)
            for n in oee_fiber(leaf)
        ]
        block_indices = {(n - 1).bit_length() - 1 for n in constructed}
        prefix_depth = depth + 5
        prefix = "O" + "E" * (depth + 4)

        for r in block_indices:
            y = 2**r
            whole_prefix_cylinder = [
                n
                for n in range(y + 1 + (y % 2), 2 * y + 1, 2)
                if word(n, prefix_depth) == prefix
            ]
            assert whole_prefix_cylinder
            assert all(
                iterate(n, prefix_depth) == 1 for n in whole_prefix_cylinder
            )

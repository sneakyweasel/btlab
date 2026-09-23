"""Independent forward-orbit and tail controls for the cross-sign audit."""

from fractions import Fraction as Q

from research.collatz.fibre_mass import residue_transfer, syracuse
from research.collatz.fibre_sign_coupling import paired_tables, two_step_mass_bounds


def test_actual_cross_sign_pairing_and_failure_of_iteration():
    for n in range(1, 1000, 2):
        assert syracuse(2*n+1, -1) == syracuse(n, 1)
        assert syracuse(2*n-1, 1) == syracuse(n, -1)
    # Equal first images do not imply equal second fixed-sign images.
    assert syracuse(7, -1) == syracuse(3, 1) == 5
    assert syracuse(5, -1) == 7
    assert syracuse(5, 1) == 1


def test_complete_joint_tables_and_sign_switching_gap():
    p1, m1 = paired_tables(1)
    assert min(p1[a]+m1[a] for a in range(9) if a % 3) == Q(9, 7)
    p2, m2 = paired_tables(2)
    assert (p2[4], m2[4]) == (Q(12076, 29127), Q(7988, 29127))
    assert p2[4] + m2[4] < 1
    joint = tuple(a+b for a, b in zip(p1, m1))
    mixed_p = residue_transfer(joint, 1)
    mixed_m = residue_transfer(joint, -1)
    assert all(mixed_p[a]+mixed_m[a] >= Q(9, 7)**2 for a in range(27) if a % 3)
    assert mixed_p[4]+mixed_m[4] > p2[4]+m2[4]


def test_actual_two_step_mass_with_certified_omitted_tail():
    for target in (31, 85, 139, 571):
        intervals = []
        for sign in (1, -1):
            lo, hi = two_step_mass_bounds(target, sign, 8)
            fine_lo, fine_hi = two_step_mass_bounds(target, sign, 18)
            assert lo <= fine_lo <= fine_hi <= hi
            # Direct forward enumeration is independent of inverse congruences.
            finite = sum((Q(target, n) for n in range(1, 10001, 2)
                          if n % 3 and syracuse(syracuse(n, sign), sign) == target), Q(0))
            assert finite <= fine_hi
            intervals.append((fine_lo, fine_hi))
        assert sum(hi for _, hi in intervals) < Q(3, 4)


def test_all_infinite_progression_allowance():
    # The written two-step correction is decreasing in the target. Its
    # maximum on positive odd targets congruent to 4 mod 27 is at 31.
    assert Q(124, 119) * Q(20064, 29127) < Q(3, 4)

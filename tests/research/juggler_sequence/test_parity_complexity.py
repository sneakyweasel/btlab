"""The depth-one parity sequence has super-linear factor complexity: not automatic."""

from __future__ import annotations

from itertools import product
from math import log

from research.juggler_sequence import parity_complexity as P

SEQ = P.odd_cube_parity(20_000)


def test_the_sequence_is_the_second_itinerary_letter_of_odd_starts() -> None:
    for k in range(500):
        assert SEQ[k] == P.juggler_second_letter(2 * k + 1)
    # the Lean `parityPrefix_eight`
    assert SEQ[:8] == [1, 1, 1, 0, 1, 0, 0, 0]


def test_every_word_of_length_at_most_six_occurs_and_the_exhaustion_indices_match_lean() -> None:
    for L in range(1, 7):
        assert P.factor_complexity(SEQ, L) == 2 ** L
    for L, n in P.LEAN_SATURATION.items():
        assert P.saturation_index(SEQ, L) == n
        assert P.factor_complexity(SEQ[:n], L) == 2 ** L
        assert P.factor_complexity(SEQ[:n - 1], L) == 2 ** L - 1


def test_length_seven_is_the_first_deficit_and_it_is_exactly_two_words() -> None:
    assert P.factor_complexity(SEQ, 7) == 126
    assert P.saturation_index(SEQ, 7) is None
    missing = set(product((0, 1), repeat=7)) - P.factor_set(SEQ, 7)
    assert missing == {(0, 0, 1, 0, 0, 0, 0), (0, 1, 0, 0, 0, 1, 0)}
    # both carry runs whose lengths differ by more than one: neither is a rotation word
    for w in missing:
        assert w not in P.rotation_words(7)


def test_the_short_prefix_already_shows_the_census_counts_up_to_length_ten() -> None:
    for L in range(1, 11):
        assert P.factor_complexity(SEQ, L) == P.REFERENCE_3M[L - 1]
    # and the census itself is far below 2^L while still growing
    for L in range(7, 22):
        assert P.REFERENCE_3M[L - 1] < P.REFERENCE_3M[L] < 2 ** (L + 1)


def test_every_rotation_word_and_every_periodic_family_word_occurs() -> None:
    for L in range(1, 11):
        fs = P.factor_set(SEQ, L)
        rot = P.rotation_words(L)
        fam = P.periodic_family(L)
        assert rot <= fs, L
        assert fam <= rot, L
        assert len(fam) == P.periodic_family_count(L), L


def test_the_rotation_count_is_super_linear_and_the_family_is_quadratic() -> None:
    R = {L: len(P.rotation_words(L)) for L in (6, 12, 22)}
    assert R == {6: 48, 12: 356, 22: 2168}
    assert log(R[22] / R[6]) / log(22 / 6) > 2.5
    for L in (8, 12, 16, 22):
        assert P.periodic_family_count(L) >= L * L / 8 - L
    assert P.periodic_family_count(22) == 55


def test_rotation_words_are_a_vanishing_share_of_the_factor_set() -> None:
    assert len(P.rotation_words(12)) == 356 < 1354 == P.REFERENCE_3M[11]


def test_the_control_coding_of_one_rotation_is_linear() -> None:
    ctrl = P.beatty_parity(20_000)
    for L in range(1, 16):
        assert P.factor_complexity(ctrl, L) == 2 * L


def test_the_curvature_bound_is_what_the_taylor_argument_needs() -> None:
    for k in (100, 1000, 10_000):
        f0 = (2 * k + 1) ** 1.5
        slope = 3 * (2 * k + 1) ** 0.5
        for L in (8, 12):
            for j in range(L):
                rem = (2 * (k + j) + 1) ** 1.5 - f0 - j * slope
                assert -1e-6 <= rem <= P.curvature_bound(k, L) + 1e-6


def test_the_joint_phase_is_close_to_uniform() -> None:
    """No cell of a 10 x 10 grid is empty or doubled: 0.812 / 1.334 at 300 000 terms."""
    u = P.joint_phase_uniformity(300_000)
    assert 0.7 < u["min"] < 1.0 < u["max"] < 1.45


def test_the_lean_layer_carries_the_exhaustion_theorems() -> None:
    from research.juggler_sequence.lean_paths import LAYERS

    src = LAYERS["ParityComplexity"].read_text(encoding="utf-8")
    for name in ("oddCubeParity_eq_floorPower", "parityPrefix_eight",
                 "factorCount_three_saturates", "factorCount_four_saturates",
                 "factorCount_five_saturates", "factorCount_six_saturates",
                 "factorCount_six_not_before"):
        assert f"theorem {name}" in src, name
    for banned in ("sorry", "admit"):
        assert banned not in src


def test_the_summary_records_the_verdict() -> None:
    s = P.summary(n=20_000, max_L=10)
    assert s["saturation_matches_lean"] is True
    assert s["first_unsaturated_length"] == 7
    assert s["automatic_excluded"] is True
    assert s["rotation_words_all_present_up_to"] == 10
    assert s["periodic_family_all_present_up_to"] == 10
    assert s["control_is_two_L"] is True

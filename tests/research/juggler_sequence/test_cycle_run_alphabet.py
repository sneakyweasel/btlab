"""Cycle height forces a run alphabet: the bookkeeping and the band."""

from __future__ import annotations

import math
from math import isqrt, log

from research.juggler_sequence import cycle_run_alphabet as A


def test_the_letter_ratio_forbids_an_odd_run_of_length_one_everywhere() -> None:
    """o/e = log2/log(3/2) > 1, but a cyclic word with no adjacent O has o <= e."""
    assert abs(A.LOG_RATIO_OE - log(2) / log(1.5)) < 1e-12
    assert A.LOG_RATIO_OE > 1.0
    assert A.summary()["adjacent_odd_forced"] is True


def test_the_run_bounds_track_the_height_ratio() -> None:
    """(3/2)^r < R for odd runs, 2^g < R for even runs."""
    assert A.max_odd_run(2.0) == 1 and A.max_even_run(2.0) == 0
    assert A.max_odd_run(2.25) == 1 and A.max_even_run(2.25) == 1
    assert A.max_odd_run(27 / 8) == 2 and A.max_even_run(27 / 8) == 1
    assert A.max_odd_run(4.0) == 3 and A.max_even_run(4.0) == 1
    assert A.max_odd_run(5.0) == 3 and A.max_even_run(5.0) == 2


def test_below_square_height_no_block_is_admissible() -> None:
    """R < 2 leaves no even letter at all, so the word cannot close: this recovers the
    laboratory's superquadratic result as the empty-alphabet case."""
    assert A.admissible_blocks(2.0) == []


def test_the_band_alphabet_is_exactly_oe_and_ooe() -> None:
    assert A.admissible_blocks(27 / 8) == [(1, 1), (2, 1)]


def test_only_ooe_climbs_and_the_mix_is_pinned() -> None:
    assert A.block_exponent(1, 1) < 1.0 < A.block_exponent(2, 1)
    assert abs(A.block_exponent(1, 1) - 0.75) < 1e-12
    assert abs(A.block_exponent(2, 1) - 1.125) < 1e-12
    mix = A.two_block_mix()
    # closing the cycle forces the proportions, and they reproduce the letter ratio
    assert abs(mix["ooe_fraction_of_blocks"] - 0.709511) < 1e-5
    assert abs(mix["letter_ratio_check"] - A.LOG_RATIO_OE) < 1e-9


def test_a_forced_oo_pushes_the_maximum_to_the_nine_quarters_power() -> None:
    s = A.summary()
    assert abs(s["forced_min_height_exponent"] - 2.25) < 1e-12
    assert s["cycle_max_lower_bound"] > 1.6e19


def test_the_integer_chain_for_two_odd_steps_holds() -> None:
    """x^9 <= (y^2+2y)^3 = y^3 (y+2)^3 <= 2 y^6 < 2 (z+1)^4, the Lean `oo_step_lower`."""
    checked = 0
    for x in range(9, 2000, 2):
        w = A.oo_integer_witness(x)
        if w is None:
            continue
        checked += 1
        y, z = w["y"], w["z"]
        assert x ** 3 <= y ** 2 + 2 * y
        assert (y + 2) ** 3 <= 2 * y ** 3
        assert y ** 6 < (z + 1) ** 4
        assert w["x9"] < w["two_z1_4"]
    assert checked > 20


def test_the_floor_defect_is_negligible_against_the_closure_equation() -> None:
    """The letter ratio is exact only up to floor losses; they are ~1e-8 relative."""
    assert A.floor_defect_bound(780_239, A.N0_CERTIFIED) < 1e-6


def test_the_probe_agrees_with_a_direct_orbit_computation() -> None:
    """An OO from an odd start really does climb by about the nine-quarters power."""
    def J(n: int) -> int:
        return isqrt(n) if n % 2 == 0 else isqrt(n ** 3)

    for x in (1001, 10007, 100003):
        y = J(x)
        if y % 2 == 0:
            continue
        z = J(y)
        assert z > x ** 2.25 / 2
        assert x ** 9 < 2 * (z + 1) ** 4


def test_the_lean_layer_carries_the_named_theorems() -> None:
    from research.juggler_sequence.lean_paths import LAYERS

    src = LAYERS["CycleRunAlphabet"].read_text(encoding="utf-8")
    for name in ("odd_step_sq_le", "odd_step_le_sq_add", "cube_shift_le_two",
                 "oo_step_lower", "odd_run_upper", "even_run_contracts",
                 "oddCount_le_of_noAdjOdd", "walk_eq_discrepancy",
                 "ee_forces_fourth_power"):
        assert f"theorem {name}" in src, name
    for banned in ("sorry", "admit"):
        assert banned not in src


# --------------------------------------------------------------------------- discrepancy


def test_the_walk_is_the_discrepancy_times_log_three() -> None:
    """u_t = (alpha+beta) D_t under closure, so log R = log 3 * Delta.  Checked on a word."""
    from fractions import Fraction

    a, b = 3, 7
    word = A.block_letters("2" * b + "1" * a)
    L, o = len(word), word.count("O")
    alpha, beta = log(1.5), log(2.0)
    # closure fails for a rational word by a defect; use the exact identity instead:
    # (alpha+beta) * (o/L) = beta  <=>  o alpha = (L-o) beta.  Here it holds only
    # approximately, so test the algebraic identity with alpha chosen to close exactly.
    alpha_exact = (L - o) * beta / o
    ot = 0
    for t, c in enumerate(word, start=1):
        ot += c == "O"
        lhs = ot * alpha_exact - (t - ot) * beta
        rhs = (alpha_exact + beta) * (ot - t * Fraction(o, L))
        assert abs(lhs - float(rhs)) < 1e-12
    assert abs(A.BAND_CAP - log(27 / 8) / log(3)) < 1e-12
    assert abs(alpha + beta - log(3)) < 1e-12


def test_the_run_climb_formulas_are_exact() -> None:
    """k OOE climb k(2-3s)+s and j OE span (1-s)+j(2s-1), measured on the D walk."""
    from fractions import Fraction

    s = A.letter_slope(7, 17)
    for k in (1, 2, 3, 4, 5):
        word = A.block_letters("2" * k)
        D, hi = Fraction(0), Fraction(0)
        for c in word:
            D += (1 - s) if c == "O" else -s
            hi = max(hi, D)
        assert hi == A.ooe_run_climb(k, s)
    for j in (1, 2, 3):
        word = A.block_letters("1" * j)
        D, hi, lo = Fraction(0), Fraction(0), Fraction(0)
        for c in word:
            D += (1 - s) if c == "O" else -s
            hi, lo = max(hi, D), min(lo, D)
        assert hi - lo == A.oe_run_range(j, s)


def test_the_run_caps_at_the_forced_slope() -> None:
    """OOE-runs: at most 3 if mechanical, 4 in the band.  OE-runs: at most 2 for both."""
    assert A.max_ooe_run(A.BALANCED_CAP) == 3
    assert A.max_ooe_run(A.BAND_CAP) == 4
    assert A.max_oe_run(A.BALANCED_CAP) == 2
    assert A.max_oe_run(A.BAND_CAP) == 2
    # five OOE in a row climb past the band; four climb past balanced
    assert A.ooe_run_climb(5, A.FORCED_SLOPE) > A.BAND_CAP
    assert A.ooe_run_climb(4, A.FORCED_SLOPE) > A.BALANCED_CAP
    assert A.ooe_run_climb(4, A.FORCED_SLOPE) < A.BAND_CAP


def test_exactly_one_balanced_necklace_per_pair_and_a_thin_sliver() -> None:
    for a, b, expect in ((2, 5, (3, 1, 1, 1)), (3, 7, (12, 1, 3, 8)), (5, 12, (364, 1, 15, 348))):
        c = A.necklace_census(a, b)
        assert (c["necklaces"], c["balanced"], c["sliver"], c["above"]) == expect, (a, b, c)
        assert c["min_nonbalanced_delta"] is not None and c["min_nonbalanced_delta"] >= 1.0
        # no balanced or sliver word carries five OOE in a row or three OE in a row
        for cls in ("balanced", "sliver"):
            for key in c["run_profile"][cls]:
                ooe = int(key.split("_")[0][3:])
                oe = int(key.split("_")[1][2:])
                assert ooe <= 4 and oe <= 2, (cls, key)


def test_a_band_cycle_can_use_only_three_of_the_five_certificates() -> None:
    """Even runs are length one and odd runs at most two, so OOEE and OOOEE cannot occur."""
    prof = A.band_certificate_profile(3, 7)
    assert prof["classes_available"] == ["E", "OE", "OOEOE"]
    assert prof["uncertified_prefixes"] == ["OOEOO"]
    assert set(prof["prefixes_seen"]) == {
        "EOEOE", "EOEOO", "EOOEO", "OEOEO", "OEOOE", "OOEOE", "OOEOO"}


def test_the_uncertified_count_is_ooe_blocks_minus_their_runs() -> None:
    """Exactly the OOE blocks followed by another OOE, verified on every necklace."""
    for a, b in ((3, 7), (5, 12)):
        prof = A.band_certificate_profile(a, b)
        assert prof["count_formula_is_b_minus_runs"] is True


def test_the_crowding_into_the_uncertified_cylinder_is_mild() -> None:
    """The corrected figure: ratio 1.24-1.57 to the fair 1/8, not the 2.1 first recorded.

    2.1 was the fraction of elements *beginning* an OOE, which is not the same as being
    uncertified: most OOE starts are certified through OOEOE.
    """
    w = A.band_uncertified_window()
    assert abs(w["ooe_block_start_fraction"] - 0.261860) < 1e-5
    assert 0.154 < w["uncertified_low"] < 0.156
    assert 0.196 < w["uncertified_high"] < 0.197
    assert 1.23 < w["ratio_low"] < 1.25
    assert 1.56 < w["ratio_high"] < 1.58
    # the mislabelled comparison, kept so the correction cannot silently regress
    assert abs(w["ooe_block_start_fraction"] / w["fair_share"] - 2.095) < 1e-3


def test_the_walk_minimum_position_is_never_certified() -> None:
    """A certificate forces a strict drop within five steps; below the cyclic minimum
    there is nothing to drop to, so every cycle has an uncertified position."""
    alpha, beta = log(1.5), log(2.0)
    for a, b in ((3, 7), (5, 12)):
        for nk in A.necklaces(a, b):
            w = A.block_letters(nk)
            u = best = 0.0
            arg = 0
            for i, c in enumerate(w):
                u += alpha if c == "O" else -beta
                if u < best:
                    best, arg = u, (i + 1) % len(w)
            assert not A.certified_at(w, arg), (nk, arg)


def test_a_double_even_step_needs_the_fourth_power() -> None:
    """EE from w lands at floor(w^(1/4)); inside [m, M] that is m^4 <= M."""
    from math import isqrt

    for w in (16, 1000, 123456, 10 ** 8):
        z = isqrt(isqrt(w))
        assert z ** 4 <= w
    s = A.summary()
    assert s["absolute_bands_at_floor"]["no_double_even_below"] > 1e34


def test_the_forced_opening_is_arithmetic_not_asymptotic() -> None:
    """OOE^k then OE has o = 2k+1, t = 3k+2; it is an exponent gap exactly for k <= 2."""
    for k, gap in ((0, True), (1, True), (2, True), (3, False), (4, False)):
        o, steps = 2 * k + 1, 3 * k + 2
        assert (3 ** o < 2 ** steps) is gap, k
    # and a second fall after three climbs is a gap too
    assert 3 ** 8 < 2 ** 13


def test_the_forced_opening_matches_the_walk_argument() -> None:
    """The integer condition reproduces the discrepancy computation: 3 climbs are needed."""
    need = (2 * A.FORCED_SLOPE - 1) / (2 - 3 * A.FORCED_SLOPE)
    assert 2.44 < need < 2.45
    assert math.ceil(need) == 3


def test_the_lean_layer_carries_the_forced_opening() -> None:
    from research.juggler_sequence.lean_paths import LAYERS

    src = LAYERS["CycleRunAlphabet"].read_text(encoding="utf-8")
    for name in ("climbRun_append_oe_exponentGap", "band_min_needs_three_climbs",
                 "climbRun_three_two_falls_exponentGap", "band_min_no_second_fall",
                 "climbRun_three"):
        assert f"theorem {name}" in src, name

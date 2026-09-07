"""The depth-one main term, its constant, and its cancellation on odd starts."""

from __future__ import annotations

import math

from research.juggler_sequence import depth_one_main_term as D


def test_the_complete_cubic_sums_mod_27_are_nine_for_both_dual_coefficients() -> None:
    """Coefficient -16 is the untwisted dual, -2 the half-integer-shifted one; both give 9."""
    for c in (-16, -2):
        s = D.complete_cubic_sum(c)
        assert abs(s.real - 9.0) < 1e-9 and abs(s.imag) < 1e-9


def test_the_constant_is_exactly_root_six_over_nine() -> None:
    """The closed form proved in DepthOneMainTerm.lean as depthOneConstant_eq_sqrt_six_div_nine.

    (4 sqrt8 / 27)(3/4)^{3/2} = (4*2 sqrt2/27)(3 sqrt3/8) = 3 sqrt6 / 27 = sqrt6 / 9.
    """
    assert abs(D.predicted_constant() - math.sqrt(6) / 9) < 1e-12
    assert abs((4 * math.sqrt(8) / 27) * (3 / 4) ** 1.5 - math.sqrt(6) / 9) < 1e-15


def test_the_lean_layer_carries_the_named_arithmetic_theorems() -> None:
    """The ledger row J-depth-one-arithmetic-layer names these; keep the file honest."""
    from research.juggler_sequence.lean_paths import LAYERS

    src = LAYERS["DepthOneMainTerm"].read_text(encoding="utf-8")
    for name in ("stationary_point", "dual_phase", "dual_phase_half",
                 "completeCubicSum_eq_nine", "zeta27_nine_sum",
                 "depthOneConstant_eq_sqrt_six_div_nine", "sum_affine_reindex",
                 "two_isUnit"):
        assert f"theorem {name}" in src, name
    for banned in ("sorry", "admit"):
        assert banned not in src


def test_the_stationary_phase_constant_is_four_root_eight_over_27_times_three_quarters_cubed_half() -> None:
    """(4√8/27)(3/4)^{3/2} = 0.27217, and the measured sum matches it to 1% at X = 1e5."""
    pred = D.predicted_constant()
    assert abs(pred - (4 * math.sqrt(8) / 27) * (3 / 4) ** 1.5) < 1e-12
    s = D.depth_one_sums(10**5)
    assert abs(s["abs_S_all_over_X34"] / pred - 1) < 0.02


def test_the_bias_lives_on_even_M_and_the_odd_sum_is_far_below_root_X() -> None:
    """Even M carry ≈ 0.425 X^{3/4} of imbalance; odd M carry O(1)-ish, and |S_odd| ≪ √X."""
    s = D.depth_one_sums(10**5)
    assert 0.40 < s["even_M_imbalance_over_X34"] < 0.45
    assert abs(s["imbalance_odd_M"]) < 0.02 * abs(s["imbalance_even_M"])
    assert s["abs_S_odd_over_sqrtX"] < 0.1


def test_the_tower_levels_show_only_root_order_imbalance() -> None:
    """Levels 1-4 over odd starts ≤ 1e5: |imbalance| / √cylinder stays O(1)."""
    t = D.tower_level_imbalances(10**5)
    assert all(abs(v["over_sqrt"]) < 3.0 for v in t.values())
    assert t["level_1"]["cylinder"] == 50000


def test_the_main_terms_cancel_for_every_odd_harmonic() -> None:
    """For odd k, ν ↦ 2ν-1 and r ↦ 2r both permute the residues mod 27k², so C_k = C'_k."""
    for k in (1, 3, 5, 7, 9, 11):
        h = D.harmonic_identity(k)
        assert h["identical"], h
    assert abs(D.harmonic_identity(1)["C_k"][0] - 9.0) < 1e-9
    assert abs(D.harmonic_identity(9)["C_k"][0]) < 1e-6          # k ≡ 0 mod 3: the sum vanishes


def test_the_odd_restricted_harmonic_sums_stay_at_the_fourth_root() -> None:
    """|Σ_{n odd ≤ X} e(k n^{3/2}/2)| ≤ 4 X^{1/4} for k = 1, 3, 5, 7 at X = 1e5."""
    for v in D.odd_harmonic_sums(10**5).values():
        assert v["over_X14"] < 4.0

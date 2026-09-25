/-
# Paper B, Lemma 4.3: the truncated sawtooth expansion

`docs/theory/juggler_parity_discrepancy_note.md`, Lemma 4.3, first assertion. With
`b(t) = {t} - 1/2`, `b_R(t) = -∑_{1 ≤ |r| ≤ R} e(rt)/(2πi r)` and `E_R(t) = min(1, 1/(R‖t‖))`,
`E_R = 1` at integers, one has `b(t) = b_R(t) + O(E_R(t))`, including at integers.

* `sawtoothPartial_eq_exp`: `b_R` in the printed exponential form equals
  `-∑_{r=1}^R sin(2π r t)/(π r)`;
* `sin_mul_dirichlet`: `sin(π s) (1 + 2 ∑_{r ≤ R} cos(2π r s)) = sin((2R+1) π s)`;
* `abs_sawtoothGap_le_of_le_half`: for `0 < f ≤ 1/2`, `|b(f) - b_R(f)| ≤ 1/(R f)`. The gap has
  derivative the Dirichlet kernel and vanishes at `1/2`; one integration by parts against the
  decreasing factor `1/sin(π s)` and `sin(π s) ≥ 2 s` give the bound;
* `abs_sawtooth_sub_le`: `|b(t) - b_R(t)| ≤ (5/2) E_R(t)` for every real `t` and `R ≥ 1`.
  Near integers, `|sin(2π r t)| ≤ 2π r ‖t‖` bounds the finite sum directly.
-/

import Problems.Juggler.PaperBCarryExpansion
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

namespace Problems.Juggler

namespace PaperBSawtoothExpansion

open Finset Real
open PaperBCarryExpansion

/-! ## The truncated series -/

/-- `b_R(t) = -∑_{r=1}^R sin(2π r t)/(π r)`, indexed by `r + 1` for `r < R`. -/
noncomputable def sawtoothPartial (R : ℕ) (t : ℝ) : ℝ :=
  -∑ r ∈ range R, sin (2 * π * (r + 1) * t) / (π * (r + 1))

/-- The gap `b(t) - b_R(t)` on the real line, with `b(t) = t - 1/2` (the value of the sawtooth
on `[0, 1)`). -/
noncomputable def sawtoothGap (R : ℕ) (t : ℝ) : ℝ := t - 1 / 2 - sawtoothPartial R t

/-- The Dirichlet kernel `1 + 2 ∑_{r=1}^R cos(2π r s)`. -/
noncomputable def dirichletKernel (R : ℕ) (s : ℝ) : ℝ :=
  1 + ∑ r ∈ range R, 2 * cos (2 * π * (r + 1) * s)

/-- A sum over `[-R, R]` splits into the zero term and symmetric pairs. -/
theorem sum_Icc_neg_eq_complex (ψ : ℤ → ℂ) (R : ℕ) :
    ∑ k ∈ Finset.Icc (-(R : ℤ)) R, ψ k =
      ψ 0 + ∑ r ∈ range R, (ψ ((r : ℤ) + 1) + ψ (-((r : ℤ) + 1))) := by
  induction R with
  | zero => simp
  | succ R ih =>
    have he : Finset.Icc (-((R + 1 : ℕ) : ℤ)) ((R + 1 : ℕ) : ℤ) =
        insert (-((R + 1 : ℕ) : ℤ)) (insert ((R + 1 : ℕ) : ℤ) (Finset.Icc (-(R : ℤ)) R)) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert, Nat.cast_add, Nat.cast_one]
      omega
    have hn : ((R + 1 : ℕ) : ℤ) ∉ Finset.Icc (-(R : ℤ)) R := by simp
    have hm : (-((R + 1 : ℕ) : ℤ)) ∉ insert ((R + 1 : ℕ) : ℤ) (Finset.Icc (-(R : ℤ)) R) := by
      simp only [Finset.mem_insert, Finset.mem_Icc, Nat.cast_add, Nat.cast_one]
      omega
    rw [he, sum_insert hm, sum_insert hn, ih, sum_range_succ]
    push_cast
    ring

/-- **The printed form of `b_R`.** `-∑_{1 ≤ |r| ≤ R} e(rt)/(2πi r) = -∑_{r=1}^R sin(2π r t)/(π r)`. -/
theorem sawtoothPartial_eq_exp (R : ℕ) (t : ℝ) :
    -(∑ k ∈ Finset.Icc (-(R : ℤ)) R,
        if k = 0 then (0 : ℂ) else
          BTCalculus.WeylDifferencing.phase ((k : ℝ) * t) / (2 * π * Complex.I * k)) =
      (sawtoothPartial R t : ℂ) := by
  rw [sum_Icc_neg_eq_complex, if_pos rfl, zero_add, sawtoothPartial]
  push_cast
  congr 1
  apply sum_congr rfl
  intro r _
  have h1 : ((r : ℤ) + 1) ≠ 0 := by omega
  have h2 : (-((r : ℤ) + 1)) ≠ 0 := by omega
  rw [if_neg h1, if_neg h2]
  have hr : ((r : ℂ) + 1) ≠ 0 := by exact_mod_cast (show (r : ℝ) + 1 ≠ 0 by positivity)
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
  unfold BTCalculus.WeylDifferencing.phase
  push_cast
  rw [Complex.sin, show (2 : ℂ) * π * (r + 1) * t = (2 * π * (r + 1) * t : ℝ) by push_cast; ring]
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring_nf

/-! ## The Dirichlet kernel -/

/-- `sin(π s) D_R(s) = sin((2R+1) π s)`. -/
theorem sin_mul_dirichlet (R : ℕ) (s : ℝ) :
    sin (π * s) * dirichletKernel R s = sin ((2 * R + 1) * π * s) := by
  induction R with
  | zero => simp [dirichletKernel]
  | succ R ih =>
    rw [dirichletKernel, sum_range_succ, ← add_assoc]
    have hD : dirichletKernel R s = 1 + ∑ r ∈ range R, 2 * cos (2 * π * (r + 1) * s) := rfl
    rw [← hD, mul_add, ih]
    set A := 2 * π * ((R : ℝ) + 1) * s
    have e1 : (2 * ((R + 1 : ℕ) : ℝ) + 1) * π * s = A + π * s := by push_cast; ring
    have e2 : (2 * (R : ℝ) + 1) * π * s = A - π * s := by ring
    rw [e1, e2, sin_add, sin_sub]
    ring

/-- The gap has derivative the Dirichlet kernel. -/
theorem hasDerivAt_sawtoothGap (R : ℕ) (s : ℝ) :
    HasDerivAt (sawtoothGap R) (dirichletKernel R s) s := by
  have hterm : ∀ r ∈ range R, HasDerivAt
      (fun t => sin (2 * π * ((r : ℝ) + 1) * t) / (π * ((r : ℝ) + 1)))
      (2 * cos (2 * π * ((r : ℝ) + 1) * s)) s := by
    intro r _
    have hlin : HasDerivAt (fun t => 2 * π * ((r : ℝ) + 1) * t) (2 * π * ((r : ℝ) + 1)) s := by
      simpa using (hasDerivAt_id s).const_mul (2 * π * ((r : ℝ) + 1))
    have h := (hlin.sin).div_const (π * ((r : ℝ) + 1))
    refine h.congr_deriv ?_
    have : π * ((r : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  have hsum := HasDerivAt.sum hterm
  have h := ((hasDerivAt_id s).sub_const (1 / 2 : ℝ)).add hsum
  have hfun : sawtoothGap R = (fun x => id x - 1 / 2) +
      ∑ i ∈ range R, fun t => sin (2 * π * ((i : ℝ) + 1) * t) / (π * ((i : ℝ) + 1)) := by
    funext t
    simp only [sawtoothGap, sawtoothPartial, Pi.add_apply, Finset.sum_apply, id, sub_neg_eq_add]
  rw [hfun]
  exact h

/-- `b_R(1/2) = 0`, so the gap vanishes at `1/2`. -/
theorem sawtoothGap_half (R : ℕ) : sawtoothGap R (1 / 2) = 0 := by
  unfold sawtoothGap sawtoothPartial
  have : ∀ r ∈ range R, sin (2 * π * ((r : ℝ) + 1) * (1 / 2)) / (π * ((r : ℝ) + 1)) = 0 := by
    intro r _
    have : 2 * π * ((r : ℝ) + 1) * (1 / 2) = ((r + 1 : ℕ) : ℝ) * π := by push_cast; ring
    rw [this, sin_nat_mul_pi, zero_div]
  rw [sum_congr rfl this]
  simp

/-- The gap is odd about `1/2`: `G(1 - t) = -G(t)`. -/
theorem sawtoothGap_one_sub (R : ℕ) (t : ℝ) : sawtoothGap R (1 - t) = -sawtoothGap R t := by
  unfold sawtoothGap sawtoothPartial
  have : ∀ r ∈ range R, sin (2 * π * ((r : ℝ) + 1) * (1 - t)) / (π * ((r : ℝ) + 1)) =
      -(sin (2 * π * ((r : ℝ) + 1) * t) / (π * ((r : ℝ) + 1))) := by
    intro r _
    have e : 2 * π * ((r : ℝ) + 1) * (1 - t) =
        ((2 * (r + 1) : ℕ) : ℝ) * π - 2 * π * ((r : ℝ) + 1) * t := by push_cast; ring
    rw [e, sin_nat_mul_pi_sub, pow_mul, neg_one_sq, one_pow, one_mul, neg_div]
  rw [sum_congr rfl this, sum_neg_distrib]
  ring

/-! ## The bound away from integers -/

/-- **Away from integers.** For `R ≥ 1` and `0 < f ≤ 1/2`, `|b(f) - b_R(f)| ≤ 1/(R f)`. -/
theorem abs_sawtoothGap_le_of_le_half {R : ℕ} (hR : 1 ≤ R) {f : ℝ} (hf0 : 0 < f)
    (hf : f ≤ 1 / 2) : |sawtoothGap R f| ≤ 1 / (R * f) := by
  set N : ℝ := 2 * R + 1 with hN
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hN0 : 0 < N := by positivity
  have hsinpos : ∀ s ∈ Set.uIcc f (1 / 2), 0 < sin (π * s) := by
    intro s hs
    rw [Set.uIcc_of_le hf] at hs
    exact sin_pos_of_pos_of_lt_pi (by nlinarith [pi_pos, hs.1]) (by nlinarith [pi_pos, hs.2])
  have hcosnn : ∀ s ∈ Set.uIcc f (1 / 2), 0 ≤ cos (π * s) := by
    intro s hs
    rw [Set.uIcc_of_le hf] at hs
    apply cos_nonneg_of_neg_pi_div_two_le_of_le <;> nlinarith [pi_pos, hs.1, hs.2]
  -- FTC for the gap
  have hftc : ∫ s in f..(1 / 2), dirichletKernel R s = sawtoothGap R (1 / 2) - sawtoothGap R f :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hasDerivAt_sawtoothGap R s)
      (by unfold dirichletKernel; exact (by fun_prop : Continuous _).intervalIntegrable _ _)
  rw [sawtoothGap_half, zero_sub] at hftc
  -- integration by parts
  set u : ℝ → ℝ := fun s => (sin (π * s))⁻¹ with hu
  set u' : ℝ → ℝ := fun s => -(cos (π * s) * π) / sin (π * s) ^ 2 with hu'
  set v : ℝ → ℝ := fun s => -cos (N * π * s) / (N * π) with hv
  set v' : ℝ → ℝ := fun s => sin (N * π * s) with hv'
  have hderu : ∀ s ∈ Set.uIcc f (1 / 2), HasDerivAt u (u' s) s := by
    intro s hs
    have hlin : HasDerivAt (fun t => π * t) π s := by
      simpa using (hasDerivAt_id s).const_mul π
    exact (hlin.sin).inv (hsinpos s hs).ne'
  have hderv : ∀ s ∈ Set.uIcc f (1 / 2), HasDerivAt v (v' s) s := by
    intro s _
    have hlin : HasDerivAt (fun t => N * π * t) (N * π) s := by
      simpa using (hasDerivAt_id s).const_mul (N * π)
    have h := (hlin.cos.neg).div_const (N * π)
    refine h.congr_deriv ?_
    have : N * π ≠ 0 := by positivity
    simp only [hv']
    field_simp
  have hu'c : ContinuousOn u' (Set.uIcc f (1 / 2)) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro s hs
    exact pow_ne_zero _ (hsinpos s hs).ne'
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hderu hderv
    hu'c.intervalIntegrable ((by fun_prop : Continuous v').intervalIntegrable _ _)
  have hcongr : ∫ s in f..(1 / 2), dirichletKernel R s = ∫ s in f..(1 / 2), u s * v' s := by
    apply intervalIntegral.integral_congr
    intro s hs
    have e : sin (N * π * s) = sin (π * s) * dirichletKernel R s := by
      rw [hN, sin_mul_dirichlet]
    have hne := (hsinpos s hs).ne'
    show dirichletKernel R s = (sin (π * s))⁻¹ * sin (N * π * s)
    rw [e]
    field_simp
  -- the pieces
  have hvb : ∀ s, |v s| ≤ 1 / (N * π) := by
    intro s
    simp only [hv, abs_div, abs_neg, abs_of_pos (by positivity : 0 < N * π)]
    exact div_le_div_of_nonneg_right (abs_cos_le_one _) (by positivity)
  have hsf : 2 * f ≤ sin (π * f) := by
    have h := mul_le_sin (x := π * f) (by positivity) (by nlinarith [pi_pos])
    have : 2 / π * (π * f) = 2 * f := by field_simp
    linarith
  have huf : u f ≤ 1 / (2 * f) := by
    simp only [hu]
    rw [← one_div]
    exact one_div_le_one_div_of_le (by positivity) hsf
  have hu1 : u (1 / 2) = 1 := by
    simp only [hu]
    rw [show π * (1 / 2) = π / 2 by ring, sin_pi_div_two, inv_one]
  have hufpos : 0 < u f := by simp only [hu]; exact inv_pos.mpr (hsinpos f (by simp))
  have hu'nonpos : ∀ s ∈ Set.uIcc f (1 / 2), u' s ≤ 0 := by
    intro s hs
    simp only [hu']
    apply div_nonpos_of_nonpos_of_nonneg
    · have := hcosnn s hs
      nlinarith [pi_pos]
    · positivity
  have hftcu : ∫ s in f..(1 / 2), u' s = u (1 / 2) - u f :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderu hu'c.intervalIntegrable
  have hint : |∫ s in f..(1 / 2), u' s * v s| ≤ (u f - u (1 / 2)) / (N * π) := by
    have hle := intervalIntegral.norm_integral_le_of_norm_le (μ := MeasureTheory.volume) hf
      (f := fun s => u' s * v s) (g := fun s => -u' s / (N * π))
      (Filter.Eventually.of_forall (fun s hs => by
        have hs' : s ∈ Set.uIcc f (1 / 2) := by
          rw [Set.uIcc_of_le hf]; exact ⟨hs.1.le, hs.2⟩
        have hn := hu'nonpos s hs'
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonpos hn]
        have := hvb s
        rw [div_eq_mul_one_div]
        exact mul_le_mul_of_nonneg_left this (by linarith)))
      ((hu'c.intervalIntegrable).neg.div_const _)
    rw [Real.norm_eq_abs] at hle
    refine hle.trans (le_of_eq ?_)
    rw [intervalIntegral.integral_div, intervalIntegral.integral_neg, hftcu]
    ring
  have hG : sawtoothGap R f = -(u (1 / 2) * v (1 / 2) - u f * v f -
      ∫ s in f..(1 / 2), u' s * v s) := by
    rw [← hibp, ← hcongr]
    linarith
  have hsum : |sawtoothGap R f| ≤ 2 * u f / (N * π) := by
    rw [hG, abs_neg]
    have h1 : |u (1 / 2) * v (1 / 2)| ≤ 1 / (N * π) := by
      rw [abs_mul, hu1, abs_one, one_mul]; exact hvb _
    have h2 : |u f * v f| ≤ u f / (N * π) := by
      rw [abs_mul, abs_of_pos hufpos, div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left (hvb _) hufpos.le
    calc _ ≤ |u (1 / 2) * v (1 / 2) - u f * v f| + |∫ s in f..(1 / 2), u' s * v s| :=
          abs_sub _ _
      _ ≤ |u (1 / 2) * v (1 / 2)| + |u f * v f| + |∫ s in f..(1 / 2), u' s * v s| := by
          gcongr; exact abs_sub _ _
      _ ≤ 1 / (N * π) + u f / (N * π) + (u f - u (1 / 2)) / (N * π) := by gcongr
      _ = 2 * u f / (N * π) := by rw [hu1]; ring
  calc |sawtoothGap R f| ≤ 2 * u f / (N * π) := hsum
    _ ≤ 2 * (1 / (2 * f)) / (N * π) := by gcongr
    _ ≤ 1 / (R * f) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hNR : (R : ℝ) ≤ N * π := by nlinarith [two_le_pi]
      field_simp
      nlinarith

/-! ## Every real `t` -/

/-- `b_R` is one-periodic: it depends only on `{t}`. -/
theorem sawtoothPartial_fract (R : ℕ) (t : ℝ) :
    sawtoothPartial R t = sawtoothPartial R (Int.fract t) := by
  unfold sawtoothPartial
  congr 1
  apply sum_congr rfl
  intro r _
  congr 1
  have e : 2 * π * ((r : ℝ) + 1) * t =
      2 * π * ((r : ℝ) + 1) * Int.fract t + (((r + 1 : ℕ) : ℤ) * ⌊t⌋ : ℤ) * (2 * π) := by
    rw [← Int.floor_add_fract t]
    push_cast
    rw [Int.floor_add_fract t]
    have := Int.floor_add_fract t
    rw [Int.fract] at this ⊢
    ring
  rw [e, sin_add_int_mul_two_pi]

/-- Near an integer, `|b_R(t)| ≤ 2 R ‖t‖`. -/
theorem abs_sawtoothPartial_le (R : ℕ) (t : ℝ) :
    |sawtoothPartial R t| ≤ 2 * R * nearestIntDist t := by
  rw [sawtoothPartial_fract]
  set f := Int.fract t with hf
  have hf0 := Int.fract_nonneg t
  have hf1 := Int.fract_lt_one t
  have hterm : ∀ r ∈ range R, |sin (2 * π * ((r : ℝ) + 1) * f) / (π * ((r : ℝ) + 1))| ≤
      2 * nearestIntDist t := by
    intro r _
    have hpos : 0 < π * ((r : ℝ) + 1) := by positivity
    rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    unfold nearestIntDist
    rw [← hf]
    rcases le_total f (1 - f) with h | h
    · rw [min_eq_left h]
      calc |sin (2 * π * ((r : ℝ) + 1) * f)| ≤ |2 * π * ((r : ℝ) + 1) * f| := abs_sin_le_abs
        _ = 2 * f * (π * ((r : ℝ) + 1)) := by rw [abs_of_nonneg (by positivity)]; ring
    · rw [min_eq_right h]
      have e : 2 * π * ((r : ℝ) + 1) * f =
          ((2 * (r + 1) : ℕ) : ℝ) * π - 2 * π * ((r : ℝ) + 1) * (1 - f) := by push_cast; ring
      rw [e, sin_nat_mul_pi_sub, pow_mul, neg_one_sq, one_pow, one_mul, abs_neg]
      calc |sin (2 * π * ((r : ℝ) + 1) * (1 - f))| ≤ |2 * π * ((r : ℝ) + 1) * (1 - f)| :=
            abs_sin_le_abs
        _ = 2 * (1 - f) * (π * ((r : ℝ) + 1)) := by
            rw [abs_of_nonneg (by nlinarith [pi_pos])]; ring
  unfold sawtoothPartial
  rw [abs_neg]
  calc _ ≤ ∑ r ∈ range R, |sin (2 * π * ((r : ℝ) + 1) * f) / (π * ((r : ℝ) + 1))| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r ∈ range R, 2 * nearestIntDist t := sum_le_sum hterm
    _ = 2 * R * nearestIntDist t := by rw [sum_const, card_range, nsmul_eq_mul]; ring

/-- **Paper B, Lemma 4.3, first assertion.** For `R ≥ 1` and every real `t`,
`|b(t) - b_R(t)| ≤ (5/2) E_R(t)`, where `b(t) = {t} - 1/2` and `E_R = 1` at integers. -/
theorem abs_sawtooth_sub_le {R : ℕ} (hR : 1 ≤ R) (t : ℝ) :
    |Int.fract t - 1 / 2 - sawtoothPartial R t| ≤ 5 / 2 * carryWeight R t := by
  obtain ⟨hd0, hd1⟩ := nearestIntDist_mem t
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hf0 := Int.fract_nonneg t
  have hf1 := Int.fract_lt_one t
  unfold carryWeight
  split_ifs with hle
  · have hb := abs_sawtoothPartial_le R t
    have hfr : |Int.fract t - 1 / 2| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
    calc _ ≤ |Int.fract t - 1 / 2| + |sawtoothPartial R t| := abs_sub _ _
      _ ≤ 1 / 2 + 2 * R * nearestIntDist t := add_le_add hfr hb
      _ ≤ 5 / 2 * 1 := by linarith
  · push Not at hle
    have hdpos : 0 < nearestIntDist t := by
      by_contra h
      have : nearestIntDist t = 0 := le_antisymm (not_lt.mp h) hd0
      rw [this, mul_zero] at hle
      linarith
    have hgap : Int.fract t - 1 / 2 - sawtoothPartial R t = sawtoothGap R (Int.fract t) := by
      rw [sawtoothPartial_fract R t, sawtoothGap]
    rw [hgap]
    have hmain : |sawtoothGap R (Int.fract t)| ≤ 1 / (R * nearestIntDist t) := by
      unfold nearestIntDist at hdpos ⊢
      rcases le_total (Int.fract t) (1 - Int.fract t) with h | h
      · rw [min_eq_left h] at hdpos ⊢
        exact abs_sawtoothGap_le_of_le_half hR hdpos (by linarith)
      · rw [min_eq_right h] at hdpos ⊢
        have := abs_sawtoothGap_le_of_le_half hR hdpos (by linarith)
        rw [sawtoothGap_one_sub, abs_neg] at this
        exact this
    have hpos : 0 < 1 / (R * nearestIntDist t) := by positivity
    linarith

end PaperBSawtoothExpansion

end Problems.Juggler

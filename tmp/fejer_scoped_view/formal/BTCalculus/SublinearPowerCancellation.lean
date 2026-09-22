import BTCalculus.KusminLandau
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Cancellation for sublinear real powers

The first-derivative estimate supplies the base case for power-phase
differencing. No assertion that shifted differences are pure powers is used.
-/

noncomputable section

namespace BTCalculus.SublinearPowerCancellation

open Finset Filter
open scoped Topology ComplexConjugate
open BTCalculus.WeylDifferencing BTCalculus.KusminLandau

/-- The derivative is positive and decreasing on the positive half-line. -/
theorem power_derivative_antitone {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ) (hθ1 : θ < 1) :
    AntitoneOn (fun x : ℝ => c * θ * x ^ (θ - 1)) (Set.Ioi 0) := by
  intro x hx y _ hxy
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hx hxy (by linarith))
    (by positivity)

/-- An explicit bound on every prefix after the derivative has fallen below one half. -/
theorem sublinear_power_sum_bound {c θ A : ℝ} (hc : 0 < c) (hθ : 0 < θ) (hθ1 : θ < 1)
    (hA : 0 < A) (hsmall : c * θ * A ^ (θ - 1) ≤ 1 / 2) (N : ℕ) :
    ‖∑ n ∈ range N, phase (c * (A + n) ^ θ)‖ ≤
      1 / (c * θ * (A + N) ^ (θ - 1)) := by
  have hAN : 0 < A + (N : ℝ) := by positivity
  have hanti := power_derivative_antitone hc hθ hθ1
  have hδ : 0 < c * θ * (A + N) ^ (θ - 1) := by positivity
  have hδsmall : c * θ * (A + N) ^ (θ - 1) ≤ 1 / 2 :=
    (hanti hA hAN (le_add_of_nonneg_right (Nat.cast_nonneg N))).trans hsmall
  apply first_derivative_sum_bound (fun x : ℝ => c * x ^ θ)
    (fun x => c * θ * x ^ (θ - 1)) A N hδ
  · apply ContinuousOn.const_mul
    exact (Real.continuous_rpow_const hθ.le).continuousOn
  · intro x hx
    have hx0 : 0 < x := hA.trans hx.1
    simpa only [mul_assoc] using
      (Real.hasDerivAt_rpow_const (p := θ) (Or.inl (ne_of_gt hx0))).const_mul c
  · intro x hx
    have hx0 : 0 < x := hA.trans hx.1
    constructor
    · exact hanti hx0 hAN hx.2.le
    · have hu := (hanti hA hx0 hx.1.le).trans hsmall
      linarith
  · right
    exact hanti.mono (fun x hx => hA.trans hx.1)

/-- Sublinear power cancellation after any admissible fixed initial shift. -/
theorem tendsto_sublinear_power_average_shift {c θ A : ℝ}
    (hc : 0 < c) (hθ : 0 < θ) (hθ1 : θ < 1) (hA : 0 < A)
    (hsmall : c * θ * A ^ (θ - 1) ≤ 1 / 2) :
    Tendsto (average (fun n => phase (c * (A + n) ^ θ))) atTop (𝓝 0) := by
  have htop : Tendsto (fun N : ℕ => A + (N : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left atTop A tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun N : ℕ => (A + N) ^ (-θ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hθ).comp htop
  have hratio : Tendsto (fun N : ℕ => (A + N) / (N : ℝ)) atTop (𝓝 1) := by
    have hlim := (tendsto_const_div_atTop_nhds_zero_nat A).add_const 1
    simp only [zero_add] at hlim
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    simp [add_div, hn]
  have hlim : Tendsto (fun N : ℕ => ((A + N) / (N : ℝ)) * (A + N) ^ (-θ) / (c * θ))
      atTop (𝓝 0) := by
    simpa using (hratio.mul hpow).div_const (c * θ)
  apply squeeze_zero_norm' (a := fun N : ℕ =>
    ((A + N) / (N : ℝ)) * (A + N) ^ (-θ) / (c * θ))
  · filter_upwards [eventually_ge_atTop 1] with N hN
    rw [norm_average]
    have hbound := sublinear_power_sum_bound hc hθ hθ1 hA hsmall N
    have hAN : 0 < A + (N : ℝ) := by positivity
    calc ‖∑ n ∈ range N, phase (c * (A + n) ^ θ)‖ / (N : ℝ)
        ≤ (1 / (c * θ * (A + N) ^ (θ - 1))) / (N : ℝ) :=
          div_le_div_of_nonneg_right hbound (by positivity)
      _ = ((A + N) / (N : ℝ)) * (A + N) ^ (-θ) / (c * θ) := by
        rw [Real.rpow_sub hAN, Real.rpow_one, Real.rpow_neg hAN.le]
        simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
        ring
  · exact hlim

/-- Discarding a fixed initial segment preserves convergence of averages to zero. -/
theorem tendsto_average_zero_of_shift (z : ℕ → ℂ) (a : ℕ)
    (hshift : Tendsto (average (fun n => z (n + a))) atTop (𝓝 0)) :
    Tendsto (average z) atTop (𝓝 0) := by
  have hp := (tendsto_const_div_atTop_nhds_zero_nat (∑ n ∈ range a, z n)).comp
    (tendsto_add_atTop_nat a)
  have hr := tendsto_natCast_div_add_atTop (a : ℂ)
  have hlim := hp.add (hshift.mul hr)
  apply (tendsto_add_atTop_iff_nat a).1
  apply (show Tendsto (fun N : ℕ =>
    (∑ n ∈ range a, z n) / ((N + a : ℕ) : ℂ) +
      average (fun n => z (n + a)) N * ((N : ℂ) / (N + a))) atTop (𝓝 0) by
        simpa using hlim).congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hs : (∑ n ∈ range (N + a), z n) =
      (∑ n ∈ range a, z n) + ∑ n ∈ range N, z (n + a) := by
    rw [Nat.add_comm N a, sum_range_add]
    simp only [Nat.add_comm]
  unfold average
  rw [hs]
  push_cast
  field_simp

/-- Unconditional cancellation for every positive multiple of a sublinear power. -/
theorem tendsto_sublinear_power_average_pos {c θ : ℝ}
    (hc : 0 < c) (hθ : 0 < θ) (hθ1 : θ < 1) :
    Tendsto (average (fun n => phase (c * (n : ℝ) ^ θ))) atTop (𝓝 0) := by
  have hp : Tendsto (fun N : ℕ => (N : ℝ) ^ (θ - 1)) atTop (𝓝 0) := by
    have he : θ - 1 = -(1 - θ) := by ring
    rw [he]
    exact (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - θ)).comp
      tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ N : ℕ in atTop, c * θ * (N : ℝ) ^ (θ - 1) < 1 / 2 := by
    have ht : Tendsto (fun N : ℕ => c * θ * (N : ℝ) ^ (θ - 1)) atTop (𝓝 0) := by
      simpa using hp.const_mul (c * θ)
    exact ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨A, hA, hs⟩ := ((eventually_ge_atTop 1).and hsmall).exists
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  apply tendsto_average_zero_of_shift _ A
  simpa only [Nat.cast_add, add_comm (A : ℝ)] using
    tendsto_sublinear_power_average_shift hc hθ hθ1 hAR hs.le

theorem phase_neg (t : ℝ) : phase (-t) = conj (phase t) := by
  unfold phase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- The sign of the nonzero coefficient is unrestricted. -/
theorem tendsto_sublinear_power_average {c θ : ℝ}
    (hc : c ≠ 0) (hθ : 0 < θ) (hθ1 : θ < 1) :
    Tendsto (average (fun n => phase (c * (n : ℝ) ^ θ))) atTop (𝓝 0) := by
  rcases lt_or_gt_of_ne hc with hc | hc
  · have hpos := tendsto_sublinear_power_average_pos (neg_pos.mpr hc) hθ hθ1
    apply tendsto_zero_iff_norm_tendsto_zero.2
    have he (N : ℕ) : average (fun n => phase (-c * (n : ℝ) ^ θ)) N =
        conj (average (fun n => phase (c * (n : ℝ) ^ θ)) N) := by
      simp only [neg_mul, phase_neg, average, map_div₀, map_sum, map_natCast]
    simpa only [he, Complex.norm_conj, norm_zero] using hpos.norm
  · exact tendsto_sublinear_power_average_pos hc hθ hθ1

end BTCalculus.SublinearPowerCancellation

import Problems.Juggler.OOEERootPhase

/-! # Slow-mode cancellation outside the OOEE resonance windows

The reference slope is explicit. The derivative estimate and its
distance from the adjacent integers are proved on the entire support.
-/

noncomputable section

namespace Problems.Juggler.OOEESlowModes

open Finset BTCalculus.WeylDifferencing BTCalculus.SecondDerivative BTCalculus.KusminLandau
open OOEECurvature OOEEPhaseComparison OOEERootPhase

def slowSlope (P : ℝ) : ℝ := (9/8)*P^(1/8:ℝ)

def Nonresonant (P C k : ℝ) : Prop :=
  ∀ z : ℤ, C*P^(-7/16:ℝ) ≤ |k*slowSlope P-(z:ℝ)|

theorem slope_variation {P D x : ℝ} (hP : 0 < P) (_hD : 0 ≤ D)
    (hx : P ≤ x) (hxD : x ≤ P+D*P^(7/16:ℝ)) (k : ℝ) :
    |(9/8)*k*x^(1/8:ℝ)-k*slowSlope P| ≤ (9/64)*D*|k| *P^(-7/16:ℝ) := by
  have hs := secant_bounds (fun y : ℝ => y^(1/8:ℝ))
    (fun y : ℝ => (1/8)*y^(-7/8:ℝ)) hx
    (lo := 0) (hi := (1/8)*P^(-7/8:ℝ))
    (by
      intro y hy
      convert deriv_power (show 0 < y by linarith [hy.1]) (1/8) using 1; norm_num)
    (by
      intro y hy
      have hy0 : 0 < y := by linarith [hy.1]
      constructor
      · positivity
      · exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hP hy.1 (by norm_num)) (by norm_num))
  have hdiff : 0 ≤ x^(1/8:ℝ)-P^(1/8:ℝ) := by simpa using hs.1
  have hprod : P^(-7/8:ℝ)*P^(7/16:ℝ) = P^(-7/16:ℝ) := by
    rw [← Real.rpow_add hP]
    norm_num
  have hupper : x^(1/8:ℝ)-P^(1/8:ℝ) ≤ (D/8)*P^(-7/16:ℝ) := by
    calc _ ≤ (1/8)*P^(-7/8:ℝ)*(x-P) := hs.2
      _ ≤ (1/8)*P^(-7/8:ℝ)*(D*P^(7/16:ℝ)) := by gcongr; linarith
      _ = _ := by rw [← hprod]; ring
  have hid : (9/8)*k*x^(1/8:ℝ)-k*slowSlope P =
      (9/8)*k*(x^(1/8:ℝ)-P^(1/8:ℝ)) := by dsimp [slowSlope]; ring
  rw [hid, abs_mul, abs_mul, abs_of_nonneg hdiff,
    abs_of_pos (by norm_num : (0:ℝ) < 9/8)]
  calc _ ≤ (9/8)*|k| *((D/8)*P^(-7/16:ℝ)) := by gcongr
    _ = _ := by ring

theorem slope_integer_band {P D C x k : ℝ} (hP : 0 < P) (hD : 0 ≤ D)
    (hx : P ≤ x) (hxD : x ≤ P+D*P^(7/16:ℝ))
    (hdom : (9/32)*D*|k| ≤ C) (hnr : Nonresonant P C k) :
    (C/2)*P^(-7/16:ℝ) ≤ (9/8)*k*x^(1/8:ℝ)-(⌊k*slowSlope P⌋:ℝ) ∧
      (9/8)*k*x^(1/8:ℝ)-(⌊k*slowSlope P⌋:ℝ) ≤ 1-(C/2)*P^(-7/16:ℝ) := by
  have hvar := slope_variation hP hD hx hxD k
  have hvar' : |(9/8)*k*x^(1/8:ℝ)-k*slowSlope P| ≤ (C/2)*P^(-7/16:ℝ) := by
    have hm := mul_le_mul_of_nonneg_right hdom (Real.rpow_pos_of_pos hP (-7/16)).le
    nlinarith
  have hv := abs_le.mp hvar'
  have hlo := hnr ⌊k*slowSlope P⌋
  rw [abs_of_nonneg (sub_nonneg.mpr (Int.floor_le _))] at hlo
  have hhi := hnr (⌊k*slowSlope P⌋+1)
  push_cast at hhi
  rw [abs_of_nonpos (by linarith [Int.lt_floor_add_one (k*slowSlope P)])] at hhi
  constructor <;> linarith

/-- The smooth slow mode, with an explicit inverse-resonance constant. -/
theorem smooth_slow_sum {P D C a k : ℝ} (N : ℕ)
    (hP : 1 ≤ P) (hD : 0 ≤ D) (hC : 0 < C)
    (ha : P ≤ a) (hb : a+2*N ≤ P+D*P^(7/16:ℝ))
    (hdom : (9/32)*D*|k| ≤ C) (hnr : Nonresonant P C k) :
    ‖∑ n ∈ range N, phase ((k/2)*(a+2*n)^(9/8:ℝ))‖ ≤ (2/C)*P^(7/16:ℝ) := by
  have hP0 : 0 < P := by linarith
  let q : ℤ := ⌊k*slowSlope P⌋
  let f : ℝ → ℝ := fun t => (k/2)*(a+2*t)^(9/8:ℝ)-(q:ℝ)*t
  let g : ℝ → ℝ := fun t => (9/8)*k*(a+2*t)^(1/8:ℝ)-(q:ℝ)
  let delta := (C/2)*P^(-7/16:ℝ)
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hmap (t : ℝ) (ht : t ∈ Set.Icc 0 (0+(N:ℝ))) :
      P ≤ a+2*t ∧ a+2*t ≤ P+D*P^(7/16:ℝ) := by constructor <;> linarith [ht.1, ht.2]
  have hd (t : ℝ) (ht : t ∈ Set.Icc 0 (0+(N:ℝ))) : HasDerivAt f (g t) t := by
    have ht0 : 0 < a+2*t := hP0.trans_le (hmap t ht).1
    have haff : HasDerivAt (fun y : ℝ => a+2*y) 2 t := by
      simpa using ((hasDerivAt_id t).const_mul 2).const_add a
    have hp := (deriv_power ht0 (9/8)).comp t haff
    have hf := (hp.const_mul (k/2)).fun_sub ((hasDerivAt_id t).const_mul (q:ℝ))
    apply hf.congr_deriv
    norm_num [g]
    ring
  have hc : ContinuousOn f (Set.Icc 0 (0+(N:ℝ))) :=
    fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hgap (t : ℝ) (ht : t ∈ Set.Ioo 0 (0+(N:ℝ))) : delta ≤ g t ∧ g t ≤ 1-delta := by
    have hm := hmap t ⟨ht.1.le, ht.2.le⟩
    exact slope_integer_band hP0 hD hm.1 hm.2 hdom hnr
  have hmono : MonotoneOn g (Set.Ioo 0 (0+(N:ℝ))) ∨ AntitoneOn g (Set.Ioo 0 (0+(N:ℝ))) := by
    rcases le_total 0 k with hk | hk
    · left
      intro x hx y hy hxy
      have hp := Real.rpow_le_rpow
        (show 0 ≤ a+2*x by linarith [hx.1]) (show a+2*x ≤ a+2*y by linarith)
        (by norm_num : (0:ℝ) ≤ 1/8)
      have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ (9/8:ℝ)*k by positivity)
      dsimp [g]
      linarith
    · right
      intro x hx y hy hxy
      have hp := Real.rpow_le_rpow
        (show 0 ≤ a+2*x by linarith [hx.1]) (show a+2*x ≤ a+2*y by linarith)
        (by norm_num : (0:ℝ) ≤ 1/8)
      have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ -((9/8:ℝ)*k) by nlinarith)
      dsimp [g]
      linarith
  have hs := first_derivative_sum_bound f g 0 N hdelta hc
    (fun t ht => hd t ⟨ht.1.le, ht.2.le⟩) hgap hmono
  simp only [f, zero_add, phase_sub_int_mul] at hs
  have hid : 1/delta = (2/C)*P^(7/16:ℝ) := by
    dsimp [delta]
    rw [show (-7/16:ℝ) = -(7/16) by norm_num, Real.rpow_neg hP0.le]
    field_simp
  exact hs.trans_eq hid

theorem actual_slow_sum {P D C a k : ℝ} (N : ℕ)
    (hP : 1 ≤ P) (hD : 0 ≤ D) (hC : 0 < C)
    (ha : P ≤ a) (hb : a+2*N ≤ P+D*P^(7/16:ℝ))
    (hdom : (9/32)*D*|k| ≤ C) (hnr : Nonresonant P C k) :
    ‖∑ n ∈ range N, phase ((k/2)*actualRoot (a+2*n))‖ ≤
      (2/C)*P^(7/16:ℝ)+3*Real.pi*|k| *D*P^(1/16:ℝ) := by
  have hN : (N:ℝ) ≤ D*P^(7/16:ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hc := actual_phase_comparison (u := 0) (v := 0) (w := k) N hP ha hD hN
  simp only [actualPhase, originalPhase, zero_mul, zero_div, zero_add] at hc
  have hs := smooth_slow_sum N hP hD hC ha hb hdom hnr
  have hn := norm_add_le
    ((∑ n ∈ range N, phase ((k/2)*actualRoot (a+2*n)))-
      ∑ n ∈ range N, phase ((k/2)*(a+2*n)^(9/8:ℝ)))
    (∑ n ∈ range N, phase ((k/2)*(a+2*n)^(9/8:ℝ)))
  rw [sub_add_cancel] at hn
  linarith

/-- No extra right support is required beyond the actual sample points. -/
theorem actual_slow_samples {P D C a k : ℝ} (N : ℕ)
    (hP : 1 ≤ P) (hD : 0 ≤ D) (hC : 0 < C)
    (hpoints : ∀ n < N, P ≤ a+2*n ∧ a+2*n ≤ P+D*P^(7/16:ℝ))
    (hdom : (9/32)*D*|k| ≤ C) (hnr : Nonresonant P C k) :
    ‖∑ n ∈ range N, phase ((k/2)*actualRoot (a+2*n))‖ ≤
      (2/C)*P^(7/16:ℝ)+3*Real.pi*|k| *D*P^(1/16:ℝ)+1 := by
  cases N with
  | zero => simp only [sum_range_zero, norm_zero]; positivity
  | succ N =>
    have ha : P ≤ a := by simpa using (hpoints 0 (by omega)).1
    have hb := (hpoints N (by omega)).2
    have hs := actual_slow_sum N hP hD hC ha hb hdom hnr
    rw [sum_range_succ]
    exact (norm_add_le _ _).trans (by rw [phase_norm]; linarith)

/-- The same estimate in the target variable of the OOEE fibres. -/
theorem target_slow_samples {m D C a k : ℝ} (N : ℕ)
    (hm : 1 ≤ m) (hD : 0 ≤ D) (hC : 0 < C)
    (hpoints : ∀ n < N, m^(16/9:ℝ) ≤ a+2*n ∧ a+2*n ≤ m^(16/9:ℝ)+D*m^(7/9:ℝ))
    (hdom : (9/32)*D*|k| ≤ C)
    (hnr : ∀ z : ℤ, C*m^(-7/9:ℝ) ≤ |k*((9/8)*m^(2/9:ℝ))-(z:ℝ)|) :
    ‖∑ n ∈ range N, phase ((k/2)*actualRoot (a+2*n))‖ ≤
      (2/C)*m^(7/9:ℝ)+3*Real.pi*|k| *D*m^(1/9:ℝ)+1 := by
  have hm0 : 0 ≤ m := by linarith
  have hp1 : (m^(16/9:ℝ))^(7/16:ℝ) = m^(7/9:ℝ) := by rw [← Real.rpow_mul hm0]; norm_num
  have hp2 : (m^(16/9:ℝ))^(1/16:ℝ) = m^(1/9:ℝ) := by rw [← Real.rpow_mul hm0]; norm_num
  have hp3 : (m^(16/9:ℝ))^(-7/16:ℝ) = m^(-7/9:ℝ) := by rw [← Real.rpow_mul hm0]; norm_num
  have hp4 : slowSlope (m^(16/9:ℝ)) = (9/8)*m^(2/9:ℝ) := by
    rw [slowSlope, ← Real.rpow_mul hm0]
    norm_num
  have hs := actual_slow_samples (P := m^(16/9:ℝ)) N
    (Real.one_le_rpow hm (by norm_num)) hD hC
    (by simpa only [hp1] using hpoints) hdom (by simpa only [Nonresonant, hp3, hp4] using hnr)
  simpa only [hp1, hp2] using hs

end Problems.Juggler.OOEESlowModes

import Problems.Juggler.BeattyGapCounting
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Integrating a gap-counting asymptotic

The truncated sum of gap lengths is the integral of their counting function.
The exponent two-thirds therefore gives a cube-root tube asymptotic, with
the exact factor three. All statements use real Lebesgue measure.
-/

namespace Problems.Juggler.BeattyPhase

open Filter Topology Set MeasureTheory Finset

/-- Summability makes the number of gaps above any positive threshold finite. -/
theorem finite_gapCount {w : ℕ → ℝ} (hw : Summable w) {x : ℝ} (hx : 0 < x) :
    {n | x ≤ w n}.Finite := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hw.tendsto_atTop_zero).2 x hx)
  apply (finite_lt_nat N).subset
  intro n hn
  change n < N
  by_contra h
  exact not_lt_of_ge hn (hN n (le_of_not_gt h))

private theorem gapCount_eq_tsum_indicator {w : ℕ → ℝ} (hw : Summable w)
    {x : ℝ} (hx : 0 < x) :
    (gapCount w x : ℝ) = ∑' n : ℕ, (Ioc 0 (w n)).indicator (fun _ => (1 : ℝ)) x := by
  classical
  let hf := finite_gapCount hw hx
  let s := hf.toFinset
  have hs (n : ℕ) : n ∈ s ↔ x ≤ w n := hf.mem_toFinset
  have hn (n : ℕ) (hn : n ∉ s) : (Ioc 0 (w n)).indicator (fun _ => (1 : ℝ)) x = 0 := by
    apply indicator_of_notMem
    intro h
    exact hn ((hs n).2 h.2)
  rw [tsum_eq_sum hn]
  have he : ∑ n ∈ s, (Ioc 0 (w n)).indicator (fun _ => (1 : ℝ)) x = (s.card : ℝ) := by
    calc
      _ = ∑ _n ∈ s, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact Set.indicator_of_mem (s := Ioc 0 (w n)) ⟨hx, (hs n).1 hn⟩ _
      _ = _ := by simp
  rw [he]
  exact_mod_cast Set.ncard_eq_toFinset_card _ hf

private theorem integral_gap_indicator {w t : ℝ} (hw : 0 ≤ w) (ht : 0 ≤ t) :
    (∫ x in Ioc (0 : ℝ) t, (Ioc 0 w).indicator (fun _ => (1 : ℝ)) x) = min w t := by
  rw [setIntegral_indicator measurableSet_Ioc, Set.Ioc_inter_Ioc, max_self]
  simp only [setIntegral_const, smul_eq_mul, mul_one, Real.volume_real_Ioc, sub_zero,
    min_comm t w, max_eq_left (le_min hw ht)]

/-- The total length retained by truncating each gap at `t` is the integral
of the number of gaps exceeding the running threshold. -/
theorem truncated_sum_eq_integral_gapCount {w : ℕ → ℝ}
    (hw : Summable w) (hn : ∀ n, 0 ≤ w n) {t : ℝ} (ht : 0 < t) :
    (∑' n, min (w n) t) = ∫ x in Ioc (0 : ℝ) t, (gapCount w x : ℝ) := by
  classical
  let f (n : ℕ) (x : ℝ) := (Ioc 0 (w n)).indicator (fun _ => (1 : ℝ)) x
  have hf (n : ℕ) : Integrable (f n) (volume.restrict (Ioc 0 t)) :=
    (integrable_const 1).indicator measurableSet_Ioc
  have hpos (n : ℕ) (x : ℝ) : 0 ≤ f n x := by
    simp only [f, Set.indicator_apply]
    split_ifs <;> positivity
  have hs : Summable (fun n => min (w n) t) :=
    Summable.of_nonneg_of_le (fun n => le_min (hn n) ht.le) (fun _ => min_le_left _ _) hw
  have hi (n : ℕ) : (∫ x in Ioc (0 : ℝ) t, f n x) = min (w n) t :=
    integral_gap_indicator (hn n) ht.le
  have hnorm : Summable (fun n => ∫ x in Ioc (0 : ℝ) t, ‖f n x‖) := by
    simpa only [Real.norm_of_nonneg (hpos _ _), hi] using hs
  have h := integral_tsum_of_summable_integral_norm hf hnorm
  simp only [hi] at h
  rw [h]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact (gapCount_eq_tsum_indicator hw hx.1).symm

private theorem gapCount_integrable {w : ℕ → ℝ}
    (hw : Summable w) (hn : ∀ n, 0 ≤ w n) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x => (gapCount w x : ℝ)) (Ioc 0 t) := by
  by_cases hz : ∀ n, w n = 0
  · apply (integrable_const (0 : ℝ) : Integrable _ (volume.restrict (Ioc 0 t))).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have he : {n | x ≤ w n} = ∅ := by
      ext n
      simp [hz, not_le_of_gt hx.1]
    simp [gapCount, he]
  push Not at hz
  obtain ⟨n, hnz⟩ := hz
  have hp : 0 < w n := lt_of_le_of_ne (hn n) (Ne.symm hnz)
  apply Integrable.of_integral_ne_zero
  rw [← truncated_sum_eq_integral_gapCount hw hn ht]
  have hs : Summable (fun n => min (w n) t) :=
    Summable.of_nonneg_of_le (fun n => le_min (hn n) ht.le) (fun _ => min_le_left _ _) hw
  exact ne_of_gt ((lt_min hp ht).trans_le (hs.le_tsum n (fun n _ => le_min (hn n) ht.le)))

private theorem integral_two_thirds (t : ℝ) :
    (∫ x in (0 : ℝ)..t, x^(-2/3 : ℝ)) = 3*t^(1/3 : ℝ) := by
  rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -2/3))]
  norm_num
  ring

/-- A two-thirds gap-counting asymptotic integrates to an exact cube-root
asymptotic for nonnegative summable gaps, including an empty localization. -/
theorem truncated_sum_asymptotic_of_gapCount_nonneg {w : ℕ → ℝ} {A : ℝ}
    (hw : Summable w) (hn : ∀ n, 0 ≤ w n)
    (hA : Tendsto (fun x : ℝ => x^(2/3 : ℝ)*(gapCount w x : ℝ))
      (𝓝[>] 0) (𝓝 A)) :
    Tendsto (fun t : ℝ => (∑' n, min (w n) t)/t^(1/3 : ℝ))
      (𝓝[>] 0) (𝓝 (3*A)) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  have he := Metric.tendsto_nhds.1 hA (ε/6) (by positivity)
  obtain ⟨δ, hδ, hh⟩ := (nhdsGT_basis_Ioc (0 : ℝ)).mem_iff.1 he
  filter_upwards [(nhdsGT_basis_Ioc (0 : ℝ)).mem_of_mem hδ] with t ht
  have hb (x : ℝ) (hx : x ∈ Ioc 0 t) :
      (A-ε/6)*x^(-2/3 : ℝ) ≤ (gapCount w x : ℝ) ∧
      (gapCount w x : ℝ) ≤ (A+ε/6)*x^(-2/3 : ℝ) := by
    have h := hh ⟨hx.1, hx.2.trans ht.2⟩
    change dist (x^(2/3 : ℝ)*(gapCount w x : ℝ)) A < ε/6 at h
    rw [Real.dist_eq, abs_lt] at h
    have hp : 0 < x^(2/3 : ℝ) := Real.rpow_pos_of_pos hx.1 _
    rw [show (-2/3 : ℝ) = -(2/3) by ring, Real.rpow_neg hx.1.le]
    constructor
    · rw [← div_eq_mul_inv, div_le_iff₀ hp]
      nlinarith
    · rw [← div_eq_mul_inv, le_div_iff₀ hp]
      nlinarith
  have hi := gapCount_integrable hw hn ht.1
  have hpow : IntervalIntegrable (fun x : ℝ => x^(-2/3 : ℝ)) volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hL := setIntegral_mono_on (hpow.const_mul (A-ε/6)).1 hi measurableSet_Ioc
    (fun x hx => (hb x hx).1)
  have hU := setIntegral_mono_on hi (hpow.const_mul (A+ε/6)).1 measurableSet_Ioc
    (fun x hx => (hb x hx).2)
  have hpi : (∫ x in Ioc (0 : ℝ) t, x^(-2/3 : ℝ)) = 3*t^(1/3 : ℝ) := by
    rw [← intervalIntegral.integral_of_le ht.1.le, integral_two_thirds]
  rw [integral_const_mul, hpi, ← truncated_sum_eq_integral_gapCount hw hn ht.1] at hL hU
  have htp : 0 < t^(1/3 : ℝ) := Real.rpow_pos_of_pos ht.1 _
  have hL' : 3*(A-ε/6) ≤ (∑' n, min (w n) t)/t^(1/3 : ℝ) := by
    rw [le_div_iff₀ htp]
    nlinarith [hL]
  have hU' : (∑' n, min (w n) t)/t^(1/3 : ℝ) ≤ 3*(A+ε/6) := by
    rw [div_le_iff₀ htp]
    nlinarith [hU]
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- A two-thirds gap-counting asymptotic integrates to an exact cube-root
asymptotic for the truncated total length. This interface retains the
positive first-gap premise used by the original content theorem. -/
theorem truncated_sum_asymptotic_of_gapCount {w : ℕ → ℝ} {A : ℝ}
    (hw : Summable w) (hn : ∀ n, 0 ≤ w n) (_hp : 0 < w 0)
    (hA : Tendsto (fun x : ℝ => x^(2/3 : ℝ)*(gapCount w x : ℝ))
      (𝓝[>] 0) (𝓝 A)) :
    Tendsto (fun t : ℝ => (∑' n, min (w n) t)/t^(1/3 : ℝ))
      (𝓝[>] 0) (𝓝 (3*A)) :=
  truncated_sum_asymptotic_of_gapCount_nonneg hw hn hA

end Problems.Juggler.BeattyPhase

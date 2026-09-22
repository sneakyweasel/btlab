import BTCalculus.WeylCancellation
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-! # Fourier cancellation and recurrence on a finite-dimensional torus

Uniform density of the Fourier monomials turns cancellation into convergence
of continuous-function averages. A nonnegative continuous function supported
inside a nonempty open set then forces arbitrarily late visits.
-/

noncomputable section

namespace BTCalculus.FourierBoxRecurrence

open Finset Filter Set
open MeasureTheory hiding average
open scoped Topology ComplexConjugate
open BTCalculus.WeylDifferencing UnitAddTorus

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {d : Type*} [Fintype d]

/-- The Haar integral of a Fourier monomial is its zero-mode indicator. -/
theorem integral_mFourier (k : d → ℤ) :
    (∫ x : UnitAddTorus d, mFourier k x) = if k = 0 then 1 else 0 := by
  classical
  have h := (orthonormal_iff_ite.mp (orthonormal_mFourier (d := d))) 0 k
  simpa [ContinuousMap.inner_toLp, mFourier_zero, RCLike.inner_apply, eq_comm] using h

omit [Fintype d] in
/-- Averaging samples is a contraction for the uniform norm, even at N=0. -/
theorem norm_average_samples_le (x : ℕ → UnitAddTorus d)
    (f : C(UnitAddTorus d, ℂ)) (N : ℕ) :
    ‖average (fun n => f (x n)) N‖ ≤ ‖f‖ := by
  rw [norm_average]
  calc ‖∑ n ∈ range N, f (x n)‖ / (N : ℝ)
      ≤ (∑ n ∈ range N, ‖f‖) / (N : ℝ) :=
        div_le_div_of_nonneg_right ((norm_sum_le _ _).trans
          (sum_le_sum (fun n _ => f.norm_coe_le_norm (x n)))) (by positivity)
    _ ≤ ‖f‖ := by
      simp only [sum_const, card_range, nsmul_eq_mul]
      by_cases hN : N = 0
      · simp [hN]
      · have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN
        exact le_of_eq (by field_simp)

/-- Haar integration is also a contraction for the uniform norm. -/
theorem norm_integral_le (f : C(UnitAddTorus d, ℂ)) :
    ‖∫ x : UnitAddTorus d, f x‖ ≤ ‖f‖ := by
  simpa using norm_integral_le_of_norm_le_const
    (μ := (volume : Measure (UnitAddTorus d))) (Eventually.of_forall f.norm_coe_le_norm)

theorem integrable_continuous {𝕜 : Type*} [RCLike 𝕜] (f : C(UnitAddTorus d, 𝕜)) :
    Integrable f (volume : Measure (UnitAddTorus d)) :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- Fourier cancellation gives the correct limit for every monomial. -/
theorem tendsto_mFourier_average (x : ℕ → UnitAddTorus d)
    (hx : ∀ k : d → ℤ, k ≠ 0 →
      Tendsto (average (fun n => mFourier k (x n))) atTop (𝓝 0)) (k : d → ℤ) :
    Tendsto (average (fun n => mFourier k (x n))) atTop
      (𝓝 (∫ y : UnitAddTorus d, mFourier k y)) := by
  classical
  rw [integral_mFourier]
  by_cases hk : k = 0
  · subst k
    simp only [mFourier_zero, ContinuousMap.one_apply]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hn : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    simp [average, hn]
  · simpa only [if_neg hk] using hx k hk

/-- Finite linear combinations inherit the Fourier average limit. -/
theorem tendsto_span_average (x : ℕ → UnitAddTorus d)
    (hx : ∀ k : d → ℤ, k ≠ 0 →
      Tendsto (average (fun n => mFourier k (x n))) atTop (𝓝 0))
    {f : C(UnitAddTorus d, ℂ)} (hf : f ∈ Submodule.span ℂ (Set.range mFourier)) :
    Tendsto (average (fun n => f (x n))) atTop (𝓝 (∫ y : UnitAddTorus d, f y)) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨k, rfl⟩ := hf
    exact tendsto_mFourier_average x hx k
  | zero =>
    change Tendsto (fun N => average (fun n => (0 : C(UnitAddTorus d, ℂ)) (x n)) N) _ _
    simp [average]
  | add f g _ _ hf hg =>
    have hlim := hf.add hg
    change Tendsto (fun N => average (fun n => (f + g) (x n)) N) _ _
    simpa only [ContinuousMap.add_apply, average, sum_add_distrib, add_div,
      integral_add (integrable_continuous f) (integrable_continuous g)] using hlim
  | smul c f _ hf =>
    have hlim := hf.const_mul c
    change Tendsto (fun N => average (fun n => (c • f) (x n)) N) _ _
    simpa only [ContinuousMap.smul_apply, smul_eq_mul, average, ← mul_sum,
      mul_div_assoc, integral_const_mul] using hlim

/-- The qualitative Weyl criterion for all continuous functions on the torus. -/
theorem tendsto_continuous_average (x : ℕ → UnitAddTorus d)
    (hx : ∀ k : d → ℤ, k ≠ 0 →
      Tendsto (average (fun n => mFourier k (x n))) atTop (𝓝 0))
    (f : C(UnitAddTorus d, ℂ)) :
    Tendsto (average (fun n => f (x n))) atTop (𝓝 (∫ y : UnitAddTorus d, f y)) := by
  have hclosure : f ∈ closure (↑(Submodule.span ℂ (Set.range (mFourier (d := d)))) :
      Set C(UnitAddTorus d, ℂ)) := by
    rw [← Submodule.topologicalClosure_coe, span_mFourier_closure_eq_top]
    trivial
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨g, hg, hgf⟩ := Metric.mem_closure_iff.1 hclosure (ε / 3) (by positivity)
  have hlim := tendsto_span_average x hx hg
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hlim (ε / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have he : average (fun i => f (x i)) n - (∫ y : UnitAddTorus d, f y) =
      average (fun i => (f - g) (x i)) n +
        (average (fun i => g (x i)) n - (∫ y : UnitAddTorus d, g y)) +
          (∫ y : UnitAddTorus d, (g - f) y) := by
    simp only [average, ContinuousMap.sub_apply, sum_sub_distrib,
      integral_sub (integrable_continuous g) (integrable_continuous f)]
    ring
  rw [dist_eq_norm, he]
  have hfg : ‖f - g‖ < ε / 3 := by simpa only [dist_eq_norm] using hgf
  have hfg' : ‖g - f‖ < ε / 3 := by simpa only [norm_sub_rev] using hfg
  have hb := norm_add_le (average (fun i => (f - g) (x i)) n +
    (average (fun i => g (x i)) n - ∫ y : UnitAddTorus d, g y))
    (∫ y : UnitAddTorus d, (g - f) y)
  have hb' := norm_add_le (average (fun i => (f - g) (x i)) n)
    (average (fun i => g (x i)) n - ∫ y : UnitAddTorus d, g y)
  have hgN := hN n hn
  rw [dist_eq_norm] at hgN
  have hfN := norm_average_samples_le x (f - g) n
  have hi := norm_integral_le (g - f)
  linarith

/-- An eventually zero sequence has averages tending to zero. -/
theorem tendsto_average_zero_of_eventually_zero {z : ℕ → ℂ}
    (hz : ∀ᶠ n in atTop, z n = 0) : Tendsto (average z) atTop (𝓝 0) := by
  have hlim : Tendsto z atTop (𝓝 0) :=
    tendsto_const_nhds.congr' (hz.mono (fun _ h => h.symm))
  change Tendsto (fun N => average z N) _ _
  simpa only [average, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast,
    div_eq_mul_inv, mul_comm] using hlim.cesaro_smul

/-- Every nonempty open set is visited after every prescribed sample index. -/
theorem exists_ge_mem_open_of_fourier (x : ℕ → UnitAddTorus d)
    (hx : ∀ k : d → ℤ, k ≠ 0 →
      Tendsto (average (fun n => mFourier k (x n))) atTop (𝓝 0))
    {U : Set (UnitAddTorus d)} (hU : IsOpen U) (hne : U.Nonempty) (T : ℕ) :
    ∃ n : ℕ, T ≤ n ∧ x n ∈ U := by
  classical
  obtain ⟨y, hy⟩ := hne
  obtain ⟨g, hg1, _, hgs, hgb⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen (isCompact_singleton (x := y))
      hU (singleton_subset_iff.mpr hy)
  have hgy : g y = 1 := by simpa using hg1 (mem_singleton y)
  have hpos : 0 < ∫ z : UnitAddTorus d, g z :=
    integral_pos_of_integrable_nonneg_nonzero g.continuous (integrable_continuous g)
      (fun z => (hgb z).1) (by rw [hgy]; norm_num)
  let f : C(UnitAddTorus d, ℂ) := ⟨fun z => (g z : ℂ), by fun_prop⟩
  have hlim := tendsto_continuous_average x hx f
  by_contra hnone
  push Not at hnone
  have hzero : ∀ᶠ n in atTop, f (x n) = 0 := by
    filter_upwards [eventually_ge_atTop T] with n hn
    have hg0 : g (x n) = 0 := by
      by_contra hg0
      exact hnone n hn (hgs (subset_tsupport g (show x n ∈ Function.support g from hg0)))
    simp only [f, ContinuousMap.coe_mk, hg0, Complex.ofReal_zero]
  have he := tendsto_nhds_unique hlim (tendsto_average_zero_of_eventually_zero hzero)
  change (∫ z : UnitAddTorus d, (g z : ℂ)) = 0 at he
  have hi := integral_complex_ofReal (μ := (volume : Measure (UnitAddTorus d)))
    (f := (g : UnitAddTorus d → ℝ))
  rw [hi, Complex.ofReal_eq_zero] at he
  exact (ne_of_gt hpos) he

/-- The open image of an interval strictly inside one unit period. -/
def circleInterval (a b : ℝ) : Set UnitAddCircle :=
  (fun t : ℝ => (t : UnitAddCircle)) '' Set.Ioo a b

theorem isOpen_circleInterval (a b : ℝ) : IsOpen (circleInterval a b) :=
  QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo

/-- Membership in a unit-period interval is precisely a fractional-part condition. -/
theorem mem_circleInterval_iff {a b t : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    (t : UnitAddCircle) ∈ circleInterval a b ↔ a < Int.fract t ∧ Int.fract t < b := by
  constructor
  · rintro ⟨u, hu, he⟩
    have hu01 : u ∈ Set.Ico (0 : ℝ) (0 + 1) := ⟨ha.trans hu.1.le, by linarith [hu.2]⟩
    have ht01 : Int.fract t ∈ Set.Ico (0 : ℝ) (0 + 1) :=
      ⟨Int.fract_nonneg t, by simpa using Int.fract_lt_one t⟩
    have he' : (u : UnitAddCircle) = ((Int.fract t : ℝ) : UnitAddCircle) := by
      simpa only [AddCircle.coe_fract] using he
    have hut := (AddCircle.coe_eq_coe_iff_of_mem_Ico hu01 ht01).1 he'
    simpa only [hut, Set.mem_Ioo] using hu
  · intro ht
    exact ⟨Int.fract t, ht, AddCircle.coe_fract t⟩

/-- Simultaneous fractional-part boxes follow from joint Fourier cancellation. -/
theorem exists_ge_fract_box (v : ℕ → d → ℝ)
    (hv : ∀ k : d → ℤ, k ≠ 0 →
      Tendsto (average (fun n => mFourier k (fun i => (v n i : UnitAddCircle))))
        atTop (𝓝 0))
    (a b : d → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, b i ≤ 1)
    (hab : ∀ i, a i < b i) (T : ℕ) :
    ∃ n : ℕ, T ≤ n ∧ ∀ i, a i < Int.fract (v n i) ∧ Int.fract (v n i) < b i := by
  let U : Set (UnitAddTorus d) := {z | ∀ i, z i ∈ circleInterval (a i) (b i)}
  have hU : IsOpen U := by
    convert isOpen_iInter_of_finite (fun i =>
      (isOpen_circleInterval (a i) (b i)).preimage (continuous_apply i)) using 1
    ext z
    simp [U]
  have hne : U.Nonempty := by
    refine ⟨fun i => (((a i + b i) / 2 : ℝ) : UnitAddCircle), fun i => ?_⟩
    exact ⟨(a i + b i) / 2, ⟨by linarith [hab i], by linarith [hab i]⟩, rfl⟩
  obtain ⟨n, hn, hmem⟩ := exists_ge_mem_open_of_fourier
    (fun n i => (v n i : UnitAddCircle)) hv hU hne T
  exact ⟨n, hn, fun i => (mem_circleInterval_iff (ha i) (hb i)).1 (hmem i)⟩

/-- The torus monomial agrees with the real dot-product phase. -/
theorem mFourier_real_eq_phase (k : d → ℤ) (v : d → ℝ) :
    mFourier k (fun i => (v i : UnitAddCircle)) = phase (∑ i, (k i : ℝ) * v i) := by
  simp only [mFourier, ContinuousMap.coe_mk, fourier_coe_apply]
  unfold phase
  push_cast
  simp only [div_one]
  rw [← Complex.exp_sum]
  congr 1
  rw [mul_sum, sum_mul]
  apply sum_congr rfl
  intro i _
  ring

/-- Fractional-part recurrence with the usual real exponential-sum hypothesis. -/
theorem exists_ge_fract_box_of_phase (v : ℕ → d → ℝ)
    (hv : ∀ k : d → ℤ, k ≠ 0 →
      Tendsto (average (fun n => phase (∑ i, (k i : ℝ) * v n i))) atTop (𝓝 0))
    (a b : d → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, b i ≤ 1)
    (hab : ∀ i, a i < b i) (T : ℕ) :
    ∃ n : ℕ, T ≤ n ∧ ∀ i, a i < Int.fract (v n i) ∧ Int.fract (v n i) < b i := by
  apply exists_ge_fract_box v _ a b ha hb hab T
  intro k hk
  simpa only [mFourier_real_eq_phase] using hv k hk

end BTCalculus.FourierBoxRecurrence

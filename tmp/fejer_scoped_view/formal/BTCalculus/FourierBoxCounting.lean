import BTCalculus.FourierBoxRecurrence
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Group.AddCircle

/-! # Counting fixed boxes from Fourier cancellation

Empirical measures converge weakly to Haar measure. The portmanteau theorem
then counts sets with null boundary, including half-open fractional-part boxes.
-/

noncomputable section

namespace BTCalculus.FourierBoxCounting

open Finset Filter Set
open MeasureTheory hiding average
open scoped Topology ENNReal
open BTCalculus.WeylDifferencing BTCalculus.FourierBoxRecurrence UnitAddTorus

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance : NullSingletonClass (volume : Measure UnitAddCircle) := by
  constructor
  intro x
  have h := AddCircle.volume_closedBall (T := 1) (x := x) 0
  change AddCircle.haarAddCircle {x} = 0
  simpa only [Metric.closedBall_zero, AddCircle.volume_eq_smul_haarAddCircle,
    ENNReal.ofReal_one, one_smul, mul_zero, min_eq_right zero_le_one,
    ENNReal.ofReal_zero] using h

variable {d : Type*} [Fintype d]

/-- The empirical distribution of the first N+1 samples. -/
def empirical (x : ℕ → UnitAddTorus d) (N : ℕ) : ProbabilityMeasure (UnitAddTorus d) :=
  ⟨((N + 1 : ℕ) : ℝ≥0∞)⁻¹ • ∑ n ∈ range (N + 1), Measure.dirac (x n), by
    constructor
    simp only [Measure.smul_apply, Measure.finsetSum_apply, Measure.dirac_apply_of_mem,
      Set.mem_univ, smul_eq_mul, sum_const, card_range, nsmul_eq_mul, mul_one]
    exact ENNReal.inv_mul_cancel (by simp) (by simp)⟩

/-- Integrating against the empirical distribution is ordinary averaging. -/
theorem integral_empirical (x : ℕ → UnitAddTorus d) (N : ℕ)
    (f : C(UnitAddTorus d, ℂ)) :
    (∫ z, f z ∂(empirical x N : Measure (UnitAddTorus d))) =
      average (fun n => f (x n)) (N + 1) := by
  change (∫ z, f z ∂(_ • _)) = _
  rw [integral_smul_measure,
    integral_finsetSum_measure (fun n _ => integrable_dirac (by simp))]
  simp only [integral_dirac, average, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast]
  ring

/-- Fourier cancellation implies weak convergence of empirical measures. -/
theorem tendsto_empirical (x : ℕ → UnitAddTorus d)
    (hx : ∀ k : d → ℤ, k ≠ 0 →
      Tendsto (average (fun n => mFourier k (x n))) atTop (𝓝 0)) :
    Tendsto (empirical x) atTop
      (𝓝 (⟨volume, inferInstance⟩ : ProbabilityMeasure (UnitAddTorus d))) := by
  apply (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).2
  intro f
  let g : C(UnitAddTorus d, ℂ) := ⟨f, f.continuous⟩
  have h := (tendsto_continuous_average x hx g).comp (tendsto_add_atTop_nat 1)
  change Tendsto (fun i => ∫ z, g z ∂(empirical x i : Measure (UnitAddTorus d))) _
    (𝓝 (∫ z, g z))
  simpa only [integral_empirical, Function.comp_def] using h

/-- Number of successful indices strictly below N. -/
def count (P : ℕ → Prop) (N : ℕ) : ℕ := by
  classical
  exact ((range N).filter P).card

omit [Fintype d] in
theorem empirical_apply (x : ℕ → UnitAddTorus d) (N : ℕ)
    {S : Set (UnitAddTorus d)} (hS : MeasurableSet S) :
    (empirical x N : Measure (UnitAddTorus d)) S =
      (count (fun n => x n ∈ S) (N + 1) : ℝ≥0∞) / (N + 1 : ℕ) := by
  classical
  simp only [empirical, ProbabilityMeasure.coe_mk, Measure.smul_apply,
    Measure.finsetSum_apply, smul_eq_mul, Measure.dirac_apply' _ hS]
  simp only [Set.indicator_apply, Pi.one_apply, ← Nat.cast_one (R := ℝ≥0∞),
    ← Nat.cast_zero (R := ℝ≥0∞), ← Nat.cast_ite, ← Nat.cast_sum]
  simp [count, Finset.sum_boole, div_eq_mul_inv, mul_comm]

/-- A null boundary upgrades the continuous-function criterion to exact frequency. -/
theorem tendsto_count_of_null_frontier (x : ℕ → UnitAddTorus d)
    (hx : ∀ k : d → ℤ, k ≠ 0 →
      Tendsto (average (fun n => mFourier k (x n))) atTop (𝓝 0))
    {S : Set (UnitAddTorus d)} (hS : MeasurableSet S)
    (hboundary : volume (frontier S) = 0) :
    Tendsto (fun N => (count (fun n => x n ∈ S) N : ℝ) / N) atTop
      (𝓝 (volume.real S)) := by
  have h := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    (tendsto_empirical x hx) hboundary
  have hr := (ENNReal.tendsto_toReal (measure_ne_top volume S)).comp h
  simp only [Function.comp_def, empirical_apply x _ hS, ENNReal.toReal_div,
    ENNReal.toReal_natCast] at hr
  exact (tendsto_add_atTop_iff_nat 1).mp hr

/-- A half-open arc, retaining the left endpoint used by floor residues. -/
def circleArc (a b : ℝ) : Set UnitAddCircle := insert (a : UnitAddCircle) (circleInterval a b)

theorem measurableSet_circleArc (a b : ℝ) : MeasurableSet (circleArc a b) :=
  (isOpen_circleInterval a b).measurableSet.insert _

theorem mem_circleArc_iff {a b t : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a < b) :
    (t : UnitAddCircle) ∈ circleArc a b ↔ a ≤ Int.fract t ∧ Int.fract t < b := by
  have ha01 : a ∈ Ico (0 : ℝ) (0 + 1) := ⟨ha, by linarith⟩
  have ht01 : Int.fract t ∈ Ico (0 : ℝ) (0 + 1) :=
    ⟨Int.fract_nonneg t, by simpa using Int.fract_lt_one t⟩
  constructor
  · rintro (he | he)
    · have he' : ((Int.fract t : ℝ) : UnitAddCircle) = (a : UnitAddCircle) := by
        simpa only [AddCircle.coe_fract] using he
      have ht := (AddCircle.coe_eq_coe_iff_of_mem_Ico ht01 ha01).1 he'
      simp [ht, hab]
    · exact ⟨((mem_circleInterval_iff ha hb).1 he).1.le,
        ((mem_circleInterval_iff ha hb).1 he).2⟩
  · rintro ⟨hat, htb⟩
    rcases hat.eq_or_lt with he | he
    · left
      rw [he, AddCircle.coe_fract]
    · right
      exact (mem_circleInterval_iff ha hb).2 ⟨he, htb⟩

theorem volume_circleInterval {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (_hab : a < b) :
    volume (circleInterval a b) = ENNReal.ofReal (b - a) := by
  have hpre : ((fun t : ℝ => (t : UnitAddCircle)) ⁻¹' circleInterval a b) ∩
      Ioc a (a + 1) = Ioo a b := by
    ext t
    constructor
    · rintro ⟨⟨u, hu, he⟩, ht⟩
      have hu' : u ∈ Ioc a (a + 1) := ⟨hu.1, by linarith [hu.2]⟩
      have hut := (AddCircle.coe_eq_coe_iff_of_mem_Ioc hu' ht).1 he
      simpa [← hut] using hu
    · intro ht
      exact ⟨⟨t, ht, rfl⟩, ht.1, by linarith [ht.2]⟩
  have h := AddCircle.add_projection_respects_measure (1 : ℝ) a
    (isOpen_circleInterval a b).measurableSet
  change AddCircle.haarAddCircle (circleInterval a b) = _
  simpa only [AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul,
    hpre, Real.volume_Ioo] using h

theorem volume_circleArc {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a < b) :
    volume (circleArc a b) = ENNReal.ofReal (b - a) := by
  rw [circleArc, measure_congr (insert_ae_eq_self _ _)]
  exact volume_circleInterval ha hb hab

theorem frontier_circleArc_subset {a b : ℝ} (hab : a < b) :
    frontier (circleArc a b) ⊆ {(a : UnitAddCircle), (b : UnitAddCircle)} := by
  have hc : IsClosed ((fun t : ℝ => (t : UnitAddCircle)) '' Icc a b) :=
    (isCompact_Icc.image (QuotientAddGroup.continuous_mk)).isClosed
  have hs : circleArc a b ⊆ (fun t : ℝ => (t : UnitAddCircle)) '' Icc a b := by
    rintro z (rfl | ⟨t, ht, rfl⟩)
    · exact ⟨a, ⟨le_rfl, hab.le⟩, rfl⟩
    · exact ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩
  intro z hz
  obtain ⟨t, ht, rfl⟩ := (closure_minimal hs hc) hz.1
  by_cases hta : t = a
  · simp [hta]
  by_cases htb : t = b
  · simp [htb]
  exfalso
  apply hz.2
  apply interior_mono (show circleInterval a b ⊆ circleArc a b from subset_insert _ _)
  rw [(isOpen_circleInterval a b).interior_eq]
  exact ⟨t, ⟨lt_of_le_of_ne ht.1 (Ne.symm hta), lt_of_le_of_ne ht.2 htb⟩, rfl⟩

theorem null_frontier_circleArc {a b : ℝ} (hab : a < b) :
    volume (frontier (circleArc a b)) = 0 :=
  measure_mono_null (frontier_circleArc_subset hab) ((Set.finite_singleton _).insert _ |>.measure_zero volume)

/-- The product of half-open arcs has null Haar boundary. -/
theorem null_frontier_box (a b : d → ℝ) (hab : ∀ i, a i < b i) :
    volume (frontier (univ.pi (fun i => circleArc (a i) (b i)))) = 0 := by
  classical
  have hcoord (i : d) : volume (frontier ((fun z : UnitAddTorus d => z i) ⁻¹'
      circleArc (a i) (b i))) = 0 :=
    measure_mono_null ((continuous_apply i).frontier_preimage_subset _)
      (Measure.pi_eval_preimage_null (fun _ : d => (volume : Measure UnitAddCircle))
        (null_frontier_circleArc (hab i)))
  have hfin (s : Finset d) : volume (frontier (⋂ i ∈ s,
      (fun z : UnitAddTorus d => z i) ⁻¹' circleArc (a i) (b i))) = 0 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      simp only [Finset.set_biInter_insert]
      exact null_frontier_inter (hcoord i) ih
  have he : univ.pi (fun i => circleArc (a i) (b i)) =
      ⋂ i ∈ (Finset.univ : Finset d),
        (fun z : UnitAddTorus d => z i) ⁻¹' circleArc (a i) (b i) := by
    ext z
    simp
  rw [he]
  exact hfin Finset.univ

/-- The frequency of any fixed half-open fractional-part box is its volume. -/
theorem tendsto_fract_box_count (v : ℕ → d → ℝ)
    (hv : ∀ k : d → ℤ, k ≠ 0 →
      Tendsto (average (fun n => phase (∑ i, (k i : ℝ) * v n i))) atTop (𝓝 0))
    (a b : d → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, b i ≤ 1)
    (hab : ∀ i, a i < b i) :
    Tendsto (fun N => (count (fun n => ∀ i,
      a i ≤ Int.fract (v n i) ∧ Int.fract (v n i) < b i) N : ℝ) / N)
      atTop (𝓝 (∏ i, (b i - a i))) := by
  let S : Set (UnitAddTorus d) := univ.pi (fun i => circleArc (a i) (b i))
  have hvol : volume.real S = ∏ i, (b i - a i) := by
    rw [Measure.real, show S = univ.pi (fun i => circleArc (a i) (b i)) from rfl,
      volume_pi_pi, ENNReal.toReal_prod]
    apply prod_congr rfl
    intro i _
    rw [volume_circleArc (ha i) (hb i) (hab i), ENNReal.toReal_ofReal (sub_nonneg.mpr (hab i).le)]
  have hfourier (k : d → ℤ) (hk : k ≠ 0) :
      Tendsto (average (fun n => mFourier k (fun i => (v n i : UnitAddCircle)))) atTop (𝓝 0) := by
    simpa only [mFourier_real_eq_phase] using hv k hk
  have h := tendsto_count_of_null_frontier (fun n i => (v n i : UnitAddCircle)) hfourier
    (MeasurableSet.univ_pi (fun i => measurableSet_circleArc (a i) (b i)))
    (null_frontier_box a b hab)
  rw [hvol] at h
  have he : (fun n => (fun i => (v n i : UnitAddCircle)) ∈ S) =
      (fun n => ∀ i, a i ≤ Int.fract (v n i) ∧ Int.fract (v n i) < b i) := by
    funext n
    simp only [S, Set.mem_univ_pi, mem_circleArc_iff (ha _) (hb _) (hab _)]
  dsimp only [S] at he
  simpa only [he] using h

end BTCalculus.FourierBoxCounting

import BTCalculus.FourierBoxCounting
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.Topology.Order.Monotone
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Weak convergence tools for discontinuous phase profiles

Almost-everywhere continuity suffices to push weak convergence through a
measurable map. Empirical laws below use the first `N+1` samples so that even
their zeroth term is a probability measure.
-/

namespace Problems.Juggler.BeattyPhase

open Filter Topology Set MeasureTheory Finset
open scoped ENNReal BoundedContinuousFunction

/-- Weak convergence passes through a measurable map that is continuous
almost everywhere for the limiting measure. No continuity is required at
the sample points themselves. -/
theorem tendsto_probability_map_of_ae_continuous
    {X Y : Type*} [MeasurableSpace X] [PseudoMetricSpace X] [BorelSpace X]
    [MeasurableSpace Y] [PseudoMetricSpace Y] [BorelSpace Y]
    {mu : ProbabilityMeasure X} {mus : ℕ → ProbabilityMeasure X}
    (hlim : Tendsto mus atTop (𝓝 mu)) {f : X → Y} (hf : Measurable f)
    (hc : ∀ᵐ x ∂(mu : Measure X), ContinuousAt f x) :
    Tendsto (fun n => (mus n).map hf.aemeasurable) atTop (𝓝 (mu.map hf.aemeasurable)) := by
  apply tendsto_of_forall_isOpen_le_liminf'
  intro U hU
  rw [ProbabilityMeasure.map_apply' _ _ hU.measurableSet]
  have he : (mu : Measure X) (f ⁻¹' U) = (mu : Measure X) (interior (f ⁻¹' U)) := by
    apply measure_congr
    filter_upwards [hc] with x hx
    apply propext
    constructor
    · intro hxU
      exact mem_interior_iff_mem_nhds.2 (hx (hU.mem_nhds hxU))
    · exact fun hxU => (interior_subset (s := f ⁻¹' U)) hxU
  rw [he]
  apply (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim isOpen_interior).trans
  apply liminf_le_liminf (hu := by isBoundedDefault) (hv := by isBoundedDefault)
  exact Eventually.of_forall fun n => by
    rw [ProbabilityMeasure.map_apply' _ _ hU.measurableSet]
    exact measure_mono interior_subset

/-- Probability law of the first `N+1` values of any measurable-space-valued
sequence. This convention avoids a separate zero-length exceptional measure. -/
noncomputable def empiricalLaw {X : Type*} [MeasurableSpace X]
    (u : ℕ → X) (N : ℕ) : ProbabilityMeasure X :=
  ⟨((N+1 : ℕ) : ℝ≥0∞)⁻¹ • ∑ n ∈ Finset.range (N+1), Measure.dirac (u n), by
    constructor
    simp only [Measure.smul_apply, Measure.finsetSum_apply, Measure.dirac_apply_of_mem,
      Set.mem_univ, smul_eq_mul, sum_const, card_range, nsmul_eq_mul, mul_one]
    exact ENNReal.inv_mul_cancel (by positivity) (by finiteness)⟩

/-- Mapping an empirical law is exactly the empirical law of mapped samples. -/
theorem empiricalLaw_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (u : ℕ → X) {f : X → Y} (hf : Measurable f) (N : ℕ) :
    (empiricalLaw u N).map hf.aemeasurable = empiricalLaw (fun n => f (u n)) N := by
  apply Subtype.ext
  simp only [ProbabilityMeasure.map, empiricalLaw, ProbabilityMeasure.coe_mk,
    Measure.map_smul, Measure.map_finset_sum hf.aemeasurable, Measure.map_dirac' hf]

/-- The mass assigned to a measurable set is its finite sampling frequency. -/
theorem empiricalLaw_apply {X : Type*} [MeasurableSpace X]
    (u : ℕ → X) (N : ℕ) {S : Set X} (hS : MeasurableSet S) :
    (empiricalLaw u N : Measure X) S =
      (BTCalculus.FourierBoxCounting.count (fun n => u n ∈ S) (N+1) : ℝ≥0∞) /
        (N+1 : ℕ) := by
  classical
  simp only [empiricalLaw, ProbabilityMeasure.coe_mk, Measure.smul_apply,
    Measure.finsetSum_apply, smul_eq_mul, Measure.dirac_apply' _ hS]
  simp only [Set.indicator_apply, Pi.one_apply, ← Nat.cast_one (R := ℝ≥0∞),
    ← Nat.cast_zero (R := ℝ≥0∞), ← Nat.cast_ite, ← Nat.cast_sum]
  simp [BTCalculus.FourierBoxCounting.count, Finset.sum_boole, div_eq_mul_inv, mul_comm]

/-- Weak convergence of empirical laws gives limiting frequencies for every
measurable set whose boundary is null for the limiting law. -/
theorem empiricalLaw_tendsto_count {X : Type*} [MeasurableSpace X]
    [PseudoMetricSpace X] [BorelSpace X] {u : ℕ → X} {mu : ProbabilityMeasure X}
    (hu : Tendsto (empiricalLaw u) atTop (𝓝 mu)) {S : Set X}
    (hS : MeasurableSet S) (hb : (mu : Measure X) (frontier S) = 0) :
    Tendsto (fun N =>
      (BTCalculus.FourierBoxCounting.count (fun n => u n ∈ S) N : ℝ) / N)
      atTop (𝓝 ((mu : Measure X).real S)) := by
  have h := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hu hb
  have hr := (ENNReal.tendsto_toReal (measure_ne_top (mu : Measure X) S)).comp h
  simp only [Function.comp_def, empiricalLaw_apply u _ hS,
    ENNReal.toReal_div, ENNReal.toReal_natCast] at hr
  exact (tendsto_add_atTop_iff_nat 1).mp hr

/-- Integration against an empirical law is the usual finite average. -/
theorem integral_empiricalLaw {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [T1Space X] (u : ℕ → X) (N : ℕ) (f : X →ᵇ ℝ) :
    (∫ x, f x ∂(empiricalLaw u N : Measure X)) =
      (∑ n ∈ Finset.range (N+1), f (u n)) / (N+1 : ℕ) := by
  rw [empiricalLaw, ProbabilityMeasure.coe_mk, integral_smul_measure, integral_finsetSum_measure]
  · simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]
    ring
  · intro n hn
    exact integrable_dirac (by simp)

/-- A vanishing error in real samples does not change their limiting
empirical probability law. -/
theorem empiricalLaw_tendsto_of_sub_tendsto_zero {u v : ℕ → ℝ}
    {mu : ProbabilityMeasure ℝ}
    (hv : Tendsto (empiricalLaw v) atTop (𝓝 mu))
    (he : Tendsto (fun n => u n - v n) atTop (𝓝 0)) :
    Tendsto (empiricalLaw u) atTop (𝓝 mu) := by
  apply tendsto_iff_forall_lipschitz_integral_tendsto.2
  intro f hb hl
  obtain ⟨L, hL⟩ := hl
  let g : ℝ →ᵇ ℝ := ⟨⟨f, hL.continuous⟩, hb⟩
  have hd : Tendsto (fun n => f (u n) - f (v n)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => hL.norm_sub_le (u n) (v n))
    simpa using he.norm.const_mul (L : ℝ)
  have ha := hd.cesaro.comp (tendsto_add_atTop_nat 1)
  have hg := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hv) g
  have he' : Tendsto (fun N =>
      (∫ x, g x ∂(empiricalLaw u N : Measure ℝ)) -
      (∫ x, g x ∂(empiricalLaw v N : Measure ℝ))) atTop (𝓝 0) := by
    simp_rw [integral_empiricalLaw]
    simpa only [g, BoundedContinuousFunction.coe_mk,
      ContinuousMap.coe_mk, Function.comp_def, Finset.sum_sub_distrib,
      div_eq_mul_inv, sub_mul, mul_sub, mul_comm] using ha
  simpa only [sub_add_cancel, zero_add, g, BoundedContinuousFunction.coe_mk,
    ContinuousMap.coe_mk] using he'.add hg

end Problems.Juggler.BeattyPhase

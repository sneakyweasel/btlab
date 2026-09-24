import Problems.Juggler.BeattyOccupationMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.Order.Monotone

/-!
# Support of the logarithmic occupation measure

The positive logarithmic kernel gives each jump interval the same support
as restricted Lebesgue measure. The support of their sum is the closure
of their union; overlap and accumulation of intervals are both allowed.
-/

namespace Problems.Juggler.BeattyPhase

open Filter Topology Set MeasureTheory
open scoped ENNReal

/-- Restricting Lebesgue measure to an open real set gives its closure
as support. No connectedness of the open set is assumed. -/
theorem support_volume_restrict_of_isOpen {s : Set ℝ} (hs : IsOpen s) :
    (volume.restrict s).support = closure s := by
  apply Subset.antisymm
  · exact fun _ hx => (Measure.support_restrict_subset hx).1
  · apply closure_minimal ?_ Measure.isClosed_support
    have h := Measure.interior_inter_support (μ := (volume : Measure ℝ)) (s := s)
    simpa only [hs.interior_eq, Measure.support_eq_univ, inter_univ] using h

/-- The strictly positive logarithmic kernel does not change the support
of its open interval. A degenerate or reversed interval gives empty support. -/
theorem support_logIntervalMeasure {a L U : ℝ} (ha : 0 < a) (hL : 0 < L) :
    (logIntervalMeasure a L U).support = closure (Ioo L U) := by
  have hm : Measurable (fun y : ℝ => ENNReal.ofReal (1/(a*y))) :=
    (measurable_const.div (measurable_const.mul measurable_id)).ennreal_ofReal
  have hp : ∀ᵐ y ∂volume.restrict (Ioo L U), ENNReal.ofReal (1/(a*y)) ≠ 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    exact one_div_pos.mpr (mul_pos ha (hL.trans hy.1))
  rw [← support_volume_restrict_of_isOpen isOpen_Ioo]
  exact Subset.antisymm
    (withDensity_absolutelyContinuous _ _).support_mono
    (withDensity_absolutelyContinuous' hm.aemeasurable hp).support_mono

/-- A sum of logarithmic interval measures is supported on exactly the
closure of the union of its open intervals, with no disjointness premise. -/
theorem support_sum_logIntervalMeasure {a : ℝ} (ha : 0 < a) {L U : ℕ → ℝ}
    (hL : ∀ i, 0 < L i) :
    (Measure.sum (fun i => logIntervalMeasure a (L i) (U i))).support =
      closure (⋃ i, Ioo (L i) (U i)) := by
  let ν (i : ℕ) := logIntervalMeasure a (L i) (U i)
  apply Subset.antisymm
  · apply Measure.support_subset_of_isClosed isClosed_closure
    change (Measure.sum ν) (closure (⋃ i, Ioo (L i) (U i)))ᶜ = 0
    rw [Measure.sum_apply _ isClosed_closure.measurableSet.compl]
    apply ENNReal.tsum_eq_zero.mpr
    intro i
    apply measure_mono_null ?_ (Measure.measure_compl_support (μ := ν i))
    apply compl_subset_compl.mpr
    rw [show (ν i).support = closure (Ioo (L i) (U i)) from
      support_logIntervalMeasure ha (hL i)]
    exact closure_mono (fun x hx => mem_iUnion.mpr ⟨i, hx⟩)
  · apply closure_minimal ?_ Measure.isClosed_support
    intro y hy
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    have hs : y ∈ (ν i).support := by
      rw [show (ν i).support = closure (Ioo (L i) (U i)) from
        support_logIntervalMeasure ha (hL i)]
      exact subset_closure hi
    exact Measure.support_mono (Measure.le_sum ν i) hs

end Problems.Juggler.BeattyPhase

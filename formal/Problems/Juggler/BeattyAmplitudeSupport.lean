import Problems.Juggler.BeattyAmplitudeRange
import Problems.Juggler.BeattyProfileGeometry
import Mathlib.MeasureTheory.Measure.Support

/-!
# Support and recurrent sampling of left-continuous amplitudes

One-sided continuity gives positive phase mass near each attained value.
Consequently the pushforward support and recurrent-sample cluster set are
both the closure of the amplitude range. Matching endpoint values allow
the closed and half-open phase conventions to be interchanged.
-/

namespace Problems.Juggler.BeattyPhase

open Filter Topology Set MeasureTheory

/-- Equal endpoint values make the closed and left-open interval images
identical. This is an exact range statement, not only equality almost everywhere. -/
theorem image_Icc_eq_image_Ioc_of_equal_endpoints {f : ℝ → ℝ}
    {a b : ℝ} (hab : a < b) (hend : f a = f b) :
    f '' Icc a b = f '' Ioc a b := by
  apply Subset.antisymm
  · rintro y ⟨t, ht, rfl⟩
    rcases eq_or_lt_of_le ht.1 with h | h
    · exact ⟨b, ⟨hab, le_rfl⟩, hend.symm.trans (congrArg f h)⟩
    · exact ⟨t, ⟨h, ht.2⟩, rfl⟩
  · exact image_mono Ioc_subset_Icc_self

/-- The law of a measurable left-continuous amplitude on `(a,b]` has
support exactly the closure of its image, including one-sided trace values. -/
theorem support_map_restrict_Ioc_eq_closure_image {f : ℝ → ℝ}
    (hf : Measurable f) (hleft : ∀ x, Tendsto f (𝓝[<] x) (𝓝 (f x)))
    (a b : ℝ) :
    ((volume.restrict (Ioc a b)).map f).support = closure (f '' Ioc a b) := by
  apply Subset.antisymm
  · apply Measure.support_subset_of_isClosed isClosed_closure
    apply (ae_map_iff hf.aemeasurable isClosed_closure.measurableSet).2
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact subset_closure ⟨t, ht, rfl⟩
  · apply closure_minimal ?_ Measure.isClosed_support
    rintro y ⟨t, ht, rfl⟩
    rw [Measure.support_eq_forall_isOpen]
    intro U htU hU
    obtain ⟨c, hc, hcU⟩ := mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset ht.1 |>.1
      ((hleft t).eventually (hU.mem_nhds htU))
    rw [Measure.map_apply hf hU.measurableSet,
      Measure.restrict_apply (hf hU.measurableSet)]
    have hvol : 0 < volume (Ioo c t) := by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hc.2)
    apply hvol.trans_le (measure_mono ?_)
    intro x hx
    exact ⟨hcU hx, ⟨hc.1.trans_lt hx.1, hx.2.le.trans ht.2⟩⟩

private theorem amplitude_mem_tail_closure {f : ℝ → ℝ} {theta : ℕ → ℝ}
    (hleft : ∀ x, Tendsto f (𝓝[<] x) (𝓝 (f x)))
    (hr : RecurrentUnitPhase theta) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1)
    (N : ℕ) : f t ∈ closure ((fun n => f (theta n)) '' Ici N) := by
  rw [mem_closure_iff_nhds]
  intro U hU
  obtain ⟨a, ha, haU⟩ := mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset ht.1 |>.1
    ((hleft t).eventually hU)
  obtain ⟨n, hn, hnt⟩ := hr a t ha.1 ha.2 ht.2 N
  exact ⟨f (theta n), haU hnt, n, hn, rfl⟩

/-- Recurrent phases sampling a left-continuous amplitude with matching
endpoint values have precisely its closed range as their cluster set. -/
theorem mapClusterPt_amplitude_iff {f : ℝ → ℝ} {theta : ℕ → ℝ}
    (hleft : ∀ x, Tendsto f (𝓝[<] x) (𝓝 (f x)))
    (hend : f 0 = f 1) (htheta : ∀ n, theta n ∈ Icc (0 : ℝ) 1)
    (hr : RecurrentUnitPhase theta) (y : ℝ) :
    MapClusterPt y atTop (fun n => f (theta n)) ↔ y ∈ closure (f '' Icc 0 1) := by
  constructor
  · intro hy
    exact isClosed_closure.mem_of_mapClusterPt hy
      (Eventually.of_forall fun n => subset_closure ⟨theta n, htheta n, rfl⟩)
  · intro hy
    rw [image_Icc_eq_image_Ioc_of_equal_endpoints zero_lt_one hend] at hy
    apply mapClusterPt_atTop_iff_forall_mem_closure.2
    intro N
    apply closure_minimal ?_ isClosed_closure hy
    rintro z ⟨t, ht, rfl⟩
    exact amplitude_mem_tail_closure hleft hr ht N

end Problems.Juggler.BeattyPhase

import Problems.Juggler.BeattyPassageDensityTopology
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.Lemmas

/-!
# Dense null blowup of the occupation density

Every tail of the rescaled jump intervals is dense in the support, by
recurrent phase sampling and left continuity. Baire's theorem gives a
dense G-delta of values lying in infinitely many intervals. The density
is infinite there, despite having total integral one.
-/

namespace Problems.Juggler.BeattyPhase

open Filter Topology Set MeasureTheory PaperBThreshold
open scoped ENNReal

/-- The open union of rescaled jump intervals after a chronological cutoff. -/
noncomputable def certificateJumpTail (N : ℕ) : Set ℝ :=
  ⋃ (r : ℕ) (_ : N ≤ r),
    Ioo (certificateAmplitudeJumpLeft (r+1)) (certificateAmplitudeJumpRight (r+1))

/-- Every chronological tail is an open set in the value axis. -/
theorem isOpen_certificateJumpTail (N : ℕ) : IsOpen (certificateJumpTail N) :=
  isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_Ioo

/-- Each tail meets every open neighborhood of every support point.
This uses recurrence of the actual Beatty phases, not an independence assumption. -/
theorem certificateJumpTail_inter_open_nonempty (N : ℕ) {U : Set ℝ} (hU : IsOpen U)
    {x : ℝ} (hx : x ∈ (certificatePassageLaw : Measure ℝ).support) (hxU : x ∈ U) :
    (U ∩ certificateJumpTail N).Nonempty := by
  have hc : MapClusterPt x atTop (fun r => certificatePhaseAmplitude (certificatePhase r)) := by
    apply (mapClusterPt_amplitude_iff certificatePhaseAmplitude_tendsto_left
      (certificatePhaseAmplitude_endpoints.1.trans certificatePhaseAmplitude_endpoints.2.symm)
      (fun r => ⟨(certificatePhase_mem_Ico r).1, (certificatePhase_mem_Ico r).2.le⟩)
      certificatePhase_recurrent x).mpr
    exact certificatePassageLaw_support_eq_closure_image ▸ hx
  obtain ⟨r, hr, hrU⟩ := frequently_atTop.mp (hc.frequently (hU.mem_nhds hxU)) (N+1)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  have hcl : certificateAmplitudeJumpLeft (k+1) ∈
      closure (Ioo (certificateAmplitudeJumpLeft (k+1)) (certificateAmplitudeJumpRight (k+1))) := by
    rw [closure_Ioo (certificateAmplitudeJumpLeft_lt_right (k+1)).ne]
    exact ⟨le_rfl, (certificateAmplitudeJumpLeft_lt_right (k+1)).le⟩
  obtain ⟨y, hyU, hy⟩ := mem_closure_iff_nhds.mp hcl U (hU.mem_nhds hrU)
  exact ⟨y, hyU, mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨by omega, hy⟩⟩⟩

private theorem augmented_tail_dense (N : ℕ) :
    Dense ((Icc certificatePassageLower certificatePassageUpper)ᶜ ∪ certificateJumpTail N) := by
  apply dense_iff_inter_open.mpr
  intro U hU hne
  obtain ⟨x, hxU⟩ := hne
  by_cases hx : x ∈ Icc certificatePassageLower certificatePassageUpper
  · have hs := certificatePassageLaw_support_eq_Icc.symm ▸ hx
    obtain ⟨y, hyU, hy⟩ := certificateJumpTail_inter_open_nonempty N hU hs hxU
    exact ⟨y, hyU, Or.inr hy⟩
  · exact ⟨x, hxU, Or.inl hx⟩

/-- A concrete G-delta subset of the support interior: values hit by jump
intervals of arbitrarily large indices. -/
noncomputable def certificateDensityBlowupSet : Set ℝ :=
  Ioo certificatePassageLower certificatePassageUpper ∩ ⋂ N, certificateJumpTail N

/-- The exceptional blowup set is G-delta, although it will have measure zero. -/
theorem isGδ_certificateDensityBlowupSet : IsGδ certificateDensityBlowupSet :=
  isOpen_Ioo.isGδ.inter (IsGδ.iInter fun N => (isOpen_certificateJumpTail N).isGδ)

/-- Blowup points are dense throughout the exact support interval. -/
theorem closure_certificateDensityBlowupSet :
    closure certificateDensityBlowupSet = Icc certificatePassageLower certificatePassageUpper := by
  have hd : Dense (⋂ N, (Icc certificatePassageLower certificatePassageUpper)ᶜ ∪ certificateJumpTail N) :=
    dense_iInter_of_isOpen (fun N => isClosed_Icc.isOpen_compl.union (isOpen_certificateJumpTail N))
      augmented_tail_dense
  apply Subset.antisymm
  · exact closure_minimal (fun _ hx => Ioo_subset_Icc_self hx.1) isClosed_Icc
  · rw [← closure_Ioo certificatePassage_endpoints_bounds.2.1.ne]
    apply closure_minimal ?_ isClosed_closure
    intro x hx
    rw [mem_closure_iff]
    intro U hU hxU
    obtain ⟨y, hyU, hy⟩ := hd.inter_open_nonempty
      (U ∩ Ioo certificatePassageLower certificatePassageUpper)
      (hU.inter isOpen_Ioo) ⟨x, hxU, hx⟩
    refine ⟨y, hyU.1, hyU.2, mem_iInter.mpr fun N => ?_⟩
    exact (mem_iInter.mp hy N).resolve_left (not_not.mpr (Ioo_subset_Icc_self hyU.2))

/-- The explicit density is infinite at every point of the dense G-delta. -/
theorem certificateDensityBlowupSet_subset_infinite :
    certificateDensityBlowupSet ⊆ {y | certificatePassageDensity y = ∞} := by
  intro y hy
  apply certificatePassageDensity_eq_top_of_mem_jump_tails
  · exact (sub_pos.mpr beta_lt_one).trans_le (certificatePassage_endpoints_bounds.1.trans hy.1.1.le)
  · intro N
    obtain ⟨r, hr⟩ := mem_iUnion.mp (mem_iInter.mp hy.2 N)
    obtain ⟨hNr, hyr⟩ := mem_iUnion.mp hr
    exact ⟨r, hNr, hyr⟩

/-- The dense G-delta blowup set has zero Lebesgue measure. -/
theorem volume_certificateDensityBlowupSet : volume certificateDensityBlowupSet = 0 :=
  measure_mono_null certificateDensityBlowupSet_subset_infinite volume_certificatePassageDensity_infinite

/-- On every open set meeting the support interior, each finite density
threshold is exceeded on a set of positive Lebesgue measure. -/
theorem certificatePassageDensity_superlevel_pos {U : Set ℝ} (hU : IsOpen U)
    (hne : (U ∩ Ioo certificatePassageLower certificatePassageUpper).Nonempty) (M : ℝ) :
    0 < volume (U ∩ {y | ENNReal.ofReal M < certificatePassageDensity y}) := by
  obtain ⟨x, hxU, hx⟩ := hne
  have hcl : x ∈ closure certificateDensityBlowupSet := by
    rw [closure_certificateDensityBlowupSet]
    exact Ioo_subset_Icc_self hx
  obtain ⟨y, hyU, hy⟩ := mem_closure_iff_nhds.mp hcl U (hU.mem_nhds hxU)
  apply (hU.inter (certificatePassageDensity_lowerSemicontinuous.isOpen_preimage
    (ENNReal.ofReal M))).measure_pos volume
  refine ⟨y, hyU, ?_⟩
  change ENNReal.ofReal M < certificatePassageDensity y
  rw [certificateDensityBlowupSet_subset_infinite hy]
  exact ENNReal.ofReal_lt_top

/-- No almost-everywhere equal version of the density is essentially
bounded on an open set meeting the support interior. The conclusion is
therefore independent of the values chosen on the null blowup set. -/
theorem certificatePassageDensity_no_ae_bounded_version {h : ℝ → ℝ≥0∞}
    (hh : h =ᵐ[volume] certificatePassageDensity) {U : Set ℝ} (hU : IsOpen U)
    (hne : (U ∩ Ioo certificatePassageLower certificatePassageUpper).Nonempty) (M : ℝ) :
    ¬ ∀ᵐ y ∂volume.restrict U, h y ≤ ENNReal.ofReal M := by
  intro hb
  have ha : ∀ᵐ y ∂volume, y ∈ U → certificatePassageDensity y ≤ ENNReal.ofReal M := by
    filter_upwards [(ae_restrict_iff' hU.measurableSet).mp hb, hh] with y hy he
    simpa only [he] using hy
  have hz : volume (U ∩ {y | ENNReal.ofReal M < certificatePassageDensity y}) = 0 := by
    simpa [ae_iff, Classical.not_imp, not_le, Set.inter_def] using ha
  exact (certificatePassageDensity_superlevel_pos hU hne M).ne' hz

end Problems.Juggler.BeattyPhase

import Problems.Juggler.BeattySlopeGammaSupport
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.Lemmas

/-!
# Dense null blowup of the Gamma density for every slope

Every tail of the rescaled jump intervals is dense in the support `[ℓ,u]`,
by recurrence of the actual Beatty phases and left continuity of the
amplitude. Baire's theorem gives a dense G-delta of values lying in
infinitely many intervals; the explicit density is infinite there although
its integral is one.
-/

namespace Problems.Juggler.BeattySlope

open Filter Topology Set MeasureTheory BeattyPhase
open scoped ENNReal

/-- The open union of rescaled jump intervals with index at least `N`. -/
noncomputable def passageGammaTail (β : ℝ) (N : ℕ) : Set ℝ :=
  ⋃ (r : ℕ) (_ : N ≤ r), Ioo (passageGammaJumpLeft β (r+1)) (passageGammaJumpRight β (r+1))

/-- Every chronological tail is open. -/
theorem isOpen_passageGammaTail (β : ℝ) (N : ℕ) : IsOpen (passageGammaTail β N) :=
  isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_Ioo

/-- The support-interior values lying in rescaled jump intervals of
arbitrarily large index. -/
noncomputable def passageGammaBlowupSet (β : ℝ) : Set ℝ :=
  Ioo (passageGammaLower β) (passageGammaUpper β) ∩ ⋂ N, passageGammaTail β N

/-- The blowup set is G-delta. -/
theorem isGδ_passageGammaBlowupSet (β : ℝ) : IsGδ (passageGammaBlowupSet β) :=
  isOpen_Ioo.isGδ.inter (IsGδ.iInter fun N => (isOpen_passageGammaTail β N).isGδ)

variable {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ : Irrational β)

include hβ0 hβ1 hβ

/-- Each tail meets every open neighborhood of every support point, by
recurrence of the actual Beatty phases. -/
theorem passageGammaTail_inter_open (N : ℕ) {U : Set ℝ} (hU : IsOpen U)
    {x : ℝ} (hx : x ∈ ((passageGammaLaw hβ0 hβ1 hβ) : Measure ℝ).support) (hxU : x ∈ U) :
    (U ∩ passageGammaTail β N).Nonempty := by
  have hends := (passageGammaAmp_endpoints hβ0 hβ1 hβ).1.trans
    (passageGammaAmp_endpoints hβ0 hβ1 hβ).2.symm
  have hc : MapClusterPt x atTop (fun r => passageGammaAmp β (passagePhase β r)) := by
    apply (mapClusterPt_amplitude_iff (passageGammaAmp_tendsto_left hβ0 hβ1 hβ) hends
      (fun r => ⟨(passagePhase_mem_Ico hβ0 r).1, (passagePhase_mem_Ico hβ0 r).2.le⟩)
      (passagePhase_recurrent hβ0 hβ) x).mpr
    exact passageGammaLaw_support_image hβ0 hβ1 hβ ▸ hx
  obtain ⟨r, hr, hrU⟩ := frequently_atTop.mp (hc.frequently (hU.mem_nhds hxU)) (N+1)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  have hlt := passageGammaJump_left_lt_right hβ0 hβ1 (k+1)
  have hcl : passageGammaJumpLeft β (k+1) ∈
      closure (Ioo (passageGammaJumpLeft β (k+1)) (passageGammaJumpRight β (k+1))) := by
    rw [closure_Ioo hlt.ne]
    exact ⟨le_rfl, hlt.le⟩
  obtain ⟨y, hyU, hy⟩ := mem_closure_iff_nhds.mp hcl U (hU.mem_nhds hrU)
  exact ⟨y, hyU, mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨by omega, hy⟩⟩⟩

private theorem augmented_tail_dense (N : ℕ) :
    Dense ((Icc (passageGammaLower β) (passageGammaUpper β))ᶜ ∪ passageGammaTail β N) := by
  apply dense_iff_inter_open.mpr
  intro U hU hne
  obtain ⟨x, hxU⟩ := hne
  by_cases hx : x ∈ Icc (passageGammaLower β) (passageGammaUpper β)
  · have hs := (passageGammaLaw_support_eq_Icc hβ0 hβ1 hβ).symm ▸ hx
    obtain ⟨y, hyU, hy⟩ := passageGammaTail_inter_open hβ0 hβ1 hβ N hU hs hxU
    exact ⟨y, hyU, Or.inr hy⟩
  · exact ⟨x, hxU, Or.inl hx⟩

/-- Blowup points are dense in the support interval `[ℓ,u]`. -/
theorem closure_passageGammaBlowupSet :
    closure (passageGammaBlowupSet β) = Icc (passageGammaLower β) (passageGammaUpper β) := by
  have hd : Dense (⋂ N, (Icc (passageGammaLower β) (passageGammaUpper β))ᶜ ∪
      passageGammaTail β N) :=
    dense_iInter_of_isOpen
      (fun N => isClosed_Icc.isOpen_compl.union (isOpen_passageGammaTail β N))
      (augmented_tail_dense hβ0 hβ1 hβ)
  apply Subset.antisymm
  · exact closure_minimal (fun _ hx => Ioo_subset_Icc_self hx.1) isClosed_Icc
  · rw [← closure_Ioo (passageGamma_endpoints_bounds hβ0 hβ1 hβ).2.1.ne]
    apply closure_minimal ?_ isClosed_closure
    intro x hx
    rw [mem_closure_iff]
    intro U hU hxU
    obtain ⟨y, hyU, hy⟩ := hd.inter_open_nonempty
      (U ∩ Ioo (passageGammaLower β) (passageGammaUpper β))
      (hU.inter isOpen_Ioo) ⟨x, hxU, hx⟩
    refine ⟨y, hyU.1, hyU.2, mem_iInter.mpr fun N => ?_⟩
    exact (mem_iInter.mp hy N).resolve_left (not_not.mpr (Ioo_subset_Icc_self hyU.2))

/-- The explicit density is infinite at every point of the blowup set. -/
theorem passageGammaBlowup_subset_top :
    passageGammaBlowupSet β ⊆ {y | passageGammaDensity β y = ∞} := by
  intro y hy
  apply passageGammaDensity_top_of_tails hβ0 hβ1
  · exact (sub_pos.mpr hβ1).trans_le
      ((passageGamma_endpoints_bounds hβ0 hβ1 hβ).1.trans hy.1.1.le)
  · intro N
    obtain ⟨r, hr⟩ := mem_iUnion.mp (mem_iInter.mp hy.2 N)
    obtain ⟨hNr, hyr⟩ := mem_iUnion.mp hr
    exact ⟨r, hNr, hyr⟩

/-- The dense G-delta blowup set is Lebesgue-null. -/
theorem volume_passageGammaBlowupSet : volume (passageGammaBlowupSet β) = 0 :=
  measure_mono_null (passageGammaBlowup_subset_top hβ0 hβ1 hβ)
    (volume_passageGammaDensity_top hβ0 hβ1 hβ)

/-- On every open set meeting `(ℓ,u)`, each finite density threshold is
exceeded on a set of positive Lebesgue measure. -/
theorem passageGammaDensity_superlevel {U : Set ℝ} (hU : IsOpen U)
    (hne : (U ∩ Ioo (passageGammaLower β) (passageGammaUpper β)).Nonempty) (M : ℝ) :
    0 < volume (U ∩ {y | ENNReal.ofReal M < passageGammaDensity β y}) := by
  obtain ⟨x, hxU, hx⟩ := hne
  have hcl : x ∈ closure (passageGammaBlowupSet β) := by
    rw [closure_passageGammaBlowupSet hβ0 hβ1 hβ]
    exact Ioo_subset_Icc_self hx
  obtain ⟨y, hyU, hy⟩ := mem_closure_iff_nhds.mp hcl U (hU.mem_nhds hxU)
  apply (hU.inter ((passageGammaDensity_lsc hβ0 hβ1 hβ).isOpen_preimage
    (ENNReal.ofReal M))).measure_pos volume
  refine ⟨y, hyU, ?_⟩
  change ENNReal.ofReal M < passageGammaDensity β y
  rw [passageGammaBlowup_subset_top hβ0 hβ1 hβ hy]
  exact ENNReal.ofReal_lt_top

/-- No almost-everywhere equal version of the density is essentially bounded
on an open set meeting `(ℓ,u)`. -/
theorem passageGammaDensity_no_ae_bound {h : ℝ → ℝ≥0∞}
    (hh : h =ᵐ[volume] passageGammaDensity β) {U : Set ℝ} (hU : IsOpen U)
    (hne : (U ∩ Ioo (passageGammaLower β) (passageGammaUpper β)).Nonempty) (M : ℝ) :
    ¬ ∀ᵐ y ∂volume.restrict U, h y ≤ ENNReal.ofReal M := by
  intro hb
  have ha : ∀ᵐ y ∂volume, y ∈ U → passageGammaDensity β y ≤ ENNReal.ofReal M := by
    filter_upwards [(ae_restrict_iff' hU.measurableSet).mp hb, hh] with y hy he
    simpa only [he] using hy
  have hz : volume (U ∩ {y | ENNReal.ofReal M < passageGammaDensity β y}) = 0 := by
    simpa [ae_iff, Classical.not_imp, not_le, Set.inter_def] using ha
  exact (passageGammaDensity_superlevel hβ0 hβ1 hβ hU hne M).ne' hz

end Problems.Juggler.BeattySlope

import Problems.Juggler.BeattyCertificateAsymptotic
import Problems.Juggler.BeattyProfileGeometry
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# The complete set of certificate accumulation values

The exact Beatty phases visit every open phase interval arbitrarily late.
Combined with the proved phase asymptotic, this identifies the subsequential
limits of the actual normalized counts with the explicit gap complement.
-/

namespace Problems.Juggler.BeattyPhase

open Filter Topology Set MeasureTheory PaperBThreshold

/-- The certificate phase agrees with the real fractional part. -/
theorem certificatePhase_eq_fract (r : ℕ) :
    certificatePhase r = Int.fract ((r : ℝ)/beta) := by
  have h : 0 ≤ (r : ℝ)/beta := div_nonneg (Nat.cast_nonneg r)
    (by linarith [beta_gt_five_eighths])
  simp only [certificatePhase, certificateIndex, Int.fract,
    ← Int.natCast_floor_eq_floor h, Int.cast_natCast]

/-- The reciprocal logarithmic slope is irrational, as already forced by
the strict positivity of every nonzero certificate phase. -/
theorem certificateSlope_irrational : Irrational (1/beta) := by
  rintro ⟨q, hq⟩
  have hd : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_nz
  have he : (q.den : ℝ)/beta = (q.num : ℝ) := by
    calc
      _ = (q.den : ℝ)*(1/beta) := by ring
      _ = (q.den : ℝ)*(q : ℝ) := by rw [hq]
      _ = (q.num : ℝ) := by rw [Rat.cast_def]; field_simp
  have hp := certificatePhase_pos q.pos
  rw [certificatePhase_eq_fract, he, Int.fract_intCast] at hp
  exact lt_irrefl _ hp

/-- Every open subinterval of the phase interval is visited at arbitrarily
large indices. This is recurrence of the actual phases, not just a density
assumption in the final count theorem. -/
theorem certificatePhase_recurrent (a b : ℝ) (ha : 0 ≤ a) (hab : a < b)
    (hb : b ≤ 1) (N : ℕ) : ∃ n : ℕ, N ≤ n ∧ certificatePhase n ∈ Ioo a b := by
  let slope : AddCircle (1 : ℝ) := ↑(1/beta : ℝ)
  have hd : DenseRange (fun n : ℤ => n • slope) :=
    AddCircle.denseRange_zsmul_coe_iff.2 (by simpa using certificateSlope_irrational)
  obtain ⟨x, hax, hxb⟩ := exists_between hab
  have hc : MapClusterPt (↑x : AddCircle (1 : ℝ)) atTop (fun n : ℕ => n • slope) :=
    (mapClusterPt_atTop_nsmul_tfae (↑x : AddCircle (1 : ℝ)) slope).out 3 0 |>.mp
      (hd (↑x))
  let U : Set (AddCircle (1 : ℝ)) := (fun x : ℝ => (↑x : AddCircle (1 : ℝ))) '' Ioo a b
  have hU : IsOpen U := QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  have hxU : (↑x : AddCircle (1 : ℝ)) ∈ U := ⟨x, ⟨hax, hxb⟩, rfl⟩
  obtain ⟨n, hn, hnU⟩ := frequently_atTop.1 (hc.frequently (hU.mem_nhds hxU)) N
  obtain ⟨y, hy, he⟩ := hnU
  have hphase : (↑(certificatePhase n) : AddCircle (1 : ℝ)) = n • slope := by
    rw [certificatePhase_eq_fract, AddCircle.coe_fract]
    change (↑((n : ℝ)/beta) : AddCircle (1 : ℝ)) = n • ↑(1/beta : ℝ)
    rw [← AddCircle.coe_nsmul, nsmul_eq_mul]
    congr 1
    ring
  have hny : certificatePhase n = y := by
    apply AddCircle.coe_eq_coe_iff_of_mem_Ico
      (p := (1 : ℝ)) (a := 0) (by simpa using certificatePhase_mem_Ico n)
      (by constructor <;> linarith [hy.1, hy.2]) |>.1
    exact hphase.trans he.symm
  exact ⟨n, hn, hny.symm ▸ hy⟩

private theorem weight_summable : Summable (fun r => certificateWeight (r+1)) :=
  certificate_jump_weights_hasSum.summable

private theorem phase_interior (r : ℕ) : certificatePhase (r+1) ∈ Ioo (0 : ℝ) 1 :=
  ⟨certificatePhase_pos (by omega), (certificatePhase_mem_Ico _).2⟩

private theorem phase_dense (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ∃ n, certificatePhase (n+1) ∈ Ioo a b := by
  obtain ⟨n, hn, hi⟩ := certificatePhase_recurrent a b ha hab hb 1
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  exact ⟨k, hi⟩

/-- The certificate profile is strictly increasing on the closed phase
interval, because every nonempty open interval contains a positive atom. -/
theorem certificateProfile_strictMonoOn : StrictMonoOn certificateProfile (Icc 0 1) :=
  jumpProfile_strictMonoOn weight_summable (fun _ => certificateWeight_pos _) phase_dense

/-- The original binomial-normalized certificate count. Only its positive
indices enter the asymptotic and subsequential-limit statements. -/
noncomputable def certificateRatio (r : ℕ) : ℝ :=
  (r : ℝ)*(minimalCertCount (certificateIndex r+1) : ℝ)/
    ((certificateIndex r-1).choose (r-1) : ℝ)

/-- The full envelope with the explicit open certificate jumps removed.
The atom index is `r+1`, so every genuine positive-index weight occurs once. -/
noncomputable def certificateClusterSet : Set ℝ :=
  Icc 1 (1+1/terminalRatio) \
    ⋃ r, Ioo (certificateProfile (certificatePhase (r+1)))
      (certificateProfile (certificatePhase (r+1)) + certificateWeight (r+1))

private theorem clusterSet_eq_jumpRange :
    certificateClusterSet = jumpRange (fun r => certificatePhase (r+1))
      (fun r => certificateWeight (r+1)) := by
  simp only [certificateClusterSet, jumpRange, certificateProfile,
    certificate_jump_weights_hasSum.tsum_eq]

/-- The explicit gap complement is exactly the closure of the complete
certificate profile range, with both traces of every jump included. -/
theorem certificateClusterSet_eq_closure_range :
    certificateClusterSet = closure (range certificateProfile) := by
  rw [clusterSet_eq_jumpRange]
  exact (closure_range_jumpProfile weight_summable (fun _ => certificateWeight_nonneg _)
    (certificatePhase_injective.comp (add_left_injective 1)) phase_interior).symm

/-- Exact characterization of all real subsequential limits of the actual
normalized integer counts. There are no remaining asymptotic or density inputs. -/
theorem certificateRatio_cluster_iff (y : ℝ) :
    MapClusterPt y atTop certificateRatio ↔ y ∈ certificateClusterSet := by
  rw [certificateClusterSet_eq_closure_range]
  have he : Tendsto (fun r => certificateRatio r - certificateProfile (certificatePhase r))
      atTop (𝓝 0) := certificate_phase_asymptotic
  rw [mapClusterPt_iff_of_sub_tendsto_zero he]
  exact mapClusterPt_jumpProfile_iff weight_summable
    (fun _ => certificateWeight_nonneg _) phase_interior certificatePhase_recurrent y

/-- The exact certificate accumulation set is compact. -/
theorem isCompact_certificateClusterSet : IsCompact certificateClusterSet := by
  rw [clusterSet_eq_jumpRange]
  exact isCompact_jumpRange weight_summable (fun _ => certificateWeight_nonneg _)
    (certificatePhase_injective.comp (add_left_injective 1)) phase_interior

/-- The exact certificate accumulation set has no isolated points. Together
with compactness and zero measure, this is the asserted Cantor-set geometry. -/
theorem perfect_certificateClusterSet : Perfect certificateClusterSet := by
  rw [clusterSet_eq_jumpRange]
  exact perfect_jumpRange weight_summable (fun _ => certificateWeight_pos _)
    (certificatePhase_injective.comp (add_left_injective 1)) phase_interior phase_dense

/-- The exact set of accumulation values has zero Lebesgue measure. -/
theorem volume_certificateClusterSet : volume certificateClusterSet = 0 := by
  rw [clusterSet_eq_jumpRange]
  exact volume_jumpRange weight_summable (fun _ => certificateWeight_nonneg _)
    (certificatePhase_injective.comp (add_left_injective 1))

/-- The certificate accumulation set has empty interior. -/
theorem interior_certificateClusterSet : interior certificateClusterSet = ∅ :=
  volume.interior_eq_empty_of_null volume_certificateClusterSet

/-- Both endpoints of each explicitly removed gap belong to the
accumulation set; no positive jump can be hidden inside a larger gap. -/
theorem certificate_gap_endpoints_mem (r : ℕ) :
    certificateProfile (certificatePhase (r+1)) ∈ certificateClusterSet ∧
    certificateProfile (certificatePhase (r+1)) + certificateWeight (r+1) ∈
      certificateClusterSet := by
  rw [certificateClusterSet_eq_closure_range]
  constructor
  · exact subset_closure (mem_range_self _)
  · have hj := certificateProfile_jump r
    have he : certificateProfile (certificatePhase (r+1)) + certificateWeight (r+1) =
        jumpProfileRight (fun j => certificatePhase (j+1)) (fun j => certificateWeight (j+1))
          (certificatePhase (r+1)) := by linarith
    rw [he]
    exact mem_closure_of_tendsto
      (jumpProfile_tendsto_right weight_summable (fun _ => certificateWeight_nonneg _) _)
      (Eventually.of_forall fun x => mem_range_self x)

/-- The actual normalized counts have subsequences approaching both sides
of every positive jump. The gap width is its exact certificate weight. -/
theorem certificateRatio_gap_endpoints_cluster (r : ℕ) :
    MapClusterPt (certificateProfile (certificatePhase (r+1))) atTop certificateRatio ∧
    MapClusterPt (certificateProfile (certificatePhase (r+1)) + certificateWeight (r+1))
      atTop certificateRatio :=
  ⟨(certificateRatio_cluster_iff _).2 (certificate_gap_endpoints_mem r).1,
    (certificateRatio_cluster_iff _).2 (certificate_gap_endpoints_mem r).2⟩

/-- Every closed interval strictly inside a listed gap is eventually
avoided by the actual count sequence. Finite-depth errors can still put
individual values near a gap endpoint; no stronger exclusion is asserted. -/
theorem certificateRatio_eventually_avoids_gap (r : ℕ) {a b : ℝ}
    (ha : certificateProfile (certificatePhase (r+1)) < a)
    (hb : b < certificateProfile (certificatePhase (r+1)) + certificateWeight (r+1)) :
    ∀ᶠ n in atTop, certificateRatio n ∉ Icc a b := by
  by_contra h
  have hf : ∃ᶠ n in atTop, certificateRatio n ∈ Icc a b := by
    simpa only [Filter.Frequently, not_not] using h
  obtain ⟨y, hy, hcy⟩ := isCompact_Icc.exists_mapClusterPt_of_frequently hf
  have hK := (certificateRatio_cluster_iff y).1 hcy
  exact hK.2 (mem_iUnion.2 ⟨r, ha.trans_le hy.1, hy.2.trans_lt hb⟩)

/-- The compact perfect accumulation set is nonempty. -/
theorem certificateClusterSet_nonempty : certificateClusterSet.Nonempty :=
  ⟨certificateProfile (certificatePhase 1), (certificate_gap_endpoints_mem 0).1⟩

end Problems.Juggler.BeattyPhase

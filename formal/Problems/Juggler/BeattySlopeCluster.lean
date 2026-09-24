import Problems.Juggler.BeattySlopeAsymptotic
import Problems.Juggler.BeattyRotation
import Problems.Juggler.BeattyProfileGeometry
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Order.LiminfLimsup

/-!
# The complete first-passage cluster set at every irrational slope

Positive actual crossing counts and recurrent irrational phases identify the
subsequential limits of the original integer ratios with the explicit gap
complement. The set is compact, perfect and null. Both jump traces are kept.
-/

namespace Problems.Juggler.BeattySlope

open Filter Topology Set MeasureTheory BeattyPhase

/-- The original odd-count binomial normalization, with actual first-passage
counts at the Beatty crossing edges. -/
noncomputable def passageRatio (β : ℝ) (r : ℕ) : ℝ :=
  (r : ℝ)*(passageCount β (passageIndex β r+1) : ℝ)/
    ((passageIndex β r-1).choose (r-1) : ℝ)

/-- The full phase envelope with every positive-index open jump removed.
Its interpretation as the cluster set uses an irrational boundary in `(0,1)`. -/
noncomputable def passageClusterSet (β : ℝ) : Set ℝ :=
  Icc 1 (1/(1-β)) \
    ⋃ r, Ioo (passageProfile β (passagePhase β (r+1)))
      (passageProfile β (passagePhase β (r+1)) + passageJumpWeight β (r+1))

variable {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ : Irrational β)

include hβ0 hβ1 hβ

omit hβ1 hβ in
/-- The Beatty phase is exactly a fractional part at every index. -/
theorem passagePhase_eq_fract (r : ℕ) :
    passagePhase β r = Int.fract ((r : ℝ)/β) := by
  have h := div_nonneg (Nat.cast_nonneg r) hβ0.le
  simp only [passagePhase, passageIndex, Int.fract,
    ← Int.natCast_floor_eq_floor h, Int.cast_natCast]

/-- Irrationality prevents different crossing indices from sharing a phase. -/
theorem passagePhase_injective : Function.Injective (passagePhase β) := by
  have hne {r s : ℕ} (hrs : r < s) : passagePhase β r ≠ passagePhase β s := by
    intro he
    have hm := passageIndex_strictMono hβ0 hβ1.le hrs
    apply mul_ne_nat hβ (show 0 < passageIndex β s-passageIndex β r by omega) (s-r)
    rw [Nat.cast_sub hm.le, Nat.cast_sub hrs.le]
    unfold passagePhase at he
    field_simp at he
    linarith
  intro r s he
  rcases lt_trichotomy r s with h | h | h
  · exact False.elim (hne h he)
  · exact h
  · exact False.elim (hne h he.symm)

omit hβ1 in
/-- Every open phase interval is visited at arbitrarily large indices by
the actual crossing phases, without a Diophantine rate assumption. -/
theorem passagePhase_recurrent (a b : ℝ) (ha : 0 ≤ a) (hab : a < b)
    (hb : b ≤ 1) (N : ℕ) : ∃ n : ℕ, N ≤ n ∧ passagePhase β n ∈ Ioo a b := by
  simpa only [passagePhase_eq_fract hβ0, div_eq_mul_inv, one_mul] using
    irrational_rotation_recurrent (by simpa using hβ.inv : Irrational (1/β)) a b ha hab hb N

private theorem weights_summable : Summable (fun r => passageJumpWeight β (r+1)) :=
  (passage_jump_weights_hasSum hβ0 hβ1 hβ).summable

private theorem phase_interior (r : ℕ) : passagePhase β (r+1) ∈ Ioo (0 : ℝ) 1 :=
  ⟨passagePhase_pos hβ0 hβ1 hβ (by omega), (passagePhase_mem_Ico hβ0 _).2⟩

omit hβ1 in
private theorem phase_dense (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ∃ n, passagePhase β (n+1) ∈ Ioo a b := by
  obtain ⟨n, hn, hi⟩ := passagePhase_recurrent hβ0 hβ a b ha hab hb 1
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  exact ⟨k, hi⟩

/-- Dense positive crossing atoms make the explicit profile strictly
increasing on the closed unit phase interval. -/
theorem passageProfile_strictMonoOn : StrictMonoOn (passageProfile β) (Icc 0 1) :=
  jumpProfile_strictMonoOn (weights_summable hβ0 hβ1 hβ)
    (fun _ => passageJumpWeight_pos hβ0 hβ1 _) (phase_dense hβ0 hβ)

/-- The actual gap complement is the generic range set of its summable
positive-index crossing weights, with the exact endpoint normalization. -/
theorem passageClusterSet_eq_jumpRange :
    passageClusterSet β = jumpRange (fun r => passagePhase β (r+1))
      (fun r => passageJumpWeight β (r+1)) := by
  have he : 1+β/(1-β) = 1/(1-β) := by
    field_simp [ne_of_gt (sub_pos.mpr hβ1)]
    ring
  simp only [passageClusterSet, jumpRange, passageProfile,
    (passage_jump_weights_hasSum hβ0 hβ1 hβ).tsum_eq, he]

/-- The cluster set is the closure of the profile range. The closure is
essential: the right trace at an atom need not be an attained profile value. -/
theorem passageClusterSet_eq_closure_range :
    passageClusterSet β = closure (range (passageProfile β)) := by
  rw [passageClusterSet_eq_jumpRange hβ0 hβ1 hβ]
  exact (closure_range_jumpProfile (weights_summable hβ0 hβ1 hβ)
    (fun _ => passageJumpWeight_nonneg hβ0 hβ1 _)
    ((passagePhase_injective hβ0 hβ1 hβ).comp (add_left_injective 1))
    (phase_interior hβ0 hβ1 hβ)).symm

/-- Exact characterization of all real subsequential limits of the actual
integer ratios at every irrational boundary in `(0,1)`. -/
theorem passageRatio_cluster_iff (y : ℝ) :
    MapClusterPt y atTop (passageRatio β) ↔ y ∈ passageClusterSet β := by
  rw [passageClusterSet_eq_closure_range hβ0 hβ1 hβ]
  have he : Tendsto (fun r => passageRatio β r-passageProfile β (passagePhase β r))
      atTop (𝓝 0) := passage_phase_asymptotic_odd_count hβ0 hβ1 hβ
  rw [mapClusterPt_iff_of_sub_tendsto_zero he]
  exact mapClusterPt_jumpProfile_iff (weights_summable hβ0 hβ1 hβ)
    (fun _ => passageJumpWeight_nonneg hβ0 hβ1 _) (phase_interior hβ0 hβ1 hβ)
    (passagePhase_recurrent hβ0 hβ) y

/-- The complete accumulation set is compact for every irrational boundary
in the nondegenerate interval. -/
theorem isCompact_passageClusterSet : IsCompact (passageClusterSet β) := by
  rw [passageClusterSet_eq_jumpRange hβ0 hβ1 hβ]
  exact isCompact_jumpRange (weights_summable hβ0 hβ1 hβ)
    (fun _ => passageJumpWeight_nonneg hβ0 hβ1 _)
    ((passagePhase_injective hβ0 hβ1 hβ).comp (add_left_injective 1))
    (phase_interior hβ0 hβ1 hβ)

/-- Dense positive atoms imply that the complete accumulation set has no
isolated points, including at the endpoints of its gaps. -/
theorem perfect_passageClusterSet : Perfect (passageClusterSet β) := by
  rw [passageClusterSet_eq_jumpRange hβ0 hβ1 hβ]
  exact perfect_jumpRange (weights_summable hβ0 hβ1 hβ)
    (fun _ => passageJumpWeight_pos hβ0 hβ1 _)
    ((passagePhase_injective hβ0 hβ1 hβ).comp (add_left_injective 1))
    (phase_interior hβ0 hβ1 hβ) (phase_dense hβ0 hβ)

/-- The jump weights exhaust the envelope length, so the complete
accumulation set has zero Lebesgue measure. -/
theorem volume_passageClusterSet : volume (passageClusterSet β) = 0 := by
  rw [passageClusterSet_eq_jumpRange hβ0 hβ1 hβ]
  exact volume_jumpRange (weights_summable hβ0 hβ1 hβ)
    (fun _ => passageJumpWeight_nonneg hβ0 hβ1 _)
    ((passagePhase_injective hβ0 hβ1 hβ).comp (add_left_injective 1))

/-- The accumulation set has empty interior throughout the irrational family. -/
theorem interior_passageClusterSet : interior (passageClusterSet β) = ∅ :=
  volume.interior_eq_empty_of_null (volume_passageClusterSet hβ0 hβ1 hβ)

/-- Both traces of every actual positive-index jump belong to the complete
accumulation set; every listed weight is the width of a genuine gap. -/
theorem passage_gap_endpoints_mem (r : ℕ) :
    passageProfile β (passagePhase β (r+1)) ∈ passageClusterSet β ∧
    passageProfile β (passagePhase β (r+1))+passageJumpWeight β (r+1) ∈ passageClusterSet β := by
  rw [passageClusterSet_eq_closure_range hβ0 hβ1 hβ]
  constructor
  · exact subset_closure (mem_range_self _)
  · have hj := jumpProfile_jump (weights_summable hβ0 hβ1 hβ)
      (fun _ => passageJumpWeight_nonneg hβ0 hβ1 _)
      ((passagePhase_injective hβ0 hβ1 hβ).comp (add_left_injective 1)) r
    have he : passageProfile β (passagePhase β (r+1))+passageJumpWeight β (r+1) =
        jumpProfileRight (fun j => passagePhase β (j+1)) (fun j => passageJumpWeight β (j+1))
          (passagePhase β (r+1)) := by
          simp only [Function.comp_def] at hj
          unfold passageProfile
          linarith
    rw [he]
    exact mem_closure_of_tendsto
      (jumpProfile_tendsto_right (weights_summable hβ0 hβ1 hβ)
        (fun _ => passageJumpWeight_nonneg hβ0 hβ1 _) _)
      (Eventually.of_forall fun x => mem_range_self x)

/-- The actual integer ratios have subsequences approaching both sides of
every positive jump, at every irrational boundary in `(0,1)`. -/
theorem passageRatio_gap_endpoints_cluster (r : ℕ) :
    MapClusterPt (passageProfile β (passagePhase β (r+1))) atTop (passageRatio β) ∧
    MapClusterPt (passageProfile β (passagePhase β (r+1))+passageJumpWeight β (r+1))
      atTop (passageRatio β) :=
  ⟨(passageRatio_cluster_iff hβ0 hβ1 hβ _).2 (passage_gap_endpoints_mem hβ0 hβ1 hβ r).1,
    (passageRatio_cluster_iff hβ0 hβ1 hβ _).2 (passage_gap_endpoints_mem hβ0 hβ1 hβ r).2⟩

/-- Every closed interval strictly inside an explicit gap is eventually
avoided by the actual ratios. This is a qualitative assertion with no rate. -/
theorem passageRatio_eventually_avoids_gap (r : ℕ) {a b : ℝ}
    (ha : passageProfile β (passagePhase β (r+1)) < a)
    (hb : b < passageProfile β (passagePhase β (r+1))+passageJumpWeight β (r+1)) :
    ∀ᶠ n in atTop, passageRatio β n ∉ Icc a b := by
  by_contra h
  have hf : ∃ᶠ n in atTop, passageRatio β n ∈ Icc a b := by
    simpa only [Filter.Frequently, not_not] using h
  obtain ⟨y, hy, hcy⟩ := isCompact_Icc.exists_mapClusterPt_of_frequently hf
  have hK := (passageRatio_cluster_iff hβ0 hβ1 hβ y).1 hcy
  exact hK.2 (mem_iUnion.mpr ⟨r, ha.trans_le hy.1, hy.2.trans_lt hb⟩)

/-- The compact perfect null accumulation set is nonempty. -/
theorem passageClusterSet_nonempty : (passageClusterSet β).Nonempty :=
  ⟨passageProfile β (passagePhase β 1), (passage_gap_endpoints_mem hβ0 hβ1 hβ 0).1⟩

/-- Both exact envelope endpoints are subsequential limits of the original
ratios, at every irrational boundary in `(0,1)`. -/
theorem passageRatio_envelope_endpoints_cluster :
    MapClusterPt 1 atTop (passageRatio β) ∧
      MapClusterPt (1/(1-β)) atTop (passageRatio β) := by
  have hm (x : ℝ) : MapClusterPt (passageProfile β x) atTop (passageRatio β) := by
    rw [passageRatio_cluster_iff hβ0 hβ1 hβ, passageClusterSet_eq_closure_range hβ0 hβ1 hβ]
    exact subset_closure (mem_range_self x)
  simpa only [(passageProfile_endpoints hβ0 hβ1 hβ).1,
    (passageProfile_endpoints hβ0 hβ1 hβ).2] using And.intro (hm 0) (hm 1)

/-- The exact liminf and limsup of the original ratios are the two profile
endpoints. No uniformity in the boundary or convergence rate is asserted. -/
theorem passageRatio_liminf_limsup :
    liminf (passageRatio β) atTop = 1 ∧ limsup (passageRatio β) atTop = 1/(1-β) := by
  have hl : IsBoundedUnder (· ≥ ·) atTop (passageRatio β) := by
    change ∃ c : ℝ, ∀ᶠ n in atTop, c ≤ passageRatio β n
    exact ⟨0, Eventually.of_forall fun n => by unfold passageRatio; positivity⟩
  have he := (tendsto_order.mp (passage_phase_asymptotic_odd_count hβ0 hβ1 hβ).abs).2
    (1 : ℝ) (by norm_num)
  have hu : IsBoundedUnder (· ≤ ·) atTop (passageRatio β) := by
    change ∃ c : ℝ, ∀ᶠ n in atTop, passageRatio β n ≤ c
    refine ⟨1/(1-β)+1, ?_⟩
    filter_upwards [he] with n hn
    have hp := (passageProfile_bounds hβ0 hβ1 hβ (passagePhase β n)).2
    change |passageRatio β n-passageProfile β (passagePhase β n)| < 1 at hn
    linarith [(abs_lt.mp hn).2]
  have hcL := (passageRatio_cluster_iff hβ0 hβ1 hβ _).mp
    (MapClusterPt.liminf hu.isCoboundedUnder_ge hl)
  have hcU := (passageRatio_cluster_iff hβ0 hβ1 hβ _).mp
    (MapClusterPt.limsup hl.isCoboundedUnder_le hu)
  have hend := passageRatio_envelope_endpoints_cluster hβ0 hβ1 hβ
  exact ⟨le_antisymm (hend.1.liminf_le hl) hcL.1.1,
    le_antisymm hcU.1.2 (hend.2.le_limsup hu)⟩

end Problems.Juggler.BeattySlope

import Problems.Juggler.BeattyPhaseTransfer
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Perfect
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Topology.Bases

/-!
# The range of a positive cumulative jump series

The closure of the range is the full envelope with the open jump intervals
removed. Its Lebesgue measure is zero because the jumps exhaust the envelope.
Dense positive atoms additionally imply that the range closure is perfect.
-/

namespace Problems.Juggler.BeattyPhase

open Filter Topology Set MeasureTheory

/-- The closed envelope with every open jump interval removed. -/
noncomputable def jumpRange (phase w : ℕ → ℝ) : Set ℝ :=
  Icc 1 (1 + ∑' n, w n) \
    ⋃ n, Ioo (jumpProfile phase w (phase n)) (jumpProfile phase w (phase n) + w n)

private theorem restrict_summable {w : ℕ → ℝ} (hw : Summable w)
    (hn : ∀ n, 0 ≤ w n) (p : ℕ → Prop) [DecidablePred p] :
    Summable (fun n => if p n then w n else 0) :=
  hw.of_norm_bounded fun n => by
    split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg (hn n), hn n]

private theorem right_le_profile {phase w : ℕ → ℝ} (hw : Summable w)
    (hn : ∀ n, 0 ≤ w n) {x y : ℝ} (hxy : x < y) :
    jumpProfileRight phase w x ≤ jumpProfile phase w y := by
  unfold jumpProfileRight jumpProfile
  apply add_le_add_right
  apply (restrict_summable hw hn _).tsum_le_tsum _ (restrict_summable hw hn _)
  intro n
  by_cases hx : phase n ≤ x
  · simp [hx, lt_of_le_of_lt hx hxy]
  · simp only [hx, if_false]
    split_ifs <;> simp [hn n]

private theorem profile_le_right {phase w : ℕ → ℝ} (hw : Summable w)
    (hn : ∀ n, 0 ≤ w n) (x : ℝ) :
    jumpProfile phase w x ≤ jumpProfileRight phase w x := by
  unfold jumpProfileRight jumpProfile
  apply add_le_add_right
  apply (restrict_summable hw hn _).tsum_le_tsum _ (restrict_summable hw hn _)
  intro n
  by_cases hx : phase n < x
  · simp [hx, hx.le]
  · simp only [hx, if_false]
    split_ifs <;> simp [hn n]

private theorem profile_zero {phase w : ℕ → ℝ} (hp : ∀ n, 0 < phase n) :
    jumpProfile phase w 0 = 1 := by
  simp [jumpProfile, fun n => not_lt_of_ge (hp n).le]

private theorem profile_one {phase w : ℕ → ℝ} (hp : ∀ n, phase n < 1) :
    jumpProfile phase w 1 = 1 + ∑' n, w n := by
  simp [jumpProfile, hp]

private theorem right_mem_closure {phase w : ℕ → ℝ} (hw : Summable w)
    (hn : ∀ n, 0 ≤ w n) (x : ℝ) :
    jumpProfileRight phase w x ∈ closure (range (jumpProfile phase w)) :=
  mem_closure_of_tendsto (jumpProfile_tendsto_right hw hn x)
    (Eventually.of_forall fun y => mem_range_self y)

private theorem gap_disjoint_range {phase w : ℕ → ℝ} (hw : Summable w)
    (hn : ∀ n, 0 ≤ w n) (hi : Function.Injective phase) (n : ℕ) :
    Disjoint (Ioo (jumpProfile phase w (phase n))
      (jumpProfile phase w (phase n) + w n)) (range (jumpProfile phase w)) := by
  apply disjoint_left.2
  rintro y hy ⟨x, rfl⟩
  rcases le_or_gt x (phase n) with hx | hx
  · exact (not_lt_of_ge (jumpProfile_monotone hw hn hx)) hy.1
  · have h := right_le_profile (phase := phase) hw hn hx
    have hj := jumpProfile_jump hw hn hi n
    linarith [hy.2]

/-- The open intervals skipped by distinct atoms are pairwise disjoint. -/
theorem jumpProfile_gaps_pairwiseDisjoint {phase w : ℕ → ℝ} (hw : Summable w)
    (hn : ∀ n, 0 ≤ w n) (hi : Function.Injective phase) :
    Pairwise (fun i j => Disjoint
      (Ioo (jumpProfile phase w (phase i)) (jumpProfile phase w (phase i) + w i))
      (Ioo (jumpProfile phase w (phase j)) (jumpProfile phase w (phase j) + w j))) := by
  intro i j hij
  have hne : phase i ≠ phase j := fun h => hij (hi h)
  rcases lt_or_gt_of_ne hne with h | h
  · apply disjoint_left.2
    intro y hy hz
    have hle := right_le_profile (phase := phase) hw hn h
    have heq := jumpProfile_jump hw hn hi i
    linarith [hy.2, hz.1]
  · apply disjoint_left.2
    intro y hy hz
    have hle := right_le_profile (phase := phase) hw hn h
    have heq := jumpProfile_jump hw hn hi j
    linarith [hz.2, hy.1]

/-- For distinct interior atoms, the range closure is precisely the
envelope minus the listed open jumps. No density assumption is needed. -/
theorem closure_range_jumpProfile {phase w : ℕ → ℝ} (hw : Summable w)
    (hn : ∀ n, 0 ≤ w n) (hi : Function.Injective phase)
    (hp : ∀ n, phase n ∈ Ioo (0 : ℝ) 1) :
    closure (range (jumpProfile phase w)) = jumpRange phase w := by
  apply Subset.antisymm
  · intro y hy
    refine ⟨?_, ?_⟩
    · exact closure_minimal (by rintro z ⟨x, rfl⟩; exact jumpProfile_bounds hw hn x)
        isClosed_Icc hy
    · intro hg
      obtain ⟨n, hng⟩ := mem_iUnion.1 hg
      have hd := gap_disjoint_range hw hn hi n
      have hc : closure (range (jumpProfile phase w)) ⊆
          (Ioo (jumpProfile phase w (phase n))
            (jumpProfile phase w (phase n) + w n))ᶜ :=
        closure_minimal (fun z hz hg => disjoint_left.1 hd hg hz) isOpen_Ioo.isClosed_compl
      exact hc hy hng
  · rintro y ⟨hy, hgap⟩
    by_contra hout
    have hzero := profile_zero (w := w) (fun n => (hp n).1)
    have hone := profile_one (w := w) (fun n => (hp n).2)
    have hy0 : 1 < y := lt_of_le_of_ne hy.1 (by
      intro he; apply hout; rw [← he, ← hzero]; exact subset_closure (mem_range_self 0))
    have hy1 : y < 1 + ∑' n, w n := lt_of_le_of_ne hy.2 (by
      intro he; apply hout; rw [he, ← hone]; exact subset_closure (mem_range_self 1))
    let S : Set ℝ := {x | jumpProfile phase w x < y}
    have hS : S.Nonempty := ⟨0, by simpa [S, hzero] using hy0⟩
    have hb : BddAbove S := ⟨1, by
      intro x hx
      by_contra h
      have hm := jumpProfile_monotone (phase := phase) hw hn (le_of_not_ge h)
      change jumpProfile phase w x < y at hx
      rw [hone] at hm
      linarith⟩
    let x := sSup S
    have hl : jumpProfile phase w x ≤ y := by
      apply le_of_tendsto (jumpProfile_tendsto_left hw hn x)
      filter_upwards [self_mem_nhdsWithin] with z hz
      obtain ⟨a, ha, hza⟩ := (lt_csSup_iff hb hS).1 (show z < sSup S from hz)
      exact ((jumpProfile_monotone hw hn hza.le).trans_lt ha).le
    have hr : y ≤ jumpProfileRight phase w x := by
      apply ge_of_tendsto (jumpProfile_tendsto_right hw hn x)
      filter_upwards [self_mem_nhdsWithin] with z hz
      by_contra hh
      have hzS : z ∈ S := lt_of_not_ge hh
      exact (not_le_of_gt hz) (le_csSup hb hzS)
    have hleft : jumpProfile phase w x < y := lt_of_le_of_ne hl (by
      intro he; apply hout; rw [← he]; exact subset_closure (mem_range_self x))
    have hright : y < jumpProfileRight phase w x := lt_of_le_of_ne hr (by
      intro he; apply hout; rw [he]; exact right_mem_closure hw hn x)
    have hx : x ∈ range phase := by
      by_contra h
      have he := jumpProfileRight_eq_of_not_mem_range (w := w) h
      linarith
    obtain ⟨n, he⟩ := hx
    rw [← he] at hleft hright
    apply hgap
    refine mem_iUnion.2 ⟨n, hleft, ?_⟩
    have he := jumpProfile_jump hw hn hi n
    linarith

/-- The range closure has zero Lebesgue measure: the disjoint open jumps
have total length equal to the entire envelope. -/
theorem volume_jumpRange {phase w : ℕ → ℝ} (hw : Summable w)
    (hn : ∀ n, 0 ≤ w n) (hi : Function.Injective phase) :
    volume (jumpRange phase w) = 0 := by
  let G : Set ℝ := ⋃ n, Ioo (jumpProfile phase w (phase n))
    (jumpProfile phase w (phase n) + w n)
  have hG : MeasurableSet G := MeasurableSet.iUnion fun _ => measurableSet_Ioo
  have hvol : volume G = ENNReal.ofReal (∑' n, w n) := by
    rw [measure_iUnion (jumpProfile_gaps_pairwiseDisjoint hw hn hi)
      (fun _ => measurableSet_Ioo)]
    simp only [Real.volume_Ioo, add_sub_cancel_left]
    exact (ENNReal.ofReal_tsum_of_nonneg hn hw).symm
  have hsub : G ⊆ Icc 1 (1 + ∑' n, w n) := by
    intro y hy
    obtain ⟨n, hnmem⟩ := mem_iUnion.1 hy
    have hlo := (jumpProfile_bounds (phase := phase) hw hn (phase n)).1
    have hhi : jumpProfileRight phase w (phase n) ≤ 1 + ∑' j, w j := by
      unfold jumpProfileRight
      apply add_le_add_right
      exact (restrict_summable hw hn _).tsum_le_tsum (fun j => by
        split_ifs <;> simp [hn j]) hw
    have hj := jumpProfile_jump hw hn hi n
    constructor <;> linarith [hnmem.1, hnmem.2]
  change volume (Icc 1 (1 + ∑' n, w n) \ G) = 0
  rw [measure_sdiff hsub hG.nullMeasurableSet (by rw [hvol]; exact ENNReal.ofReal_ne_top),
    Real.volume_Icc, add_sub_cancel_left, hvol, tsub_self]

/-- Dense positive atoms make the cumulative profile strictly increasing
on its entire phase interval, despite its countably many discontinuities. -/
theorem jumpProfile_strictMonoOn {phase w : ℕ → ℝ} (hw : Summable w)
    (hwpos : ∀ n, 0 < w n)
    (hd : ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 → ∃ n, phase n ∈ Ioo a b) :
    StrictMonoOn (jumpProfile phase w) (Icc 0 1) := by
  intro x hx y hy hxy
  obtain ⟨k, hk⟩ := hd x y hx.1 hxy hy.2
  have hn : ∀ n, 0 ≤ w n := fun n => (hwpos n).le
  unfold jumpProfile
  apply add_lt_add_right
  apply Summable.tsum_lt_tsum (i := k) ?_ ?_
    (restrict_summable hw hn _) (restrict_summable hw hn _)
  · intro n
    by_cases h : phase n < x
    · simp [h, h.trans hxy]
    · simp only [h, if_false]
      split_ifs <;> simp [hn n]
  · simpa [not_lt_of_ge hk.1.le, hk.2] using hwpos k

private theorem range_eq_image_interval {phase w : ℕ → ℝ}
    (hp : ∀ n, phase n ∈ Ioo (0 : ℝ) 1) :
    range (jumpProfile phase w) = jumpProfile phase w '' Icc 0 1 := by
  apply Subset.antisymm
  · rintro y ⟨x, rfl⟩
    by_cases hx0 : x < 0
    · refine ⟨0, by norm_num, ?_⟩
      simp [jumpProfile, fun n => not_lt_of_ge (hp n).1.le,
        fun n => not_lt_of_ge (hx0.le.trans (hp n).1.le)]
    · by_cases hx1 : 1 < x
      · refine ⟨1, by norm_num, ?_⟩
        simp [jumpProfile, fun n => (hp n).2, fun n => (hp n).2.trans hx1]
      · exact ⟨x, ⟨le_of_not_gt hx0, le_of_not_gt hx1⟩, rfl⟩
  · exact image_subset_range _ _

/-- A dense positive jump profile has a perfect range closure. The proof
uses its one-sided continuity, not continuity across the atoms. -/
theorem perfect_jumpRange {phase w : ℕ → ℝ} (hw : Summable w)
    (hwpos : ∀ n, 0 < w n) (hi : Function.Injective phase)
    (hp : ∀ n, phase n ∈ Ioo (0 : ℝ) 1)
    (hd : ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 → ∃ n, phase n ∈ Ioo a b) :
    Perfect (jumpRange phase w) := by
  have hn : ∀ n, 0 ≤ w n := fun n => (hwpos n).le
  rw [← closure_range_jumpProfile hw hn hi hp]
  apply Preperfect.perfect_closure
  rw [preperfect_iff_nhds]
  intro y hy U hU
  rw [range_eq_image_interval hp] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hm := jumpProfile_strictMonoOn hw hwpos hd
  by_cases hx0 : x = 0
  · subst x
    have hright : jumpProfileRight phase w 0 = jumpProfile phase w 0 := by
      apply jumpProfileRight_eq_of_not_mem_range
      rintro ⟨n, hn0⟩
      linarith [(hp n).1]
    have ht := jumpProfile_tendsto_right (phase := phase) hw hn 0
    rw [hright] at ht
    obtain ⟨b, hb, hbU⟩ := mem_nhdsGT_iff_exists_mem_Ioc_Ioo_subset zero_lt_one |>.1
      (ht.eventually hU)
    obtain ⟨z, hz0, hzb⟩ := exists_between hb.1
    refine ⟨jumpProfile phase w z, ⟨hbU ⟨hz0, hzb⟩, mem_range_self z⟩, ?_⟩
    exact (hm (by norm_num) ⟨hz0.le, hzb.le.trans hb.2⟩ hz0).ne'
  · have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
    obtain ⟨a, ha, haU⟩ := mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset hxpos |>.1
      ((jumpProfile_tendsto_left (phase := phase) hw hn x).eventually hU)
    obtain ⟨z, haz, hzx⟩ := exists_between ha.2
    refine ⟨jumpProfile phase w z, ⟨haU ⟨haz, hzx⟩, mem_range_self z⟩, ?_⟩
    exact (hm ⟨ha.1.trans haz.le, hzx.le.trans hx.2⟩ hx hzx).ne

/-- The gap complement is compact, with no separate boundedness premise. -/
theorem isCompact_jumpRange {phase w : ℕ → ℝ} (hw : Summable w)
    (hn : ∀ n, 0 ≤ w n) (hi : Function.Injective phase)
    (hp : ∀ n, phase n ∈ Ioo (0 : ℝ) 1) :
    IsCompact (jumpRange phase w) := by
  have hclosed : IsClosed (jumpRange phase w) := by
    rw [← closure_range_jumpProfile hw hn hi hp]
    exact isClosed_closure
  exact isCompact_Icc.of_isClosed_subset hclosed (fun _ h => h.1)

/-- A phase sequence visits every open subinterval of the unit interval
arbitrarily late. No frequency or quantitative discrepancy is required. -/
def RecurrentUnitPhase (theta : ℕ → ℝ) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 → ∀ N : ℕ,
    ∃ n : ℕ, N ≤ n ∧ theta n ∈ Ioo a b

private theorem profile_mem_tail_closure {phase w theta : ℕ → ℝ}
    (hw : Summable w) (hn : ∀ n, 0 ≤ w n)
    (hp : ∀ n, phase n ∈ Ioo (0 : ℝ) 1) (hr : RecurrentUnitPhase theta)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (N : ℕ) :
    jumpProfile phase w x ∈ closure ((fun n => jumpProfile phase w (theta n)) '' Ici N) := by
  rw [mem_closure_iff_nhds]
  intro U hU
  by_cases hx0 : x = 0
  · subst x
    have he : jumpProfileRight phase w 0 = jumpProfile phase w 0 := by
      apply jumpProfileRight_eq_of_not_mem_range
      rintro ⟨n, hn0⟩
      linarith [(hp n).1]
    have ht := jumpProfile_tendsto_right (phase := phase) hw hn 0
    rw [he] at ht
    obtain ⟨b, hb, hbU⟩ := mem_nhdsGT_iff_exists_mem_Ioc_Ioo_subset zero_lt_one |>.1
      (ht.eventually hU)
    obtain ⟨n, hnN, hnI⟩ := hr 0 b le_rfl hb.1 hb.2 N
    exact ⟨jumpProfile phase w (theta n), hbU hnI, n, hnN, rfl⟩
  · have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
    obtain ⟨a, ha, haU⟩ := mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset hxpos |>.1
      ((jumpProfile_tendsto_left (phase := phase) hw hn x).eventually hU)
    obtain ⟨n, hnN, hnI⟩ := hr a x ha.1 ha.2 hx.2 N
    exact ⟨jumpProfile phase w (theta n), haU hnI, n, hnN, rfl⟩

/-- Sampling a cumulative jump profile along recurrent phases has exactly
its range closure as the set of subsequential limits. Values at the jumps
use the strict left-continuous convention throughout. -/
theorem mapClusterPt_jumpProfile_iff {phase w theta : ℕ → ℝ}
    (hw : Summable w) (hn : ∀ n, 0 ≤ w n)
    (hp : ∀ n, phase n ∈ Ioo (0 : ℝ) 1) (hr : RecurrentUnitPhase theta) (y : ℝ) :
    MapClusterPt y atTop (fun n => jumpProfile phase w (theta n)) ↔
      y ∈ closure (range (jumpProfile phase w)) := by
  constructor
  · intro hy
    exact isClosed_closure.mem_of_mapClusterPt hy
      (Eventually.of_forall fun n => subset_closure (mem_range_self (theta n)))
  · intro hy
    apply mapClusterPt_atTop_iff_forall_mem_closure.2
    intro N
    apply closure_minimal ?_ isClosed_closure hy
    intro z hz
    rw [range_eq_image_interval hp] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact profile_mem_tail_closure hw hn hp hr hx N

private theorem cluster_of_sub_zero {f g : ℕ → ℝ} {y : ℝ}
    (he : Tendsto (fun n => f n-g n) atTop (𝓝 0)) (hy : MapClusterPt y atTop f) :
    MapClusterPt y atTop g := by
  obtain ⟨u, hu, hfu⟩ := hy.tendsto_subseq
  have hg : Tendsto (g ∘ u) atTop (𝓝 y) := by
    have ht := hfu.sub (he.comp hu.tendsto_atTop)
    simpa only [Function.comp_def, sub_sub_cancel, sub_zero] using ht
  exact hg.mapClusterPt.of_comp hu.tendsto_atTop

/-- An additive error tending to zero preserves every real subsequential
limit, in both directions. No rate or global boundedness is assumed. -/
theorem mapClusterPt_iff_of_sub_tendsto_zero {f g : ℕ → ℝ}
    (he : Tendsto (fun n => f n-g n) atTop (𝓝 0)) (y : ℝ) :
    MapClusterPt y atTop f ↔ MapClusterPt y atTop g := by
  constructor
  · exact cluster_of_sub_zero he
  · apply cluster_of_sub_zero
    simpa only [neg_sub, neg_zero] using he.neg

end Problems.Juggler.BeattyPhase

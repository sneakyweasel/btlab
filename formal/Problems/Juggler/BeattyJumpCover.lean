import Problems.Juggler.BeattyProfileGeometry
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Finite cut covers of a jump range

A finite set of phase cuts covers the gap complement of a cumulative jump
profile by the two traces at each cut and one closed interval per gap between
consecutive cuts. The interval length is the atomic mass strictly inside the
gap. Covers whose gap masses are small in every power give Hausdorff measure
zero, and hence Hausdorff dimension zero.
-/

namespace Problems.Juggler.BeattyPhase

open Filter Topology Set MeasureTheory Metric
open scoped NNReal ENNReal

private theorem restrict_summable' {w : ℕ → ℝ} (hw : Summable w)
    (hn : ∀ n, 0 ≤ w n) (p : ℕ → Prop) [DecidablePred p] :
    Summable (fun n => if p n then w n else 0) :=
  hw.of_norm_bounded fun n => by
    split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg (hn n), hn n]

/-- The right trace at a point is at most the profile at any later point. -/
theorem jumpProfileRight_le_of_lt {phase w : ℕ → ℝ} (hw : Summable w)
    (hn : ∀ n, 0 ≤ w n) {x y : ℝ} (hxy : x < y) :
    jumpProfileRight phase w x ≤ jumpProfile phase w y := by
  unfold jumpProfileRight jumpProfile
  apply add_le_add_right
  apply (restrict_summable' hw hn _).tsum_le_tsum _ (restrict_summable' hw hn _)
  intro n
  by_cases hx : phase n ≤ x
  · simp [hx, lt_of_le_of_lt hx hxy]
  · simp only [hx, if_false]
    split_ifs <;> simp [hn n]

/-- The left-continuous profile never exceeds its right trace. -/
theorem jumpProfile_le_right {phase w : ℕ → ℝ} (hw : Summable w)
    (hn : ∀ n, 0 ≤ w n) (x : ℝ) :
    jumpProfile phase w x ≤ jumpProfileRight phase w x := by
  unfold jumpProfileRight jumpProfile
  apply add_le_add_right
  apply (restrict_summable' hw hn _).tsum_le_tsum _ (restrict_summable' hw hn _)
  intro n
  by_cases hx : phase n < x
  · simp [hx, hx.le]
  · simp only [hx, if_false]
    split_ifs <;> simp [hn n]

/-- Every point of the envelope lies between the two traces at some phase
of the closed unit interval. No gap condition is needed here. -/
theorem jumpRange_bracket {phase w : ℕ → ℝ} (hw : Summable w)
    (hn : ∀ n, 0 ≤ w n) (hp : ∀ n, phase n ∈ Ioo (0 : ℝ) 1) {y : ℝ}
    (hy : y ∈ Icc 1 (1 + ∑' n, w n)) :
    ∃ x ∈ Icc (0 : ℝ) 1, jumpProfile phase w x ≤ y ∧ y ≤ jumpProfileRight phase w x := by
  have hzero : jumpProfile phase w 0 = 1 := by
    simp [jumpProfile, fun n => not_lt_of_ge (hp n).1.le]
  have hrzero : jumpProfileRight phase w 0 = 1 := by
    simp [jumpProfileRight, fun n => not_le_of_gt (hp n).1]
  have hone : jumpProfile phase w 1 = 1 + ∑' n, w n := by
    simp [jumpProfile, fun n => (hp n).2]
  rcases eq_or_lt_of_le hy.1 with h1 | h1
  · exact ⟨0, ⟨le_rfl, zero_le_one⟩, by rw [hzero, h1], by rw [hrzero, h1]⟩
  let S : Set ℝ := {x | jumpProfile phase w x < y}
  have h0S : (0 : ℝ) ∈ S := by simpa [S, hzero] using h1
  have hS : S.Nonempty := ⟨0, h0S⟩
  have hub : ∀ x ∈ S, x ≤ 1 := by
    intro x hx
    by_contra h
    have hm := jumpProfile_monotone (phase := phase) hw hn (le_of_not_ge h)
    change jumpProfile phase w x < y at hx
    rw [hone] at hm
    linarith [hy.2]
  have hb : BddAbove S := ⟨1, hub⟩
  refine ⟨sSup S, ⟨le_csSup hb h0S, csSup_le hS hub⟩, ?_, ?_⟩
  · apply le_of_tendsto (jumpProfile_tendsto_left hw hn (sSup S))
    filter_upwards [self_mem_nhdsWithin] with z hz
    obtain ⟨a, ha, hza⟩ := (lt_csSup_iff hb hS).1 (show z < sSup S from hz)
    exact ((jumpProfile_monotone hw hn hza.le).trans_lt ha).le
  · apply ge_of_tendsto (jumpProfile_tendsto_right hw hn (sSup S))
    filter_upwards [self_mem_nhdsWithin] with z hz
    by_contra hh
    have hzS : z ∈ S := lt_of_not_ge hh
    exact (not_le_of_gt hz) (le_csSup hb hzS)

/-- A point of the gap complement between the two traces at one phase is
one of those two traces. -/
theorem jumpRange_eq_of_bracket {phase w : ℕ → ℝ} (hw : Summable w)
    (hn : ∀ n, 0 ≤ w n) (hi : Function.Injective phase) {x y : ℝ}
    (hy : y ∈ jumpRange phase w) (hl : jumpProfile phase w x ≤ y)
    (hr : y ≤ jumpProfileRight phase w x) :
    y = jumpProfile phase w x ∨ y = jumpProfileRight phase w x := by
  by_cases hx : x ∈ range phase
  · obtain ⟨k, rfl⟩ := hx
    have hj := jumpProfile_jump hw hn hi k
    by_contra hne
    push Not at hne
    apply hy.2
    refine mem_iUnion.2 ⟨k, lt_of_le_of_ne hl hne.1.symm, ?_⟩
    have := lt_of_le_of_ne hr hne.2
    linarith
  · have he := jumpProfileRight_eq_of_not_mem_range (w := w) hx
    left
    linarith

/-- The gaps between consecutive points of a finite cut set, as ordered
pairs with no cut strictly between them. -/
noncomputable def cutGaps (C : Finset ℝ) : Finset (ℝ × ℝ) := by
  classical
  exact (C ×ˢ C).filter (fun g => g.1 < g.2 ∧ ∀ e ∈ C, e ≤ g.1 ∨ g.2 ≤ e)

/-- Membership in the consecutive-gap set, unfolded. -/
theorem mem_cutGaps {C : Finset ℝ} {g : ℝ × ℝ} :
    g ∈ cutGaps C ↔ g.1 ∈ C ∧ g.2 ∈ C ∧ g.1 < g.2 ∧ ∀ e ∈ C, e ≤ g.1 ∨ g.2 ≤ e := by
  classical
  unfold cutGaps
  simp only [Finset.mem_filter, Finset.mem_product]
  tauto

/-- Every uncut point of the unit interval lies strictly inside a gap,
provided both endpoints are cuts. -/
theorem exists_cutGap {C : Finset ℝ} (h0 : (0 : ℝ) ∈ C) (h1 : (1 : ℝ) ∈ C)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hxC : x ∉ C) :
    ∃ g ∈ cutGaps C, g.1 < x ∧ x < g.2 := by
  classical
  have hL : (C.filter (· < x)).Nonempty :=
    ⟨0, Finset.mem_filter.2 ⟨h0, lt_of_le_of_ne hx.1 (fun h => hxC (h ▸ h0))⟩⟩
  have hU : (C.filter (x < ·)).Nonempty :=
    ⟨1, Finset.mem_filter.2 ⟨h1, lt_of_le_of_ne hx.2 (fun h => hxC (h ▸ h1))⟩⟩
  set c := (C.filter (· < x)).max' hL
  set d := (C.filter (x < ·)).min' hU
  have hc := Finset.mem_filter.1 (Finset.max'_mem _ hL)
  have hd := Finset.mem_filter.1 (Finset.min'_mem _ hU)
  refine ⟨(c, d), mem_cutGaps.2 ⟨hc.1, hd.1, hc.2.trans hd.2, ?_⟩, hc.2, hd.2⟩
  intro e he
  rcases lt_trichotomy e x with h | h | h
  · exact Or.inl (Finset.le_max' _ e (Finset.mem_filter.2 ⟨he, h⟩))
  · exact absurd (h ▸ he) hxC
  · exact Or.inr (Finset.min'_le _ e (Finset.mem_filter.2 ⟨he, h⟩))

/-- Two gaps sharing an interior point coincide. -/
theorem cutGap_eq_of_mem {C : Finset ℝ} {g g' : ℝ × ℝ} (hg : g ∈ cutGaps C)
    (hg' : g' ∈ cutGaps C) {x : ℝ} (hx : x ∈ Ioo g.1 g.2) (hx' : x ∈ Ioo g'.1 g'.2) :
    g = g' := by
  obtain ⟨h1, h2, -, hc⟩ := mem_cutGaps.1 hg
  obtain ⟨h1', h2', -, hc'⟩ := mem_cutGaps.1 hg'
  have a1 : g'.1 ≤ g.1 := (hc _ h1').resolve_right (fun h => by linarith [hx.1, hx.2, hx'.1, hx'.2])
  have a2 : g.1 ≤ g'.1 := (hc' _ h1).resolve_right (fun h => by linarith [hx.1, hx.2, hx'.1, hx'.2])
  have b1 : g.2 ≤ g'.2 := (hc _ h2').resolve_left (fun h => by linarith [hx.1, hx.2, hx'.1, hx'.2])
  have b2 : g'.2 ≤ g.2 := (hc' _ h2).resolve_left (fun h => by linarith [hx.1, hx.2, hx'.1, hx'.2])
  exact Prod.ext (le_antisymm a2 a1) (le_antisymm b1 b2)

/-- Two interior points not separated by any cut lie in the same gap. -/
theorem cutGap_eq_of_no_cut {C : Finset ℝ} {g g' : ℝ × ℝ} (hg : g ∈ cutGaps C)
    (hg' : g' ∈ cutGaps C) {u v : ℝ} (hu : u ∈ Ioo g.1 g.2) (hv : v ∈ Ioo g'.1 g'.2)
    (hsep : ∀ e ∈ C, e ≤ u ↔ e ≤ v) : g = g' := by
  obtain ⟨h1, h2, -, -⟩ := mem_cutGaps.1 hg
  obtain ⟨-, -, -, hc'⟩ := mem_cutGaps.1 hg'
  have hvC : v ∉ C := fun h => by
    rcases hc' v h with h | h <;> linarith [hv.1, hv.2]
  have l : g.1 < v := lt_of_le_of_ne ((hsep _ h1).1 hu.1.le) (fun h => hvC (h ▸ h1))
  have r : v < g.2 := lt_of_not_ge fun h => absurd ((hsep _ h2).2 h) (not_le_of_gt hu.2)
  exact cutGap_eq_of_mem hg hg' ⟨l, r⟩ hv

/-- There are at most as many gaps as cuts: a gap is fixed by its left end. -/
theorem card_cutGaps_le (C : Finset ℝ) : (cutGaps C).card ≤ C.card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro g hg
    exact (mem_cutGaps.1 hg).1
  · intro g hg g' hg' he
    have hg1 := mem_cutGaps.1 hg
    have hg2 := mem_cutGaps.1 hg'
    change g.1 = g'.1 at he
    have hm : (g.1 + min g.2 g'.2) / 2 ∈ Ioo g.1 g.2 := by
      constructor <;> linarith [min_le_left g.2 g'.2, lt_min hg1.2.2.1 (he ▸ hg2.2.2.1)]
    have hm' : (g.1 + min g.2 g'.2) / 2 ∈ Ioo g'.1 g'.2 := by
      rw [← he]
      constructor <;> linarith [min_le_right g.2 g'.2, lt_min hg1.2.2.1 (he ▸ hg2.2.2.1)]
    exact cutGap_eq_of_mem hg hg' hm hm'

/-- The gap complement is covered by the two traces at every cut and by
the closed interval from the right trace to the left profile across each gap. -/
theorem jumpRange_subset_cuts {phase w : ℕ → ℝ} (hw : Summable w)
    (hn : ∀ n, 0 ≤ w n) (hi : Function.Injective phase)
    (hp : ∀ n, phase n ∈ Ioo (0 : ℝ) 1) {C : Finset ℝ}
    (h0 : (0 : ℝ) ∈ C) (h1 : (1 : ℝ) ∈ C) :
    jumpRange phase w ⊆ (⋃ c ∈ C, ({jumpProfile phase w c} ∪ {jumpProfileRight phase w c})) ∪
      ⋃ g ∈ cutGaps C, Icc (jumpProfileRight phase w g.1) (jumpProfile phase w g.2) := by
  intro y hy
  obtain ⟨x, hx, hl, hr⟩ := jumpRange_bracket hw hn hp hy.1
  by_cases hxC : x ∈ C
  · left
    refine mem_iUnion₂.2 ⟨x, hxC, ?_⟩
    rcases jumpRange_eq_of_bracket hw hn hi hy hl hr with h | h
    · exact Or.inl h
    · exact Or.inr h
  · right
    obtain ⟨g, hg, hgx, hxg⟩ := exists_cutGap h0 h1 hx hxC
    refine mem_iUnion₂.2 ⟨g, hg, ?_, ?_⟩
    · exact (jumpProfileRight_le_of_lt hw hn hgx).trans hl
    · exact hr.trans (jumpProfileRight_le_of_lt hw hn hxg)

/-- The length of the interval across a gap is at most the mass of the atoms
satisfying any property shared by all atoms strictly inside the gap. -/
theorem jumpGap_mass_le {phase w : ℕ → ℝ} (hw : Summable w)
    (hn : ∀ n, 0 ≤ w n) {c d : ℝ} (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ n, c < phase n → phase n < d → P n) :
    jumpProfile phase w d - jumpProfileRight phase w c ≤
      ∑' n, if P n then w n else 0 := by
  unfold jumpProfileRight jumpProfile
  rw [add_sub_add_left_eq_sub,
    ← (restrict_summable' hw hn _).tsum_sub (restrict_summable' hw hn _)]
  apply Summable.tsum_le_tsum _ ((restrict_summable' hw hn _).sub
    (restrict_summable' hw hn _)) (restrict_summable' hw hn _)
  intro n
  by_cases h1 : phase n ≤ c
  · have h2 : phase n < d ∨ ¬ phase n < d := em _
    rcases h2 with h2 | h2 <;> simp only [h1, h2, if_true, if_false] <;>
      split_ifs <;> linarith [hn n]
  · by_cases h2 : phase n < d
    · simp only [h1, h2, hP n (lt_of_not_ge h1) h2, if_true, if_false]
      linarith
    · simp only [h1, h2, if_false]
      split_ifs <;> linarith [hn n]

/-- Cut covers whose gap intervals are uniformly short and have small total
`s`-th power length force zero `s`-dimensional Hausdorff measure. -/
theorem jumpRange_hausdorff_zero {phase w : ℕ → ℝ} (hw : Summable w)
    (hn : ∀ n, 0 ≤ w n) (hi : Function.Injective phase)
    (hp : ∀ n, phase n ∈ Ioo (0 : ℝ) 1) {s : ℝ} (hs : 0 < s)
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : Finset ℝ, (0 : ℝ) ∈ C ∧ (1 : ℝ) ∈ C ∧
      (∀ g ∈ cutGaps C, jumpProfile phase w g.2 - jumpProfileRight phase w g.1 ≤ ε) ∧
      ∑ g ∈ cutGaps C, (jumpProfile phase w g.2 - jumpProfileRight phase w g.1) ^ s ≤ ε) :
    Measure.hausdorffMeasure s (jumpRange phase w) = 0 := by
  choose C h0 h1 hd hsum using fun n : ℕ => h (1 / ((n : ℝ) + 1)) (by positivity)
  set F := jumpProfile phase w
  set R := jumpProfileRight phase w
  let ι : ℕ → Type := fun n => ↥(C n) ⊕ ↥(C n) ⊕ ↥(cutGaps (C n))
  let t : ∀ n, ι n → Set ℝ := fun n => Sum.elim (fun c => {F c})
    (Sum.elim (fun c => {R c}) (fun g => Icc (R g.1.1) (F g.1.2)))
  let r : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (1 / ((n : ℝ) + 1))
  have hr : Tendsto r atTop (𝓝 0) := by
    have hh : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hc := (ENNReal.continuous_ofReal.tendsto 0).comp hh
    simpa only [r, Function.comp_def, ENNReal.ofReal_zero] using hc
  have hmass (n : ℕ) (g : ℝ × ℝ) (hg : g ∈ cutGaps (C n)) : 0 ≤ F g.2 - R g.1 :=
    sub_nonneg.2 (jumpProfileRight_le_of_lt hw hn (mem_cutGaps.1 hg).2.2.1)
  have ht (n : ℕ) (i : ι n) : ediam (t n i) ≤ r n := by
    rcases i with c | c | g
    · simp [t]
    · simp [t]
    · simp only [t, Sum.elim_inr, Real.ediam_Icc]
      exact ENNReal.ofReal_le_ofReal (hd n g.1 g.2)
  have hcover (n : ℕ) : jumpRange phase w ⊆ ⋃ i, t n i := by
    intro y hy
    rcases mem_union _ _ _ |>.1 (jumpRange_subset_cuts hw hn hi hp (h0 n) (h1 n) hy) with
      hy | hy
    · obtain ⟨c, hc, hyc⟩ := mem_iUnion₂.1 hy
      rcases hyc with hyc | hyc
      · exact mem_iUnion.2 ⟨Sum.inl ⟨c, hc⟩, hyc⟩
      · exact mem_iUnion.2 ⟨Sum.inr (Sum.inl ⟨c, hc⟩), hyc⟩
    · obtain ⟨g, hg, hyg⟩ := mem_iUnion₂.1 hy
      exact mem_iUnion.2 ⟨Sum.inr (Sum.inr ⟨g, hg⟩), hyg⟩
  have hbound (n : ℕ) : (∑ i, ediam (t n i) ^ s) ≤ r n := by
    change ∑ i : ↥(C n) ⊕ ↥(C n) ⊕ ↥(cutGaps (C n)), ediam (t n i) ^ s ≤ r n
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [t, Sum.elim_inl, Sum.elim_inr, ediam_singleton,
      ENNReal.zero_rpow_of_pos hs, Finset.sum_const_zero, zero_add, Real.ediam_Icc]
    rw [Finset.sum_coe_sort (cutGaps (C n)) (fun g => ENNReal.ofReal (F g.2 - R g.1) ^ s)]
    calc
      _ = ∑ g ∈ cutGaps (C n), ENNReal.ofReal ((F g.2 - R g.1) ^ s) := by
        apply Finset.sum_congr rfl
        intro g hg
        exact ENNReal.ofReal_rpow_of_nonneg (hmass n g hg) hs.le
      _ = ENNReal.ofReal (∑ g ∈ cutGaps (C n), (F g.2 - R g.1) ^ s) :=
        (ENNReal.ofReal_sum_of_nonneg fun g hg =>
          Real.rpow_nonneg (hmass n g hg) s).symm
      _ ≤ r n := ENNReal.ofReal_le_ofReal (hsum n)
  have hle := Measure.hausdorffMeasure_le_liminf_sum s (jumpRange phase w) r hr t
    (Eventually.of_forall ht) (Eventually.of_forall hcover)
  apply le_antisymm _ bot_le
  calc
    _ ≤ _ := hle
    _ ≤ liminf r atTop := liminf_le_liminf (Eventually.of_forall hbound)
    _ = 0 := hr.liminf_eq

/-- A set whose Hausdorff measure vanishes in every positive dimension has
Hausdorff dimension zero. -/
theorem dimH_eq_zero_of_hausdorff {K : Set ℝ}
    (h : ∀ s : ℝ, 0 < s → Measure.hausdorffMeasure s K = 0) : dimH K = 0 := by
  apply le_antisymm _ bot_le
  apply dimH_le
  intro d hd
  by_contra hpos
  have hd0 : (0 : ℝ) < d := by
    have : (0 : ℝ≥0∞) < d := lt_of_not_ge hpos
    exact_mod_cast this
  rw [h d hd0] at hd
  exact ENNReal.zero_ne_top hd

end Problems.Juggler.BeattyPhase

import Problems.Juggler.BeattyGapVolume

/-!
# Spatial localization of complementary-gap tube volumes

Above any real threshold, the metric tube volume differs from the sum of
truncated gaps whose left endpoints exceed that threshold by at most four
times the radius. Only the exterior collars and one crossing gap contribute.
-/

namespace Problems.Juggler.BeattyPhase

open Set MeasureTheory

/-- Inside a complementary gap, the metric tube retains exactly its length
truncated at twice the radius. -/
theorem volume_thickening_inter_gap {K : Set ℝ} {l w ε : ℝ}
    (hl : l ∈ K) (hr : l+w ∈ K) (hg : Disjoint (Ioo l (l+w)) K)
    (hw : 0 ≤ w) (hε : 0 < ε) :
    volume.real (Metric.thickening ε K ∩ Ioo l (l+w)) = min w (2*ε) := by
  have he : Metric.thickening ε K ∩ Ioo l (l+w) =
      Ioo l (l+w) \ Icc (l+ε) (l+w-ε) := by
    ext x
    constructor
    · rintro ⟨hx, hxg⟩
      refine ⟨hxg, ?_⟩
      intro hc
      obtain ⟨z, hz, hd⟩ := Metric.mem_thickening_iff.1 hx
      have hz' : z ≤ l ∨ l+w ≤ z := by
        by_contra hh
        push Not at hh
        exact Set.disjoint_left.1 hg hh hz
      rw [Real.dist_eq, abs_lt] at hd
      rcases hz' with hz' | hz' <;> linarith [hc.1, hc.2]
    · rintro ⟨hx, hc⟩
      refine ⟨Metric.mem_thickening_iff.2 ?_, hx⟩
      by_cases hh : x < l+ε
      · exact ⟨l, hl, by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hx.1]⟩
      · have hh' : l+w-ε < x := by
          by_contra h
          exact hc ⟨le_of_not_gt hh, le_of_not_gt h⟩
        exact ⟨l+w, hr, by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hx.2]⟩
  have hsub : Icc (l+ε) (l+w-ε) ⊆ Ioo l (l+w) := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  rw [he, measureReal_sdiff hsub measurableSet_Icc (by simp [Real.volume_Ioo]),
    Real.volume_real_Ioo, Real.volume_real_Icc]
  rw [show l+w-l = w by ring, max_eq_left hw,
    show l+w-ε-(l+ε) = w-2*ε by ring]
  by_cases h : w ≤ 2*ε
  · rw [min_eq_left h, max_eq_right (by linarith)]; ring
  · rw [min_eq_right (le_of_not_ge h), max_eq_left (by linarith)]; ring

private theorem tube_bounded {K : Set ℝ} {a b ε : ℝ}
    (hK : K ⊆ Icc a b) : Metric.thickening ε K ⊆ Ioo (a-ε) (b+ε) := by
  intro x hx
  obtain ⟨z, hz, hd⟩ := Metric.mem_thickening_iff.1 hx
  rw [Real.dist_eq, abs_lt] at hd
  constructor <;> linarith [(hK hz).1, (hK hz).2]

private theorem selected_gap_volume {K : Set ℝ} {l w : ℕ → ℝ}
    (he : ∀ n, l n ∈ K ∧ l n+w n ∈ K)
    (hg : ∀ n, Disjoint (Ioo (l n) (l n+w n)) K)
    (hd : Pairwise fun i j => Disjoint (Ioo (l i) (l i+w i)) (Ioo (l j) (l j+w j)))
    (hw : Summable w) (hn : ∀ n, 0 ≤ w n)
    (p : ℕ → Prop) [DecidablePred p] {ε : ℝ} (hε : 0 < ε) :
    volume.real (⋃ n, if p n then Metric.thickening ε K ∩ Ioo (l n) (l n+w n) else ∅) =
      ∑' n, if p n then min (w n) (2*ε) else 0 := by
  let s (n : ℕ) := if p n then Metric.thickening ε K ∩ Ioo (l n) (l n+w n) else ∅
  have hs (n : ℕ) : s n ⊆ Ioo (l n) (l n+w n) := by dsimp [s]; split_ifs <;> simp
  have hd' : Pairwise fun i j => Disjoint (s i) (s j) := fun i j hij => (hd hij).mono (hs i) (hs j)
  have hm (n : ℕ) : MeasurableSet (s n) := by
    dsimp [s]
    split_ifs
    · exact (Metric.isOpen_thickening.inter isOpen_Ioo).measurableSet
    · exact MeasurableSet.empty
  have hv (n : ℕ) : volume (s n) = ENNReal.ofReal (if p n then min (w n) (2*ε) else 0) := by
    by_cases hp : p n
    · have hf : volume (s n) ≠ ⊤ := measure_ne_top_of_subset (hs n) (by simp [Real.volume_Ioo])
      rw [← ENNReal.ofReal_toReal hf]
      congr 1
      simpa [s, hp, measureReal_def] using volume_thickening_inter_gap (he n).1 (he n).2 (hg n) (hn n) hε
    · simp [s, hp]
  have hn' (n : ℕ) : 0 ≤ if p n then min (w n) (2*ε) else 0 := by
    split_ifs
    · exact le_min (hn n) (by positivity)
    · exact le_rfl
  have hsum : Summable (fun n => if p n then min (w n) (2*ε) else 0) :=
    Summable.of_nonneg_of_le hn' (fun n => by
      split_ifs
      · exact min_le_left _ _
      · exact hn n) hw
  change (volume (⋃ n, s n)).toReal = _
  rw [measure_iUnion hd' hm]
  simp_rw [hv]
  rw [← ENNReal.ofReal_tsum_of_nonneg hn' hsum, ENNReal.toReal_ofReal (tsum_nonneg hn')]

private theorem crossing_unique {l w : ℕ → ℝ}
    (hd : Pairwise fun i j => Disjoint (Ioo (l i) (l i+w i)) (Ioo (l j) (l j+w j)))
    (y : ℝ) : {n | y ∈ Ico (l n) (l n+w n)}.Subsingleton := by
  intro i hi j hj
  by_contra hne
  let z := (y+min (l i+w i) (l j+w j))/2
  have hz : y < z := by dsimp [z]; linarith [lt_min hi.2 hj.2]
  have hzi : z < l i+w i := by
    dsimp [z]; linarith [hi.2, min_le_left (l i+w i) (l j+w j)]
  have hzj : z < l j+w j := by
    dsimp [z]; linarith [hj.2, min_le_right (l i+w i) (l j+w j)]
  exact Set.disjoint_left.1 (hd hne) ⟨hi.1.trans_lt hz, hzi⟩ ⟨hj.1.trans_lt hz, hzj⟩

/-- A spatial tail of the true metric tube is approximated by placing each
truncated gap at its left endpoint. The error is nonnegative and at most
`4*ε`, uniformly in the threshold. -/
theorem volume_thickening_tail_bounds {K : Set ℝ} {a b : ℝ} {l w : ℕ → ℝ}
    (hK : K = Icc a b \ ⋃ n, Ioo (l n) (l n+w n))
    (he : ∀ n, l n ∈ K ∧ l n+w n ∈ K)
    (hd : Pairwise fun i j => Disjoint (Ioo (l i) (l i+w i)) (Ioo (l j) (l j+w j)))
    (hw : Summable w) (hn : ∀ n, 0 ≤ w n) (hnull : volume K = 0)
    (y : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (∑' n, if y < l n then min (w n) (2*ε) else 0) ≤
        volume.real (Metric.thickening ε K ∩ Ioi y) ∧
    volume.real (Metric.thickening ε K ∩ Ioi y) ≤
        (∑' n, if y < l n then min (w n) (2*ε) else 0)+4*ε := by
  classical
  let T := Metric.thickening ε K
  let J := ⋃ n, if y < l n then T ∩ Ioo (l n) (l n+w n) else ∅
  let C := ⋃ n, if y ∈ Ico (l n) (l n+w n) then T ∩ Ioo (l n) (l n+w n) else ∅
  let O := Ioo (a-ε) a ∪ Ioo b (b+ε)
  have hsub : K ⊆ Icc a b := by rw [hK]; exact sdiff_subset
  have hab : a ≤ b := (hsub (he 0).1).1.trans (hsub (he 0).1).2
  have hTb : T ⊆ Ioo (a-ε) (b+ε) := tube_bounded hsub
  have hTf : volume T ≠ ⊤ := measure_ne_top_of_subset hTb (by simp [Real.volume_Ioo])
  have hg (n : ℕ) : Disjoint (Ioo (l n) (l n+w n)) K := by
    apply Set.disjoint_left.2
    intro z hz hzK
    rw [hK] at hzK
    exact hzK.2 (mem_iUnion.2 ⟨n,hz⟩)
  have hJ : volume.real J = ∑' n, if y < l n then min (w n) (2*ε) else 0 :=
    selected_gap_volume he hg hd hw hn _ hε
  have hJT : J ⊆ T ∩ Ioi y := by
    intro z hz
    obtain ⟨n, hn⟩ := mem_iUnion.1 hz
    split_ifs at hn with hp
    · exact ⟨hn.1, hp.trans hn.2.1⟩
    · exact False.elim hn
  have hCT : C ⊆ T := by
    intro z hz
    obtain ⟨n, hn⟩ := mem_iUnion.1 hz
    split_ifs at hn
    · exact hn.1
    · exact False.elim hn
  have hC : volume.real C ≤ 2*ε := by
    by_cases hh : ∃ n, y ∈ Ico (l n) (l n+w n)
    · obtain ⟨n, hn'⟩ := hh
      have hEq : C = T ∩ Ioo (l n) (l n+w n) := by
        apply Set.Subset.antisymm
        · intro z hz
          obtain ⟨m, hm⟩ := mem_iUnion.1 hz
          split_ifs at hm with hp
          · have := crossing_unique hd y hp hn'
            simpa only [this] using hm
          · exact False.elim hm
        · intro z hz
          exact mem_iUnion.2 ⟨n, by simpa only [if_pos hn'] using hz⟩
      rw [hEq, volume_thickening_inter_gap (he n).1 (he n).2 (hg n) (hn n) hε]
      exact min_le_right _ _
    · have hEq : C = ∅ := by
        ext z
        simp only [C, mem_iUnion, mem_empty_iff_false, iff_false, not_exists]
        intro n
        simp only [if_neg (fun h => hh ⟨n,h⟩), mem_empty_iff_false, not_false_eq_true]
      rw [hEq, measureReal_empty]
      positivity
  have hO : volume.real O ≤ 2*ε := by
    have h := measureReal_union_le (μ := volume) (Ioo (a-ε) a) (Ioo b (b+ε))
    simp only [Real.volume_real_Ioo, sub_sub_cancel, add_sub_cancel_left, max_eq_left hε.le] at h
    dsimp only [O]
    linarith
  have hupper : T ∩ Ioi y ⊆ J ∪ (K ∪ (O ∪ C)) := by
    rintro z ⟨hzT, hzy⟩
    by_cases hzK : z ∈ K
    · exact Or.inr (Or.inl hzK)
    by_cases hzI : z ∈ Icc a b
    · have hzg : z ∈ ⋃ n, Ioo (l n) (l n+w n) := by
        by_contra hh
        exact hzK (hK ▸ ⟨hzI, hh⟩)
      obtain ⟨n, hng⟩ := mem_iUnion.1 hzg
      by_cases hyl : y < l n
      · exact Or.inl (mem_iUnion.2 ⟨n, by simp only [if_pos hyl]; exact ⟨hzT,hng⟩⟩)
      · have hyc : y ∈ Ico (l n) (l n+w n) := ⟨le_of_not_gt hyl, hzy.trans hng.2⟩
        exact Or.inr (Or.inr (Or.inr (mem_iUnion.2 ⟨n, by
          simp only [if_pos hyc]; exact ⟨hzT,hng⟩⟩)))
    · have ho : z ∈ O := by
        have hz := hTb hzT
        by_cases hza : z < a
        · exact Or.inl ⟨hz.1,hza⟩
        · exact Or.inr ⟨by by_contra hh; exact hzI ⟨le_of_not_gt hza,le_of_not_gt hh⟩,hz.2⟩
      exact Or.inr (Or.inr (Or.inl ho))
  have hfin : volume (J ∪ (K ∪ (O ∪ C))) ≠ ⊤ := by
    apply measure_ne_top_of_subset (s := Icc (a-ε) (b+ε)) _ (by simp [Real.volume_Icc])
    intro z hz
    rcases hz with hz | hz | hz | hz
    · exact ⟨(hTb (hJT hz).1).1.le, (hTb (hJT hz).1).2.le⟩
    · constructor <;> linarith [(hsub hz).1,(hsub hz).2]
    · rcases hz with hz | hz <;> constructor <;> linarith [hz.1,hz.2]
    · exact ⟨(hTb (hCT hz)).1.le, (hTb (hCT hz)).2.le⟩
  constructor
  · rw [← hJ]
    exact measureReal_mono hJT (measure_ne_top_of_subset inter_subset_left hTf)
  · have h := measureReal_mono hupper hfin
    have h1 := measureReal_union_le (μ := volume) J (K ∪ (O ∪ C))
    have h2 := measureReal_union_le (μ := volume) K (O ∪ C)
    have h3 := measureReal_union_le (μ := volume) O C
    have hK0 : volume.real K = 0 := by simp [measureReal_def,hnull]
    rw [hJ] at h1
    linarith

end Problems.Juggler.BeattyPhase

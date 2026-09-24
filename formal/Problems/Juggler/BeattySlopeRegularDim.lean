import Problems.Juggler.BeattySlopeExactDim

/-!
# Regular slopes: the exact dimension `2/(2+ν)`

Suppose every convergent level of the slope `α` is good: there are
approximations `p_n/q_n` with `|q_n α - p_n| ≤ 1/q_(n+1)`, the best-approximation
separation `|mα - p| ≥ 1/(2q_n)` for `0 < m < q_n`, and growth
`q_(n+1) ≥ q_n^ν`. Then the complete cluster set `K_α` has Hausdorff
dimension at most `2/(2+ν)`.

The proof uses a multi-scale cover. A level-`n` cell is a phase interval of
length at most `4/q_n` without atoms of index below `q_n`. It is cut at its
atoms of index below `E = ⌊q_n^y⌋`. The gaps holding an atom of index below
`N_n = ⌊1/|θ_n|⌋` lie in at most seven chains and are covered directly; the
other gaps are level-`(n+1)` cells and are refined recursively. At each level
the cost exponent `σ` of a cell improves to `(3s + sνσ)/(2+s)`, and a bounded
number of levels pushes it above one exactly when `s > 2/(2+ν)`.

With the matching upper growth `q_(n+1) ≤ C q_n^ν`, the separation also gives
a uniform Diophantine bound of exponent `ν`, and the known Hölder lower bound
closes the equality `dim_H K_α = 2/(2+ν)`.
-/

namespace Problems.Juggler.BeattySlope

open Filter Topology Set MeasureTheory BeattyPhase Metric
open scoped NNReal ENNReal

/-! ### Covers built from phase intervals -/

/-- The profile increase across a phase interval `g`, from the right trace at
`g.1` to the left profile at `g.2`. -/
noncomputable def gapMass (φ w : ℕ → ℝ) (g : ℝ × ℝ) : ℝ :=
  jumpProfile φ w g.2 - jumpProfileRight φ w g.1

/-- A finite cover of the phase interval `(a,b)`: finitely many cut points
and nonempty phase intervals such that every uncut point of `(a,b)` lies
strictly inside one of the intervals, with total `s`-cost at most `c`. -/
def CellCover (φ w : ℕ → ℝ) (s a b c : ℝ) : Prop :=
  ∃ C : Finset ℝ, ∃ F : Finset (ℝ × ℝ), (∀ g ∈ F, g.1 < g.2) ∧
    (∀ x ∈ Ioo a b, x ∉ C → ∃ g ∈ F, g.1 < x ∧ x < g.2) ∧
    ∑ g ∈ F, gapMass φ w g ^ s ≤ c

/-- The mass across a nonempty phase interval is nonnegative. -/
theorem gapMass_nonneg {φ w : ℕ → ℝ} (hw : Summable w) (hn : ∀ n, 0 ≤ w n)
    {g : ℝ × ℝ} (hg : g.1 < g.2) : 0 ≤ gapMass φ w g :=
  sub_nonneg.2 (jumpProfileRight_le_of_lt hw hn hg)

/-- A cover can only get cheaper to certify: raising the budget keeps it. -/
theorem CellCover.mono {φ w : ℕ → ℝ} {s a b c c' : ℝ} (h : CellCover φ w s a b c)
    (hc : c ≤ c') : CellCover φ w s a b c' := by
  obtain ⟨C, F, h1, h2, h3⟩ := h
  exact ⟨C, F, h1, h2, h3.trans hc⟩

/-- One interval covers itself, at the cost of its own mass. -/
theorem cellCover_self (φ w : ℕ → ℝ) (s : ℝ) {a b : ℝ} (hab : a < b) :
    CellCover φ w s a b (gapMass φ w (a, b) ^ s) :=
  ⟨∅, {(a, b)}, by simpa using hab, fun x hx _ => ⟨(a, b), by simp, hx.1, hx.2⟩,
    by simp⟩

/-- Every uncut point of `[a,b]` lies strictly inside a gap of a cut set
containing both endpoints. -/
theorem exists_cutGap_Icc {C : Finset ℝ} {a b : ℝ} (ha : a ∈ C) (hb : b ∈ C)
    {x : ℝ} (hx : x ∈ Icc a b) (hxC : x ∉ C) :
    ∃ g ∈ cutGaps C, g.1 < x ∧ x < g.2 := by
  classical
  have hL : (C.filter (· < x)).Nonempty :=
    ⟨a, Finset.mem_filter.2 ⟨ha, lt_of_le_of_ne hx.1 (fun h => hxC (h ▸ ha))⟩⟩
  have hU : (C.filter (x < ·)).Nonempty :=
    ⟨b, Finset.mem_filter.2 ⟨hb, lt_of_le_of_ne hx.2 (fun h => hxC (h ▸ hb))⟩⟩
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

/-- A sum of nonnegative terms over a finite union is at most the sum of the
sums over the pieces. -/
theorem sum_biUnion_le_of_nonneg {ι κ : Type*} [DecidableEq κ] (G : Finset ι)
    (F : ι → Finset κ) {f : κ → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ G.biUnion F, f x ≤ ∑ g ∈ G, ∑ x ∈ F g, f x := by
  classical
  induction G using Finset.induction_on with
  | empty => simp
  | insert a G ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have h := Finset.sum_union_inter (s₁ := F a) (s₂ := G.biUnion F) (f := f)
    have h0 : 0 ≤ ∑ x ∈ F a ∩ G.biUnion F, f x := Finset.sum_nonneg fun x _ => hf x
    linarith

/-- Covers of all gaps of a cut set of `[a,b]` containing both endpoints
combine into a cover of `(a,b)` whose cost is the sum of their costs. -/
theorem cellCover_of_gaps {φ w : ℕ → ℝ} {s a b : ℝ} (hw : Summable w)
    (hn : ∀ n, 0 ≤ w n) {C : Finset ℝ} (ha : a ∈ C) (hb : b ∈ C)
    (c : ℝ × ℝ → ℝ) (h : ∀ g ∈ cutGaps C, CellCover φ w s g.1 g.2 (c g)) :
    CellCover φ w s a b (∑ g ∈ cutGaps C, c g) := by
  classical
  choose! D F hF hcov hcost using h
  refine ⟨C ∪ (cutGaps C).biUnion D, (cutGaps C).biUnion F, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, hgF⟩ := Finset.mem_biUnion.1 hg
    exact hF g0 hg0 g hgF
  · intro x hx hxC
    have hxC' : x ∉ C := fun h => hxC (Finset.mem_union_left _ h)
    obtain ⟨g0, hg0, h1, h2⟩ := exists_cutGap_Icc ha hb (Ioo_subset_Icc_self hx) hxC'
    have hxD : x ∉ D g0 := fun h =>
      hxC (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨g0, hg0, h⟩))
    obtain ⟨g, hg, hg1, hg2⟩ := hcov g0 hg0 x ⟨h1, h2⟩ hxD
    exact ⟨g, Finset.mem_biUnion.2 ⟨g0, hg0, hg⟩, hg1, hg2⟩
  · have hnn : ∀ g : ℝ × ℝ, 0 ≤ (max (gapMass φ w g) 0) ^ s := fun g =>
      Real.rpow_nonneg (le_max_right _ _) s
    have heq : ∀ g ∈ (cutGaps C).biUnion F,
        gapMass φ w g ^ s = (max (gapMass φ w g) 0) ^ s := by
      intro g hg
      obtain ⟨g0, hg0, hgF⟩ := Finset.mem_biUnion.1 hg
      rw [max_eq_left (gapMass_nonneg hw hn (hF g0 hg0 g hgF))]
    rw [Finset.sum_congr rfl heq]
    refine (sum_biUnion_le_of_nonneg _ F hnn).trans (Finset.sum_le_sum fun g0 hg0 => ?_)
    refine le_of_eq_of_le (Finset.sum_congr rfl fun g hg => ?_) (hcost g0 hg0)
    rw [max_eq_left (gapMass_nonneg hw hn (hF g0 hg0 g hg))]

/-- Covers of the unit phase interval of arbitrarily small cost force zero
`s`-dimensional Hausdorff measure of the jump range. -/
theorem cellCover_hausdorff_zero {φ w : ℕ → ℝ} (hw : Summable w)
    (hn : ∀ n, 0 ≤ w n) (hi : Function.Injective φ)
    (hp : ∀ n, φ n ∈ Ioo (0 : ℝ) 1) {s : ℝ} (hs : 0 < s)
    (h : ∀ ε : ℝ, 0 < ε → CellCover φ w s 0 1 ε) :
    Measure.hausdorffMeasure s (jumpRange φ w) = 0 := by
  classical
  choose C F hF hcov hcost using fun n : ℕ =>
    h (min (1 / ((n : ℝ) + 1)) ((1 / ((n : ℝ) + 1)) ^ s))
      (lt_min (by positivity) (Real.rpow_pos_of_pos (by positivity) s))
  set P := jumpProfile φ w
  set R := jumpProfileRight φ w
  let C' : ℕ → Finset ℝ := fun n => insert 0 (insert 1 (C n))
  let ι : ℕ → Type := fun n => ↥(C' n) ⊕ ↥(C' n) ⊕ ↥(F n)
  let t : ∀ n, ι n → Set ℝ := fun n => Sum.elim (fun c => {P c})
    (Sum.elim (fun c => {R c}) (fun g => Icc (R g.1.1) (P g.1.2)))
  let r : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (1 / ((n : ℝ) + 1))
  have hr : Tendsto r atTop (𝓝 0) := by
    have hh : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hc := (ENNReal.continuous_ofReal.tendsto 0).comp hh
    simpa only [r, Function.comp_def, ENNReal.ofReal_zero] using hc
  have hmass (n : ℕ) (g : ℝ × ℝ) (hg : g ∈ F n) : 0 ≤ P g.2 - R g.1 :=
    gapMass_nonneg hw hn (hF n g hg)
  have hone (n : ℕ) (g : ℝ × ℝ) (hg : g ∈ F n) : P g.2 - R g.1 ≤ 1 / ((n : ℝ) + 1) := by
    have hnn : ∀ g ∈ F n, 0 ≤ gapMass φ w g ^ s := fun g hg =>
      Real.rpow_nonneg (gapMass_nonneg hw hn (hF n g hg)) s
    have h1 : gapMass φ w g ^ s ≤ (1 / ((n : ℝ) + 1)) ^ s :=
      (Finset.single_le_sum hnn hg).trans ((hcost n).trans (min_le_right _ _))
    exact (Real.rpow_le_rpow_iff (gapMass_nonneg hw hn (hF n g hg)) (by positivity) hs).1 h1
  have ht (n : ℕ) (i : ι n) : ediam (t n i) ≤ r n := by
    rcases i with c | c | g
    · simp [t]
    · simp [t]
    · simp only [t, Sum.elim_inr, Real.ediam_Icc]
      exact ENNReal.ofReal_le_ofReal (hone n g.1 g.2)
  have hcover (n : ℕ) : jumpRange φ w ⊆ ⋃ i, t n i := by
    intro y hy
    obtain ⟨x, hx, hl, hrr⟩ := jumpRange_bracket hw hn hp hy.1
    by_cases hxC : x ∈ C' n
    · rcases jumpRange_eq_of_bracket hw hn hi hy hl hrr with h | h
      · exact mem_iUnion.2 ⟨Sum.inl ⟨x, hxC⟩, h⟩
      · exact mem_iUnion.2 ⟨Sum.inr (Sum.inl ⟨x, hxC⟩), h⟩
    · have hx0 : x ≠ 0 := fun h => hxC (h ▸ Finset.mem_insert_self _ _)
      have hx1 : x ≠ 1 := fun h =>
        hxC (h ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      have hxc : x ∉ C n := fun h =>
        hxC (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
      obtain ⟨g, hg, hg1, hg2⟩ := hcov n x
        ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), lt_of_le_of_ne hx.2 hx1⟩ hxc
      refine mem_iUnion.2 ⟨Sum.inr (Sum.inr ⟨g, hg⟩), ?_, ?_⟩
      · exact (jumpProfileRight_le_of_lt hw hn hg1).trans hl
      · exact hrr.trans (jumpProfileRight_le_of_lt hw hn hg2)
  have hbound (n : ℕ) : (∑ i, ediam (t n i) ^ s) ≤ r n := by
    change ∑ i : ↥(C' n) ⊕ ↥(C' n) ⊕ ↥(F n), ediam (t n i) ^ s ≤ r n
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [t, Sum.elim_inl, Sum.elim_inr, ediam_singleton,
      ENNReal.zero_rpow_of_pos hs, Finset.sum_const_zero, zero_add, Real.ediam_Icc]
    rw [Finset.sum_coe_sort (F n) (fun g => ENNReal.ofReal (P g.2 - R g.1) ^ s)]
    calc
      _ = ∑ g ∈ F n, ENNReal.ofReal ((P g.2 - R g.1) ^ s) := by
        apply Finset.sum_congr rfl
        intro g hg
        exact ENNReal.ofReal_rpow_of_nonneg (hmass n g hg) hs.le
      _ = ENNReal.ofReal (∑ g ∈ F n, (P g.2 - R g.1) ^ s) :=
        (ENNReal.ofReal_sum_of_nonneg fun g hg =>
          Real.rpow_nonneg (hmass n g hg) s).symm
      _ ≤ r n := ENNReal.ofReal_le_ofReal ((hcost n).trans (min_le_left _ _))
  have hle := Measure.hausdorffMeasure_le_liminf_sum s (jumpRange φ w) r hr t
    (Eventually.of_forall ht) (Eventually.of_forall hcover)
  apply le_antisymm _ bot_le
  calc
    _ ≤ _ := hle
    _ ≤ liminf r atTop := liminf_le_liminf (Eventually.of_forall hbound)
    _ = 0 := hr.liminf_eq

/-! ### Separated orbit points in short intervals -/

/-- A finite set of reals in `[a,b]` with pairwise distances at least `δ`
has at most `(b-a)/δ + 1` points. -/
theorem card_le_of_separated {a δ : ℝ} (hδ : 0 < δ) :
    ∀ (S : Finset ℝ) (b : ℝ), a - δ ≤ b → (∀ x ∈ S, a ≤ x ∧ x ≤ b) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ |x - y|) → (S.card : ℝ) ≤ (b - a) / δ + 1 := by
  classical
  intro S
  induction S using Finset.induction_on_max with
  | empty =>
    intro b hb _ _
    have : -1 ≤ (b - a) / δ := by rw [le_div_iff₀ hδ]; linarith
    simp only [Finset.card_empty, Nat.cast_zero]
    linarith
  | insert m S hlt ih =>
    intro b _ hS hsep
    have hmS : m ∉ S := fun h => lt_irrefl _ (hlt m h)
    have hm := hS m (Finset.mem_insert_self _ _)
    have hS' : ∀ x ∈ S, a ≤ x ∧ x ≤ m - δ := by
      intro x hx
      have h1 := hsep x (Finset.mem_insert_of_mem hx) m (Finset.mem_insert_self _ _)
        (ne_of_lt (hlt x hx))
      rw [abs_of_neg (sub_neg.2 (hlt x hx))] at h1
      exact ⟨(hS x (Finset.mem_insert_of_mem hx)).1, by linarith⟩
    have hih := ih (m - δ) (by linarith [hm.1]) hS' fun x hx y hy hxy =>
      hsep x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy
    rw [Finset.card_insert_of_notMem hmS]
    push_cast
    have e : (m - δ - a) / δ + 1 = (m - a) / δ := by field_simp; ring
    have e2 : (m - a) / δ ≤ (b - a) / δ := div_le_div_of_nonneg_right (by linarith [hm.2]) hδ.le
    linarith

/-- Orbit phases whose indices differ by less than `Q` are at least `δ`
apart, when `|m*α - p| ≥ δ` for all `0 < m < Q`. -/
theorem phase_separated {φ : ℕ → ℝ} {α δ : ℝ}
    (hfr : ∀ k : ℕ, φ k = Int.fract (((k : ℝ) + 1) * α)) {Q : ℕ}
    (hsep : ∀ m : ℕ, 0 < m → m < Q → ∀ p : ℤ, δ ≤ |(m : ℝ) * α - p|)
    {k k' : ℕ} (hkk : k' < k) (hQ : k < k' + Q) : δ ≤ |φ k - φ k'| := by
  have h := hsep (k - k') (by omega) (by omega)
    (⌊((k : ℝ) + 1) * α⌋ - ⌊((k' : ℝ) + 1) * α⌋)
  rw [hfr, hfr, Int.fract, Int.fract]
  have e : ((k - k' : ℕ) : ℝ) = (k : ℝ) - k' := by
    rw [Nat.cast_sub hkk.le]
  rw [e] at h
  push_cast at h
  convert h using 2
  ring

/-- A phase interval of length at most `L` contains at most `L/δ + 1` orbit
points from any block of `Q` consecutive indices. -/
theorem block_count_le {φ : ℕ → ℝ} {α δ L : ℝ} (hδ : 0 < δ)
    (hfr : ∀ k : ℕ, φ k = Int.fract (((k : ℝ) + 1) * α)) {Q : ℕ}
    (hsep : ∀ m : ℕ, 0 < m → m < Q → ∀ p : ℤ, δ ≤ |(m : ℝ) * α - p|)
    {a b : ℝ} (hab : a ≤ b) (hL : b - a ≤ L) (t : ℕ) :
    (((Finset.range Q).filter (fun j => φ (t + j) ∈ Ioo a b)).card : ℝ) ≤ L / δ + 1 := by
  classical
  set J := (Finset.range Q).filter (fun j => φ (t + j) ∈ Ioo a b)
  have hinj : Set.InjOn (fun j => φ (t + j)) J := by
    intro j hj j' hj' he
    by_contra hne
    have hj1 := Finset.mem_range.1 (Finset.mem_filter.1 hj).1
    have hj2 := Finset.mem_range.1 (Finset.mem_filter.1 hj').1
    rcases lt_or_gt_of_ne hne with h | h
    · have := phase_separated hfr hsep (k := t + j') (k' := t + j) (by omega) (by omega)
      simp only at he
      rw [he, sub_self, abs_zero] at this
      linarith
    · have := phase_separated hfr hsep (k := t + j) (k' := t + j') (by omega) (by omega)
      simp only at he
      rw [he, sub_self, abs_zero] at this
      linarith
  rw [← Finset.card_image_of_injOn hinj]
  have hc := card_le_of_separated (a := a) hδ (J.image fun j => φ (t + j)) b (by linarith)
    (by
      intro x hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hx
      exact ⟨(Finset.mem_filter.1 hj).2.1.le, (Finset.mem_filter.1 hj).2.2.le⟩)
    (by
      intro x hx y hy hxy
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨j', hj', rfl⟩ := Finset.mem_image.1 hy
      have hj1 := Finset.mem_range.1 (Finset.mem_filter.1 hj).1
      have hj2 := Finset.mem_range.1 (Finset.mem_filter.1 hj').1
      rcases lt_trichotomy j j' with h | h | h
      · rw [abs_sub_comm]
        exact phase_separated hfr hsep (by omega) (by omega)
      · exact absurd (by rw [h]) hxy
      · exact phase_separated hfr hsep (by omega) (by omega))
  exact hc.trans (by gcongr)

/-- Partial sums of `(M+k+1)^(-3/2)` over `k` are at most `2 M^(-1/2)`. -/
theorem sum_range_three_halves_le {M : ℕ} (hM : 0 < M) (K : ℕ) :
    ∑ k ∈ Finset.range K, 1 / ((M : ℝ) + k + 1) ^ (3/2 : ℝ) ≤
      2 * (M : ℝ) ^ (-(1/2) : ℝ) := by
  classical
  set v : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) ^ (3/2 : ℝ)
  have hv0 : ∀ n, 0 ≤ v n := fun n => by positivity
  have hvs : Summable v := by
    have h := (summable_nat_add_iff 1).2
      (Real.summable_one_div_nat_rpow.2 (by norm_num : (1 : ℝ) < 3/2))
    refine h.congr fun n => ?_
    simp [v]
  have ht := tailMass_le hvs hv0 zero_le_one (fun n => by simp [v]) hM
  have hs : Summable (fun n => if M ≤ n then v n else 0) :=
    hvs.of_norm_bounded fun n => by
      split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg (hv0 n), hv0 n]
  have hle : ∑ k ∈ Finset.range K, 1 / ((M : ℝ) + k + 1) ^ (3/2 : ℝ) ≤ tailMass v M := by
    unfold tailMass
    have h1 := hs.sum_le_tsum ((Finset.range K).image (M + ·))
      (fun n _ => by split_ifs <;> simp [hv0 n])
    rw [Finset.sum_image (fun x _ y _ h => by simpa using h)] at h1
    refine le_of_eq_of_le (Finset.sum_congr rfl fun k _ => ?_) h1
    simp [v]
  linarith

/-- Orbit mass in a phase interval beyond index `M`: if every block of `Q`
consecutive indices puts at most `P` points in `(a,b)`, and `Q ≤ M`, the
atoms of index at least `M` in `(a,b)` weigh at most `3PB/(Q√M)`. -/
theorem cell_tail_le {φ w : ℕ → ℝ} (hn : ∀ n, 0 ≤ w n) {B : ℝ}
    (hb : ∀ n, w n ≤ B / ((n : ℝ) + 1) ^ (3/2 : ℝ)) {a b P : ℝ} {Q M : ℕ} (hQ : 0 < Q)
    (hQM : Q ≤ M)
    (hcount : ∀ t, (((Finset.range Q).filter (fun j => φ (t + j) ∈ Ioo a b)).card : ℝ) ≤ P) :
    ∑' k, (if φ k ∈ Ioo a b ∧ M ≤ k then w k else 0) ≤
      3 * P * B * ((Q : ℝ)⁻¹ * (M : ℝ) ^ (-(1/2) : ℝ)) := by
  classical
  have hB : 0 ≤ B := by
    have := (hn 0).trans (hb 0)
    have hp : (0 : ℝ) < ((0 : ℕ) + 1 : ℝ) ^ (3/2 : ℝ) := by positivity
    exact (div_nonneg_iff.1 this).elim (fun h => h.1) fun h => absurd h.2 (not_le.2 hp)
  have hP : 0 ≤ P := (Nat.cast_nonneg _).trans (hcount 0)
  have hM : 0 < M := lt_of_lt_of_le hQ hQM
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  set f : ℕ → ℝ := fun k => if φ k ∈ Ioo a b ∧ M ≤ k then w k else 0 with hfdef
  have hf0 : ∀ k, 0 ≤ f k := fun k => by simp only [f]; split_ifs <;> simp [hn k]
  have hblock : ∀ t : ℕ, ∑ j ∈ Finset.range Q, f (t + j) ≤
      P * (B / ((t : ℝ) + 1) ^ (3/2 : ℝ)) := by
    intro t
    calc
      _ ≤ ∑ j ∈ Finset.range Q,
          (if φ (t + j) ∈ Ioo a b then B / ((t : ℝ) + 1) ^ (3/2 : ℝ) else 0) := by
        apply Finset.sum_le_sum
        intro j _
        by_cases h : φ (t + j) ∈ Ioo a b
        · rw [if_pos h]
          refine (show f (t + j) ≤ w (t + j) by
            simp only [f]; split_ifs <;> simp [hn]).trans ((hb _).trans ?_)
          apply div_le_div_of_nonneg_left hB (by positivity)
          apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
          push_cast
          linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
        · rw [if_neg h]
          simp only [f]
          rw [if_neg (fun hh => h hh.1)]
      _ = (((Finset.range Q).filter (fun j => φ (t + j) ∈ Ioo a b)).card : ℝ) *
          (B / ((t : ℝ) + 1) ^ (3/2 : ℝ)) := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (hcount t) (by positivity)
  set u : ℕ → ℝ := fun k => 1 / ((M : ℝ) + k + 1) ^ (3/2 : ℝ) with hudef
  have hind : ∀ T : ℕ, ∑ k ∈ Finset.range ((T + 1) * Q), f (M + k) ≤
      P * B * (1 / ((M : ℝ) + 1) ^ (3/2 : ℝ) +
        (Q : ℝ)⁻¹ * ∑ k ∈ Finset.range (T * Q), u k) := by
    intro T
    induction T with
    | zero =>
      simp only [zero_add, one_mul, zero_mul, Finset.range_zero, Finset.sum_empty, mul_zero,
        add_zero]
      refine (hblock M).trans (le_of_eq ?_)
      ring
    | succ T ih =>
      have hsplit : ∑ k ∈ Finset.range ((T + 1 + 1) * Q), f (M + k) =
          ∑ k ∈ Finset.range ((T + 1) * Q), f (M + k) +
            ∑ j ∈ Finset.range Q, f (M + (T + 1) * Q + j) := by
        rw [show (T + 1 + 1) * Q = (T + 1) * Q + Q by ring, Finset.sum_range_add]
        exact congrArg _ (Finset.sum_congr rfl fun j _ => by rw [add_assoc])
      have husplit : ∑ k ∈ Finset.range ((T + 1) * Q), u k =
          ∑ k ∈ Finset.range (T * Q), u k + ∑ j ∈ Finset.range Q, u (T * Q + j) := by
        rw [show (T + 1) * Q = T * Q + Q by ring, Finset.sum_range_add]
      rw [hsplit, husplit]
      have hb2 := hblock (M + (T + 1) * Q)
      have hcmp : (Q : ℝ) * (1 / (((M + (T + 1) * Q : ℕ) : ℝ) + 1) ^ (3/2 : ℝ)) ≤
          ∑ j ∈ Finset.range Q, u (T * Q + j) := by
        have : ∀ j ∈ Finset.range Q, 1 / (((M + (T + 1) * Q : ℕ) : ℝ) + 1) ^ (3/2 : ℝ) ≤
            u (T * Q + j) := by
          intro j hj
          have hjQ : (j : ℝ) < Q := by exact_mod_cast Finset.mem_range.1 hj
          simp only [u]
          apply div_le_div_of_nonneg_left zero_le_one (by positivity)
          apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
          push_cast
          linarith
        have h2 := Finset.sum_le_sum this
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h2
        exact h2
      have hQi : (Q : ℝ)⁻¹ * (Q : ℝ) = 1 := inv_mul_cancel₀ hQR.ne'
      have key : P * (B / (((M + (T + 1) * Q : ℕ) : ℝ) + 1) ^ (3/2 : ℝ)) ≤
          P * B * ((Q : ℝ)⁻¹ * ∑ j ∈ Finset.range Q, u (T * Q + j)) := by
        have e : P * (B / (((M + (T + 1) * Q : ℕ) : ℝ) + 1) ^ (3/2 : ℝ)) =
            P * B * ((Q : ℝ)⁻¹ * ((Q : ℝ) *
              (1 / (((M + (T + 1) * Q : ℕ) : ℝ) + 1) ^ (3/2 : ℝ)))) := by
          rw [← mul_assoc ((Q : ℝ)⁻¹), hQi]
          ring
        rw [e]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hcmp (inv_nonneg.2 hQR.le)) (mul_nonneg hP hB)
      nlinarith [hb2, ih, key]
  have hpart : ∀ n : ℕ, ∑ k ∈ Finset.range n, f k ≤
      P * B * (1 / ((M : ℝ) + 1) ^ (3/2 : ℝ) + (Q : ℝ)⁻¹ * (2 * (M : ℝ) ^ (-(1/2) : ℝ))) := by
    intro n
    have hsub : Finset.range n ⊆ Finset.range (M + (n + 1) * Q) := by
      apply Finset.range_subset_range.2
      nlinarith
    calc
      _ ≤ ∑ k ∈ Finset.range (M + (n + 1) * Q), f k :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => hf0 k
      _ = ∑ k ∈ Finset.range ((n + 1) * Q), f (M + k) := by
        rw [Finset.sum_range_add, Finset.sum_eq_zero (fun k hk => ?_), zero_add]
        have hk' : ¬ M ≤ k := not_le.2 (Finset.mem_range.1 hk)
        simp [f, hk']
      _ ≤ _ := (hind n).trans (by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hP hB)
        apply add_le_add_right
        exact mul_le_mul_of_nonneg_left (sum_range_three_halves_le hM _)
          (inv_nonneg.2 hQR.le))
  have hfirst : 1 / ((M : ℝ) + 1) ^ (3/2 : ℝ) ≤ (Q : ℝ)⁻¹ * (M : ℝ) ^ (-(1/2) : ℝ) := by
    have h1 : (M : ℝ) ^ (3/2 : ℝ) = M * (M : ℝ) ^ (1/2 : ℝ) := by
      rw [show (3/2 : ℝ) = 1 + 1/2 by norm_num, Real.rpow_add hMR, Real.rpow_one]
    have h2 : (M : ℝ) ^ (-(1/2) : ℝ) = ((M : ℝ) ^ (1/2 : ℝ))⁻¹ := Real.rpow_neg hMR.le _
    have hs0 : 0 < (M : ℝ) ^ (1/2 : ℝ) := Real.rpow_pos_of_pos hMR _
    have hQM' : (Q : ℝ) ≤ M := by exact_mod_cast hQM
    calc
      1 / ((M : ℝ) + 1) ^ (3/2 : ℝ) ≤ 1 / (M : ℝ) ^ (3/2 : ℝ) :=
        div_le_div_of_nonneg_left zero_le_one (Real.rpow_pos_of_pos hMR _)
          (Real.rpow_le_rpow hMR.le (by linarith) (by norm_num))
      _ = (M : ℝ)⁻¹ * ((M : ℝ) ^ (1/2 : ℝ))⁻¹ := by rw [h1]; field_simp
      _ ≤ (Q : ℝ)⁻¹ * ((M : ℝ) ^ (1/2 : ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_right (inv_anti₀ hQR hQM') (inv_nonneg.2 hs0.le)
      _ = _ := by rw [h2]
  refine (Real.tsum_le_of_sum_range_le hf0 hpart).trans ?_
  have e : 3 * P * B * ((Q : ℝ)⁻¹ * (M : ℝ) ^ (-(1/2) : ℝ)) =
      P * B * ((Q : ℝ)⁻¹ * (M : ℝ) ^ (-(1/2) : ℝ) +
        (Q : ℝ)⁻¹ * (2 * (M : ℝ) ^ (-(1/2) : ℝ))) := by ring
  rw [e]
  exact mul_le_mul_of_nonneg_left (add_le_add_left hfirst _) (mul_nonneg hP hB)

/-! ### Chains inside a cell and short gaps -/

/-- Two middle atoms of one chain inside `(a,b)` lie in the same gap of any
cut set whose cuts are outside `(a,b)` or early phases. -/
theorem chain_same_cell_gap {φ : ℕ → ℝ} (hi : Function.Injective φ)
    {Z : ℕ → ℤ} {q : ℕ} {θ : ℝ} (hq : 0 < q) (hθ : θ ≠ 0)
    (hφ : ∀ k, (q : ℝ) * φ k = Z k + ((k : ℝ) + 1) * θ)
    {E N : ℕ} (hN : (N : ℝ) * |θ| ≤ 1) {C : Finset ℝ} {a b : ℝ}
    (hC : ∀ e ∈ C, e ≤ a ∨ b ≤ e ∨ ∃ k < E, φ k = e) {g g' : ℝ × ℝ}
    (hg : g ∈ cutGaps C) (hg' : g' ∈ cutGaps C)
    {m m' : ℕ} (hEm : E ≤ m) (hmN : m < N) (hEm' : E ≤ m') (hmN' : m' < N)
    (hZ : Z m = Z m') (ha : a < φ m) (hb : φ m < b) (ha' : a < φ m') (hb' : φ m' < b)
    (h1 : g.1 < φ m) (h2 : φ m < g.2) (h1' : g'.1 < φ m') (h2' : φ m' < g'.2) :
    g = g' := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have habs : 0 < |θ| := abs_pos.2 hθ
  apply cutGap_eq_of_no_cut hg hg' ⟨h1, h2⟩ ⟨h1', h2'⟩
  intro e he
  rcases hC e he with h | h | ⟨k, hk, rfl⟩
  · exact ⟨fun _ => by linarith, fun _ => by linarith⟩
  · constructor <;> intro h' <;> linarith
  · have hkm : k < m := lt_of_lt_of_le hk hEm
    have hkm' : k < m' := lt_of_lt_of_le hk hEm'
    have hc (j : ℕ) (hj : j < N) : ((j : ℝ) - k) * |θ| < 1 := by
      have hjN : (j : ℝ) < N := by exact_mod_cast hj
      have : (j : ℝ) - k < N := by linarith [Nat.cast_nonneg (α := ℝ) k]
      exact (mul_lt_mul_of_pos_right this habs).trans_le hN
    have n1 := chain_no_cut_between hqR hφ hkm hkm' hZ (hc m hmN) (hc m' hmN')
    have n2 := chain_no_cut_between hqR hφ hkm' hkm hZ.symm (hc m' hmN') (hc m hmN)
    have ne1 : φ k ≠ φ m := fun h => (Nat.ne_of_lt hkm) (hi h)
    have ne2 : φ k ≠ φ m' := fun h => (Nat.ne_of_lt hkm') (hi h)
    constructor
    · intro h
      by_contra h'
      push Not at h'
      exact n2 ⟨h', lt_of_le_of_ne h ne1⟩
    · intro h
      by_contra h'
      push Not at h'
      exact n1 ⟨h', lt_of_le_of_ne h ne2⟩

open Classical in
/-- Inside a phase interval `(a,b)`, the gaps of a cut set of early phases
that contain a middle atom number at most `q(b-a) + 3`: one per chain label. -/
theorem card_mid_gaps_le {φ : ℕ → ℝ} (hi : Function.Injective φ)
    {Z : ℕ → ℤ} {q : ℕ} {θ : ℝ} (hq : 0 < q) (hθ : θ ≠ 0)
    (hφ : ∀ k, (q : ℝ) * φ k = Z k + ((k : ℝ) + 1) * θ)
    {E N : ℕ} (hN : (N : ℝ) * |θ| ≤ 1) {C : Finset ℝ} {a b : ℝ} (hab : a ≤ b)
    (hCab : ∀ e ∈ C, a ≤ e ∧ e ≤ b)
    (hC : ∀ e ∈ C, e ≤ a ∨ b ≤ e ∨ ∃ k < E, φ k = e) :
    ((((cutGaps C).filter fun g => ∃ m, E ≤ m ∧ m < N ∧ g.1 < φ m ∧ φ m < g.2).card : ℕ)
      : ℝ) ≤ q * (b - a) + 3 := by
  classical
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  set G := (cutGaps C).filter fun g => ∃ m, E ≤ m ∧ m < N ∧ g.1 < φ m ∧ φ m < g.2
  set L : Finset ℤ := Finset.Icc ⌈(q : ℝ) * a - 1⌉ ⌊(q : ℝ) * b + 1⌋
  let T : ℤ → Finset (ℝ × ℝ) := fun z =>
    G.filter fun g => ∃ m, E ≤ m ∧ m < N ∧ g.1 < φ m ∧ φ m < g.2 ∧ Z m = z
  have hin : ∀ g ∈ G, ∀ m, g.1 < φ m → φ m < g.2 → a < φ m ∧ φ m < b := by
    intro g hg m h1 h2
    have hg' := (Finset.mem_filter.1 hg).1
    obtain ⟨c1, c2, -, -⟩ := mem_cutGaps.1 hg'
    exact ⟨(hCab _ c1).1.trans_lt h1, h2.trans_le (hCab _ c2).2⟩
  have hsub : G ⊆ L.biUnion T := by
    intro g hg
    obtain ⟨m, hEm, hmN, h1, h2⟩ := (Finset.mem_filter.1 hg).2
    obtain ⟨ha, hb⟩ := hin g hg m h1 h2
    have hm1 : ((m : ℝ) + 1) * |θ| ≤ 1 := by
      have : (m : ℝ) + 1 ≤ N := by exact_mod_cast hmN
      exact (mul_le_mul_of_nonneg_right this (abs_nonneg θ)).trans hN
    have hA : -(((m : ℝ) + 1) * |θ|) ≤ ((m : ℝ) + 1) * θ := by
      have := neg_abs_le θ
      nlinarith
    have hB : ((m : ℝ) + 1) * θ ≤ ((m : ℝ) + 1) * |θ| := by
      have := le_abs_self θ
      nlinarith
    have hZe := hφ m
    have hqa : (q : ℝ) * a < q * φ m := mul_lt_mul_of_pos_left ha hqR
    have hqb : (q : ℝ) * φ m < q * b := mul_lt_mul_of_pos_left hb hqR
    have hz1 : (q : ℝ) * a - 1 < Z m := by linarith
    have hz2 : (Z m : ℝ) < q * b + 1 := by linarith
    refine Finset.mem_biUnion.2 ⟨Z m, Finset.mem_Icc.2 ⟨Int.ceil_le.2 hz1.le,
      Int.le_floor.2 hz2.le⟩, Finset.mem_filter.2 ⟨hg, m, hEm, hmN, h1, h2, rfl⟩⟩
  have hone : ∀ z ∈ L, (T z).card ≤ 1 := by
    intro z _
    apply Finset.card_le_one.2
    intro g hg g' hg'
    obtain ⟨hgG, m, hEm, hmN, h1, h2, hz⟩ := Finset.mem_filter.1 hg
    obtain ⟨hgG', m', hEm', hmN', h1', h2', hz'⟩ := Finset.mem_filter.1 hg'
    obtain ⟨ha, hb⟩ := hin g hgG m h1 h2
    obtain ⟨ha', hb'⟩ := hin g' hgG' m' h1' h2'
    exact chain_same_cell_gap hi hq hθ hφ hN hC (Finset.mem_filter.1 hgG).1
      (Finset.mem_filter.1 hgG').1 hEm hmN hEm' hmN' (hz.trans hz'.symm) ha hb ha' hb'
      h1 h2 h1' h2'
  have hcard : G.card ≤ L.card :=
    (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans
      ((Finset.sum_le_sum hone).trans (by simp)))
  have hL : (L.card : ℝ) ≤ q * (b - a) + 3 := by
    simp only [L, Int.card_Icc]
    have e1 := Int.le_ceil ((q : ℝ) * a - 1)
    have e2 := Int.floor_le ((q : ℝ) * b + 1)
    have e3 := Int.ceil_lt_add_one ((q : ℝ) * a - 1)
    have hqab : 0 ≤ (q : ℝ) * (b - a) := mul_nonneg hqR.le (by linarith)
    rcases le_or_gt 0 (⌊(q : ℝ) * b + 1⌋ + 1 - ⌈(q : ℝ) * a - 1⌉) with h | h
    · have := Int.toNat_of_nonneg h
      have h' : ((⌊(q : ℝ) * b + 1⌋ + 1 - ⌈(q : ℝ) * a - 1⌉).toNat : ℝ) =
          ((⌊(q : ℝ) * b + 1⌋ + 1 - ⌈(q : ℝ) * a - 1⌉ : ℤ) : ℝ) := by
        exact_mod_cast this
      rw [h']
      push_cast
      nlinarith
    · rw [Int.toNat_of_nonpos h.le]
      simp only [Nat.cast_zero]
      linarith
  exact (Nat.cast_le.2 hcard).trans hL

/-- A phase interval inside `[0,1]` holding no orbit point `fract(nα)` with
`0 < n < q` has length at most `4/q`, for a reduced `p/q` with
`|α - p/q| ≤ 1/q^2`. -/
theorem gap_short_of_approx {φ : ℕ → ℝ} {α : ℝ}
    (hfr : ∀ k : ℕ, φ k = Int.fract (((k : ℝ) + 1) * α)) {p : ℤ} {q : ℕ} (hq : 0 < q)
    (hcop : Nat.Coprime p.natAbs q) (happ : |α - p / q| ≤ 1 / (q : ℝ) ^ 2)
    {c d : ℝ} (hc : 0 ≤ c) (hd : d ≤ 1) (hno : ∀ k : ℕ, k + 1 < q → φ k ∉ Ioo c d) :
    d - c ≤ 4 / q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  by_contra hlt
  push Not at hlt
  set r : ℚ := (p : ℚ) / (q : ℤ)
  have hden : (r.den : ℤ) = q := by
    have := Rat.den_div_eq_of_coprime (a := p) (b := (q : ℤ)) (by exact_mod_cast hq)
      (by simpa using hcop)
    exact this
  have hden' : (r.den : ℝ) = q := by exact_mod_cast hden
  have hr : (r : ℝ) = p / q := by simp [r]
  have hw : 4 < (r.den : ℝ) * (d - c) := by
    rw [hden']
    rwa [div_lt_iff₀ hqR, mul_comm] at hlt
  obtain ⟨n, hn0, hnq, hmem⟩ := rotation_hits_interval_of_rat_approx r hc hd hw
    (by rw [hden', hr]; exact happ)
  have hnq' : n < q := by
    have : (n : ℤ) < q := by rw [← hden]; exact_mod_cast hnq
    exact_mod_cast this
  apply hno (n - 1) (by omega)
  rw [hfr]
  have e : ((n - 1 : ℕ) : ℝ) + 1 = n := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [e]
  exact hmem

/-- If every block of `Q` consecutive indices puts at most `P` orbit points
in `(a,b)`, then the first `E` indices put at most `P(E/Q + 1)` there. -/
theorem card_range_filter_le {φ : ℕ → ℝ} {a b P : ℝ} {Q : ℕ} (hQ : 0 < Q)
    (hcount : ∀ t, (((Finset.range Q).filter (fun j => φ (t + j) ∈ Ioo a b)).card : ℝ) ≤ P)
    (E : ℕ) :
    (((Finset.range E).filter (fun k => φ k ∈ Ioo a b)).card : ℝ) ≤ P * ((E : ℝ) / Q + 1) := by
  classical
  have hP : 0 ≤ P := (Nat.cast_nonneg _).trans (hcount 0)
  have hind : ∀ T : ℕ,
      (((Finset.range (T * Q)).filter (fun k => φ k ∈ Ioo a b)).card : ℝ) ≤ T * P := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
      rw [show (T + 1) * Q = T * Q + Q by ring, Finset.natCast_card_filter,
        Finset.sum_range_add, ← Finset.natCast_card_filter, ← Finset.natCast_card_filter]
      push_cast
      linarith [hcount (T * Q)]
  set T := E / Q + 1
  have hET : E ≤ T * Q := by
    have h1 := Nat.div_add_mod E Q
    have h2 := Nat.mod_lt E hQ
    simp only [T]
    nlinarith
  have hsub : (Finset.range E).filter (fun k => φ k ∈ Ioo a b) ⊆
      (Finset.range (T * Q)).filter (fun k => φ k ∈ Ioo a b) :=
    Finset.filter_subset_filter _ (Finset.range_subset_range.2 hET)
  have hT : (T : ℝ) ≤ (E : ℝ) / Q + 1 := by
    simp only [T]
    push_cast
    linarith [Nat.cast_div_le (α := ℝ) (m := E) (n := Q)]
  calc
    _ ≤ (((Finset.range (T * Q)).filter (fun k => φ k ∈ Ioo a b)).card : ℝ) :=
      Nat.cast_le.2 (Finset.card_le_card hsub)
    _ ≤ T * P := hind T
    _ ≤ ((E : ℝ) / Q + 1) * P := mul_le_mul_of_nonneg_right hT hP
    _ = _ := mul_comm _ _

/-- Good approximation data at every convergent level: positive reduced
denominators `q_n` with `|q_n α - p_n| ≤ 1/q_(n+1)` and the separation
`|mα - r| ≥ 1/(2q_n)` for `0 < m < q_n`. The continued-fraction convergents
of an irrational `α` satisfy all four conditions. -/
structure GoodConvergents (α : ℝ) (p : ℕ → ℤ) (q : ℕ → ℕ) : Prop where
  pos : ∀ n, 0 < q n
  coprime : ∀ n, Nat.Coprime (p n).natAbs (q n)
  approx : ∀ n, |(q n : ℝ) * α - p n| ≤ 1 / (q (n + 1) : ℝ)
  sep : ∀ n, ∀ m : ℕ, 0 < m → m < q n → ∀ r : ℤ, 1 / (2 * (q n : ℝ)) ≤ |(m : ℝ) * α - r|

/-- Block counts in a level cell: an interval of length at most `4/q` holds
at most nine orbit points from any `q` consecutive indices. -/
theorem cell_block_count {φ : ℕ → ℝ} {α : ℝ}
    (hfr : ∀ k : ℕ, φ k = Int.fract (((k : ℝ) + 1) * α)) {q : ℕ} (hq : 0 < q)
    (hsep : ∀ m : ℕ, 0 < m → m < q → ∀ r : ℤ, 1 / (2 * (q : ℝ)) ≤ |(m : ℝ) * α - r|)
    {a b : ℝ} (hab : a ≤ b) (hlen : b - a ≤ 4 / q) (t : ℕ) :
    (((Finset.range q).filter (fun j => φ (t + j) ∈ Ioo a b)).card : ℝ) ≤ 9 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have h := block_count_le (δ := 1 / (2 * (q : ℝ))) (by positivity) hfr hsep hab hlen t
  have e : 4 / (q : ℝ) / (1 / (2 * q)) + 1 = 9 := by field_simp; norm_num
  linarith

/-- One refinement step of a level cell. Cut the cell `(a,b)` of length at
most `4/q` at its orbit points of index below `E`, with `q ≤ E ≤ q'`. At most
seven gaps contain an atom of index below `N = ⌊1/|qα-p|⌋` and are covered
directly, each at cost at most `(27B q⁻¹ E^(-1/2))^s`; every other gap is a
cell of the next level and is covered at cost `X`. -/
theorem cell_refine_step {φ w : ℕ → ℝ} {α : ℝ} (hα : Irrational α) (hw : Summable w)
    (hn : ∀ n, 0 ≤ w n) (hi : Function.Injective φ)
    (hfr : ∀ k : ℕ, φ k = Int.fract (((k : ℝ) + 1) * α))
    {B : ℝ} (hb : ∀ n, w n ≤ B / ((n : ℝ) + 1) ^ (3/2 : ℝ)) {s : ℝ} (hs : 0 < s)
    {q q' : ℕ} {p p' : ℤ} (hq : 0 < q) (hq' : 0 < q') (hcop' : Nat.Coprime p'.natAbs q')
    (happ' : |α - p' / q'| ≤ 1 / (q' : ℝ) ^ 2)
    (happ : |(q : ℝ) * α - p| ≤ 1 / (q' : ℝ))
    (hsep : ∀ m : ℕ, 0 < m → m < q → ∀ r : ℤ, 1 / (2 * (q : ℝ)) ≤ |(m : ℝ) * α - r|)
    {E : ℕ} (hqE : q ≤ E) (hEq' : E ≤ q') {X : ℝ}
    (hX : ∀ c d : ℝ, 0 ≤ c → c < d → d ≤ 1 → d - c ≤ 4 / q' →
      (∀ k < q', φ k ∉ Ioo c d) → CellCover φ w s c d X) (hX0 : 0 ≤ X)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb1 : b ≤ 1) (hlen : b - a ≤ 4 / q) :
    CellCover φ w s a b (7 * (27 * B * ((q : ℝ)⁻¹ * (E : ℝ) ^ (-(1/2) : ℝ))) ^ s +
      (9 * ((E : ℝ) / q + 1) + 2) * X) := by
  classical
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq'R : (0 : ℝ) < q' := by exact_mod_cast hq'
  set θ := (q : ℝ) * α - p with hθdef
  have hθ : θ ≠ 0 := by
    intro h
    exact (hα.natCast_mul hq.ne').ne_int p (by linarith)
  have habs : 0 < |θ| := abs_pos.2 hθ
  set N := ⌊1 / |θ|⌋₊
  have hN : (N : ℝ) * |θ| ≤ 1 := by
    have := Nat.floor_le (by positivity : (0 : ℝ) ≤ 1 / |θ|)
    rwa [le_div_iff₀ habs] at this
  have hq'N : q' ≤ N := by
    apply Nat.le_floor
    rw [le_div_iff₀ habs]
    have := mul_le_mul_of_nonneg_left happ hq'R.le
    rwa [mul_one_div_cancel hq'R.ne'] at this
  have hEN : E ≤ N := hEq'.trans hq'N
  set Z : ℕ → ℤ := fun k => ((k : ℤ) + 1) * p - q * ⌊((k : ℝ) + 1) * α⌋
  have hφZ : ∀ k, (q : ℝ) * φ k = Z k + ((k : ℝ) + 1) * θ := by
    intro k
    rw [hfr k, Int.fract]
    simp only [Z, θ]
    push_cast
    ring
  have hcount := cell_block_count hfr hq hsep hab.le hlen
  set Cut := ((Finset.range E).filter (fun k => φ k ∈ Ioo a b)).image φ
  set C' : Finset ℝ := insert a (insert b Cut)
  have haC : a ∈ C' := Finset.mem_insert_self _ _
  have hbC : b ∈ C' := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hCut : ∀ e ∈ Cut, ∃ k < E, φ k ∈ Ioo a b ∧ φ k = e := by
    intro e he
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨hk1, hk2⟩ := Finset.mem_filter.1 hk
    exact ⟨k, Finset.mem_range.1 hk1, hk2, rfl⟩
  have hCab : ∀ e ∈ C', a ≤ e ∧ e ≤ b := by
    intro e he
    rcases Finset.mem_insert.1 he with rfl | he
    · exact ⟨le_rfl, hab.le⟩
    rcases Finset.mem_insert.1 he with rfl | he
    · exact ⟨hab.le, le_rfl⟩
    obtain ⟨k, -, hk, rfl⟩ := hCut e he
    exact ⟨hk.1.le, hk.2.le⟩
  have hCe : ∀ e ∈ C', e ≤ a ∨ b ≤ e ∨ ∃ k < E, φ k = e := by
    intro e he
    rcases Finset.mem_insert.1 he with rfl | he
    · exact Or.inl le_rfl
    rcases Finset.mem_insert.1 he with rfl | he
    · exact Or.inr (Or.inl le_rfl)
    obtain ⟨k, hk, -, rfl⟩ := hCut e he
    exact Or.inr (Or.inr ⟨k, hk, rfl⟩)
  have hinside : ∀ g ∈ cutGaps C', ∀ k, g.1 < φ k → φ k < g.2 → φ k ∈ Ioo a b ∧ E ≤ k := by
    intro g hg k h1 h2
    obtain ⟨c1, c2, -, hsepg⟩ := mem_cutGaps.1 hg
    have hin : φ k ∈ Ioo a b := ⟨(hCab _ c1).1.trans_lt h1, h2.trans_le (hCab _ c2).2⟩
    refine ⟨hin, ?_⟩
    by_contra hk
    push Not at hk
    have hmem : φ k ∈ C' := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_image.2 ⟨k, Finset.mem_filter.2 ⟨Finset.mem_range.2 hk, hin⟩, rfl⟩))
    rcases hsepg _ hmem with h | h <;> linarith
  set Tb := 27 * B * ((q : ℝ)⁻¹ * (E : ℝ) ^ (-(1/2) : ℝ))
  have htail : ∑' k, (if φ k ∈ Ioo a b ∧ E ≤ k then w k else 0) ≤ Tb := by
    have h := cell_tail_le hn hb hq hqE hcount
    simp only [Tb]
    linarith
  let mid : ℝ × ℝ → Prop := fun g => ∃ m, E ≤ m ∧ m < N ∧ g.1 < φ m ∧ φ m < g.2
  have hcov := cellCover_of_gaps (φ := φ) (w := w) (s := s) hw hn haC hbC
    (fun g => if mid g then Tb ^ s else X) (by
      intro g hg
      obtain ⟨c1, c2, hlt, hsepg⟩ := mem_cutGaps.1 hg
      by_cases hm : mid g
      · simp only [hm, if_true]
        refine (cellCover_self φ w s hlt).mono ?_
        have hmass : gapMass φ w (g.1, g.2) ≤ Tb := by
          refine (jumpGap_mass_le hw hn (fun k => φ k ∈ Ioo a b ∧ E ≤ k)
            fun k h1 h2 => hinside g hg k h1 h2).trans htail
        exact Real.rpow_le_rpow (gapMass_nonneg hw hn hlt) hmass hs.le
      · simp only [hm, if_false]
        have hnoN : ∀ k < N, φ k ∉ Ioo g.1 g.2 := by
          intro k hk hmem
          exact hm ⟨k, (hinside g hg k hmem.1 hmem.2).2, hk, hmem.1, hmem.2⟩
        apply hX g.1 g.2 (ha.trans (hCab _ c1).1) hlt ((hCab _ c2).2.trans hb1)
        · exact gap_short_of_approx hfr hq' hcop' happ' (ha.trans (hCab _ c1).1)
            ((hCab _ c2).2.trans hb1) fun k hk => hnoN k (by omega)
        · exact fun k hk => hnoN k (lt_of_lt_of_le hk hq'N))
  refine hcov.mono ?_
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
  have hmidc : ((((cutGaps C').filter mid).card : ℕ) : ℝ) ≤ 7 := by
    have h := card_mid_gaps_le hi hq hθ hφZ hN hab.le hCab hCe
    have h4 : (q : ℝ) * (b - a) ≤ 4 := by
      rw [le_div_iff₀ hqR] at hlen
      linarith
    exact h.trans (by linarith)
  have hcutc : (Cut.card : ℝ) ≤ 9 * ((E : ℝ) / q + 1) :=
    (Nat.cast_le.2 Finset.card_image_le).trans (card_range_filter_le hq hcount E)
  have hgc : ((((cutGaps C').filter fun g => ¬ mid g).card : ℕ) : ℝ) ≤
      9 * ((E : ℝ) / q + 1) + 2 := by
    have h1 : ((cutGaps C').filter fun g => ¬ mid g).card ≤ C'.card :=
      (Finset.card_filter_le _ _).trans (card_cutGaps_le C')
    have h2 : C'.card ≤ Cut.card + 2 :=
      (Finset.card_insert_le _ _).trans (Nat.add_le_add_right (Finset.card_insert_le _ _) 1)
    have h3 : ((((cutGaps C').filter fun g => ¬ mid g).card : ℕ) : ℝ) ≤ Cut.card + 2 := by
      exact_mod_cast h1.trans h2
    linarith
  have hTb : 0 ≤ Tb ^ s := by
    have hB : 0 ≤ B := by
      have := (hn 0).trans (hb 0)
      have hp : (0 : ℝ) < ((0 : ℕ) + 1 : ℝ) ^ (3/2 : ℝ) := by positivity
      exact (div_nonneg_iff.1 this).elim (fun h => h.1) fun h => absurd h.2 (not_le.2 hp)
    exact Real.rpow_nonneg (by positivity) s
  have := mul_le_mul_of_nonneg_right hmidc hTb
  have := mul_le_mul_of_nonneg_right hgc hX0
  linarith

/-! ### Cost exponents of level cells -/

/-- The cost of one refinement step in powers of the level denominator `Q`:
with `E ≈ Q^y` and `Q' ≥ Q^ν`, the step cost is at most a constant times
`Q^(-σ')` whenever `σ' ≤ s(1+y/2)` and `σ' ≤ νσ + 1 - y`. -/
theorem step_cost_le {Q Q' E B K s y ν σ σ' : ℝ} (hQ : 1 ≤ Q) (hE1 : Q ^ y / 2 ≤ E)
    (hE2 : E ≤ Q ^ y) (hQ' : Q ^ ν ≤ Q') (hy : 1 ≤ y) (hσ : 0 ≤ σ) (hK : 0 ≤ K)
    (hB : 0 ≤ B) (hs : 0 < s) (h1 : σ' ≤ s * (1 + y / 2)) (h2 : σ' ≤ ν * σ + 1 - y) :
    7 * (27 * B * (Q⁻¹ * E ^ (-(1/2) : ℝ))) ^ s + (9 * (E / Q + 1) + 2) * (K * Q' ^ (-σ)) ≤
      (7 * (54 * B) ^ s + 20 * K) * Q ^ (-σ') := by
  have hQ0 : 0 < Q := by linarith
  have hQy : 0 < Q ^ y := Real.rpow_pos_of_pos hQ0 y
  have hE0 : 0 < E := lt_of_lt_of_le (by linarith) hE1
  -- first term
  have hEr : E ^ (-(1/2) : ℝ) ≤ 2 * Q ^ (-(y / 2)) := by
    calc
      E ^ (-(1/2) : ℝ) ≤ (Q ^ y / 2) ^ (-(1/2) : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hE1 (by norm_num)
      _ = 2 ^ (1/2 : ℝ) * Q ^ (-(y / 2)) := by
        rw [Real.div_rpow hQy.le (by norm_num), ← Real.rpow_mul hQ0.le,
          Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul, mul_comm]
        ring_nf
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hQ0.le _)
        simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          (by norm_num : (1/2 : ℝ) ≤ 1)
  have hinv : Q⁻¹ * Q ^ (-(y / 2)) = Q ^ (-(1 + y / 2)) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hQ0]
    ring_nf
  have hfirst : (27 * B * (Q⁻¹ * E ^ (-(1/2) : ℝ))) ^ s ≤ (54 * B) ^ s * Q ^ (-σ') := by
    calc
      (27 * B * (Q⁻¹ * E ^ (-(1/2) : ℝ))) ^ s ≤ (54 * B * Q ^ (-(1 + y / 2))) ^ s := by
        apply Real.rpow_le_rpow (by positivity) _ hs.le
        rw [← hinv]
        have := mul_le_mul_of_nonneg_left hEr (inv_nonneg.2 hQ0.le)
        nlinarith [Real.rpow_nonneg hQ0.le (-(y / 2)), inv_nonneg.2 hQ0.le]
      _ = (54 * B) ^ s * Q ^ (-(s * (1 + y / 2))) := by
        rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hQ0.le _), ← Real.rpow_mul hQ0.le]
        ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hQ (by linarith)) (Real.rpow_nonneg (by positivity) _)
  -- second term
  have hQy1 : 1 ≤ Q ^ (y - 1) := Real.one_le_rpow hQ (by linarith)
  have hEQ : E / Q ≤ Q ^ (y - 1) := by
    rw [div_le_iff₀ hQ0, Real.rpow_sub_one hQ0.ne', div_mul_cancel₀ _ hQ0.ne']
    exact hE2
  have hcnt : 9 * (E / Q + 1) + 2 ≤ 20 * Q ^ (y - 1) := by linarith
  have hQ'σ : Q' ^ (-σ) ≤ Q ^ (-(ν * σ)) := by
    calc
      Q' ^ (-σ) ≤ (Q ^ ν) ^ (-σ) :=
        Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hQ0 ν) hQ' (by linarith)
      _ = _ := by
        rw [← Real.rpow_mul hQ0.le]
        ring_nf
  have hsecond : (9 * (E / Q + 1) + 2) * (K * Q' ^ (-σ)) ≤ 20 * K * Q ^ (-σ') := by
    calc
      (9 * (E / Q + 1) + 2) * (K * Q' ^ (-σ)) ≤ (20 * Q ^ (y - 1)) * (K * Q ^ (-(ν * σ))) :=
        mul_le_mul hcnt (mul_le_mul_of_nonneg_left hQ'σ hK)
          (mul_nonneg hK (Real.rpow_nonneg ((Real.rpow_pos_of_pos hQ0 ν).le.trans hQ') _))
          (by positivity)
      _ = 20 * K * Q ^ (y - 1 + -(ν * σ)) := by
        rw [Real.rpow_add hQ0]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hQ (by linarith)) (by positivity)
  nlinarith [hfirst, hsecond]

/-- Level-cell covers with cost exponent `σ` and constant `K` from level
`n₁` on: every phase interval in `[0,1]` of length at most `4/q_n` without
orbit points of index below `q_n` has a cover of cost `K q_n^(-σ)`. -/
def LevelCovers (φ w : ℕ → ℝ) (q : ℕ → ℕ) (s σ K : ℝ) (n₁ : ℕ) : Prop :=
  ∀ n, n₁ ≤ n → ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 → b - a ≤ 4 / q n →
    (∀ k < q n, φ k ∉ Ioo a b) → CellCover φ w s a b (K * (q n : ℝ) ^ (-σ))

/-- The weight bound `w_n ≤ B/(n+1)^(3/2)` forces `B ≥ 0` when `w ≥ 0`. -/
theorem weight_const_nonneg {w : ℕ → ℝ} (hn : ∀ n, 0 ≤ w n) {B : ℝ}
    (hb : ∀ n, w n ≤ B / ((n : ℝ) + 1) ^ (3/2 : ℝ)) : 0 ≤ B := by
  have := (hn 0).trans (hb 0)
  have hp : (0 : ℝ) < ((0 : ℕ) + 1 : ℝ) ^ (3/2 : ℝ) := by positivity
  exact (div_nonneg_iff.1 this).elim (fun h => h.1) fun h => absurd h.2 (not_le.2 hp)

/-- Base case: a single interval covers a level cell at exponent `3s/2`. -/
theorem levelCovers_base {φ w : ℕ → ℝ} {α : ℝ} (hw : Summable w) (hn : ∀ n, 0 ≤ w n)
    (hfr : ∀ k : ℕ, φ k = Int.fract (((k : ℝ) + 1) * α))
    {B : ℝ} (hb : ∀ n, w n ≤ B / ((n : ℝ) + 1) ^ (3/2 : ℝ)) {s : ℝ} (hs : 0 < s)
    {p : ℕ → ℤ} {q : ℕ → ℕ} (hG : GoodConvergents α p q) :
    LevelCovers φ w q s (3 * s / 2) ((27 * B) ^ s) 0 := by
  intro n _ a b ha hab hb1 hlen hno
  have hB := weight_const_nonneg hn hb
  have hq := hG.pos n
  have hqR : (0 : ℝ) < q n := by exact_mod_cast hq
  have hcount := cell_block_count hfr hq (hG.sep n) hab.le hlen
  have htail := cell_tail_le hn hb hq le_rfl hcount
  refine (cellCover_self φ w s hab).mono ?_
  have hmass : gapMass φ w (a, b) ≤ 27 * B * (q n : ℝ) ^ (-(3/2) : ℝ) := by
    refine (jumpGap_mass_le hw hn (fun k => φ k ∈ Ioo a b ∧ q n ≤ k) fun k h1 h2 => ?_).trans
      (htail.trans (le_of_eq ?_))
    · refine ⟨⟨h1, h2⟩, ?_⟩
      by_contra hk
      exact hno k (not_le.1 hk) ⟨h1, h2⟩
    · rw [← Real.rpow_neg_one, ← Real.rpow_add hqR]
      ring_nf
  calc
    gapMass φ w (a, b) ^ s ≤ (27 * B * (q n : ℝ) ^ (-(3/2) : ℝ)) ^ s :=
      Real.rpow_le_rpow (gapMass_nonneg hw hn hab) hmass hs.le
    _ = _ := by
      rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hqR.le _), ← Real.rpow_mul hqR.le]
      ring_nf

/-- The approximation at level `n+1` has inverse-square quality once the
denominators do not decrease. -/
theorem good_approx_sq {α : ℝ} {p : ℕ → ℤ} {q : ℕ → ℕ} (hG : GoodConvergents α p q)
    {n : ℕ} (hmono : q n ≤ q (n + 1)) :
    |α - p n / q n| ≤ 1 / (q n : ℝ) ^ 2 := by
  have hqR : (0 : ℝ) < q n := by exact_mod_cast hG.pos n
  have hq'R : (q n : ℝ) ≤ q (n + 1) := by exact_mod_cast hmono
  have e : α - p n / q n = ((q n : ℝ) * α - p n) / q n := by field_simp
  rw [e, abs_div, abs_of_pos hqR, div_le_div_iff₀ hqR (by positivity)]
  have h := hG.approx n
  have h2 : 1 / (q (n + 1) : ℝ) ≤ 1 / q n := one_div_le_one_div_of_le hqR hq'R
  have h3 : |(q n : ℝ) * α - p n| * q n ≤ 1 := (le_div_iff₀ hqR).1 (h.trans h2)
  nlinarith [abs_nonneg ((q n : ℝ) * α - p n)]

/-- Induction step: level covers at exponent `σ` give level covers at any
`σ' ≤ min(s(1+y/2), νσ+1-y)`, for `1 ≤ y ≤ ν`, one level earlier. -/
theorem levelCovers_step {φ w : ℕ → ℝ} {α ν : ℝ} (hα : Irrational α) (hw : Summable w)
    (hn : ∀ n, 0 ≤ w n) (hi : Function.Injective φ)
    (hfr : ∀ k : ℕ, φ k = Int.fract (((k : ℝ) + 1) * α))
    {B : ℝ} (hb : ∀ n, w n ≤ B / ((n : ℝ) + 1) ^ (3/2 : ℝ)) {s : ℝ} (hs : 0 < s)
    {p : ℕ → ℤ} {q : ℕ → ℕ} (hG : GoodConvergents α p q) (hν : 1 ≤ ν) {n₀ : ℕ}
    (hgrow : ∀ n, n₀ ≤ n → (q n : ℝ) ^ ν ≤ q (n + 1))
    {σ K : ℝ} {n₁ : ℕ} (hσ : 0 ≤ σ) (hK : 0 ≤ K) (hL : LevelCovers φ w q s σ K n₁)
    {y σ' : ℝ} (hy1 : 1 ≤ y) (hyν : y ≤ ν) (h1 : σ' ≤ s * (1 + y / 2))
    (h2 : σ' ≤ ν * σ + 1 - y) :
    LevelCovers φ w q s σ' (7 * (54 * B) ^ s + 20 * K) (max n₁ n₀) := by
  intro n hn1 a b ha hab hb1 hlen hno
  have hB := weight_const_nonneg hn hb
  have hq := hG.pos n
  have hq' := hG.pos (n + 1)
  have hqR : (1 : ℝ) ≤ q n := by exact_mod_cast hq
  have hq'R : (0 : ℝ) < q (n + 1) := by exact_mod_cast hq'
  have hg0 := hgrow n (le_of_max_le_right hn1)
  have hg1 := hgrow (n + 1) (by have := le_of_max_le_right hn1; omega)
  have hself : ∀ m, n₀ ≤ m → q m ≤ q (m + 1) := by
    intro m hm
    have h := hgrow m hm
    have hm1 : (1 : ℝ) ≤ q m := by exact_mod_cast hG.pos m
    have : (q m : ℝ) ≤ (q m : ℝ) ^ ν := by
      simpa using Real.rpow_le_rpow_of_exponent_le hm1 hν
    exact_mod_cast this.trans h
  have hmono1 := hself (n + 1) (by have := le_of_max_le_right hn1; omega)
  set E := ⌊(q n : ℝ) ^ y⌋₊
  have hQy1 : 1 ≤ (q n : ℝ) ^ y := Real.one_le_rpow hqR (by linarith)
  have hE2 : (E : ℝ) ≤ (q n : ℝ) ^ y := Nat.floor_le (by linarith)
  have hE1 : (q n : ℝ) ^ y / 2 ≤ E := by
    have h1 := Nat.lt_floor_add_one ((q n : ℝ) ^ y)
    have h2 : (1 : ℝ) ≤ E := by exact_mod_cast Nat.le_floor (by simpa using hQy1)
    linarith
  have hqE : q n ≤ E := by
    apply Nat.le_floor
    simpa using Real.rpow_le_rpow_of_exponent_le hqR hy1
  have hEq' : E ≤ q (n + 1) := by
    have : (E : ℝ) ≤ q (n + 1) :=
      hE2.trans ((Real.rpow_le_rpow_of_exponent_le hqR hyν).trans hg0)
    exact_mod_cast this
  have hstep := cell_refine_step hα hw hn hi hfr hb hs hq hq' (hG.coprime (n + 1))
    (good_approx_sq hG hmono1) (hG.approx n) (hG.sep n) hqE hEq'
    (X := K * (q (n + 1) : ℝ) ^ (-σ))
    (fun c d hc hcd hd hl hno' =>
      hL (n + 1) (by have := le_of_max_le_left hn1; omega) c d hc hcd hd hl hno')
    (mul_nonneg hK (Real.rpow_nonneg hq'R.le _)) ha hab hb1 hlen
  exact hstep.mono (step_cost_le hqR hE1 hE2 hg0 hy1 hσ hK hB hs h1 h2)

/-- Iterating the refinement step: when `s > 2/(2+ν)`, a bounded number of
steps produces level covers with cost exponent above one. Each step raises
the exponent from `σ ≤ 1` to `(3s + sνσ)/(2+s)`, a gain of at least
`min(3s, s(2+ν)-2)/(2+s)`. -/
theorem levelCovers_exists {φ w : ℕ → ℝ} {α ν : ℝ} (hα : Irrational α) (hw : Summable w)
    (hn : ∀ n, 0 ≤ w n) (hi : Function.Injective φ)
    (hfr : ∀ k : ℕ, φ k = Int.fract (((k : ℝ) + 1) * α))
    {B : ℝ} (hb : ∀ n, w n ≤ B / ((n : ℝ) + 1) ^ (3/2 : ℝ)) {s : ℝ} (hs0 : 0 < s)
    {p : ℕ → ℤ} {q : ℕ → ℕ} (hG : GoodConvergents α p q) (hν : 1 ≤ ν) {n₀ : ℕ}
    (hgrow : ∀ n, n₀ ≤ n → (q n : ℝ) ^ ν ≤ q (n + 1)) (hs : 2 / (2 + ν) < s) :
    ∃ σ K n₁, 1 < σ ∧ 0 ≤ K ∧ LevelCovers φ w q s σ K n₁ := by
  have hB := weight_const_nonneg hn hb
  have hsν : 2 < s * (2 + ν) := by rwa [div_lt_iff₀ (by linarith)] at hs
  set η := min (3 * s) (s * (2 + ν) - 2) / (2 + s) with hηdef
  have hη : 0 < η := div_pos (lt_min (by linarith) (by linarith)) (by linarith)
  have claim : ∀ j : ℕ, ∃ σ K n₁, 3 * s / 2 ≤ σ ∧ 0 ≤ K ∧
      (1 < σ ∨ 3 * s / 2 + j * η ≤ σ) ∧ LevelCovers φ w q s σ K n₁ := by
    intro j
    induction j with
    | zero =>
      exact ⟨3 * s / 2, (27 * B) ^ s, 0, le_rfl, Real.rpow_nonneg (by positivity) s,
        Or.inr (by simp), levelCovers_base hw hn hfr hb hs0 hG⟩
    | succ j ih =>
      obtain ⟨σ, K, n₁, hσ, hK, hor, hL⟩ := ih
      by_cases h : 1 < σ
      · exact ⟨σ, K, n₁, hσ, hK, Or.inl h, hL⟩
      push Not at h
      have hj : 3 * s / 2 + j * η ≤ σ := hor.resolve_left (not_lt.2 h)
      have hσ0 : 0 ≤ σ := le_trans (by positivity) hσ
      set y := (1 - s + ν * σ) / (1 + s / 2) with hydef
      set σ' := (3 * s + s * ν * σ) / (2 + s) with hσ'def
      have hs2 : 0 < 1 + s / 2 := by linarith
      have hy1 : 1 ≤ y := by
        rw [hydef, le_div_iff₀ hs2]
        nlinarith
      have hyν : y ≤ ν := by
        rw [hydef, div_le_iff₀ hs2]
        nlinarith
      have e1 : s * (1 + y / 2) = σ' := by
        rw [hydef, hσ'def]
        field_simp
        ring
      have e2 : ν * σ + 1 - y = σ' := by
        rw [hydef, hσ'def]
        field_simp
        ring
      have hL' := levelCovers_step hα hw hn hi hfr hb hs0 hG hν hgrow hσ0 hK hL hy1 hyν
        e1.ge e2.ge
      have hgain : σ + η ≤ σ' := by
        have hc : min (3 * s) (s * (2 + ν) - 2) ≤ 3 * s - (2 + s - s * ν) * σ := by
          rcases le_or_gt (2 + s - s * ν) 0 with hc | hc
          · exact (min_le_left _ _).trans (by nlinarith)
          · exact (min_le_right _ _).trans (by nlinarith)
        have e3 : σ' = σ + (3 * s - (2 + s - s * ν) * σ) / (2 + s) := by
          rw [hσ'def]
          field_simp
          ring
        rw [e3, hηdef]
        exact add_le_add_right (div_le_div_of_nonneg_right hc (by linarith)) σ
      refine ⟨σ', 7 * (54 * B) ^ s + 20 * K, max n₁ n₀, by linarith, by positivity,
        Or.inr ?_, hL'⟩
      push_cast
      linarith
  obtain ⟨j, hj⟩ := exists_nat_gt ((1 - 3 * s / 2) / η)
  obtain ⟨σ, K, n₁, -, hK, hor, hL⟩ := claim j
  refine ⟨σ, K, n₁, ?_, hK, hL⟩
  rcases hor with h | h
  · exact h
  · have : 1 - 3 * s / 2 < j * η := by rwa [div_lt_iff₀ hη] at hj
    linarith

/-! ### The upper bound for regular slopes -/

/-- If every convergent level of the slope `α > 1` is good, with growth
`q_(n+1) ≥ q_n^ν` from some level on (`ν ≥ 1`), then every Hausdorff measure
of the complete cluster set with exponent `s > 2/(2+ν)` vanishes. -/
theorem regular_hausdorff_zero {α ν : ℝ} (hα1 : 1 < α) (hα : Irrational α) (hν : 1 ≤ ν)
    {p : ℕ → ℤ} {q : ℕ → ℕ} (hG : GoodConvergents α p q) (hq : Tendsto q atTop atTop)
    (hgrow : ∀ᶠ n in atTop, (q n : ℝ) ^ ν ≤ q (n + 1)) {s : ℝ} (hs : 2 / (2 + ν) < s) :
    Measure.hausdorffMeasure s (passageClusterSet (1/α)) = 0 := by
  classical
  have hα0 : 0 < α := by linarith
  have hβ0 : 0 < 1/α := one_div_pos.mpr hα0
  have hβ1 : 1/α < 1 := (div_lt_one hα0).mpr hα1
  have hβ : Irrational (1/α) := by simpa using hα.inv
  have hs0 : 0 < s := lt_trans (by positivity) hs
  rw [passageClusterSet_eq_jumpRange hβ0 hβ1 hβ]
  set φ : ℕ → ℝ := fun r => passagePhase (1/α) (r+1) with hφdef
  set w : ℕ → ℝ := fun r => passageJumpWeight (1/α) (r+1) with hwdef
  have hw : Summable w := (passage_jump_weights_hasSum hβ0 hβ1 hβ).summable
  have hn : ∀ n, 0 ≤ w n := fun n => passageJumpWeight_nonneg hβ0 hβ1 _
  have hi : Function.Injective φ :=
    (passagePhase_injective hβ0 hβ1 hβ).comp (add_left_injective 1)
  have hp : ∀ n, φ n ∈ Ioo (0 : ℝ) 1 := fun n =>
    ⟨passagePhase_pos hβ0 hβ1 hβ (Nat.succ_pos n), (passagePhase_mem_Ico hβ0 _).2⟩
  have hfr : ∀ k : ℕ, φ k = Int.fract (((k : ℝ) + 1) * α) := by
    intro k
    simp only [hφdef]
    rw [passagePhase_eq_fract hβ0]
    push_cast
    congr 1
    field_simp
  obtain ⟨A, B, hA, hB, hwB⟩ := passageWeight_three_halves hβ0 hβ1 hβ
  have hb : ∀ n, w n ≤ B / ((n : ℝ) + 1) ^ (3/2 : ℝ) := fun n => (hwB n).2
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hgrow
  obtain ⟨σ, K, n₁, hσ1, hK, hL⟩ :=
    levelCovers_exists hα hw hn hi hfr hb hs0 hG hν hn₀ hs
  apply cellCover_hausdorff_zero hw hn hi hp hs0
  intro ε hε
  have tq : Tendsto (fun n => ((q n : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hq
  have hlim : Tendsto (fun n => 3 * K * ((q n : ℕ) : ℝ) ^ (-(σ - 1))) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop (by linarith : 0 < σ - 1)).comp tq).const_mul (3 * K)
  obtain ⟨n, hsmall, hn1⟩ := ((hlim.eventually (ge_mem_nhds hε)).and
    (eventually_ge_atTop (max n₁ n₀))).exists
  have hq0 := hG.pos n
  have hqR : (1 : ℝ) ≤ q n := by exact_mod_cast hq0
  have hmono : q n ≤ q (n + 1) := by
    have h := hn₀ n (le_of_max_le_right hn1)
    have : (q n : ℝ) ≤ (q n : ℝ) ^ ν := by
      simpa using Real.rpow_le_rpow_of_exponent_le hqR hν
    exact_mod_cast this.trans h
  set C := earlyCuts φ (q n)
  have h0 : (0 : ℝ) ∈ C := mem_earlyCuts.2 (Or.inl rfl)
  have h1 : (1 : ℝ) ∈ C := mem_earlyCuts.2 (Or.inr (Or.inl rfl))
  have hC01 : ∀ e ∈ C, 0 ≤ e ∧ e ≤ 1 := by
    intro e he
    rcases mem_earlyCuts.1 he with rfl | rfl | ⟨k, -, rfl⟩
    · norm_num
    · norm_num
    · exact ⟨(hp k).1.le, (hp k).2.le⟩
  have hcov := cellCover_of_gaps (φ := φ) (w := w) (s := s) hw hn h0 h1
    (fun _ => K * (q n : ℝ) ^ (-σ)) (by
      intro g hg
      obtain ⟨c1, c2, hlt, hsepg⟩ := mem_cutGaps.1 hg
      have hno : ∀ k < q n, φ k ∉ Ioo g.1 g.2 := by
        intro k hk hmem
        have hkC : φ k ∈ C := mem_earlyCuts.2 (Or.inr (Or.inr ⟨k, hk, rfl⟩))
        rcases hsepg _ hkC with h | h
        · linarith [hmem.1]
        · linarith [hmem.2]
      exact hL n (le_of_max_le_left hn1) g.1 g.2 (hC01 _ c1).1 hlt (hC01 _ c2).2
        (gap_short_of_approx hfr hq0 (hG.coprime n) (good_approx_sq hG hmono)
          (hC01 _ c1).1 (hC01 _ c2).2 fun k hk => hno k (by omega)) hno)
  refine hcov.mono ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((cutGaps C).card : ℝ) ≤ 3 * q n := by
    have h := (card_cutGaps_le C).trans (card_earlyCuts_le φ (q n))
    have h' : ((cutGaps C).card : ℝ) ≤ q n + 2 := by exact_mod_cast h
    linarith
  have hpow : (q n : ℝ) * (q n : ℝ) ^ (-σ) = (q n : ℝ) ^ (-(σ - 1)) := by
    rw [← Real.rpow_one_add' (by linarith) (by linarith)]
    ring_nf
  have hK' : 0 ≤ K * (q n : ℝ) ^ (-σ) := mul_nonneg hK (Real.rpow_nonneg (by linarith) _)
  calc
    ((cutGaps C).card : ℝ) * (K * (q n : ℝ) ^ (-σ)) ≤ (3 * q n) * (K * (q n : ℝ) ^ (-σ)) :=
      mul_le_mul_of_nonneg_right hcard hK'
    _ = 3 * K * ((q n : ℝ) * (q n : ℝ) ^ (-σ)) := by ring
    _ = 3 * K * ((q n : ℕ) : ℝ) ^ (-(σ - 1)) := by rw [hpow]
    _ ≤ ε := hsmall

/-- Dimension form of `regular_hausdorff_zero`: the complete cluster set has
Hausdorff dimension at most `2/(2+ν)`. -/
theorem regular_cluster_dimH_le {α ν : ℝ} (hα1 : 1 < α) (hα : Irrational α) (hν : 1 ≤ ν)
    {p : ℕ → ℤ} {q : ℕ → ℕ} (hG : GoodConvergents α p q) (hq : Tendsto q atTop atTop)
    (hgrow : ∀ᶠ n in atTop, (q n : ℝ) ^ ν ≤ q (n + 1)) :
    dimH (passageClusterSet (1/α)) ≤ ENNReal.ofReal (2 / (2 + ν)) := by
  have hD0 : 0 ≤ 2 / (2 + ν) := by positivity
  apply le_of_forall_gt_imp_ge_of_dense
  intro c hc
  by_cases hct : c = ⊤
  · rw [hct]
    exact le_top
  set r := c.toReal
  have hcr : c = ENNReal.ofReal r := (ENNReal.ofReal_toReal hct).symm
  have hr : 2 / (2 + ν) < r := by
    rw [hcr] at hc
    exact (ENNReal.ofReal_lt_ofReal_iff'.1 hc).1
  have hr0 : 0 ≤ r := hD0.trans hr.le
  have h0 := regular_hausdorff_zero hα1 hα hν hG hq hgrow hr
  have hne : Measure.hausdorffMeasure ((r.toNNReal : ℝ≥0) : ℝ)
      (passageClusterSet (1/α)) ≠ ⊤ := by
    rw [Real.coe_toNNReal _ hr0, h0]
    exact ENNReal.zero_ne_top
  calc
    _ ≤ ((r.toNNReal : ℝ≥0) : ℝ≥0∞) := dimH_le_of_hausdorffMeasure_ne_top hne
    _ = ENNReal.ofReal r := rfl
    _ = c := hcr.symm

/-- The upper bound with a constant in the growth: if `c q_n^ν ≤ q_(n+1)`
from some level on, with `c > 0` and `ν > 1`, then `dim_H K_α ≤ 2/(2+ν)`. -/
theorem regular_cluster_dimH_le' {α ν c : ℝ} (hα1 : 1 < α) (hα : Irrational α)
    (hν : 1 < ν) {p : ℕ → ℤ} {q : ℕ → ℕ} (hG : GoodConvergents α p q)
    (hq : Tendsto q atTop atTop) (hc : 0 < c)
    (hgrow : ∀ᶠ n in atTop, c * (q n : ℝ) ^ ν ≤ q (n + 1)) :
    dimH (passageClusterSet (1/α)) ≤ ENNReal.ofReal (2 / (2 + ν)) := by
  have tq : Tendsto (fun n => ((q n : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hq
  -- every exponent `ν' ∈ [1, ν)` is attained without a constant
  have hsub : ∀ ν', 1 ≤ ν' → ν' < ν →
      dimH (passageClusterSet (1/α)) ≤ ENNReal.ofReal (2 / (2 + ν')) := by
    intro ν' h1 h2
    apply regular_cluster_dimH_le hα1 hα h1 hG hq
    have hlim : Tendsto (fun n => ((q n : ℕ) : ℝ) ^ (-(ν - ν'))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by linarith)).comp tq
    filter_upwards [hgrow, hlim.eventually (ge_mem_nhds hc), tq.eventually_ge_atTop 1]
      with n hg hl hq1
    have hq0 : (0 : ℝ) < q n := by linarith
    calc
      (q n : ℝ) ^ ν' = (q n : ℝ) ^ (-(ν - ν')) * (q n : ℝ) ^ ν := by
        rw [← Real.rpow_add hq0]
        ring_nf
      _ ≤ c * (q n : ℝ) ^ ν := mul_le_mul_of_nonneg_right hl (Real.rpow_nonneg hq0.le _)
      _ ≤ _ := hg
  -- pass to the limit `ν' ↑ ν`
  have hcont : ContinuousAt (fun τ : ℝ => ENNReal.ofReal ((2 : ℝ) / (2 + τ))) ν :=
    ENNReal.continuous_ofReal.continuousAt.comp
      (continuousAt_const.div (continuousAt_const.add continuousAt_id) (by linarith))
  have hlim := hcont.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[<] ν ≤ 𝓝 ν)
  apply ge_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsLT hν] with τ hτ
  exact hsub τ hτ.1.le hτ.2

/-! ### The lower bound and the exact dimension -/

/-- Good convergents whose denominators grow at most like `q_(n+1) ≤ C q_n^ν`
give a uniform Diophantine lower bound of exponent `ν`. -/
theorem regular_dio_lower {α ν C : ℝ} (hν : 0 ≤ ν) {p : ℕ → ℤ} {q : ℕ → ℕ}
    (hG : GoodConvergents α p q) (hq : Tendsto q atTop atTop) (hC : 0 < C)
    (hup : ∀ n, (q (n + 1) : ℝ) ≤ C * (q n : ℝ) ^ ν) :
    ∃ c : ℝ, 0 < c ∧ DiophantineLowerBound α c ν := by
  classical
  have hq00 : (0 : ℝ) < q 0 := by exact_mod_cast hG.pos 0
  refine ⟨min (1 / (2 * (q 0 : ℝ))) (1 / (2 * C)), lt_min (by positivity) (by positivity), ?_⟩
  intro m hm r
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm1 : 1 ≤ (m : ℝ) ^ ν := Real.one_le_rpow hmR hν
  have hex : ∃ n, m < q n := (hq.eventually_gt_atTop m).exists
  set n := Nat.find hex with hndef
  have hmn : m < q n := Nat.find_spec hex
  have hab := abs_nonneg ((m : ℝ) * α - r)
  rcases Nat.eq_zero_or_eq_succ_pred n with h0 | hs
  · have hsep := hG.sep 0 m hm (by rw [← h0]; exact hmn) r
    calc
      min (1 / (2 * (q 0 : ℝ))) (1 / (2 * C)) ≤ 1 / (2 * (q 0 : ℝ)) := min_le_left _ _
      _ ≤ |(m : ℝ) * α - r| := hsep
      _ ≤ (m : ℝ) ^ ν * |(m : ℝ) * α - r| := le_mul_of_one_le_left hab hm1
  · set k := n.pred
    have hk : ¬ m < q k := Nat.find_min hex (by omega)
    have hkm : (q k : ℝ) ≤ m := by exact_mod_cast not_lt.1 hk
    have hmk : m < q (k + 1) := by
      have e : k + 1 = n := hs.symm
      rw [e]
      exact hmn
    have hsep := hG.sep (k + 1) m hm hmk r
    have hup' : (q (k + 1) : ℝ) ≤ C * (m : ℝ) ^ ν :=
      (hup k).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) hkm hν) hC.le)
    have hqk : (0 : ℝ) < q (k + 1) := by exact_mod_cast hG.pos (k + 1)
    have hmν : 0 < (m : ℝ) ^ ν := by linarith
    have h2 : 1 / (2 * C) ≤ (m : ℝ) ^ ν * (1 / (2 * (q (k + 1) : ℝ))) := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    calc
      min (1 / (2 * (q 0 : ℝ))) (1 / (2 * C)) ≤ 1 / (2 * C) := min_le_right _ _
      _ ≤ (m : ℝ) ^ ν * (1 / (2 * (q (k + 1) : ℝ))) := h2
      _ ≤ _ := mul_le_mul_of_nonneg_left hsep hmν.le

/-- Exact dimension at regular slopes: if the convergent denominators of the
irrational slope `α > 1` satisfy `c q_n^ν ≤ q_(n+1) ≤ C q_n^ν` for all `n`,
with `ν > 1`, then the complete cluster set has Hausdorff dimension exactly
`2/(2+ν)`. -/
theorem regular_cluster_dimH_eq {α ν c C : ℝ} (hα1 : 1 < α) (hα : Irrational α)
    (hν : 1 < ν) {p : ℕ → ℤ} {q : ℕ → ℕ} (hG : GoodConvergents α p q)
    (hq : Tendsto q atTop atTop) (hc : 0 < c) (hC : 0 < C)
    (hlow : ∀ n, c * (q n : ℝ) ^ ν ≤ q (n + 1))
    (hup : ∀ n, (q (n + 1) : ℝ) ≤ C * (q n : ℝ) ^ ν) :
    dimH (passageClusterSet (1/α)) = ENNReal.ofReal (2 / (2 + ν)) := by
  apply le_antisymm
  · exact regular_cluster_dimH_le' hα1 hα hν hG hq hc (Eventually.of_forall hlow)
  · obtain ⟨c', hc', hdio⟩ := regular_dio_lower (by linarith) hG hq hC hup
    exact cluster_dimH_ge_sharp hα1 hα hc' (by linarith) hdio

end Problems.Juggler.BeattySlope

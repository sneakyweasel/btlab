import Problems.Juggler.BeattySlopeLiouville
import Problems.Juggler.BeattySlopeHausdorff

/-!
# The critical two-thirds measure and Diophantine approximation

Splitting every gap mass of the early cut cover into chain and late parts,
and applying concavity of `x ↦ x^s` separately to the at most `q+1` chains
and the at most `E+2` gaps, sharpens the Liouville cut estimate. At the
critical exponent two-thirds it shows that the two-thirds Hausdorff measure
of the complete cluster set is positive exactly for badly approximable slopes.
-/

namespace Problems.Juggler.BeattySlope

open Filter Topology Set MeasureTheory BeattyPhase
open scoped NNReal ENNReal

/-- Finite subadditivity of `x ↦ x^s` on nonnegative reals for `0 < s ≤ 1`. -/
theorem rpow_finset_sum_le {ι : Type*} (I : Finset ι) {x : ι → ℝ}
    (hx : ∀ i ∈ I, 0 ≤ x i) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    (∑ i ∈ I, x i) ^ s ≤ ∑ i ∈ I, x i ^ s := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [Real.zero_rpow hs.ne']
  | insert a I ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hxa := hx a (Finset.mem_insert_self a I)
    have hI : ∀ i ∈ I, 0 ≤ x i := fun i hi => hx i (Finset.mem_insert_of_mem hi)
    calc
      _ ≤ x a ^ s + (∑ i ∈ I, x i) ^ s :=
        Real.rpow_add_le_add_rpow hxa (Finset.sum_nonneg hI) hs.le hs1
      _ ≤ _ := by linarith [ih hI]

/-- Concavity of `x ↦ x^s` over a finite family, `0 < s ≤ 1`. -/
theorem sum_rpow_le_card_mul {ι : Type*} (I : Finset ι) {x : ι → ℝ}
    (hx : ∀ i ∈ I, 0 ≤ x i) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    ∑ i ∈ I, x i ^ s ≤ (I.card : ℝ) ^ (1 - s) * (∑ i ∈ I, x i) ^ s := by
  have hp : 1 ≤ 1/s := by rw [le_div_iff₀ hs]; linarith
  have hy : ∀ i ∈ I, 0 ≤ x i ^ s := fun i hi => Real.rpow_nonneg (hx i hi) s
  have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (s := I) hp hy
  have he : ∀ i ∈ I, (x i ^ s) ^ (1/s) = x i := fun i hi => by
    rw [← Real.rpow_mul (hx i hi), mul_one_div_cancel hs.ne', Real.rpow_one]
  rw [Finset.sum_congr rfl he] at h
  have hS := Finset.sum_nonneg hy
  have hX := Finset.sum_nonneg hx
  have hc : (0 : ℝ) ≤ I.card := Nat.cast_nonneg _
  have h2 := Real.rpow_le_rpow (Real.rpow_nonneg hS _) h hs.le
  rw [← Real.rpow_mul hS, one_div_mul_cancel hs.ne', Real.rpow_one,
    Real.mul_rpow (Real.rpow_nonneg hc _) hX, ← Real.rpow_mul hc] at h2
  convert h2 using 3
  field_simp

/-- Finitely many restrictions of a nonnegative summable series whose
supports are pairwise disjoint and contained in `Q` have total mass at most
the restriction to `Q`. -/
theorem sum_tsum_le_of_disjoint {ι : Type*} (G : Finset ι) {w : ℕ → ℝ}
    (hw : Summable w) (hn : ∀ n, 0 ≤ w n) (P : ι → ℕ → Prop)
    [∀ g, DecidablePred (P g)] (Q : ℕ → Prop) [DecidablePred Q]
    (hdisj : ∀ n, ∀ g ∈ G, ∀ g' ∈ G, P g n → P g' n → g = g')
    (hPQ : ∀ g ∈ G, ∀ n, P g n → Q n) :
    ∑ g ∈ G, ∑' n, (if P g n then w n else 0) ≤ ∑' n, if Q n then w n else 0 := by
  classical
  have hsum (R : ℕ → Prop) [DecidablePred R] : Summable (fun n => if R n then w n else 0) :=
    hw.of_norm_bounded fun n => by
      split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg (hn n), hn n]
  rw [← Summable.tsum_finsetSum (fun g _ => hsum (P g))]
  refine Summable.tsum_le_tsum (fun n => ?_) (summable_sum fun g _ => hsum (P g)) (hsum Q)
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have hcard : (G.filter (fun g => P g n)).card ≤ 1 :=
    Finset.card_le_one.2 fun g hg g' hg' =>
      hdisj n g (Finset.mem_filter.1 hg).1 g' (Finset.mem_filter.1 hg').1
        (Finset.mem_filter.1 hg).2 (Finset.mem_filter.1 hg').2
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hcard with h0 | h1
  · rw [h0]
    split_ifs <;> simp [hn n]
  · obtain ⟨g, hg⟩ := Finset.card_eq_one.1 h1
    have hmem : g ∈ G.filter (fun g => P g n) := by rw [hg]; exact Finset.mem_singleton_self g
    have hQ := hPQ g (Finset.mem_filter.1 hmem).1 n (Finset.mem_filter.1 hmem).2
    rw [h1]
    simp [hQ]

/-- Two middle atoms with the same chain label lie in the same gap of the
early cut set. -/
theorem chain_same_gap {φ : ℕ → ℝ} (hi : Function.Injective φ)
    (hp : ∀ n, φ n ∈ Ioo (0 : ℝ) 1) {Z : ℕ → ℤ} {q : ℕ} {θ : ℝ} (hq : 0 < q)
    (hθ : θ ≠ 0) (hφ : ∀ k, (q : ℝ) * φ k = Z k + ((k : ℝ) + 1) * θ)
    {E N : ℕ} (hN : (N : ℝ) * |θ| ≤ 1) {g g' : ℝ × ℝ}
    (hg : g ∈ cutGaps (earlyCuts φ E)) (hg' : g' ∈ cutGaps (earlyCuts φ E))
    {m m' : ℕ} (hEm : E ≤ m) (hmN : m < N) (hEm' : E ≤ m') (hmN' : m' < N)
    (hZ : Z m = Z m') (h1 : g.1 < φ m) (h2 : φ m < g.2) (h1' : g'.1 < φ m')
    (h2' : φ m' < g'.2) : g = g' := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have habs : 0 < |θ| := abs_pos.2 hθ
  apply cutGap_eq_of_no_cut hg hg' ⟨h1, h2⟩ ⟨h1', h2'⟩
  intro e he
  rcases mem_earlyCuts.1 he with rfl | rfl | ⟨k, hk, rfl⟩
  · exact ⟨fun _ => (hp m').1.le, fun _ => (hp m).1.le⟩
  · constructor <;> intro h <;> linarith [(hp m).2, (hp m').2]
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

/-- The sharpened cut estimate for `0 < s ≤ 1`: concavity over the at most
`q+1` chains and the at most `E+2` gaps replaces the counting factors of
`chain_cut_bound` by their `(1-s)`-th powers. -/
theorem chain_cut_bound_sharp {φ w : ℕ → ℝ} (hw : Summable w) (hn : ∀ n, 0 ≤ w n)
    (hi : Function.Injective φ) (hp : ∀ n, φ n ∈ Ioo (0 : ℝ) 1)
    {Z : ℕ → ℤ} {q : ℕ} {θ : ℝ} (hq : 0 < q) (hθ : θ ≠ 0)
    (hφ : ∀ k, (q : ℝ) * φ k = Z k + ((k : ℝ) + 1) * θ)
    {E N : ℕ} (hN : (N : ℝ) * |θ| ≤ 1) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    (∀ g ∈ cutGaps (earlyCuts φ E),
      jumpProfile φ w g.2 - jumpProfileRight φ w g.1 ≤ tailMass w E) ∧
    ∑ g ∈ cutGaps (earlyCuts φ E), (jumpProfile φ w g.2 - jumpProfileRight φ w g.1) ^ s ≤
      ((q : ℝ) + 1) ^ (1 - s) * tailMass w E ^ s +
        ((E : ℝ) + 2) ^ (1 - s) * tailMass w N ^ s := by
  classical
  refine ⟨(chain_cut_bound hw hn hi hp hq hθ hφ hN hs).1, ?_⟩
  set C := earlyCuts φ E
  set G := cutGaps C
  have hsum (R : ℕ → Prop) [DecidablePred R] : Summable (fun n => if R n then w n else 0) :=
    hw.of_norm_bounded fun n => by
      split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg (hn n), hn n]
  have hnn (R : ℕ → Prop) [DecidablePred R] : 0 ≤ ∑' n, if R n then w n else 0 :=
    tsum_nonneg fun n => by split_ifs <;> simp [hn n]
  have hearly : ∀ g ∈ G, ∀ n, g.1 < φ n → φ n < g.2 → E ≤ n := by
    intro g hg n h1 h2
    by_contra hlt
    push Not at hlt
    have hC : φ n ∈ C := mem_earlyCuts.2 (Or.inr (Or.inr ⟨n, hlt, rfl⟩))
    rcases (mem_cutGaps.1 hg).2.2.2 _ hC with h | h <;> linarith
  let mid : ℝ × ℝ → ℝ := fun g =>
    ∑' n, if (g.1 < φ n ∧ φ n < g.2) ∧ E ≤ n ∧ n < N then w n else 0
  let late : ℝ × ℝ → ℝ := fun g =>
    ∑' n, if (g.1 < φ n ∧ φ n < g.2) ∧ N ≤ n then w n else 0
  let lab : ℤ → ℝ × ℝ → ℝ := fun z g =>
    ∑' n, if ((g.1 < φ n ∧ φ n < g.2) ∧ E ≤ n ∧ n < N) ∧ Z n = z then w n else 0
  let chain : ℤ → ℝ := fun z => ∑' n, if (E ≤ n ∧ n < N) ∧ Z n = z then w n else 0
  have hsplit : ∀ g ∈ G, jumpProfile φ w g.2 - jumpProfileRight φ w g.1 ≤ mid g + late g := by
    intro g hg
    refine (jumpGap_mass_le hw hn (fun n => g.1 < φ n ∧ φ n < g.2) fun n h1 h2 =>
      ⟨h1, h2⟩).trans (le_of_eq ?_)
    rw [← (hsum _).tsum_add (hsum _)]
    apply tsum_congr
    intro n
    by_cases hin : g.1 < φ n ∧ φ n < g.2
    · have hE := hearly g hg n hin.1 hin.2
      by_cases hN' : n < N
      · simp [hin, hE, hN', not_le_of_gt hN']
      · simp [hin, hE, hN', le_of_not_gt hN']
    · simp [hin]
  have hlabel : ∀ n, E ≤ n → n < N → Z n ∈ Finset.Icc (0 : ℤ) q := by
    intro n _ hnN
    apply chain_label_mem hq hφ hp
    have : (n : ℝ) + 1 ≤ N := by exact_mod_cast hnN
    exact (mul_le_mul_of_nonneg_right this (abs_nonneg θ)).trans hN
  have hmid : ∀ g, mid g = ∑ z ∈ Finset.Icc (0 : ℤ) q, lab z g := by
    intro g
    simp only [mid, lab]
    rw [← Summable.tsum_finsetSum (fun z _ => hsum _)]
    apply tsum_congr
    intro n
    by_cases hP : (g.1 < φ n ∧ φ n < g.2) ∧ E ≤ n ∧ n < N
    · simp only [hP, true_and, if_true]
      rw [Finset.sum_ite_eq]
      simp [hlabel n hP.2.1 hP.2.2]
    · simp [hP]
  have hlab_le : ∀ z g, lab z g ≤ chain z := by
    intro z g
    refine Summable.tsum_le_tsum (fun n => ?_) (hsum _) (hsum _)
    by_cases hP : ((g.1 < φ n ∧ φ n < g.2) ∧ E ≤ n ∧ n < N) ∧ Z n = z
    · simp [hP]
    · simp only [hP, if_false]
      split_ifs <;> simp [hn n]
  have hlab_pos : ∀ z g, lab z g ≠ 0 → ∃ n, ((g.1 < φ n ∧ φ n < g.2) ∧ E ≤ n ∧ n < N) ∧
      Z n = z := by
    intro z g h
    by_contra hno
    push Not at hno
    apply h
    simp only [lab]
    rw [tsum_congr (fun n => if_neg (fun hP => hno n hP.1 hP.2)), tsum_zero]
  have hone : ∀ z, ∑ g ∈ G, lab z g ^ s ≤ chain z ^ s := by
    intro z
    by_cases hex : ∃ g ∈ G, lab z g ≠ 0
    · obtain ⟨g0, hg0, hne⟩ := hex
      rw [Finset.sum_eq_single_of_mem g0 hg0]
      · exact Real.rpow_le_rpow (hnn _) (hlab_le z g0) hs.le
      · intro g hg hgne
        by_contra hne'
        have hne'' : lab z g ≠ 0 := fun h0 => hne' (by rw [h0, Real.zero_rpow hs.ne'])
        obtain ⟨m, ⟨⟨a1, a2⟩, b1, b2⟩, c1⟩ := hlab_pos z g hne''
        obtain ⟨m', ⟨⟨a1', a2'⟩, b1', b2'⟩, c1'⟩ := hlab_pos z g0 hne
        exact hgne (chain_same_gap hi hp hq hθ hφ hN hg hg0 b1 b2 b1' b2'
          (c1.trans c1'.symm) a1 a2 a1' a2')
    · push Not at hex
      rw [Finset.sum_eq_zero (fun g hg => by rw [hex g hg, Real.zero_rpow hs.ne'])]
      exact Real.rpow_nonneg (hnn _) s
  have hchain : ∑ z ∈ Finset.Icc (0 : ℤ) q, chain z ≤ tailMass w E :=
    sum_tsum_le_of_disjoint _ hw hn (fun z n => (E ≤ n ∧ n < N) ∧ Z n = z) (fun n => E ≤ n)
      (fun n z _ z' _ h h' => h.2.symm.trans h'.2) (fun z _ n h => h.1.1)
  have hlate : ∑ g ∈ G, late g ≤ tailMass w N :=
    sum_tsum_le_of_disjoint G hw hn (fun g n => (g.1 < φ n ∧ φ n < g.2) ∧ N ≤ n)
      (fun n => N ≤ n) (fun n g hg g' hg' h h' => cutGap_eq_of_mem hg hg' h.1 h'.1)
      (fun g _ n h => h.2)
  have hcardZ : ((Finset.Icc (0 : ℤ) q).card : ℝ) = (q : ℝ) + 1 := by
    simp
  have hcardG : (G.card : ℝ) ≤ (E : ℝ) + 2 := by
    exact_mod_cast (card_cutGaps_le C).trans (card_earlyCuts_le φ E)
  have hs1' : 0 ≤ 1 - s := by linarith
  have hmidsum : ∑ g ∈ G, mid g ^ s ≤ ((q : ℝ) + 1) ^ (1 - s) * tailMass w E ^ s := by
    calc
      _ ≤ ∑ g ∈ G, ∑ z ∈ Finset.Icc (0 : ℤ) q, lab z g ^ s := by
        apply Finset.sum_le_sum
        intro g _
        rw [hmid g]
        exact rpow_finset_sum_le _ (fun z _ => hnn _) hs hs1
      _ = ∑ z ∈ Finset.Icc (0 : ℤ) q, ∑ g ∈ G, lab z g ^ s := Finset.sum_comm
      _ ≤ ∑ z ∈ Finset.Icc (0 : ℤ) q, chain z ^ s := Finset.sum_le_sum fun z _ => hone z
      _ ≤ ((Finset.Icc (0 : ℤ) q).card : ℝ) ^ (1 - s) *
          (∑ z ∈ Finset.Icc (0 : ℤ) q, chain z) ^ s :=
        sum_rpow_le_card_mul _ (fun z _ => hnn _) hs hs1
      _ ≤ _ := by
        rw [hcardZ]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Finset.sum_nonneg fun z _ => hnn _) hchain hs.le)
          (Real.rpow_nonneg (by positivity) _)
  have hlatesum : ∑ g ∈ G, late g ^ s ≤ ((E : ℝ) + 2) ^ (1 - s) * tailMass w N ^ s := by
    calc
      _ ≤ (G.card : ℝ) ^ (1 - s) * (∑ g ∈ G, late g) ^ s :=
        sum_rpow_le_card_mul _ (fun g _ => hnn _) hs hs1
      _ ≤ _ := mul_le_mul (Real.rpow_le_rpow (Nat.cast_nonneg _) hcardG hs1')
        (Real.rpow_le_rpow (Finset.sum_nonneg fun g _ => hnn _) hlate hs.le)
        (Real.rpow_nonneg (Finset.sum_nonneg fun g _ => hnn _) _)
        (Real.rpow_nonneg (by positivity) _)
  calc
    _ ≤ ∑ g ∈ G, (mid g ^ s + late g ^ s) := by
      apply Finset.sum_le_sum
      intro g hg
      have hm0 : 0 ≤ jumpProfile φ w g.2 - jumpProfileRight φ w g.1 :=
        sub_nonneg.2 (jumpProfileRight_le_of_lt hw hn (mem_cutGaps.1 hg).2.2.1)
      exact (Real.rpow_le_rpow hm0 (hsplit g hg) hs.le).trans
        (Real.rpow_add_le_add_rpow (hnn _) (hnn _) hs.le hs1)
    _ = ∑ g ∈ G, mid g ^ s + ∑ g ∈ G, late g ^ s := Finset.sum_add_distrib
    _ ≤ _ := add_le_add hmidsum hlatesum

private theorem cube_ratio_term {x M T B δ : ℝ} (hx : 0 ≤ x) (hM : 0 < M) (hT : 0 ≤ T)
    (hB : 0 ≤ B) (hTle : T ≤ B * M ^ (-(1/2) : ℝ)) (hxM : x ≤ δ * M) :
    x ^ (1 - 2/3 : ℝ) * T ^ (2/3 : ℝ) ≤ B ^ (2/3 : ℝ) * δ ^ (1/3 : ℝ) := by
  have e1 : (1 - 2/3 : ℝ) = 1/3 := by norm_num
  rw [e1]
  have hT' : T ^ (2/3 : ℝ) ≤ B ^ (2/3 : ℝ) * (M ^ (1/3 : ℝ))⁻¹ := by
    calc
      T ^ (2/3 : ℝ) ≤ (B * M ^ (-(1/2) : ℝ)) ^ (2/3 : ℝ) :=
        Real.rpow_le_rpow hT hTle (by norm_num)
      _ = B ^ (2/3 : ℝ) * (M ^ (-(1/2) : ℝ)) ^ (2/3 : ℝ) :=
        Real.mul_rpow hB (Real.rpow_nonneg hM.le _)
      _ = _ := by
        rw [← Real.rpow_mul hM.le, ← Real.rpow_neg hM.le]
        norm_num
  have hr : x ^ (1/3 : ℝ) * (M ^ (1/3 : ℝ))⁻¹ ≤ δ ^ (1/3 : ℝ) := by
    rw [← div_eq_mul_inv, ← Real.div_rpow hx hM.le]
    exact Real.rpow_le_rpow (div_nonneg hx hM.le) ((div_le_iff₀ hM).2 hxM) (by norm_num)
  have hx3 := Real.rpow_nonneg hx (1/3 : ℝ)
  have hB3 := Real.rpow_nonneg hB (2/3 : ℝ)
  calc
    x ^ (1/3 : ℝ) * T ^ (2/3 : ℝ) ≤ x ^ (1/3 : ℝ) * (B ^ (2/3 : ℝ) * (M ^ (1/3 : ℝ))⁻¹) :=
      mul_le_mul_of_nonneg_left hT' hx3
    _ = B ^ (2/3 : ℝ) * (x ^ (1/3 : ℝ) * (M ^ (1/3 : ℝ))⁻¹) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hr hB3

private theorem side_first {q δ E : ℝ} (hq1 : 1 ≤ q) (hδ0 : 0 < δ)
    (hE : 2 * q / δ ≤ E) : q + 1 ≤ δ * E := by
  have h := mul_le_mul_of_nonneg_left hE hδ0.le
  have e : δ * (2 * q / δ) = 2 * q := by field_simp
  linarith

private theorem side_second {q δ E N : ℝ} (hq1 : 1 ≤ q) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hE : E < 2 * q / δ + 1) (hN : 5 * q / δ ^ 2 ≤ N) : E + 2 ≤ δ * N := by
  have h := mul_le_mul_of_nonneg_left hN hδ0.le
  have e : δ * (5 * q / δ ^ 2) = 5 * (q / δ) := by field_simp
  have e2 : 2 * q / δ = 2 * (q / δ) := by ring
  have hqd : 1 ≤ q / δ := by rw [le_div_iff₀ hδ0]; linarith
  linarith

/-- If the slope `α > 1` is irrational and not badly approximable, the
complete cluster set of the actual first-passage ratios has zero two-thirds
Hausdorff measure. -/
theorem not_bad_cluster_hausdorff {α : ℝ} (hα1 : 1 < α) (hα : Irrational α)
    (hnb : ∀ c : ℝ, 0 < c → ¬ DiophantineLowerBound α c 1) :
    Measure.hausdorffMeasure (2/3 : ℝ) (passageClusterSet (1/α)) = 0 := by
  have hα0 : 0 < α := by linarith
  have hβ0 : 0 < 1/α := one_div_pos.mpr hα0
  have hβ1 : 1/α < 1 := (div_lt_one hα0).mpr hα1
  have hβ : Irrational (1/α) := by simpa using hα.inv
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
  have hc : 0 < 2 * B := by positivity
  apply jumpRange_hausdorff_zero hw hn hi hp (by norm_num : (0 : ℝ) < 2/3)
  intro ε hε
  set K := (2 * B) ^ (2/3 : ℝ)
  have hK : 0 ≤ K := Real.rpow_nonneg hc.le _
  have hδt : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have t3 : Tendsto (fun j : ℕ => 2 * K * (1 / ((j : ℝ) + 1)) ^ (1/3 : ℝ)) atTop (𝓝 0) := by
    have h := ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1/3)).tendsto 0).comp hδt
    rw [Real.zero_rpow (by norm_num)] at h
    simpa using h.const_mul (2 * K)
  have t2 : Tendsto (fun j : ℕ => 2 * B * (1 / ((j : ℝ) + 1)) ^ (1/2 : ℝ)) atTop (𝓝 0) := by
    have h := ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1/2)).tendsto 0).comp hδt
    rw [Real.zero_rpow (by norm_num)] at h
    simpa using h.const_mul (2 * B)
  obtain ⟨j, hj3, hj2⟩ := ((t3.eventually (ge_mem_nhds hε)).and
    (t2.eventually (ge_mem_nhds hε))).exists
  set δ : ℝ := 1 / ((j : ℝ) + 1) with hδdef
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by
    rw [hδdef, div_le_one (by positivity)]
    linarith [Nat.cast_nonneg (α := ℝ) j]
  have hcpos : 0 < δ ^ 2 / 10 := by positivity
  have hq := hnb (δ ^ 2 / 10) hcpos
  unfold DiophantineLowerBound at hq
  push Not at hq
  obtain ⟨q, hq0, p, hqp⟩ := hq
  rw [Real.rpow_one] at hqp
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq0
  set θ := (q : ℝ) * α - p with hθdef
  have hθ : θ ≠ 0 := by
    intro h
    exact (hα.natCast_mul hq0.ne').ne_int p (by linarith)
  have habs : 0 < |θ| := abs_pos.2 hθ
  let Z : ℕ → ℤ := fun k => ((k : ℤ) + 1) * p - q * ⌊((k : ℝ) + 1) * α⌋
  have hφ : ∀ k, (q : ℝ) * φ k = Z k + ((k : ℝ) + 1) * θ := by
    intro k
    rw [hfr k, Int.fract]
    simp only [Z, θ]
    push_cast
    ring
  set N := ⌊1/|θ|⌋₊
  have hN : (N : ℝ) * |θ| ≤ 1 := by
    have := Nat.floor_le (by positivity : (0 : ℝ) ≤ 1/|θ|)
    rwa [le_div_iff₀ habs] at this
  have hNlow : 5 * q / δ ^ 2 ≤ (N : ℝ) := by
    have h1 := Nat.lt_floor_add_one (1/|θ|)
    have h2 : 10 * q / δ ^ 2 < 1/|θ| := by
      rw [lt_div_iff₀ habs, div_mul_eq_mul_div, div_lt_one (by positivity)]
      nlinarith
    have h3 : 1 ≤ 5 * q / δ ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have h4 : 10 * q / δ ^ 2 = 2 * (5 * q / δ ^ 2) := by ring
    change 1/|θ| < (N : ℝ) + 1 at h1
    linarith
  set E := ⌈2 * q / δ⌉₊
  have hE1 : 2 * q / δ ≤ (E : ℝ) := Nat.le_ceil _
  have hE2 : (E : ℝ) < 2 * q / δ + 1 := Nat.ceil_lt_add_one (by positivity)
  have hqδ : (1 : ℝ) ≤ 2 * q / δ := by
    rw [le_div_iff₀ hδ0]
    linarith
  have hE0 : 0 < E := by exact_mod_cast (show (0 : ℝ) < E by linarith)
  have hNR : (0 : ℝ) < N := by
    have : (0 : ℝ) < 5 * q / δ ^ 2 := by positivity
    linarith
  have hN0 : 0 < N := by exact_mod_cast hNR
  have hER : (0 : ℝ) < E := by exact_mod_cast hE0
  obtain ⟨hdiam, hsum⟩ := chain_cut_bound_sharp hw hn hi hp hq0 hθ hφ hN (E := E)
    (by norm_num : (0 : ℝ) < 2/3) (by norm_num)
  have hTE := tailMass_le hw hn hB.le hb hE0
  have hTN := tailMass_le hw hn hB.le hb hN0
  refine ⟨earlyCuts φ E, by simp [earlyCuts], by simp [earlyCuts], fun g hg => ?_, hsum.trans ?_⟩
  · have hEδ : δ⁻¹ ≤ (E : ℝ) := by
      have : δ⁻¹ ≤ 2 * q / δ := by
        rw [inv_eq_one_div, div_le_div_iff_of_pos_right hδ0]
        linarith
      linarith
    have h1 := Real.rpow_le_rpow_of_nonpos (by positivity) hEδ (by norm_num : (-(1/2) : ℝ) ≤ 0)
    have hkey : (δ⁻¹) ^ (-(1/2) : ℝ) = δ ^ (1/2 : ℝ) := by
      rw [Real.rpow_neg (inv_nonneg.2 hδ0.le), Real.inv_rpow hδ0.le, inv_inv]
    rw [hkey] at h1
    have hj2' : 2 * B * δ ^ (1/2 : ℝ) ≤ ε := hj2
    calc
      _ ≤ tailMass w E := hdiam g hg
      _ ≤ 2 * B * (E : ℝ) ^ (-(1/2) : ℝ) := hTE
      _ ≤ 2 * B * δ ^ (1/2 : ℝ) := mul_le_mul_of_nonneg_left h1 hc.le
      _ ≤ ε := hj2'
  · have e1 := cube_ratio_term (x := (q : ℝ) + 1) (by positivity) hER (tailMass_nonneg hn E)
      hc.le hTE (side_first hq1 hδ0 hE1)
    have e2 := cube_ratio_term (x := (E : ℝ) + 2) (by positivity) hNR (tailMass_nonneg hn N)
      hc.le hTN (side_second hq1 hδ0 hδ1 hE2 hNlow)
    have hj3' : 2 * K * δ ^ (1/3 : ℝ) ≤ ε := hj3
    calc
      _ ≤ K * δ ^ (1/3 : ℝ) + K * δ ^ (1/3 : ℝ) := add_le_add e1 e2
      _ ≤ ε := by linarith

/-- The two-thirds Hausdorff measure of the complete cluster set at an
irrational slope `α > 1` is positive exactly when `α` is badly approximable. -/
theorem cluster_hausdorff_pos_iff {α : ℝ} (hα1 : 1 < α) (hα : Irrational α) :
    0 < Measure.hausdorffMeasure (2/3 : ℝ) (passageClusterSet (1/α)) ↔
      ∃ c : ℝ, 0 < c ∧ DiophantineLowerBound α c 1 := by
  have hα0 : 0 < α := by linarith
  have hβ0 : 0 < 1/α := one_div_pos.mpr hα0
  have hβ1 : 1/α < 1 := (div_lt_one hα0).mpr hα1
  have hβ : Irrational (1/α) := by simpa using hα.inv
  constructor
  · intro hpos
    by_contra hno
    push Not at hno
    rw [not_bad_cluster_hausdorff hα1 hα hno] at hpos
    exact lt_irrefl _ hpos
  · rintro ⟨c, hc, hdio⟩
    exact (passageCluster_hausdorff_bad hβ0 hβ1 hβ hc
      (by simpa only [one_div_one_div] using hdio)).1

private theorem tail_pow_le {T c M s : ℝ} (hM : 0 < M) (hT : 0 ≤ T) (hc : 0 ≤ c)
    (h : T ≤ c * M ^ (-(1/2) : ℝ)) (hs : 0 < s) :
    T ^ s ≤ c ^ s * M ^ (-(s/2)) := by
  calc
    T ^ s ≤ (c * M ^ (-(1/2) : ℝ)) ^ s := Real.rpow_le_rpow hT h hs.le
    _ = c ^ s * (M ^ (-(1/2) : ℝ)) ^ s := Real.mul_rpow hc (Real.rpow_nonneg hM.le _)
    _ = _ := by
      rw [← Real.rpow_mul hM.le]
      ring_nf

private theorem term_first {q E T c e s : ℝ} (hq1 : 1 ≤ q)
    (hE : q ^ e ≤ E) (hT : 0 ≤ T) (hc : 0 ≤ c) (hTE : T ≤ c * E ^ (-(1/2) : ℝ))
    (hs : 0 < s) (hs1 : s ≤ 1) :
    (q + 1) ^ (1 - s) * T ^ s ≤ 2 * c ^ s * q ^ ((1 - s) - e * s / 2) := by
  have hq0 : 0 < q := by linarith
  have hqe : 0 < q ^ e := Real.rpow_pos_of_pos hq0 e
  have hE0 : 0 < E := hqe.trans_le hE
  have h1 := tail_pow_le hE0 hT hc hTE hs
  have h2 : E ^ (-(s/2)) ≤ q ^ (-(e * s / 2)) := by
    calc
      E ^ (-(s/2)) ≤ (q ^ e) ^ (-(s/2)) :=
        Real.rpow_le_rpow_of_nonpos hqe hE (by linarith)
      _ = _ := by
        rw [← Real.rpow_mul hq0.le]
        ring_nf
  have h3 : (q + 1) ^ (1 - s) ≤ 2 * q ^ (1 - s) := by
    calc
      (q + 1) ^ (1 - s) ≤ (2 * q) ^ (1 - s) :=
        Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
      _ = 2 ^ (1 - s) * q ^ (1 - s) := Real.mul_rpow (by norm_num) hq0.le
      _ ≤ 2 * q ^ (1 - s) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hq0.le _)
        simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          (by linarith : 1 - s ≤ 1)
  have hcs := Real.rpow_nonneg hc s
  have hq1s := Real.rpow_nonneg hq0.le (1 - s)
  calc
    (q + 1) ^ (1 - s) * T ^ s ≤ (2 * q ^ (1 - s)) * (c ^ s * q ^ (-(e * s / 2))) :=
      mul_le_mul h3 (h1.trans (mul_le_mul_of_nonneg_left h2 hcs)) (Real.rpow_nonneg hT s)
        (by positivity)
    _ = 2 * c ^ s * (q ^ (1 - s) * q ^ (-(e * s / 2))) := by ring
    _ = _ := by
      rw [← Real.rpow_add hq0]
      ring_nf

private theorem term_second {q E N T c e ν s : ℝ} (hq1 : 1 ≤ q) (he : 0 ≤ e)
    (hE : E ≤ q ^ e + 1) (hE0 : 0 ≤ E) (hν : 2 ≤ q ^ ν) (hN : q ^ ν / 2 ≤ N) (hT : 0 ≤ T)
    (hc : 0 ≤ c) (hTN : T ≤ c * N ^ (-(1/2) : ℝ)) (hs : 0 < s) (hs1 : s ≤ 1) :
    (E + 2) ^ (1 - s) * T ^ s ≤ 8 * c ^ s * q ^ (e * (1 - s) - ν * s / 2) := by
  have hq0 : 0 < q := by linarith
  have hqe1 : 1 ≤ q ^ e := Real.one_le_rpow hq1 he
  have hqν : 0 < q ^ ν / 2 := by linarith
  have hN0 : 0 < N := hqν.trans_le hN
  have h1 := tail_pow_le hN0 hT hc hTN hs
  have h2 : N ^ (-(s/2)) ≤ 2 * q ^ (-(ν * s / 2)) := by
    calc
      N ^ (-(s/2)) ≤ (q ^ ν / 2) ^ (-(s/2)) :=
        Real.rpow_le_rpow_of_nonpos hqν hN (by linarith)
      _ = (2 ^ (s/2)) * q ^ (-(ν * s / 2)) := by
        rw [Real.div_rpow (Real.rpow_nonneg hq0.le _) (by norm_num), ← Real.rpow_mul hq0.le,
          Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul, mul_comm]
        ring_nf
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hq0.le _)
        simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          (by linarith : s/2 ≤ 1)
  have h3 : (E + 2) ^ (1 - s) ≤ 4 * q ^ (e * (1 - s)) := by
    calc
      (E + 2) ^ (1 - s) ≤ (4 * q ^ e) ^ (1 - s) :=
        Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
      _ = 4 ^ (1 - s) * q ^ (e * (1 - s)) := by
        rw [Real.mul_rpow (by norm_num) (by linarith), ← Real.rpow_mul hq0.le]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hq0.le _)
        simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4)
          (by linarith : 1 - s ≤ 1)
  have hcs := Real.rpow_nonneg hc s
  calc
    (E + 2) ^ (1 - s) * T ^ s ≤ (4 * q ^ (e * (1 - s))) *
        (c ^ s * (2 * q ^ (-(ν * s / 2)))) :=
      mul_le_mul h3 (h1.trans (mul_le_mul_of_nonneg_left h2 hcs)) (Real.rpow_nonneg hT s)
        (by positivity)
    _ = 8 * c ^ s * (q ^ (e * (1 - s)) * q ^ (-(ν * s / 2))) := by ring
    _ = _ := by
      rw [← Real.rpow_add hq0]
      ring_nf

/-- If `|q*α - p| ≤ q^(-ν)` has solutions with arbitrarily large `q`, for
some `ν > 1`, then every Hausdorff measure of the complete cluster set with
exponent `s` in `(2/(2+√ν), 1]` vanishes. -/
theorem dio_exponent_hausdorff {α ν : ℝ} (hα1 : 1 < α) (hα : Irrational α) (hν : 1 < ν)
    (happ : ∀ Q : ℕ, ∃ q : ℕ, Q < q ∧ ∃ p : ℤ, |(q : ℝ) * α - p| ≤ (q : ℝ) ^ (-ν))
    {s : ℝ} (hs : 2 / (2 + Real.sqrt ν) < s) (hs1 : s ≤ 1) :
    Measure.hausdorffMeasure s (passageClusterSet (1/α)) = 0 := by
  have hα0 : 0 < α := by linarith
  have hβ0 : 0 < 1/α := one_div_pos.mpr hα0
  have hβ1 : 1/α < 1 := (div_lt_one hα0).mpr hα1
  have hβ : Irrational (1/α) := by simpa using hα.inv
  have hsq : 0 < Real.sqrt ν := Real.sqrt_pos.2 (by linarith)
  have hs0 : 0 < s := lt_trans (by positivity) hs
  have hwin : 4 * (1 - s) ^ 2 < ν * s ^ 2 := by
    have h1 : 2 < s * (2 + Real.sqrt ν) := by
      rwa [div_lt_iff₀ (by positivity)] at hs
    have h2 : 2 * (1 - s) < Real.sqrt ν * s := by linarith
    have h3 : 0 ≤ 2 * (1 - s) := by linarith
    have h4 := mul_self_lt_mul_self h3 h2
    have h5 : Real.sqrt ν * Real.sqrt ν = ν := Real.mul_self_sqrt (by linarith)
    nlinarith
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
  have hc : 0 < 2 * B := by positivity
  set K := (2 * B) ^ s
  -- exponents
  set m := ν * s / 2 - 2 * (1 - s) ^ 2 / s with hmdef
  have hm : 0 < m := by
    rw [hmdef, sub_pos, div_lt_div_iff₀ hs0 (by norm_num)]
    nlinarith
  set e := 2 * (1 - s) / s + m / 2 with hedef
  have he : 0 < e := by
    have : 0 ≤ 2 * (1 - s) / s := div_nonneg (by linarith) hs0.le
    linarith
  have ha1 : (1 - s) - e * s / 2 = -(m * s / 4) := by
    rw [hedef]
    field_simp
    ring
  have ha2 : e * (1 - s) - ν * s / 2 ≤ -(m / 2) := by
    have h0 : 2 * (1 - s) / s * (1 - s) = 2 * (1 - s) ^ 2 / s := by ring
    have h1 : e * (1 - s) - ν * s / 2 = -m + m / 2 * (1 - s) := by
      rw [hedef, add_mul, h0, hmdef]
      ring
    rw [h1]
    nlinarith
  apply jumpRange_hausdorff_zero hw hn hi hp hs0
  intro ε hε
  have tq : Tendsto (fun q : ℕ => (q : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have lim (y : ℝ) (hy : 0 < y) (C : ℝ) :
      Tendsto (fun q : ℕ => C * (q : ℝ) ^ (-y)) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop hy).comp tq).const_mul C
  have ev1 : ∀ᶠ q : ℕ in atTop, (2 : ℝ) ≤ (q : ℝ) ^ ν :=
    ((tendsto_rpow_atTop (by linarith : (0 : ℝ) < ν)).comp tq).eventually_ge_atTop 2
  have ev2 : ∀ᶠ q : ℕ in atTop, (1 : ℝ) ≤ q := tq.eventually_ge_atTop 1
  have ev3 := (lim _ (by positivity : 0 < m * s / 4) (2 * K)).eventually
    (ge_mem_nhds (half_pos hε))
  have ev4 := (lim _ (by positivity : 0 < m / 2) (8 * K)).eventually
    (ge_mem_nhds (half_pos hε))
  have ev5 := (lim _ (by positivity : 0 < e / 2) (2 * B)).eventually (ge_mem_nhds hε)
  have hfreq : ∃ᶠ q : ℕ in atTop, ∃ p : ℤ, |(q : ℝ) * α - p| ≤ (q : ℝ) ^ (-ν) :=
    frequently_atTop.2 fun Q => by
      obtain ⟨q, hq, h⟩ := happ Q
      exact ⟨q, hq.le, h⟩
  obtain ⟨q, ⟨p, hqp⟩, hqν, hq1, h3, h4, h5⟩ :=
    (hfreq.and_eventually (ev1.and (ev2.and (ev3.and (ev4.and ev5))))).exists
  have hqR : (0 : ℝ) < q := by linarith
  have hq0 : 0 < q := by exact_mod_cast hqR
  set θ := (q : ℝ) * α - p with hθdef
  have hθ : θ ≠ 0 := by
    intro h
    exact (hα.natCast_mul hq0.ne').ne_int p (by linarith)
  have habs : 0 < |θ| := abs_pos.2 hθ
  let Z : ℕ → ℤ := fun k => ((k : ℤ) + 1) * p - q * ⌊((k : ℝ) + 1) * α⌋
  have hφ : ∀ k, (q : ℝ) * φ k = Z k + ((k : ℝ) + 1) * θ := by
    intro k
    rw [hfr k, Int.fract]
    simp only [Z, θ]
    push_cast
    ring
  set N := ⌊1/|θ|⌋₊
  have hN : (N : ℝ) * |θ| ≤ 1 := by
    have := Nat.floor_le (by positivity : (0 : ℝ) ≤ 1/|θ|)
    rwa [le_div_iff₀ habs] at this
  have hNlow : (q : ℝ) ^ ν / 2 ≤ N := by
    have h1 := Nat.lt_floor_add_one (1/|θ|)
    have h2 : (q : ℝ) ^ ν ≤ 1/|θ| := by
      rw [le_div_iff₀ habs]
      have e1 : (q : ℝ) ^ ν * (q : ℝ) ^ (-ν) = 1 := by
        rw [← Real.rpow_add hqR]
        simp
      have := mul_le_mul_of_nonneg_left hqp (Real.rpow_nonneg hqR.le ν)
      linarith
    change 1/|θ| < (N : ℝ) + 1 at h1
    linarith
  set E := ⌈(q : ℝ) ^ e⌉₊
  have hE1 : (q : ℝ) ^ e ≤ E := Nat.le_ceil _
  have hE2 : (E : ℝ) < (q : ℝ) ^ e + 1 := Nat.ceil_lt_add_one (Real.rpow_nonneg hqR.le _)
  have hqe : 0 < (q : ℝ) ^ e := Real.rpow_pos_of_pos hqR e
  have hER : (0 : ℝ) < E := hqe.trans_le hE1
  have hE0 : 0 < E := by exact_mod_cast hER
  have hNR : (0 : ℝ) < N := lt_of_lt_of_le (by linarith) hNlow
  have hN0 : 0 < N := by exact_mod_cast hNR
  obtain ⟨hdiam, hsum⟩ := chain_cut_bound_sharp hw hn hi hp hq0 hθ hφ hN (E := E) hs0 hs1
  have hTE := tailMass_le hw hn hB.le hb hE0
  have hTN := tailMass_le hw hn hB.le hb hN0
  refine ⟨earlyCuts φ E, by simp [earlyCuts], by simp [earlyCuts], fun g hg => ?_, hsum.trans ?_⟩
  · have h1 : (E : ℝ) ^ (-(1/2) : ℝ) ≤ (q : ℝ) ^ (-(e / 2)) := by
      calc
        (E : ℝ) ^ (-(1/2) : ℝ) ≤ ((q : ℝ) ^ e) ^ (-(1/2) : ℝ) :=
          Real.rpow_le_rpow_of_nonpos hqe hE1 (by norm_num)
        _ = _ := by
          rw [← Real.rpow_mul hqR.le]
          ring_nf
    calc
      _ ≤ tailMass w E := hdiam g hg
      _ ≤ 2 * B * (E : ℝ) ^ (-(1/2) : ℝ) := hTE
      _ ≤ 2 * B * (q : ℝ) ^ (-(e / 2)) := mul_le_mul_of_nonneg_left h1 hc.le
      _ ≤ ε := h5
  · have t1 := term_first hq1 hE1 (tailMass_nonneg hn E) hc.le hTE hs0 hs1
    have t2 := term_second hq1 he.le hE2.le hER.le hqν hNlow (tailMass_nonneg hn N) hc.le
      hTN hs0 hs1
    rw [ha1] at t1
    have t2' : 8 * K * (q : ℝ) ^ (e * (1 - s) - ν * s / 2) ≤ 8 * K * (q : ℝ) ^ (-(m / 2)) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hq1 ha2)
        (by positivity)
    linarith

/-- If `|q*α - p| ≤ q^(-ν)` has solutions with arbitrarily large `q`, for
some `ν > 1`, then the complete cluster set at the slope `α` has Hausdorff
dimension at most `2/(2+√ν)`. -/
theorem dio_exponent_dimH_le {α ν : ℝ} (hα1 : 1 < α) (hα : Irrational α) (hν : 1 < ν)
    (happ : ∀ Q : ℕ, ∃ q : ℕ, Q < q ∧ ∃ p : ℤ, |(q : ℝ) * α - p| ≤ (q : ℝ) ^ (-ν)) :
    dimH (passageClusterSet (1/α)) ≤ ENNReal.ofReal (2 / (2 + Real.sqrt ν)) := by
  have hsq : 0 < Real.sqrt ν := Real.sqrt_pos.2 (by linarith)
  have hD : 2 / (2 + Real.sqrt ν) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  have hD0 : 0 ≤ 2 / (2 + Real.sqrt ν) := by positivity
  apply le_of_forall_gt_imp_ge_of_dense
  intro c hc
  by_cases hct : c = ⊤
  · rw [hct]
    exact le_top
  set r := c.toReal
  have hcr : c = ENNReal.ofReal r := (ENNReal.ofReal_toReal hct).symm
  have hr : 2 / (2 + Real.sqrt ν) < r := by
    rw [hcr] at hc
    exact (ENNReal.ofReal_lt_ofReal_iff'.1 hc).1
  set s := min r 1
  have hs : 2 / (2 + Real.sqrt ν) < s := lt_min hr hD
  have hs0 : 0 ≤ s := hD0.trans hs.le
  have h0 := dio_exponent_hausdorff hα1 hα hν happ hs (min_le_right _ _)
  have hne : Measure.hausdorffMeasure ((s.toNNReal : ℝ≥0) : ℝ)
      (passageClusterSet (1/α)) ≠ ⊤ := by
    rw [Real.coe_toNNReal _ hs0, h0]
    exact ENNReal.zero_ne_top
  calc
    _ ≤ ((s.toNNReal : ℝ≥0) : ℝ≥0∞) := dimH_le_of_hausdorffMeasure_ne_top hne
    _ = ENNReal.ofReal s := rfl
    _ ≤ ENNReal.ofReal r := ENNReal.ofReal_le_ofReal (min_le_left _ _)
    _ = c := hcr.symm

end Problems.Juggler.BeattySlope

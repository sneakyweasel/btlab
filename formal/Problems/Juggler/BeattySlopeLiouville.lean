import Problems.Juggler.BeattyJumpCover
import Problems.Juggler.BeattySlopeWeights
import Problems.Juggler.BeattyGapDecay
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith

/-!
# Zero Hausdorff dimension at Liouville slopes

A very good rational approximation `p/q` of the slope arranges all early
crossing phases along `q+1` short arithmetic chains. Cutting at the early
atoms leaves at most `q+1` gaps that meet a chain; every other gap carries
only late mass. The three-halves weight bound then makes every positive
Hausdorff measure of the complete cluster set vanish at Liouville slopes.
-/

namespace Problems.Juggler.BeattySlope

open Filter Topology Set MeasureTheory BeattyPhase
open scoped NNReal ENNReal

/-- The mass of the atoms with index at least `M`. -/
noncomputable def tailMass (w : ℕ → ℝ) (M : ℕ) : ℝ := ∑' n, if M ≤ n then w n else 0

/-- Tail masses of nonnegative weights are nonnegative. -/
theorem tailMass_nonneg {w : ℕ → ℝ} (hn : ∀ n, 0 ≤ w n) (M : ℕ) : 0 ≤ tailMass w M :=
  tsum_nonneg fun n => by split_ifs <;> simp [hn n]

/-- Along a common approximation `q*x = Z + (k+1)*θ`, an earlier phase never
lies strictly between two later phases of one chain, while `|θ|` times the
index differences stays below one. -/
theorem chain_no_cut_between {φ : ℕ → ℝ} {Z : ℕ → ℤ} {q θ : ℝ} (hq : 0 < q)
    (hφ : ∀ k, q * φ k = Z k + ((k : ℝ) + 1) * θ) {n m m' : ℕ} (hm : n < m)
    (hm' : n < m') (hZ : Z m = Z m') (h1 : ((m : ℝ) - n) * |θ| < 1)
    (h2 : ((m' : ℝ) - n) * |θ| < 1) : ¬ (φ m < φ n ∧ φ n < φ m') := by
  rintro ⟨ha, hb⟩
  have ha' := mul_lt_mul_of_pos_left ha hq
  have hb' := mul_lt_mul_of_pos_left hb hq
  rw [hφ, hφ] at ha' hb'
  have hmn : (0 : ℝ) < (m : ℝ) - n := by
    have : (n : ℝ) < m := by exact_mod_cast hm
    linarith
  have hmn' : (0 : ℝ) < (m' : ℝ) - n := by
    have : (n : ℝ) < m' := by exact_mod_cast hm'
    linarith
  have hA : -(((m : ℝ) - n) * |θ|) ≤ ((m : ℝ) - n) * θ := by
    have := neg_abs_le θ
    nlinarith
  have hB : ((m' : ℝ) - n) * θ ≤ ((m' : ℝ) - n) * |θ| := by
    have := le_abs_self θ
    nlinarith
  have e1 : (-1 : ℝ) < ((Z n - Z m : ℤ) : ℝ) := by push_cast; nlinarith
  have e2 : ((Z n - Z m' : ℤ) : ℝ) < 1 := by push_cast; nlinarith
  have e1' : (-1 : ℤ) < Z n - Z m := by exact_mod_cast e1
  have e2' : Z n - Z m' < 1 := by exact_mod_cast e2
  have hZn : Z n = Z m := by omega
  have hZn' : (Z n : ℝ) = Z m := by exact_mod_cast hZn
  have hZm : (Z m : ℝ) = Z m' := by exact_mod_cast hZ
  have c1 : ((m : ℝ) - n) * θ < 0 := by nlinarith
  have c2 : 0 < ((m' : ℝ) - n) * θ := by nlinarith
  rcases lt_or_ge θ 0 with h | h
  · nlinarith
  · nlinarith

/-- The chain label of a phase with `(k+1)*|θ| ≤ 1` lies in `[0, q]`. -/
theorem chain_label_mem {φ : ℕ → ℝ} {Z : ℕ → ℤ} {q : ℕ} {θ : ℝ} (hq : 0 < q)
    (hφ : ∀ k, (q : ℝ) * φ k = Z k + ((k : ℝ) + 1) * θ)
    (hp : ∀ n, φ n ∈ Ioo (0 : ℝ) 1) {m : ℕ} (hm : ((m : ℝ) + 1) * |θ| ≤ 1) :
    Z m ∈ Finset.Icc (0 : ℤ) q := by
  have h := hφ m
  have hq : (0 : ℝ) < q := by exact_mod_cast hq
  have h0 := (hp m).1
  have h1 := (hp m).2
  have hpos : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
  have hA : -(((m : ℝ) + 1) * |θ|) ≤ ((m : ℝ) + 1) * θ := by
    have := neg_abs_le θ
    nlinarith
  have hB : ((m : ℝ) + 1) * θ ≤ ((m : ℝ) + 1) * |θ| := by
    have := le_abs_self θ
    nlinarith
  have hqφ : 0 < (q : ℝ) * φ m := mul_pos hq h0
  have hqφ' : (q : ℝ) * φ m < q := by nlinarith
  have e1 : (-1 : ℝ) < (Z m : ℝ) := by linarith
  have e2 : (Z m : ℝ) < (q : ℝ) + 1 := by linarith
  have e1' : (-1 : ℤ) < Z m := by exact_mod_cast e1
  have e2' : Z m < (q : ℤ) + 1 := by exact_mod_cast e2
  rw [Finset.mem_Icc]
  omega

/-- The cuts at both unit endpoints and at the first `E` phases. -/
noncomputable def earlyCuts (φ : ℕ → ℝ) (E : ℕ) : Finset ℝ :=
  insert 0 (insert 1 ((Finset.range E).image φ))

/-- The early cut set has at most `E+2` points. -/
theorem card_earlyCuts_le (φ : ℕ → ℝ) (E : ℕ) : (earlyCuts φ E).card ≤ E + 2 := by
  unfold earlyCuts
  have h1 := Finset.card_insert_le (0 : ℝ) (insert 1 ((Finset.range E).image φ))
  have h2 := Finset.card_insert_le (1 : ℝ) ((Finset.range E).image φ)
  have h3 := Finset.card_image_le (s := Finset.range E) (f := φ)
  rw [Finset.card_range] at h3
  omega

/-- Membership in the early cut set. -/
theorem mem_earlyCuts {φ : ℕ → ℝ} {E : ℕ} {e : ℝ} :
    e ∈ earlyCuts φ E ↔ e = 0 ∨ e = 1 ∨ ∃ k < E, φ k = e := by
  simp [earlyCuts]

/-- The finite cut estimate along a common approximation `q*x = Z+(k+1)*θ`:
every gap has length at most the tail from `E`, and the `s`-th powers sum
to at most `(q+1)` early-tail terms plus `E+2` late-tail terms. -/
theorem chain_cut_bound {φ w : ℕ → ℝ} (hw : Summable w) (hn : ∀ n, 0 ≤ w n)
    (hi : Function.Injective φ) (hp : ∀ n, φ n ∈ Ioo (0 : ℝ) 1)
    {Z : ℕ → ℤ} {q : ℕ} {θ : ℝ} (hq : 0 < q) (hθ : θ ≠ 0)
    (hφ : ∀ k, (q : ℝ) * φ k = Z k + ((k : ℝ) + 1) * θ)
    {E N : ℕ} (hN : (N : ℝ) * |θ| ≤ 1) {s : ℝ} (hs : 0 < s) :
    (∀ g ∈ cutGaps (earlyCuts φ E),
      jumpProfile φ w g.2 - jumpProfileRight φ w g.1 ≤ tailMass w E) ∧
    ∑ g ∈ cutGaps (earlyCuts φ E), (jumpProfile φ w g.2 - jumpProfileRight φ w g.1) ^ s ≤
      ((q : ℝ) + 1) * tailMass w E ^ s + ((E : ℝ) + 2) * tailMass w N ^ s := by
  classical
  set C := earlyCuts φ E
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have habs : 0 < |θ| := abs_pos.2 hθ
  have hearly : ∀ g ∈ cutGaps C, ∀ n, g.1 < φ n → φ n < g.2 → E ≤ n := by
    intro g hg n h1 h2
    by_contra hlt
    push Not at hlt
    have hC : φ n ∈ C := mem_earlyCuts.2 (Or.inr (Or.inr ⟨n, hlt, rfl⟩))
    rcases (mem_cutGaps.1 hg).2.2.2 _ hC with h | h <;> linarith
  let hit : ℝ × ℝ → Prop := fun g => ∃ m, E ≤ m ∧ m < N ∧ g.1 < φ m ∧ φ m < g.2
  have hmass0 : ∀ g ∈ cutGaps C, 0 ≤ jumpProfile φ w g.2 - jumpProfileRight φ w g.1 :=
    fun g hg => sub_nonneg.2 (jumpProfileRight_le_of_lt hw hn (mem_cutGaps.1 hg).2.2.1)
  have hmassE : ∀ g ∈ cutGaps C,
      jumpProfile φ w g.2 - jumpProfileRight φ w g.1 ≤ tailMass w E :=
    fun g hg => jumpGap_mass_le hw hn (fun n => E ≤ n) (hearly g hg)
  have hmassN : ∀ g ∈ cutGaps C, ¬ hit g →
      jumpProfile φ w g.2 - jumpProfileRight φ w g.1 ≤ tailMass w N := by
    intro g hg hng
    apply jumpGap_mass_le hw hn (fun n => N ≤ n)
    intro n h1 h2
    by_contra h
    push Not at h
    exact hng ⟨n, hearly g hg n h1 h2, h, h1, h2⟩
  have hTE := Real.rpow_nonneg (tailMass_nonneg hn E) s
  have hTN := Real.rpow_nonneg (tailMass_nonneg hn N) s
  have hterm : ∀ g ∈ cutGaps C, (jumpProfile φ w g.2 - jumpProfileRight φ w g.1) ^ s ≤
      (if hit g then tailMass w E ^ s else 0) + tailMass w N ^ s := by
    intro g hg
    split_ifs with hh
    · have := Real.rpow_le_rpow (hmass0 g hg) (hmassE g hg) hs.le
      linarith
    · simpa using Real.rpow_le_rpow (hmass0 g hg) (hmassN g hg hh) hs.le
  have hone (z : ℤ) : ((cutGaps C).filter (fun g => ∃ m, E ≤ m ∧ m < N ∧ Z m = z ∧
      g.1 < φ m ∧ φ m < g.2)).card ≤ 1 := by
    apply Finset.card_le_one.2
    intro g hg g' hg'
    obtain ⟨hgG, m, hEm, hmN, hz, h1, h2⟩ := Finset.mem_filter.1 hg
    obtain ⟨hgG', m', hEm', hmN', hz', h1', h2'⟩ := Finset.mem_filter.1 hg'
    apply cutGap_eq_of_no_cut hgG hgG' ⟨h1, h2⟩ ⟨h1', h2'⟩
    intro e he
    rcases mem_earlyCuts.1 he with rfl | rfl | ⟨k, hk, rfl⟩
    · exact ⟨fun _ => (hp m').1.le, fun _ => (hp m).1.le⟩
    · constructor <;> intro h <;> linarith [(hp m).2, (hp m').2]
    · have hkm : k < m := lt_of_lt_of_le hk hEm
      have hkm' : k < m' := lt_of_lt_of_le hk hEm'
      have hZ : Z m = Z m' := hz.trans hz'.symm
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
  have hsub : (cutGaps C).filter hit ⊆ (Finset.Icc (0 : ℤ) q).biUnion (fun z =>
      (cutGaps C).filter (fun g => ∃ m, E ≤ m ∧ m < N ∧ Z m = z ∧
        g.1 < φ m ∧ φ m < g.2)) := by
    intro g hg
    obtain ⟨hgG, m, hEm, hmN, h1, h2⟩ := Finset.mem_filter.1 hg
    have hm : ((m : ℝ) + 1) * |θ| ≤ 1 := by
      have : (m : ℝ) + 1 ≤ N := by exact_mod_cast hmN
      exact (mul_le_mul_of_nonneg_right this habs.le).trans hN
    exact Finset.mem_biUnion.2 ⟨Z m, chain_label_mem hq hφ hp hm,
      Finset.mem_filter.2 ⟨hgG, m, hEm, hmN, rfl, h1, h2⟩⟩
  have hcard : ((cutGaps C).filter hit).card ≤ q + 1 := by
    refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans
      ((Finset.sum_le_sum fun z _ => hone z).trans ?_))
    simp
  have hcardG : (cutGaps C).card ≤ E + 2 := (card_cutGaps_le C).trans (card_earlyCuts_le φ E)
  have hcardR : (((cutGaps C).filter hit).card : ℝ) ≤ (q : ℝ) + 1 := by exact_mod_cast hcard
  have hcardGR : ((cutGaps C).card : ℝ) ≤ (E : ℝ) + 2 := by exact_mod_cast hcardG
  refine ⟨hmassE, ?_⟩
  calc
    _ ≤ ∑ g ∈ cutGaps C, ((if hit g then tailMass w E ^ s else 0) + tailMass w N ^ s) :=
      Finset.sum_le_sum hterm
    _ = (((cutGaps C).filter hit).card : ℝ) * tailMass w E ^ s +
        ((cutGaps C).card : ℝ) * tailMass w N ^ s := by
      rw [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero,
        Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hcardR hTE)
        (mul_le_mul_of_nonneg_right hcardGR hTN)

/-- A three-halves weight bound gives an inverse square-root tail bound. -/
theorem tailMass_le {w : ℕ → ℝ} (hw : Summable w) (hn : ∀ n, 0 ≤ w n) {B : ℝ}
    (hB : 0 ≤ B) (hb : ∀ n, w n ≤ B / ((n : ℝ) + 1) ^ (3/2 : ℝ)) {M : ℕ} (hM : 0 < M) :
    tailMass w M ≤ 2 * B * (M : ℝ) ^ (-(1/2) : ℝ) := by
  classical
  have hs : Summable (fun n => if M ≤ n then w n else 0) :=
    hw.of_norm_bounded fun n => by
      split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg (hn n), hn n]
  have he : tailMass w M = ∑' i, w (i + M) := by
    unfold tailMass
    rw [← hs.sum_add_tsum_nat_add M, Finset.sum_eq_zero (fun i hi => by
      simp [not_le_of_gt (Finset.mem_range.1 hi)]), zero_add]
    simp
  have hsum : Summable (fun i : ℕ => ((i : ℝ) + M + 1) ^ (-(3/2) : ℝ)) := by
    have h := (summable_nat_add_iff (M + 1)).2
      (Real.summable_nat_rpow.2 (by norm_num : (-(3/2) : ℝ) < -1))
    refine h.congr fun i => ?_
    push_cast
    ring_nf
  have hle : ∀ i, w (i + M) ≤ B * ((i : ℝ) + M + 1) ^ (-(3/2) : ℝ) := by
    intro i
    have hpos : 0 < (i : ℝ) + M + 1 := by positivity
    rw [Real.rpow_neg hpos.le, ← div_eq_mul_inv]
    simpa [add_assoc] using hb (i + M)
  have hT := three_halves_tail_le hM
  rw [he]
  calc
    _ ≤ ∑' i : ℕ, B * ((i : ℝ) + M + 1) ^ (-(3/2) : ℝ) :=
      (hw.comp_injective (add_left_injective M)).tsum_le_tsum hle (hsum.mul_left B)
    _ = B * ∑' i : ℕ, ((i : ℝ) + M + 1) ^ (-(3/2) : ℝ) := tsum_mul_left
    _ ≤ B * (2 * (M : ℝ) ^ (-1/2 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hB
      have e : (-(3/2) : ℝ) = -3/2 := by norm_num
      rw [e]
      exact hT
    _ = _ := by
      have e : (-1/2 : ℝ) = -(1/2) := by norm_num
      rw [e]
      ring

private theorem tail_rpow_le {T c : ℝ} {M : ℕ} (hT : 0 ≤ T) (hc : 0 ≤ c)
    (h : T ≤ c * (M : ℝ) ^ (-(1/2) : ℝ)) {s : ℝ} (hs : 0 < s) :
    T ^ s ≤ c ^ s * (M : ℝ) ^ (-(s/2)) := by
  calc
    T ^ s ≤ (c * (M : ℝ) ^ (-(1/2) : ℝ)) ^ s := Real.rpow_le_rpow hT h hs.le
    _ = c ^ s * ((M : ℝ) ^ (-(1/2) : ℝ)) ^ s :=
      Real.mul_rpow hc (Real.rpow_nonneg (Nat.cast_nonneg M) _)
    _ = _ := by
      rw [← Real.rpow_mul (Nat.cast_nonneg M)]
      ring_nf

private theorem pow_rpow_le {q x y : ℝ} (hq : 1 ≤ q) {k : ℕ} (h : y ≤ k * x) :
    (q ^ k) ^ (-x) ≤ q ^ (-y) := by
  rw [← Real.rpow_natCast_mul (by linarith)]
  apply Real.rpow_le_rpow_of_exponent_le hq
  rw [mul_neg]
  linarith

private theorem rpow_neg_nat {q : ℝ} (hq : 0 < q) (j : ℕ) : q ^ (-(j : ℝ)) = (q ^ j)⁻¹ := by
  rw [Real.rpow_neg hq.le, Real.rpow_natCast]

/-- At every Liouville slope `α > 1`, the complete cluster set of the actual
first-passage ratios has zero `s`-dimensional Hausdorff measure for every `s > 0`. -/
theorem liouville_cluster_hausdorff {α : ℝ} (hα1 : 1 < α) (hL : Liouville α)
    {s : ℝ} (hs : 0 < s) :
    Measure.hausdorffMeasure s (passageClusterSet (1/α)) = 0 := by
  have hα0 : 0 < α := by linarith
  have hβ0 : 0 < 1/α := one_div_pos.mpr hα0
  have hβ1 : 1/α < 1 := (div_lt_one hα0).mpr hα1
  have hβ : Irrational (1/α) := by simpa using hL.irrational.inv
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
  apply jumpRange_hausdorff_zero hw hn hi hp hs
  intro ε hε
  set a : ℕ := ⌈4/s⌉₊
  have ha : 4 ≤ (a : ℝ) * s := by
    have := Nat.le_ceil (4/s)
    rw [div_le_iff₀ hs] at this
    linarith
  set m : ℕ := ⌈2 * ((a : ℝ) + 1)/s⌉₊
  have hm : (a : ℝ) + 1 ≤ (m : ℝ) * (s/2) := by
    have := Nat.le_ceil (2 * ((a : ℝ) + 1)/s)
    rw [div_le_iff₀ hs] at this
    linarith
  set K := (2 * B) ^ s
  have hK : 0 ≤ K := Real.rpow_nonneg hc.le s
  have hev : ∀ᶠ q : ℕ in atTop, (2 : ℝ) ≤ q ∧ 5 * K ≤ ε * q ∧
      2 * B * (q : ℝ) ^ (-(1/2) : ℝ) ≤ ε := by
    have h1 : ∀ᶠ q : ℕ in atTop, (2 : ℝ) ≤ q :=
      (eventually_ge_atTop 2).mono fun q hq => by exact_mod_cast hq
    have h2 : ∀ᶠ q : ℕ in atTop, 5 * K ≤ ε * q :=
      (eventually_ge_atTop ⌈5 * K/ε⌉₊).mono fun q hq => by
        have := Nat.ceil_le.1 hq
        rw [div_le_iff₀ hε] at this
        linarith
    have h3 : ∀ᶠ q : ℕ in atTop, 2 * B * (q : ℝ) ^ (-(1/2) : ℝ) ≤ ε := by
      have ht := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/2)).comp
        tendsto_natCast_atTop_atTop).const_mul (2 * B)
      rw [mul_zero] at ht
      exact ht.eventually (ge_mem_nhds hε)
    exact h1.and (h2.and h3)
  obtain ⟨q, ⟨p, hne, happ⟩, hq2, hqK, hqd⟩ :=
    ((hL.frequently_exists_num (m+1)).and_eventually hev).exists
  have hqR : (0 : ℝ) < q := by linarith
  have hq0 : 0 < q := by exact_mod_cast hqR
  have hq1 : (1 : ℝ) ≤ q := by linarith
  set θ := (q : ℝ) * α - p with hθdef
  have hθ : θ ≠ 0 := by
    intro h
    apply hne
    field_simp
    linarith
  have hθlt : |θ| * (q : ℝ) ^ m < 1 := by
    have e : θ = q * (α - p/q) := by
      rw [hθdef, mul_sub, mul_div_cancel₀ _ hqR.ne']
    rw [e, abs_mul, abs_of_pos hqR]
    rw [lt_div_iff₀ (by positivity)] at happ
    calc
      (q : ℝ) * |α - p/q| * (q : ℝ) ^ m = |α - p/q| * (q : ℝ) ^ (m+1) := by ring
      _ < 1 := happ
  let Z : ℕ → ℤ := fun k => ((k : ℤ) + 1) * p - q * ⌊((k : ℝ) + 1) * α⌋
  have hφ : ∀ k, (q : ℝ) * φ k = Z k + ((k : ℝ) + 1) * θ := by
    intro k
    rw [hfr k, Int.fract]
    simp only [Z, θ]
    push_cast
    ring
  have habs : 0 < |θ| := abs_pos.2 hθ
  set N := ⌊1/|θ|⌋₊
  have hN : (N : ℝ) * |θ| ≤ 1 := by
    have := Nat.floor_le (by positivity : (0 : ℝ) ≤ 1/|θ|)
    rwa [le_div_iff₀ habs] at this
  have hNq : ((q ^ m : ℕ) : ℝ) ≤ N := by
    have : q ^ m ≤ N := Nat.le_floor (by
      rw [le_div_iff₀ habs]
      push_cast
      linarith)
    exact_mod_cast this
  set E := q ^ a
  obtain ⟨hdiam, hsum⟩ := chain_cut_bound hw hn hi hp hq0 hθ hφ hN (E := E) hs
  have hE0 : 0 < E := pow_pos hq0 a
  have hN0 : 0 < N := by
    have : (1 : ℝ) ≤ N := le_trans (by push_cast; exact one_le_pow₀ hq1) hNq
    exact_mod_cast (show (0 : ℝ) < N by linarith)
  have hTE := tailMass_le hw hn hB.le hb hE0
  have hTN := tailMass_le hw hn hB.le hb hN0
  have hER : (E : ℝ) = (q : ℝ) ^ a := by push_cast [E]; rfl
  refine ⟨earlyCuts φ E, by simp [earlyCuts], by simp [earlyCuts], fun g hg => ?_, hsum.trans ?_⟩
  · have hqE : (q : ℝ) ≤ E := by
      rw [hER]
      have ha1 : a ≠ 0 := by
        intro h
        rw [h] at ha
        simp at ha
        linarith
      exact le_self_pow₀ hq1 ha1
    have := Real.rpow_le_rpow_of_nonpos hqR hqE (by norm_num : (-(1/2) : ℝ) ≤ 0)
    calc
      _ ≤ tailMass w E := hdiam g hg
      _ ≤ 2 * B * (E : ℝ) ^ (-(1/2) : ℝ) := hTE
      _ ≤ 2 * B * (q : ℝ) ^ (-(1/2) : ℝ) := mul_le_mul_of_nonneg_left this hc.le
      _ ≤ ε := hqd
  · have hE' : (E : ℝ) ^ (-(s/2)) ≤ ((q : ℝ) ^ 2)⁻¹ := by
      rw [hER]
      calc
        ((q : ℝ) ^ a) ^ (-(s/2)) ≤ (q : ℝ) ^ (-((2 : ℕ) : ℝ)) :=
          pow_rpow_le hq1 (by push_cast; linarith)
        _ = _ := rpow_neg_nat hqR 2
    have hN' : (N : ℝ) ^ (-(s/2)) ≤ ((q : ℝ) ^ (a+1))⁻¹ := by
      calc
        (N : ℝ) ^ (-(s/2)) ≤ ((q : ℝ) ^ m) ^ (-(s/2)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) (by exact_mod_cast hNq) (by linarith)
        _ ≤ (q : ℝ) ^ (-((a+1 : ℕ) : ℝ)) := pow_rpow_le hq1 (by push_cast; linarith)
        _ = _ := rpow_neg_nat hqR _
    have hTEs := tail_rpow_le (tailMass_nonneg hn E) hc.le hTE hs
    have hTNs := tail_rpow_le (tailMass_nonneg hn N) hc.le hTN hs
    have hqa : (1 : ℝ) ≤ (q : ℝ) ^ a := one_le_pow₀ hq1
    have e1 : ((q : ℝ) + 1) * (K * ((q : ℝ) ^ 2)⁻¹) ≤ 2 * K / q := by
      rw [show 2 * K / q = (2 * (q : ℝ)) * (K * ((q : ℝ) ^ 2)⁻¹) by field_simp]
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have e2 : ((q : ℝ) ^ a + 2) * (K * ((q : ℝ) ^ (a+1))⁻¹) ≤ 3 * K / q := by
      rw [show 3 * K / q = (3 * (q : ℝ) ^ a) * (K * ((q : ℝ) ^ (a+1))⁻¹) by
        field_simp
        ring]
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    calc
      _ ≤ ((q : ℝ) + 1) * (K * ((q : ℝ) ^ 2)⁻¹) +
          ((q : ℝ) ^ a + 2) * (K * ((q : ℝ) ^ (a+1))⁻¹) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (hTEs.trans (mul_le_mul_of_nonneg_left hE' hK))
            (by positivity)
        · rw [← hER]
          exact mul_le_mul_of_nonneg_left (hTNs.trans (mul_le_mul_of_nonneg_left hN' hK))
            (by positivity)
      _ ≤ 2 * K / q + 3 * K / q := add_le_add e1 e2
      _ ≤ ε := by
        rw [← add_div, div_le_iff₀ hqR]
        linarith

/-- At every Liouville slope `α > 1`, the complete cluster set of the actual
first-passage ratios has Hausdorff dimension zero, in contrast with the
almost-everywhere value two-thirds. -/
theorem liouville_cluster_dimH {α : ℝ} (hα1 : 1 < α) (hL : Liouville α) :
    dimH (passageClusterSet (1/α)) = 0 :=
  dimH_eq_zero_of_hausdorff fun _ hs => liouville_cluster_hausdorff hα1 hL hs

end Problems.Juggler.BeattySlope

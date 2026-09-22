import Problems.Juggler.QuarticBand
import Problems.Juggler.QuarticCells

namespace Problems.Juggler.QuarticDefect

open CubicReturn
open QuarticCells (B F G)
open scoped BigOperators

/-!
Power cells and logarithmic losses of the actual quartic return map.
The strict F loss uses the parity of its actual final E source and target.
-/

theorem G_upper_pow (x : ℕ) : G x ^ 8 ≤ x ^ 9 := by
  have h₁ := Nat.pow_le_pow_left (CubicReturn.O_sq_le (B x)) 4
  have h₂ := Nat.pow_le_pow_left (ReturnCells.oe_cell x).1 3
  have ha : G x ^ 8 ≤ B x ^ 12 := by
    simpa [G, ← pow_mul] using h₁
  have hb : B x ^ 12 ≤ x ^ 9 := by
    simpa [← pow_mul] using h₂
  exact ha.trans hb

theorem return_lower_pow {m x : ℕ} (hl : B x ^ 3 < m ^ 4) :
    QuarticBand.returnMap m x ^ 8 ≤ x ^ 9 := by
  unfold QuarticBand.returnMap
  split_ifs with ho
  · exact ReturnCells.ooe_upper_pow x
  · simpa [G] using G_upper_pow x

theorem return_upper_pow {C : Set ℕ} {m M x : ℕ}
    (D : PeriodicExtrema C m M) (hm : 5 ≤ m) (hM : M < m ^ 4)
    (hx : x ∈ C) (hs : QuarticBand.Section m x) (hu : m ^ 4 ≤ B x ^ 3) :
    QuarticBand.returnMap m x ^ 4 ≤ x ^ 3 := by
  have hn : ¬ O x % 2 = 1 := by
    intro ho
    have hh := QuarticBand.odd_high_forces_lower_cell D (by omega) hM hx hs ho
    change B x ^ 3 < m ^ 4 at hh
    omega
  have hncell : ¬ B x ^ 3 < m ^ 4 := by omega
  simpa [QuarticBand.returnMap, hn, hncell] using (ReturnCells.oe_cell x).1

theorem F_strict_upper_pow {C : Set ℕ} {m M x : ℕ}
    (D : PeriodicExtrema C m M) (hm : 5 ≤ m) (hM : M < m ^ 4)
    (hx : x ∈ C) (hs : QuarticBand.Section m x) (ho : O x % 2 = 1) :
    F x ^ 8 < x ^ 9 := by
  have hxo := QuarticBand.low_odd D hx hs.1
  have hox := QuarticBand.odd_image_mem D hx hxo
  have hv := QuarticBand.high_odd_image_even D (by omega) hM hox ho
    (QuarticBand.first_image_high hs)
  obtain ⟨_, hfmem, hfsec⟩ := QuarticBand.section_ooe D hm hM hx hs ho
  have hfodd : F x % 2 = 1 := QuarticBand.low_odd D hfmem hfsec.1
  have hfloor : F x ^ 2 < O (O x) := by
    have hle : F x ^ 2 ≤ O (O x) := Nat.sqrt_le' (O (O x))
    have hmod : F x ^ 2 % 2 = 1 := by simp [Nat.pow_mod, hfodd]
    change O (O x) % 2 = 0 at hv
    omega
  have h₁ := Nat.pow_lt_pow_left hfloor (by decide : 4 ≠ 0)
  have h₂ := Nat.pow_le_pow_left (CubicReturn.O_sq_le (O x)) 2
  have h₃ := Nat.pow_le_pow_left (CubicReturn.O_sq_le x) 3
  have ha : F x ^ 8 < O (O x) ^ 4 := by simpa [← pow_mul] using h₁
  have hb : O (O x) ^ 4 ≤ O x ^ 6 := by simpa [← pow_mul] using h₂
  have hc : O x ^ 6 ≤ x ^ 9 := by simpa [← pow_mul] using h₃
  exact (ha.trans_le hb).trans_le hc

noncomputable def multiplier (m x : ℕ) : ℝ :=
  if B x ^ 3 < m ^ 4 then 9 / 8 else 3 / 4

noncomputable def blockDefect (m x : ℕ) : ℝ :=
  Real.log (multiplier m x) + Real.log (Real.log (x : ℝ)) -
    Real.log (Real.log (QuarticBand.returnMap m x : ℝ))

theorem log_defect_nonneg {a x y : ℝ} (ha : 0 < a) (hx : 1 < x)
    (hy : 1 < y) (hb : Real.log y ≤ a * Real.log x) :
    0 ≤ Real.log a + Real.log (Real.log x) - Real.log (Real.log y) := by
  have hh := Real.log_le_log (Real.log_pos hy) hb
  rw [Real.log_mul (ne_of_gt ha) (ne_of_gt (Real.log_pos hx))] at hh
  linarith

theorem log_defect_pos {a x y : ℝ} (ha : 0 < a) (hx : 1 < x)
    (hy : 1 < y) (hb : Real.log y < a * Real.log x) :
    0 < Real.log a + Real.log (Real.log x) - Real.log (Real.log y) := by
  have hh := Real.log_lt_log (Real.log_pos hy) hb
  rw [Real.log_mul (ne_of_gt ha) (ne_of_gt (Real.log_pos hx))] at hh
  linarith

theorem blockDefect_nonneg {C : Set ℕ} {m M x : ℕ}
    (D : PeriodicExtrema C m M) (hm : 5 ≤ m) (hM : M < m ^ 4)
    (hx : x ∈ C) (hs : QuarticBand.Section m x) : 0 ≤ blockDefect m x := by
  have hret := QuarticBand.returnMap_closed D hm hM hx hs
  have hxp : 1 < (x : ℝ) := by
    exact_mod_cast (show 1 < x by have := (D.bounds _ hx).1; omega)
  have hyp : 1 < (QuarticBand.returnMap m x : ℝ) := by
    exact_mod_cast (show 1 < QuarticBand.returnMap m x by
      have := (D.bounds _ hret.1).1; omega)
  unfold blockDefect multiplier
  split_ifs with hl
  · apply log_defect_nonneg (by norm_num) hxp hyp
    have hp : (QuarticBand.returnMap m x : ℝ) ^ 8 ≤ (x : ℝ) ^ 9 := by
      exact_mod_cast return_lower_pow hl
    have hh := Real.log_le_log (pow_pos (show 0 < (QuarticBand.returnMap m x : ℝ)
      by linarith) 8) hp
    rw [Real.log_pow, Real.log_pow] at hh
    norm_num at hh
    linarith
  · apply log_defect_nonneg (by norm_num) hxp hyp
    have hp : (QuarticBand.returnMap m x : ℝ) ^ 4 ≤ (x : ℝ) ^ 3 := by
      exact_mod_cast return_upper_pow D hm hM hx hs (by omega)
    have hh := Real.log_le_log (pow_pos (show 0 < (QuarticBand.returnMap m x : ℝ)
      by linarith) 4) hp
    rw [Real.log_pow, Real.log_pow] at hh
    norm_num at hh
    linarith

theorem blockDefect_pos_F {C : Set ℕ} {m M x : ℕ}
    (D : PeriodicExtrema C m M) (hm : 5 ≤ m) (hM : M < m ^ 4)
    (hx : x ∈ C) (hs : QuarticBand.Section m x) (ho : O x % 2 = 1) :
    0 < blockDefect m x := by
  have hret := QuarticBand.returnMap_closed D hm hM hx hs
  have hxp : 1 < (x : ℝ) := by
    exact_mod_cast (show 1 < x by have := (D.bounds _ hx).1; omega)
  have hyp : 1 < (F x : ℝ) := by
    have hfmem := (QuarticBand.section_ooe D hm hM hx hs ho).2.1
    have hb : m ≤ F x := (D.bounds _ hfmem).1
    exact_mod_cast (show 1 < F x by omega)
  have hl := QuarticBand.odd_high_forces_lower_cell D (by omega) hM hx hs ho
  simp only [blockDefect, multiplier, QuarticBand.returnMap, if_pos ho, if_pos hl]
  apply log_defect_pos (by norm_num) hxp hyp
  have hp : (F x : ℝ) ^ 8 < (x : ℝ) ^ 9 := by
    exact_mod_cast F_strict_upper_pow D hm hM hx hs ho
  have hh := Real.log_lt_log (pow_pos (show 0 < (F x : ℝ) by linarith) 8) hp
  rw [Real.log_pow, Real.log_pow] at hh
  norm_num at hh
  linarith

def upperIndices {ι : Type*} [Fintype ι] (m : ℕ) (c : ι → ℕ) : Finset ι :=
  Finset.univ.filter (fun i => m ^ 4 ≤ B (c i) ^ 3)

theorem log_three_fourths : Real.log ((3 : ℝ) / 4) =
    Real.log ((9 : ℝ) / 8) - Real.log ((3 : ℝ) / 2) := by
  rw [← Real.log_div (by norm_num : (9 : ℝ) / 8 ≠ 0)
    (by norm_num : (3 : ℝ) / 2 ≠ 0)]
  norm_num

theorem blockDefect_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ℕ) (c : ι → ℕ) (p : Equiv.Perm ι)
    (hstep : ∀ i, c (p i) = QuarticBand.returnMap m (c i)) :
    ∑ i, blockDefect m (c i) =
      (Fintype.card ι : ℝ) * Real.log ((9 : ℝ) / 8) -
      ((upperIndices m c).card : ℝ) * Real.log ((3 : ℝ) / 2) := by
  have hs : (∑ i, blockDefect m (c i)) = ∑ i, Real.log (multiplier m (c i)) := by
    have hperm : (∑ i, Real.log (Real.log (c (p i) : ℝ))) =
        ∑ i, Real.log (Real.log (c i : ℝ)) :=
      Equiv.sum_comp p (fun i => Real.log (Real.log (c i : ℝ)))
    calc
      (∑ i, blockDefect m (c i)) = ∑ i,
          (Real.log (multiplier m (c i)) + Real.log (Real.log (c i : ℝ)) -
            Real.log (Real.log (c (p i) : ℝ))) := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [blockDefect, hstep]
      _ = ∑ i, Real.log (multiplier m (c i)) := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, hperm]
        ring
  rw [hs]
  have he : ∀ i, Real.log (multiplier m (c i)) =
      Real.log ((9 : ℝ) / 8) -
        if i ∈ upperIndices m c then Real.log ((3 : ℝ) / 2) else 0 := by
    intro i
    by_cases hl : B (c i) ^ 3 < m ^ 4
    · have hu : ¬ m ^ 4 ≤ B (c i) ^ 3 := by omega
      simp [multiplier, upperIndices, hl, hu]
    · have hu : m ^ 4 ≤ B (c i) ^ 3 := by omega
      simp [multiplier, upperIndices, hl, hu, log_three_fourths]
  simp_rw [he]
  simp [Finset.sum_sub_distrib, Finset.sum_ite_mem]

theorem selected_defect_sum_pos {ι : Type*} [Fintype ι]
    {C : Set ℕ} {m M : ℕ} (D : PeriodicExtrema C m M)
    (hm : 5 ≤ m) (hM : M < m ^ 4) (c : ι → ℕ)
    (hc : ∀ i, c i ∈ C ∧ QuarticBand.Section m (c i))
    (hF : ∃ i, O (c i) % 2 = 1) : 0 < ∑ i, blockDefect m (c i) := by
  apply Finset.sum_pos'
  · intro i _
    exact blockDefect_nonneg D hm hM (hc i).1 (hc i).2
  · obtain ⟨i, hi⟩ := hF
    exact ⟨i, Finset.mem_univ _, blockDefect_pos_F D hm hM (hc i).1 (hc i).2 hi⟩

theorem actual_sorted_positive_surplus {C : Set ℕ} {m M : ℕ}
    (D : PeriodicExtrema C m M) (hm : 5 ≤ m)
    (hM : M < m ^ 4) (htall : m ^ 3 ≤ M) :
    ∃ (e : ℕ) (c : Fin e → ℕ) (p : Equiv.Perm (Fin e)),
      0 < e ∧ StrictMono c ∧
      (∀ i, c i ∈ C ∧ QuarticBand.Section m (c i)) ∧
      (∀ x ∈ C, QuarticBand.Section m x → ∃ i, c i = x) ∧
      (∀ i, c (p i) = QuarticBand.returnMap m (c i)) ∧
      (∀ i, 0 ≤ blockDefect m (c i)) ∧
      (∃ i, O (c i) % 2 = 1 ∧ 0 < blockDefect m (c i)) ∧
      0 < (e : ℝ) * Real.log ((9 : ℝ) / 8) -
        ((upperIndices m c).card : ℝ) * Real.log ((3 : ℝ) / 2) := by
  obtain ⟨e, c, p, he, hmono, hc, hcover, hstep⟩ :=
    QuarticBand.sorted_return_model D hm hM
  obtain ⟨x, hx, hs, ho, _⟩ := QuarticBand.exists_F_source D hm hM htall
  obtain ⟨i, hi⟩ := hcover x hx hs
  have hF : O (c i) % 2 = 1 := by simpa [hi] using ho
  have hpos : 0 < ∑ j, blockDefect m (c j) :=
    selected_defect_sum_pos D hm hM c hc ⟨i, hF⟩
  rw [blockDefect_sum m c p hstep] at hpos
  refine ⟨e, c, p, he, hmono, hc, hcover, hstep, ?_, ?_, ?_⟩
  · intro j
    exact blockDefect_nonneg D hm hM (hc j).1 (hc j).2
  · exact ⟨i, hF, blockDefect_pos_F D hm hM (hc i).1 (hc i).2 hF⟩
  · simpa only [Fintype.card_fin] using hpos

end Problems.Juggler.QuarticDefect

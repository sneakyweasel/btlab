/-
Arithmetic obstruction: `n ≢ 0, 12 (mod 24)` implies `t_n` is not
origin-reachable. The classes `n ≡ 0, 12 (mod 24)` and `|L₀|` are left
open. This file does not classify exceptional `t_n` as unreachable.
-/

import Problems.Ostrowski.NP.KernelFamily

namespace Ostrowski.NP

/-- Every origin-reachable state has first coordinate divisible by `3`. -/
theorem origin_reachable_fst_dvd_three {s : State} (h : OriginReachable s) :
    (3 : ℤ) ∣ s.1 := by
  induction h with
  | refl => exact origin_fst_dvd_three
  | tail _ hstep _ =>
    rcases hstep with ⟨w, hw⟩
    rw [← hw]
    exact step_fst_dvd_three w _

/-- Every origin-reachable state other than the origin has an origin-reachable predecessor:
some `s` and letter `w` with `step w s = t`. -/
theorem origin_reachable_pred {t : State} (h : OriginReachable t)
    (hne : t ≠ origin) :
    ∃ s w, OriginReachable s ∧ step w s = t := by
  induction h with
  | refl => exact (hne rfl).elim
  | tail hab hstep _ =>
    rcases hstep with ⟨w, hw⟩
    exact ⟨_, w, hab, hw⟩

private lemma combo_mod9_of_res (n r : ℕ) (hn : 2 ≤ n) (hr : n % 24 = r)
    (hr2 : 2 ≤ r) :
    ((q (n - 1) + 3 * qPrev (n - 1) : ℤ) : ZMod 9) =
      ((q (r - 1) + 3 * q (r - 2) : ℤ) : ZMod 9) := by
  have hn1 : n - 1 = 24 * (n / 24) + (r - 1) := by omega
  have hn2 : n - 2 = 24 * (n / 24) + (r - 2) := by omega
  have hpos : 0 < n - 1 := by omega
  have hsub : n - 1 - 1 = n - 2 := by omega
  rw [qPrev_of_pos hpos, hsub, hn1, hn2]
  have h1 := q_mod9_add_mul (n / 24) (r - 1)
  have h2 := q_mod9_add_mul (n / 24) (r - 2)
  simp [Int.cast_add, Int.cast_mul, h1, h2]

private lemma combo_residue_ne_zero_four :
    ((q 3 + 3 * q 2 : ℤ) : ZMod 9) ≠ 0 := by
  rw [q_eq_triple_fst 3, q_eq_triple_fst 2]
  native_decide

private lemma combo_residue_ne_zero_eight :
    ((q 7 + 3 * q 6 : ℤ) : ZMod 9) ≠ 0 := by
  rw [q_eq_triple_fst 7, q_eq_triple_fst 6]
  native_decide

private lemma combo_residue_ne_zero_sixteen :
    ((q 15 + 3 * q 14 : ℤ) : ZMod 9) ≠ 0 := by
  rw [q_eq_triple_fst 15, q_eq_triple_fst 14]
  native_decide

private lemma combo_residue_ne_zero_twenty :
    ((q 19 + 3 * q 18 : ℤ) : ZMod 9) ≠ 0 := by
  rw [q_eq_triple_fst 19, q_eq_triple_fst 18]
  native_decide

private lemma not_nine_dvd_combo_of_res (n : ℕ) (hn : 2 ≤ n)
    (hres : n % 24 = 4 ∨ n % 24 = 8 ∨ n % 24 = 16 ∨ n % 24 = 20) :
    ¬ (9 : ℤ) ∣ q (n - 1) + 3 * qPrev (n - 1) := by
  intro h
  have hz : ((q (n - 1) + 3 * qPrev (n - 1) : ℤ) : ZMod 9) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (q (n - 1) + 3 * qPrev (n - 1)) 9).mpr
      (by exact_mod_cast h)
  rcases hres with hr | hr | hr | hr
  · rw [combo_mod9_of_res n 4 hn hr (by decide)] at hz
    exact combo_residue_ne_zero_four hz
  · rw [combo_mod9_of_res n 8 hn hr (by decide)] at hz
    exact combo_residue_ne_zero_eight hz
  · rw [combo_mod9_of_res n 16 hn hr (by decide)] at hz
    exact combo_residue_ne_zero_sixteen hz
  · rw [combo_mod9_of_res n 20 hn hr (by decide)] at hz
    exact combo_residue_ne_zero_twenty hz

/-- Enumeration of `ℤ/24ℤ`: residues with `n ≡ 0 or 4 (mod 8)` except `0, 12`. -/
private lemma four_residues (r : ℕ) (hr : r < 24)
    (h8 : r % 8 = 0 ∨ r % 8 = 4) (h0 : r ≠ 0) (h12 : r ≠ 12) :
    r = 4 ∨ r = 8 ∨ r = 16 ∨ r = 20 := by
  interval_cases r <;> omega

private lemma nmod8_of_q_dvd {n : ℕ} (hn : 0 < n) (hdiv : (3 : ℤ) ∣ q (n - 1)) :
    n % 8 = 0 ∨ n % 8 = 4 := by
  have := (q_dvd_three_iff (n - 1)).mp hdiv
  omega

/-- Off `{0, 12} (mod 24)`, either `t_n` itself or every predecessor fails `3 ∣ s₁`. -/
theorem not_exceptional_blocks (n : ℕ) (hn : 0 < n)
    (hmod : ¬ (n % 24 = 0 ∨ n % 24 = 12)) :
    ¬ (3 : ℤ) ∣ q (n - 1) ∨ ¬ (3 : ℤ) ∣ kernelPredFst n hn := by
  by_cases hdiv : (3 : ℤ) ∣ q (n - 1)
  · refine Or.inr ?_
    have hn2 : 2 ≤ n := by
      have : n ≠ 1 := by
        intro h
        subst h
        simp [q_zero] at hdiv
      omega
    have h8 := nmod8_of_q_dvd hn hdiv
    have hcongr : n % 24 % 8 = n % 8 :=
      Nat.mod_mod_of_dvd n (by decide : (8 : ℕ) ∣ 24)
    have hres := four_residues (n % 24) (Nat.mod_lt n (by decide))
      (by rw [hcongr]; exact h8)
      (by intro h; exact hmod (Or.inl h))
      (by intro h; exact hmod (Or.inr h))
    have h9 := not_nine_dvd_combo_of_res n hn2 hres
    intro hk
    exact h9 ((kernelPredFst_dvd_three_iff n hn hdiv).mp hk)
  · exact Or.inl hdiv

/-- For `n > 0` outside the residues `0` and `12` modulo `24`, the kernel family target
`kernelTarget n` is not origin-reachable under unrestricted integer steps. -/
theorem kernel_unreachable_of_not_exceptional
    (n : ℕ) (hn : 0 < n)
    (hmod : ¬ (n % 24 = 0 ∨ n % 24 = 12)) :
    ¬ OriginReachable (kernelTarget n hn) := by
  intro hR
  have hfst := origin_reachable_fst_dvd_three hR
  simp [kernelTarget] at hfst
  obtain ⟨s, w, hsR, hstep⟩ :=
    origin_reachable_pred hR (kernel_ne_origin n hn)
  have hs1 := origin_reachable_fst_dvd_three hsR
  have hpred := kernel_pred_fst n hn w s hstep
  have hblock := not_exceptional_blocks n hn hmod
  rcases hblock with h | h
  · exact h hfst
  · rw [hpred] at hs1
    exact h hs1

end Ostrowski.NP

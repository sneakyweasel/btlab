import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import BTCalculus.Derivative

noncomputable section

namespace BTCalculus

open Polynomial

def powShift (a : ℤ) : ℕ → ℤ[X]
  | 0 => 0
  | n + 1 => C a * powShift a n + C (a ^ n) * X + 3 * X * powShift a n

theorem powShift_spec (a : ℤ) :
    ∀ n : ℕ, (C a + 3 * (X : ℤ[X])) ^ n = C (a ^ n) + 3 * powShift a n
  | 0 => by
    simp [powShift]
  | n + 1 => by
    rw [pow_succ, powShift_spec a n, powShift]
    simp
    ring

theorem powShift_eval (a x : ℤ) (n : ℕ) :
    (a + 3 * x) ^ n = a ^ n + 3 * eval x (powShift a n) := by
  have h := congrArg (eval x) (powShift_spec a n)
  simpa [eval_add, eval_C, eval_mul, eval_X, eval_pow] using h

def sectionDeriv (a : ℤ) (f : ℤ[X]) : ℤ[X] :=
  C (DZ (eval a f)) + ∑ n ∈ f.support, C (f.coeff n) * powShift a n

theorem eval_sectionDeriv (f : ℤ[X]) (a x : ℤ) :
    eval x (sectionDeriv a f) =
      DZ (eval a f) + ∑ n ∈ f.support, f.coeff n * eval x (powShift a n) := by
  simp [sectionDeriv, eval_add, eval_finsetSum, eval_mul]

theorem section_reconstruction_eval (f : ℤ[X]) (a x : ℤ) :
    eval (a + 3 * x) f =
      lsdZ (eval a f) + 3 * eval x (sectionDeriv a f) := by
  have hpow := powShift_eval a x
  have lhs :
      eval (a + 3 * x) f = ∑ n ∈ f.support, f.coeff n * (a + 3 * x) ^ n := by
    simp [eval_eq_sum, Polynomial.sum]
  have ha : eval a f = ∑ n ∈ f.support, f.coeff n * a ^ n := by
    simp [eval_eq_sum, Polynomial.sum]
  have hterms :
      ∑ n ∈ f.support, f.coeff n * (a + 3 * x) ^ n =
        ∑ n ∈ f.support, (f.coeff n * a ^ n + 3 * f.coeff n * eval x (powShift a n)) := by
    refine Finset.sum_congr rfl ?_
    intro n _hn
    rw [hpow n]
    ring
  have hsplit :
      ∑ n ∈ f.support, f.coeff n * (a + 3 * x) ^ n =
        (∑ n ∈ f.support, f.coeff n * a ^ n) +
          3 * ∑ n ∈ f.support, f.coeff n * eval x (powShift a n) := by
    rw [hterms, Finset.sum_add_distrib, Finset.mul_sum]
    simp [mul_assoc, mul_comm]
  have hde : eval a f = lsdZ (eval a f) + 3 * DZ (eval a f) := decomp (eval a f)
  have hsd := eval_sectionDeriv f a x
  calc
    eval (a + 3 * x) f
        = ∑ n ∈ f.support, f.coeff n * (a + 3 * x) ^ n := lhs
    _ = (∑ n ∈ f.support, f.coeff n * a ^ n) +
          3 * ∑ n ∈ f.support, f.coeff n * eval x (powShift a n) := hsplit
    _ = eval a f + 3 * ∑ n ∈ f.support, f.coeff n * eval x (powShift a n) := by
        rw [ha]
    _ = lsdZ (eval a f) + 3 * DZ (eval a f) +
          3 * ∑ n ∈ f.support, f.coeff n * eval x (powShift a n) := by
        conv_lhs => rw [hde]
    _ = lsdZ (eval a f) + 3 * eval x (sectionDeriv a f) := by
        conv_rhs => rw [hsd]
        ring

/-- Polynomial (not merely pointwise) reconstruction. -/
theorem section_reconstruction (f : ℤ[X]) (a : ℤ) :
    f.comp (C a + 3 * X) = C (lsdZ (eval a f)) + 3 * sectionDeriv a f := by
  refine Polynomial.funext (fun x => ?_)
  have h := section_reconstruction_eval f a x
  simpa [eval_comp, eval_add, eval_C, eval_mul, eval_X] using h

lemma three_ne_zero_int : (3 : ℤ) ≠ 0 := by decide

lemma three_as_C : (3 : ℤ[X]) = C (3 : ℤ) :=
  (C_eq_intCast (3 : ℤ)).symm

lemma three_mul_eq_C_mul (p : ℤ[X]) : (3 : ℤ[X]) * p = C (3 : ℤ) * p := by
  rw [three_as_C]

lemma natDegree_three_mul (p : ℤ[X]) :
    natDegree ((3 : ℤ[X]) * p) = natDegree p := by
  rw [three_mul_eq_C_mul, natDegree_C_mul three_ne_zero_int]

lemma leadingCoeff_C_three : leadingCoeff (C (3 : ℤ)) = 3 := by
  rw [leadingCoeff, natDegree_C, coeff_C]
  simp

lemma leadingCoeff_three_mul (p : ℤ[X]) :
    leadingCoeff ((3 : ℤ[X]) * p) = 3 * leadingCoeff p := by
  rw [three_mul_eq_C_mul, leadingCoeff_mul, leadingCoeff_C_three]

lemma coeff_three_mul_X : ∀ n, coeff ((3 : ℤ[X]) * X) n = if n = 1 then 3 else 0
  | 0 => by
    rw [three_mul_eq_C_mul, coeff_C_mul, coeff_X]
    simp
  | 1 => by
    rw [three_mul_eq_C_mul, coeff_C_mul, coeff_X]
    simp
  | n + 2 => by
    rw [three_mul_eq_C_mul, coeff_C_mul, coeff_X]
    simp

lemma coeff_C_add_three_mul_X (a : ℤ) (n : ℕ) :
    coeff (C a + 3 * (X : ℤ[X])) n =
      if n = 0 then a else if n = 1 then 3 else 0 := by
  rw [coeff_add, coeff_C, coeff_three_mul_X]
  by_cases h0 : n = 0
  · subst h0
    simp
  · by_cases h1 : n = 1
    · subst h1
      simp
    · simp [h0, h1]

lemma natDegree_three_mul_X : natDegree ((3 : ℤ[X]) * X) = 1 := by
  rw [three_mul_eq_C_mul, natDegree_C_mul three_ne_zero_int, natDegree_X]

lemma three_mul_X_ne_zero : (3 : ℤ[X]) * X ≠ 0 := by
  intro h
  have : natDegree ((3 : ℤ[X]) * X) = 0 := by simp [h]
  rw [natDegree_three_mul_X] at this
  exact (by decide : ¬1 = 0) this

lemma natDegree_C_add_three_mul_X (a : ℤ) :
    natDegree (C a + 3 * (X : ℤ[X])) = 1 := by
  have hlt : natDegree (C a) < natDegree ((3 : ℤ[X]) * X) := by
    rw [natDegree_C, natDegree_three_mul_X]
    exact Nat.zero_lt_one
  rw [natDegree_add_eq_right_of_natDegree_lt hlt, natDegree_three_mul_X]

lemma leadingCoeff_C_add_three_mul_X (a : ℤ) :
    leadingCoeff (C a + 3 * (X : ℤ[X])) = 3 := by
  have hlt : degree (C a) < degree ((3 : ℤ[X]) * X) :=
    degree_C_le.trans_lt (by
      rw [degree_eq_natDegree three_mul_X_ne_zero, natDegree_three_mul_X]
      exact WithBot.coe_lt_coe.mpr Nat.zero_lt_one)
  rw [leadingCoeff_add_of_degree_lt hlt, three_mul_eq_C_mul, leadingCoeff_mul,
    leadingCoeff_C_three, leadingCoeff_X, mul_one]

lemma C_add_three_mul_X_ne_zero (a : ℤ) : C a + 3 * (X : ℤ[X]) ≠ 0 := by
  intro h
  have hcoeff : coeff (C a + 3 * (X : ℤ[X])) 1 = 0 := by
    rw [h, coeff_zero]
  rw [coeff_C_add_three_mul_X] at hcoeff
  simp at hcoeff

lemma natDegree_C_add_three_mul_X_pow (a : ℤ) (n : ℕ) :
    natDegree ((C a + 3 * (X : ℤ[X])) ^ n) = n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hq := C_add_three_mul_X_ne_zero a
    have hpow : (C a + 3 * (X : ℤ[X])) ^ n ≠ 0 := pow_ne_zero n hq
    rw [pow_succ, natDegree_mul hpow hq, ih, natDegree_C_add_three_mul_X]

lemma leadingCoeff_C_add_three_mul_X_pow (a : ℤ) (n : ℕ) :
    leadingCoeff ((C a + 3 * (X : ℤ[X])) ^ n) = 3 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, leadingCoeff_mul, ih, leadingCoeff_C_add_three_mul_X, pow_succ,
      mul_comm]

lemma three_mul_powShift_ne_zero {a : ℤ} {n : ℕ} (hn : 1 ≤ n) :
    (3 : ℤ[X]) * powShift a n ≠ 0 := by
  intro hz
  have heq : (C a + 3 * (X : ℤ[X])) ^ n = C (a ^ n) := by
    rw [powShift_spec a n, hz, add_zero]
  have hle : n ≤ 0 := by
    have hC : natDegree (C (a ^ n)) ≤ 0 := by
      rw [natDegree_C]
    rwa [← heq, natDegree_C_add_three_mul_X_pow] at hC
  exact (Nat.not_succ_le_zero 0) (hn.trans hle)

lemma natDegree_powShift {a : ℤ} {n : ℕ} (hn : 1 ≤ n) :
    natDegree (powShift a n) = n := by
  have hspec := powShift_spec a n
  have hL := natDegree_C_add_three_mul_X_pow a n
  have hne := three_mul_powShift_ne_zero (a := a) hn
  have hpos : 0 < natDegree ((3 : ℤ[X]) * powShift a n) := by
    refine Nat.pos_of_ne_zero ?_
    intro hz
    have hsum : natDegree (C (a ^ n) + 3 * powShift a n) ≤ 0 := by
      refine (natDegree_add_le _ _).trans ?_
      rw [natDegree_C, hz, max_self]
    have : n ≤ 0 := by rwa [← hspec, hL] at hsum
    exact (Nat.not_succ_le_zero 0) (hn.trans this)
  have hdeg :
      natDegree (C (a ^ n) + 3 * powShift a n) =
        natDegree ((3 : ℤ[X]) * powShift a n) :=
    natDegree_add_eq_right_of_natDegree_lt (by
      rw [natDegree_C]
      exact hpos)
  calc
    natDegree (powShift a n)
        = natDegree ((3 : ℤ[X]) * powShift a n) := (natDegree_three_mul _).symm
    _ = natDegree (C (a ^ n) + 3 * powShift a n) := hdeg.symm
    _ = natDegree ((C a + 3 * (X : ℤ[X])) ^ n) := by rw [hspec]
    _ = n := hL

lemma leadingCoeff_powShift {a : ℤ} {n : ℕ} (hn : 1 ≤ n) :
    leadingCoeff (powShift a n) = 3 ^ (n - 1) := by
  have hspec := powShift_spec a n
  have hL := leadingCoeff_C_add_three_mul_X_pow a n
  have hdeg := natDegree_powShift (a := a) hn
  have hne := three_mul_powShift_ne_zero (a := a) hn
  have hlt : degree (C (a ^ n)) < degree ((3 : ℤ[X]) * powShift a n) :=
    degree_C_le.trans_lt (by
      rw [degree_eq_natDegree hne, natDegree_three_mul, hdeg]
      exact WithBot.coe_lt_coe.mpr hn)
  have hlc :
      leadingCoeff (C (a ^ n) + 3 * powShift a n) =
        leadingCoeff ((3 : ℤ[X]) * powShift a n) :=
    leadingCoeff_add_of_degree_lt hlt
  have h3 : (3 : ℤ) * leadingCoeff (powShift a n) = 3 ^ n := by
    rw [← leadingCoeff_three_mul, ← hlc, ← hspec, hL]
  apply mul_left_cancel₀ three_ne_zero_int
  calc
    3 * leadingCoeff (powShift a n) = 3 ^ n := h3
    _ = 3 ^ (n - 1 + 1) := by rw [Nat.sub_add_cancel hn]
    _ = 3 ^ (n - 1) * 3 := pow_succ _ _
    _ = 3 * 3 ^ (n - 1) := mul_comm _ _

lemma coeff_powShift_eq_zero_of_lt (a : ℤ) {k m : ℕ} (h : k < m) :
    coeff (powShift a k) m = 0 := by
  cases k with
  | zero => simp [powShift]
  | succ k =>
    have hk : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le _)
    exact coeff_eq_zero_of_natDegree_lt (by
      rw [natDegree_powShift hk]
      exact h)

lemma coeff_powShift_degree {a : ℤ} {n : ℕ} (hn : 1 ≤ n) :
    coeff (powShift a n) n = 3 ^ (n - 1) := by
  have hlc := leadingCoeff_powShift (a := a) hn
  rw [leadingCoeff, natDegree_powShift hn] at hlc
  exact hlc

lemma coeff_finset_sum' (s : Finset ℕ) (p : ℕ → ℤ[X]) (m : ℕ) :
    coeff (∑ n ∈ s, p n) m = ∑ n ∈ s, coeff (p n) m := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro n s hs ih
    simp [Finset.sum_insert hs, coeff_add, ih]

lemma coeff_sectionDeriv (a : ℤ) (f : ℤ[X]) (m : ℕ) :
    coeff (sectionDeriv a f) m =
      (if m = 0 then DZ (eval a f) else 0) +
        ∑ n ∈ f.support, f.coeff n * coeff (powShift a n) m := by
  unfold sectionDeriv
  rw [coeff_add, coeff_C, coeff_finset_sum']
  refine congrArg _ (Finset.sum_congr rfl ?_)
  intro n _hn
  rw [coeff_C_mul]

lemma coeff_sectionDeriv_of_pos (a : ℤ) (f : ℤ[X]) {m : ℕ} (hm : 1 ≤ m) :
    coeff (sectionDeriv a f) m =
      ∑ n ∈ f.support, f.coeff n * coeff (powShift a n) m := by
  have hm0 : m ≠ 0 := Nat.ne_of_gt hm
  simp [coeff_sectionDeriv, hm0]

/-- For ``deg f = d ≥ 1``, ``deg(𝔇_a f) = d``. -/
theorem sectionDeriv_natDegree (f : ℤ[X]) (a : ℤ) (hd : 1 ≤ f.natDegree) :
    (sectionDeriv a f).natDegree = f.natDegree := by
  set d := f.natDegree
  have hf0 : f ≠ 0 := by
    intro hf
    have : d = 0 := by simp [d, hf]
    omega
  have hdmem : d ∈ f.support := natDegree_mem_support_of_nonzero hf0
  have hcoeff :
      coeff (sectionDeriv a f) d = f.leadingCoeff * 3 ^ (d - 1) := by
    rw [coeff_sectionDeriv_of_pos a f hd]
    refine (Finset.sum_eq_single d ?_ ?_).trans ?_
    · intro n hn hne
      have hnle : n ≤ d := le_natDegree_of_mem_supp n hn
      have hnlt : n < d := lt_of_le_of_ne hnle hne
      simp [coeff_powShift_eq_zero_of_lt a hnlt]
    · intro h
      exact (h hdmem).elim
    · rw [coeff_powShift_degree hd]
      simp only [leadingCoeff]
      ring
  have hne : coeff (sectionDeriv a f) d ≠ 0 := by
    rw [hcoeff]
    exact mul_ne_zero (leadingCoeff_ne_zero.mpr hf0)
      (pow_ne_zero _ three_ne_zero_int)
  apply le_antisymm
  · refine natDegree_le_iff_coeff_eq_zero.mpr ?_
    intro m hm
    have hmpos : 1 ≤ m := le_trans hd (le_of_lt hm)
    rw [coeff_sectionDeriv_of_pos a f hmpos]
    refine Finset.sum_eq_zero ?_
    intro n hn
    have hnle : n ≤ d := le_natDegree_of_mem_supp n hn
    have hnlt : n < m := lt_of_le_of_lt hnle hm
    simp [coeff_powShift_eq_zero_of_lt a hnlt]
  · exact le_natDegree_of_ne_zero hne

/-- For ``deg f = d ≥ 1``, ``LC(𝔇_a f) = 3^{d-1} LC(f)``. -/
theorem sectionDeriv_leadingCoeff (f : ℤ[X]) (a : ℤ) (hd : 1 ≤ f.natDegree) :
    (sectionDeriv a f).leadingCoeff =
      3 ^ (f.natDegree - 1) * f.leadingCoeff := by
  have hdeg := sectionDeriv_natDegree f a hd
  have hf0 : f ≠ 0 := by
    intro hf
    have : f.natDegree = 0 := by simp [hf]
    omega
  have hdmem : f.natDegree ∈ f.support := natDegree_mem_support_of_nonzero hf0
  rw [leadingCoeff, hdeg, coeff_sectionDeriv_of_pos a f hd]
  refine (Finset.sum_eq_single f.natDegree ?_ ?_).trans ?_
  · intro n hn hne
    have hnle : n ≤ f.natDegree := le_natDegree_of_mem_supp n hn
    have hnlt : n < f.natDegree := lt_of_le_of_ne hnle hne
    simp [coeff_powShift_eq_zero_of_lt a hnlt]
  · intro h
    exact (h hdmem).elim
  · rw [coeff_powShift_degree hd, mul_comm]
    simp only [leadingCoeff]

end BTCalculus

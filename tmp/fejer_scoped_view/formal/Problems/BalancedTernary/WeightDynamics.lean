import BTCalculus.Normalization
import BTCalculus.NormalizedDerivative

namespace Problems.BalancedTernary

open BTCalculus

/-!
Integer iterates of ``W(n) = ∑ d_i²`` on the canonical expansion.
Local semantics: ``W(n) = (lsdZ n).natAbs + W(DZ n)``. The map
strictly decreases ``natAbs`` off ``{0,±1,±2}``.
-/

def weightZ (n : ℤ) : ℤ :=
  ((encodeZ n).map Int.natAbs).sum

theorem weightZ_zero : weightZ 0 = 0 := by
  simp [weightZ, encodeZ_zero]

theorem weightZ_rec {n : ℤ} (hn : n ≠ 0) :
    weightZ n = (lsdZ n).natAbs + weightZ (DZ n) := by
  unfold weightZ
  rw [encodeZ_of_ne_zero hn]
  by_cases hq : DZ n = 0
  · simp [hq, encodeZ_zero, List.map_cons, List.sum_cons]
  · simp [hq, List.map_cons, List.sum_cons]

theorem lsdZ_one : lsdZ 1 = 1 := by
  unfold lsdZ
  decide

theorem lsdZ_neg_one : lsdZ (-1) = -1 := by
  unfold lsdZ
  decide

theorem lsdZ_neg (n : ℤ) : lsdZ (-n) = -lsdZ n := by
  have ht := lsdZ_is_trit n
  have hmod := (lsdZ_mod n).neg
  have htrit : -lsdZ n = -1 ∨ -lsdZ n = 0 ∨ -lsdZ n = 1 := by
    rcases ht with h | h | h <;> simp [h]
  exact lsdZ_unique htrit hmod

theorem DZ_neg (n : ℤ) : DZ (-n) = -DZ n := by
  have hpos := decomp n
  have hneg := decomp (-n)
  have hr := lsdZ_neg n
  linarith

theorem encodeZ_one : encodeZ 1 = [1] := by
  rw [encodeZ_of_ne_zero (by decide : (1 : ℤ) ≠ 0)]
  have hdz : DZ 1 = 0 := by
    unfold DZ
    simp [lsdZ_one]
  simp [hdz, lsdZ_one]

theorem encodeZ_neg_one : encodeZ (-1) = [-1] := by
  rw [encodeZ_of_ne_zero (by decide : (-1 : ℤ) ≠ 0)]
  have hdz : DZ (-1) = 0 := by
    unfold DZ
    simp [lsdZ_neg_one]
  simp [hdz, lsdZ_neg_one]

theorem lsdZ_neg_two : lsdZ (-2) = 1 := by
  unfold lsdZ
  decide

theorem DZ_neg_two : DZ (-2) = -1 := by
  unfold DZ
  simp [lsdZ_neg_two]

theorem weightZ_one : weightZ 1 = 1 := by
  simp [weightZ, encodeZ_one]

theorem weightZ_neg_one : weightZ (-1) = 1 := by
  simp [weightZ, encodeZ_neg_one]

theorem weightZ_two : weightZ 2 = 2 := by
  rw [weightZ_rec (by decide : (2 : ℤ) ≠ 0), lsdZ_two, DZ_two, weightZ_one]
  decide

theorem weightZ_neg_two : weightZ (-2) = 2 := by
  rw [weightZ_rec (by decide : (-2 : ℤ) ≠ 0), lsdZ_neg_two, DZ_neg_two, weightZ_neg_one]
  decide

theorem weightZ_of_natAbs_le_two {n : ℤ} (h : n.natAbs ≤ 2) :
    weightZ n = n.natAbs := by
  have : n.natAbs = 0 ∨ n.natAbs = 1 ∨ n.natAbs = 2 := by omega
  rcases this with h0 | h1 | h2
  · have : n = 0 := Int.natAbs_eq_zero.mp h0
    simp [this, weightZ_zero]
  · have hex := (Int.natAbs_eq_iff (n := 1)).mp h1
    rcases hex with rfl | rfl
    · exact weightZ_one
    · exact weightZ_neg_one
  · have hex := (Int.natAbs_eq_iff (n := 2)).mp h2
    rcases hex with rfl | rfl
    · exact weightZ_two
    · exact weightZ_neg_two

theorem weightZ_nonneg (n : ℤ) : 0 ≤ weightZ n := by
  induction hn : n.natAbs using Nat.strong_induction_on generalizing n with
  | h k ih =>
    subst hn
    by_cases hz : n = 0
    · subst hz
      simp [weightZ_zero]
    · have hform := weightZ_rec hz
      have hdz := DZ_natAbs_lt hz
      have hih := ih (DZ n).natAbs hdz (DZ n) rfl
      have hlsd : 0 ≤ (lsdZ n).natAbs := Nat.zero_le _
      linarith

theorem weightZ_even (n : ℤ) : weightZ (-n) = weightZ n := by
  induction hn : n.natAbs using Nat.strong_induction_on generalizing n with
  | h k ih =>
    subst hn
    by_cases hz : n = 0
    · subst hz
      simp [weightZ_zero]
    · have hneg : (-n) ≠ 0 := neg_ne_zero.mpr hz
      rw [weightZ_rec hneg, weightZ_rec hz, lsdZ_neg, DZ_neg, Int.natAbs_neg]
      have hdz := DZ_natAbs_lt hz
      have hih := ih (DZ n).natAbs hdz (DZ n) rfl
      simpa using hih

theorem weightZ_natAbs_lt {n : ℤ} (h : 3 ≤ n.natAbs) :
    (weightZ n).natAbs < n.natAbs := by
  have hne : n ≠ 0 := by
    intro hz
    subst hz
    simp at h
  have hform := weightZ_rec hne
  have hdzlt := DZ_natAbs_lt hne
  have hlsd := lsdZ_natAbs_le_one n
  have hnn : 0 ≤ weightZ n := weightZ_nonneg n
  have htri : (weightZ n).natAbs ≤ (lsdZ n).natAbs + (weightZ (DZ n)).natAbs := by
    rw [hform]
    exact Int.natAbs_add_le _ _
  by_cases hsmall : (DZ n).natAbs ≤ 2
  · have hdzsum := weightZ_of_natAbs_le_two hsmall
    have hbound : (weightZ n).natAbs ≤ 3 := by
      rw [hdzsum] at htri
      omega
    by_cases hthree : n.natAbs = 3
    · have hn3 : n = 3 ∨ n = -3 := (Int.natAbs_eq_iff (n := 3)).mp hthree
      have hlsd3 : lsdZ 3 = 0 := by
        unfold lsdZ
        decide
      have hdz3 : DZ 3 = 1 := by
        unfold DZ
        simp [hlsd3]
      have hlsd_neg3 : lsdZ (-3) = 0 := by
        unfold lsdZ
        decide
      have hdz_neg3 : DZ (-3) = -1 := by
        unfold DZ
        simp [hlsd_neg3]
      rcases hn3 with rfl | rfl
      · rw [weightZ_rec (by decide : (3 : ℤ) ≠ 0), hlsd3, hdz3, weightZ_one]
        decide
      · rw [weightZ_rec (by decide : (-3 : ℤ) ≠ 0), hlsd_neg3, hdz_neg3, weightZ_neg_one]
        decide
    · omega
  · have hge : 3 ≤ (DZ n).natAbs := by omega
    have ih := weightZ_natAbs_lt (n := DZ n) hge
    have : (weightZ n).natAbs ≤ (DZ n).natAbs := by
      have : (weightZ (DZ n)).natAbs + 1 ≤ (DZ n).natAbs := Nat.add_one_le_of_lt ih
      omega
    omega
termination_by n.natAbs
decreasing_by
  exact DZ_natAbs_lt hne

theorem weightZ_eq_self_iff (n : ℤ) :
    weightZ n = n ↔ n = 0 ∨ n = 1 ∨ n = 2 := by
  constructor
  · intro h
    have hnneg : 0 ≤ n := by
      have := weightZ_nonneg n
      linarith
    by_contra hne
    have hge : 3 ≤ n.natAbs := by
      have : n ≠ 0 ∧ n ≠ 1 ∧ n ≠ 2 := by tauto
      omega
    have hlt := weightZ_natAbs_lt hge
    have : n.natAbs = (weightZ n).natAbs := by simp [h]
    omega
  · intro h
    rcases h with rfl | rfl | rfl
    · exact weightZ_zero
    · exact weightZ_one
    · exact weightZ_two

def weightIterate : Nat → ℤ → ℤ
  | 0, n => n
  | k + 1, n => weightIterate k (weightZ n)

theorem weightIterate_add (a b : Nat) (n : ℤ) :
    weightIterate (a + b) n = weightIterate a (weightIterate b n) := by
  induction b generalizing n with
  | zero => simp [weightIterate]
  | succ b ih =>
    rw [Nat.add_succ]
    change weightIterate (a + b + 1) n = weightIterate a (weightIterate (b + 1) n)
    simp [weightIterate, ih]

theorem weightIterate_small (n : ℤ) (h : n.natAbs ≤ 2) :
    ∀ k, (weightIterate k n).natAbs ≤ 2 := by
  intro k
  induction k generalizing n h with
  | zero => simpa [weightIterate] using h
  | succ k ih =>
    have himg : (weightZ n).natAbs ≤ 2 := by
      rw [weightZ_of_natAbs_le_two h]
      omega
    simpa [weightIterate] using ih (weightZ n) himg

theorem weightIterate_reaches_le_two (n : ℤ) :
    (weightIterate n.natAbs n).natAbs ≤ 2 := by
  induction hn : n.natAbs using Nat.strong_induction_on generalizing n with
  | h k ih =>
    subst hn
    by_cases hsmall : n.natAbs ≤ 2
    · exact weightIterate_small n hsmall _
    · have hge : 3 ≤ n.natAbs := by omega
      have hdrop := weightZ_natAbs_lt hge
      obtain ⟨m, hm⟩ : ∃ m, n.natAbs = m + 1 :=
        Nat.exists_eq_succ_of_ne_zero (by omega)
      have hle : (weightZ n).natAbs ≤ m := by omega
      have hreach := ih (weightZ n).natAbs (by omega) (weightZ n) rfl
      have : weightIterate n.natAbs n =
          weightIterate (m - (weightZ n).natAbs)
            (weightIterate (weightZ n).natAbs (weightZ n)) := by
        rw [hm]
        have hdecomp : m = (m - (weightZ n).natAbs) + (weightZ n).natAbs :=
          (Nat.sub_add_cancel hle).symm
        rw [hdecomp]
        simp [weightIterate, weightIterate_add]
      have himg : (weightIterate (weightZ n).natAbs (weightZ n)).natAbs ≤ 2 := hreach
      rw [this]
      exact weightIterate_small (weightIterate (weightZ n).natAbs (weightZ n)) himg _

end Problems.BalancedTernary

import Problems.BalancedTernary.WeightDynamics

namespace Problems.BalancedTernary

open BTCalculus

/-!
Integer iterates of ``F(n) = n + W(n)``. Off zero the map strictly
increases. Nonpositive integers stay nonpositive and reach ``0``.
-/

def weightDriftZ (n : ℤ) : ℤ :=
  n + weightZ n

theorem weightDriftZ_zero : weightDriftZ 0 = 0 := by
  simp [weightDriftZ, weightZ_zero]

theorem weightZ_pos {n : ℤ} (hn : n ≠ 0) : 1 ≤ weightZ n := by
  induction habs : n.natAbs using Nat.strong_induction_on generalizing n with
  | h k ih =>
    subst habs
    have hform := weightZ_rec hn
    by_cases hq : DZ n = 0
    · have hde := decomp n
      simp [hq] at hde
      have hlsd0 : (lsdZ n).natAbs ≠ 0 := by
        intro h0
        exact hn (hde.trans (Int.natAbs_eq_zero.mp h0))
      have : (lsdZ n).natAbs = 1 := by
        have := lsdZ_natAbs_le_one n
        omega
      rw [hform, hq, weightZ_zero]
      simp [this]
    · have hih := ih (DZ n).natAbs (DZ_natAbs_lt hn) hq rfl
      have hlsd : 0 ≤ (lsdZ n).natAbs := Nat.zero_le _
      linarith [hform, hih, weightZ_nonneg (DZ n)]

theorem weightZ_eq_zero_iff (n : ℤ) : weightZ n = 0 ↔ n = 0 := by
  constructor
  · intro h
    by_contra hne
    have := weightZ_pos hne
    linarith
  · intro h
    subst h
    exact weightZ_zero

theorem weightZ_le_natAbs (n : ℤ) : weightZ n ≤ n.natAbs := by
  induction habs : n.natAbs using Nat.strong_induction_on generalizing n with
  | h k ih =>
    subst habs
    by_cases hz : n = 0
    · subst hz
      simp [weightZ_zero]
    · have hform := weightZ_rec hz
      have hde := decomp n
      have hlsd := lsdZ_natAbs_le_one n
      by_cases hq : DZ n = 0
      · have hnlsd : n = lsdZ n := by
          simp [hq] at hde
          exact hde
        have hw : weightZ n = (lsdZ n).natAbs := by
          rw [hform, hq, weightZ_zero]
          simp
        have hnabs : n.natAbs = (lsdZ n).natAbs :=
          congrArg Int.natAbs hnlsd
        omega
      · have hih := ih (DZ n).natAbs (DZ_natAbs_lt hz) (DZ n) rfl
        have hmul : ((3 : ℤ) * DZ n).natAbs = 3 * (DZ n).natAbs := by
          rw [Int.natAbs_mul]
          simp
        have hsub : ((3 : ℤ) * DZ n).natAbs ≤ n.natAbs + (lsdZ n).natAbs := by
          have : (3 : ℤ) * DZ n = n - lsdZ n := by linarith [hde]
          rw [this]
          simpa using Int.natAbs_sub_le n (lsdZ n)
        have hqpos : 1 ≤ (DZ n).natAbs := by
          have : (DZ n).natAbs ≠ 0 := by
            intro h0
            exact hq (Int.natAbs_eq_zero.mp h0)
          omega
        have hbound : weightZ n ≤ (1 : ℤ) + (DZ n).natAbs := by
          have hlsdZ : ((lsdZ n).natAbs : ℤ) ≤ 1 := Nat.cast_le.mpr hlsd
          linarith [hform, hih]
        have hgap : (1 : ℤ) + (DZ n).natAbs ≤ n.natAbs := by
          omega
        linarith

theorem weightDriftZ_gt {n : ℤ} (hn : n ≠ 0) : n < weightDriftZ n := by
  have := weightZ_pos hn
  simp [weightDriftZ]
  linarith

theorem weightDriftZ_eq_self_iff (n : ℤ) :
    weightDriftZ n = n ↔ n = 0 := by
  constructor
  · intro h
    simp [weightDriftZ] at h
    exact (weightZ_eq_zero_iff n).mp h
  · intro h
    subst h
    exact weightDriftZ_zero

theorem weightDriftZ_nonpos {n : ℤ} (hn : n ≤ 0) : weightDriftZ n ≤ 0 := by
  have hW := weightZ_le_natAbs n
  have hnn := weightZ_nonneg n
  have habs : (n.natAbs : ℤ) = -n := by omega
  simp [weightDriftZ]
  linarith

theorem weightDriftZ_nonneg {n : ℤ} (hn : 0 ≤ n) : 0 ≤ weightDriftZ n := by
  have := weightZ_nonneg n
  simp [weightDriftZ]
  linarith

theorem weightDriftZ_natAbs_lt_of_neg {n : ℤ} (hn : n < 0) :
    (weightDriftZ n).natAbs < n.natAbs := by
  have hle := weightDriftZ_nonpos (le_of_lt hn)
  have hW := weightZ_pos (ne_of_lt hn)
  have hnabs : (n.natAbs : ℤ) = -n := by omega
  have hF : weightDriftZ n = n + weightZ n := rfl
  have hnegF : -weightDriftZ n = -n - weightZ n := by
    simp [weightDriftZ]
    ring
  have hFabs : ((weightDriftZ n).natAbs : ℤ) = -weightDriftZ n := by omega
  omega

def weightDriftIterate : Nat → ℤ → ℤ
  | 0, n => n
  | k + 1, n => weightDriftIterate k (weightDriftZ n)

theorem weightDriftIterate_zero (k : Nat) : weightDriftIterate k 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp [weightDriftIterate, weightDriftZ_zero, ih]

theorem weightDriftIterate_add (a b : Nat) (n : ℤ) :
    weightDriftIterate (a + b) n = weightDriftIterate a (weightDriftIterate b n) := by
  induction b generalizing n with
  | zero => simp [weightDriftIterate]
  | succ b ih =>
    rw [Nat.add_succ]
    change weightDriftIterate (a + b + 1) n =
      weightDriftIterate a (weightDriftIterate (b + 1) n)
    simp [weightDriftIterate, ih]

theorem weightDriftIterate_reaches_zero {n : ℤ} (hn : n ≤ 0) :
    weightDriftIterate n.natAbs n = 0 := by
  induction habs : n.natAbs using Nat.strong_induction_on generalizing n with
  | h k ih =>
    subst habs
    by_cases hz : n = 0
    · subst hz
      simp [weightDriftIterate]
    · have hneg : n < 0 := lt_of_le_of_ne hn hz
      have hdrop := weightDriftZ_natAbs_lt_of_neg hneg
      have hle := weightDriftZ_nonpos hn
      obtain ⟨m, hm⟩ : ∃ m, n.natAbs = m + 1 :=
        Nat.exists_eq_succ_of_ne_zero (by omega)
      have hFbound : (weightDriftZ n).natAbs ≤ m := by omega
      have hreach := ih (weightDriftZ n).natAbs (by omega) hle rfl
      have : weightDriftIterate n.natAbs n =
          weightDriftIterate (m - (weightDriftZ n).natAbs)
            (weightDriftIterate (weightDriftZ n).natAbs (weightDriftZ n)) := by
        rw [hm]
        have hdecomp : m = (m - (weightDriftZ n).natAbs) + (weightDriftZ n).natAbs :=
          (Nat.sub_add_cancel hFbound).symm
        rw [hdecomp]
        simp [weightDriftIterate, weightDriftIterate_add]
      rw [this, hreach, weightDriftIterate_zero]

theorem weightDriftIterate_ge_add {n : ℤ} (hn : 0 < n) :
    ∀ k, (n : ℤ) + k ≤ weightDriftIterate k n := by
  intro k
  induction k generalizing n hn with
  | zero => simp [weightDriftIterate]
  | succ k ih =>
    have hne : n ≠ 0 := ne_of_gt hn
    have hgt := weightDriftZ_gt hne
    have hpos : 0 < weightDriftZ n := lt_trans hn hgt
    have hstep : (n : ℤ) + 1 ≤ weightDriftZ n := by
      have := weightZ_pos hne
      simp [weightDriftZ]
      linarith
    have := ih hpos
    simp [weightDriftIterate]
    linarith

end Problems.BalancedTernary

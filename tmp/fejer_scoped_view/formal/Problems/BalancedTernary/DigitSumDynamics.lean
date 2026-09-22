import BTCalculus.Normalization
import BTCalculus.NormalizedDerivative

namespace Problems.BalancedTernary

open BTCalculus

/-!
Integer iterates of the balanced-ternary digit-sum map
``T(n) = ∑ digits of encodeZ n``. Local semantics are the certified
fold ``T(n) = lsdZ n + T(DZ n)``. The map strictly decreases
``natAbs`` off ``{-1,0,1}``.
-/

def digitSumZ (n : ℤ) : ℤ :=
  (encodeZ n).sum

theorem digitSumZ_zero : digitSumZ 0 = 0 := by
  simp [digitSumZ, encodeZ_zero]

theorem digitSumZ_rec {n : ℤ} (hn : n ≠ 0) :
    digitSumZ n = lsdZ n + digitSumZ (DZ n) := by
  unfold digitSumZ
  rw [encodeZ_of_ne_zero hn]
  by_cases hq : DZ n = 0
  · simp [hq, encodeZ_zero, List.sum_cons]
  · simp [hq, List.sum_cons]

theorem lsdZ_one : lsdZ 1 = 1 := by
  unfold lsdZ
  decide

theorem lsdZ_neg_one : lsdZ (-1) = -1 := by
  unfold lsdZ
  decide

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

theorem digitSumZ_of_natAbs_le_one {n : ℤ} (h : n.natAbs ≤ 1) :
    digitSumZ n = n := by
  have hcases : n = -1 ∨ n = 0 ∨ n = 1 := by
    have : n.natAbs = 0 ∨ n.natAbs = 1 := by omega
    rcases this with h0 | h1
    · exact Or.inr (Or.inl (Int.natAbs_eq_zero.mp h0))
    · have hex := (Int.natAbs_eq_iff (n := 1)).mp h1
      rcases hex with hpos | hneg
      · exact Or.inr (Or.inr hpos)
      · exact Or.inl hneg
  rcases hcases with rfl | rfl | rfl
  · simp [digitSumZ, encodeZ_neg_one]
  · exact digitSumZ_zero
  · simp [digitSumZ, encodeZ_one]

theorem dz_ne_zero_of_natAbs_ge_two {n : ℤ} (h : 2 ≤ n.natAbs) : DZ n ≠ 0 := by
  intro hz
  have hde := decomp n
  rw [hz] at hde
  simp at hde
  have hlsd := lsdZ_natAbs_le_one n
  have : n.natAbs ≤ 1 := by
    rw [hde]
    exact hlsd
  omega

theorem lsdZ_neg_two : lsdZ (-2) = 1 := by
  unfold lsdZ
  decide

theorem DZ_neg_two : DZ (-2) = -1 := by
  unfold DZ
  simp [lsdZ_neg_two]

theorem digitSumZ_two : digitSumZ 2 = 0 := by
  rw [digitSumZ_rec (by decide : (2 : ℤ) ≠ 0), lsdZ_two, DZ_two]
  rw [digitSumZ_of_natAbs_le_one (by decide : (1 : ℤ).natAbs ≤ 1)]
  decide

theorem digitSumZ_neg_two : digitSumZ (-2) = 0 := by
  rw [digitSumZ_rec (by decide : (-2 : ℤ) ≠ 0), lsdZ_neg_two, DZ_neg_two]
  rw [digitSumZ_of_natAbs_le_one (by decide : (-1 : ℤ).natAbs ≤ 1)]
  decide

theorem digitSumZ_natAbs_lt {n : ℤ} (h : 2 ≤ n.natAbs) :
    (digitSumZ n).natAbs < n.natAbs := by
  have hne : n ≠ 0 := by
    intro hz
    subst hz
    simp at h
  have hform := digitSumZ_rec hne
  have hdzlt := DZ_natAbs_lt hne
  have hlsd := lsdZ_natAbs_le_one n
  have htri : (digitSumZ n).natAbs ≤ (lsdZ n).natAbs + (digitSumZ (DZ n)).natAbs := by
    rw [hform]
    exact Int.natAbs_add_le _ _
  by_cases hsmall : (DZ n).natAbs ≤ 1
  · have hdzsum := digitSumZ_of_natAbs_le_one hsmall
    have hbound : (digitSumZ n).natAbs ≤ 2 := by
      rw [hdzsum] at htri
      omega
    by_cases htwo : n.natAbs = 2
    · have hn2 : n = 2 ∨ n = -2 := (Int.natAbs_eq_iff (n := 2)).mp htwo
      rcases hn2 with rfl | rfl
      · simp [digitSumZ_two]
      · simp [digitSumZ_neg_two]
    · omega
  · have hge : 2 ≤ (DZ n).natAbs := by omega
    have ih := digitSumZ_natAbs_lt (n := DZ n) hge
    have : (digitSumZ n).natAbs ≤ (DZ n).natAbs := by
      have : (digitSumZ (DZ n)).natAbs + 1 ≤ (DZ n).natAbs := Nat.add_one_le_of_lt ih
      omega
    omega
termination_by n.natAbs
decreasing_by
  exact DZ_natAbs_lt hne

theorem digitSumZ_eq_self_iff (n : ℤ) :
    digitSumZ n = n ↔ n.natAbs ≤ 1 := by
  constructor
  · intro h
    by_contra hge
    have : 2 ≤ n.natAbs := by omega
    have hlt := digitSumZ_natAbs_lt this
    have : n.natAbs = (digitSumZ n).natAbs := by simp [h]
    omega
  · exact digitSumZ_of_natAbs_le_one

def digitSumIterate : Nat → ℤ → ℤ
  | 0, n => n
  | k + 1, n => digitSumIterate k (digitSumZ n)

theorem digitSumIterate_add (a b : Nat) (n : ℤ) :
    digitSumIterate (a + b) n = digitSumIterate a (digitSumIterate b n) := by
  induction b generalizing n with
  | zero => simp [digitSumIterate]
  | succ b ih =>
    rw [Nat.add_succ]
    change digitSumIterate (a + b + 1) n = digitSumIterate a (digitSumIterate (b + 1) n)
    simp [digitSumIterate, ih]

theorem digitSumIterate_stable {n : ℤ} (h : n.natAbs ≤ 1) :
    ∀ k, digitSumIterate k n = n := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    simp [digitSumIterate, digitSumZ_of_natAbs_le_one h, ih]

theorem digitSumIterate_reaches_unit (n : ℤ) :
    (digitSumIterate n.natAbs n).natAbs ≤ 1 := by
  induction hn : n.natAbs using Nat.strong_induction_on generalizing n with
  | h k ih =>
    subst hn
    by_cases hsmall : n.natAbs ≤ 1
    · simpa [digitSumIterate_stable hsmall] using hsmall
    · have hge : 2 ≤ n.natAbs := by omega
      have hdrop := digitSumZ_natAbs_lt hge
      obtain ⟨m, hm⟩ : ∃ m, n.natAbs = m + 1 :=
        Nat.exists_eq_succ_of_ne_zero (by omega)
      have hle : (digitSumZ n).natAbs ≤ m := by omega
      have hreach := ih (digitSumZ n).natAbs (by omega) (digitSumZ n) rfl
      have : digitSumIterate n.natAbs n =
          digitSumIterate (m - (digitSumZ n).natAbs)
            (digitSumIterate (digitSumZ n).natAbs (digitSumZ n)) := by
        rw [hm]
        have hdecomp : m = (m - (digitSumZ n).natAbs) + (digitSumZ n).natAbs :=
          (Nat.sub_add_cancel hle).symm
        rw [hdecomp]
        simp [digitSumIterate, digitSumIterate_add]
      rw [this, digitSumIterate_stable hreach]
      exact hreach

end Problems.BalancedTernary

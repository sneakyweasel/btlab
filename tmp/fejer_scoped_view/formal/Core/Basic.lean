import Mathlib

namespace Core.Basic

def EventuallyConstant (R : ℕ → ℕ) : Prop :=
  ∃ N, ∀ m, N ≤ m → R m = R N

def EventuallyZero (t : ℕ → ℕ) : Prop :=
  ∃ N, ∀ m, N ≤ m → t m = 0

def Bounded (R : ℕ → ℕ) : Prop :=
  ∃ B, ∀ m, R m ≤ B

theorem monotone_bounded_eventuallyConstant
    (R : ℕ → ℕ) (hmono : Monotone R) (hbounded : Bounded R) :
    EventuallyConstant R := by
  obtain ⟨B, hB⟩ := hbounded
  induction B using Nat.strong_induction_on with
  | h B ih =>
      by_cases hhit : ∃ N, R N = B
      · obtain ⟨N, hN⟩ := hhit
        refine ⟨N, ?_⟩
        intro m hm
        apply Nat.le_antisymm
        · simpa [hN] using hB m
        · exact hmono hm
      · have hsmall : ∀ m, R m < B := by
          intro m
          exact Nat.lt_of_le_of_ne (hB m) (fun h => hhit ⟨m, h⟩)
        by_cases hzero : B = 0
        · subst B
          exact False.elim (Nat.not_lt_zero _ (hsmall 0))
        · have hpred : B - 1 < B := Nat.sub_lt (Nat.zero_lt_of_ne_zero hzero) Nat.zero_lt_one
          apply ih (B - 1) hpred
          exact fun m => Nat.le_sub_one_of_lt (hsmall m)

theorem monotone_eventuallyConstant_bounded
    (R : ℕ → ℕ) (hmono : Monotone R) (hstable : EventuallyConstant R) :
    Bounded R := by
  obtain ⟨N, hN⟩ := hstable
  refine ⟨R N, ?_⟩
  intro m
  by_cases hm : m ≤ N
  · exact hmono hm
  · have hNm : N ≤ m := Nat.le_of_lt (Nat.lt_of_not_ge hm)
    simp [hN m hNm]

theorem monotone_bounded_iff_eventuallyConstant
    (R : ℕ → ℕ) (hmono : Monotone R) :
    Bounded R ↔ EventuallyConstant R :=
  ⟨monotone_bounded_eventuallyConstant R hmono,
   monotone_eventuallyConstant_bounded R hmono⟩

end Core.Basic

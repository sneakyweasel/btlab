import Problems.Collatz.Lift
import Core.Basic

namespace Problems.Collatz

open Core.Basic

structure NestedCylinderSystem where
  R : ℕ → ℕ
  modulus : ℕ → ℕ
  RealizesPrefix : ℕ → ℕ → Prop
  R_pos : ∀ m, 0 < R m
  self_realizes : ∀ m, RealizesPrefix (R m) m
  nested :
    ∀ {n m q}, m ≤ q → RealizesPrefix n q → RealizesPrefix n m
  unique_below :
    ∀ {n m}, RealizesPrefix n m → n < modulus m → n = R m
  modulus_eventually_exceeds :
    ∀ n, ∃ N, ∀ m, N ≤ m → n < modulus m

def HasPositiveIntegerRealizer (S : NestedCylinderSystem) : Prop :=
  ∃ n, 0 < n ∧ ∀ m, S.RealizesPrefix n m

theorem realizer_iff_eventuallyConstant (S : NestedCylinderSystem) :
    HasPositiveIntegerRealizer S ↔ EventuallyConstant S.R := by
  constructor
  · rintro ⟨n, _hnpos, hn⟩
    obtain ⟨N, hlarge⟩ := S.modulus_eventually_exceeds n
    refine ⟨N, ?_⟩
    intro m hm
    have hmn : n = S.R m :=
      S.unique_below (hn m) (hlarge m hm)
    have hNN : n = S.R N :=
      S.unique_below (hn N) (hlarge N (Nat.le_refl N))
    exact hmn.symm.trans hNN
  · rintro ⟨N, hR⟩
    refine ⟨S.R N, S.R_pos N, ?_⟩
    intro m
    by_cases hm : m ≤ N
    · exact S.nested hm (S.self_realizes N)
    · have hNm : N ≤ m := Nat.le_of_lt (Nat.lt_of_not_ge hm)
      simpa [hR m hNm] using S.self_realizes m

theorem infiniteRealizer_iff_eventuallyZero
    (C : NestedCylinderSystem)
    (L : LiftSystem)
    (sameR : C.R = L.R) :
    HasPositiveIntegerRealizer C ↔ EventuallyZero L.liftDigit := by
  rw [realizer_iff_eventuallyConstant C]
  rw [sameR]
  exact eventuallyConstant_iff_eventuallyZero L

structure ZeroLiftLaw (Prefix : Type) where
  nextValuation : Prefix → ℕ
  liftDigit : Prefix → ℕ → ℕ
  zero_iff : ∀ p k, liftDigit p k = 0 ↔ k = nextValuation p

theorem unique_zero_lift_child
    {Prefix : Type} (Z : ZeroLiftLaw Prefix) (p : Prefix) :
    ∃! k, Z.liftDigit p k = 0 := by
  refine ⟨Z.nextValuation p, (Z.zero_iff p _).mpr rfl, ?_⟩
  intro k hk
  exact (Z.zero_iff p k).mp hk

end Problems.Collatz

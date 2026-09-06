import Core.Basic

namespace Problems.Collatz

open Core.Basic

structure LiftSystem where
  R : ℕ → ℕ
  K : ℕ → ℕ
  valuation : ℕ → ℕ
  liftDigit : ℕ → ℕ
  valuation_pos : ∀ m, 0 < valuation m
  K_step : ∀ m, K (m + 1) = K m + valuation m
  lift_step :
    ∀ m, R (m + 1) = R m + liftDigit m * 2 ^ (K m + 1)
  lift_bound : ∀ m, liftDigit m < 2 ^ valuation m

/-- Lift digits are nonnegative. -/
theorem lift_nonnegative (S : LiftSystem) (m : ℕ) :
    0 ≤ S.liftDigit m := Nat.zero_le _

/-- The realizer `R` is monotone. -/
theorem realizer_monotone (S : LiftSystem) : Monotone S.R := by
  apply monotone_nat_of_le_succ
  intro m
  rw [S.lift_step m]
  exact Nat.le_add_right _ _

/-- `R` holds still across step `m` exactly when the lift digit at `m` is zero. -/
theorem step_eq_iff_liftDigit_zero (S : LiftSystem) (m : ℕ) :
    S.R (m + 1) = S.R m ↔ S.liftDigit m = 0 := by
  rw [S.lift_step m]
  constructor
  · intro h
    have hp : 0 < 2 ^ (S.K m + 1) := pow_pos (by omega) _
    nlinarith
  · intro h
    simp [h]

/-- `R` is eventually constant exactly when the lift digits are eventually zero. -/
theorem eventuallyConstant_iff_eventuallyZero (S : LiftSystem) :
    EventuallyConstant S.R ↔ EventuallyZero S.liftDigit := by
  constructor
  · rintro ⟨N, hR⟩
    refine ⟨N, ?_⟩
    intro m hm
    apply (step_eq_iff_liftDigit_zero S m).mp
    rw [hR m hm, hR (m + 1) (Nat.le_trans hm (Nat.le_add_right m 1))]
  · rintro ⟨N, ht⟩
    refine ⟨N, ?_⟩
    intro m hm
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
    induction d with
    | zero => simp
    | succ d ih =>
        rw [Nat.add_succ]
        calc
          S.R (N + d + 1) = S.R (N + d) :=
            (step_eq_iff_liftDigit_zero S (N + d)).mpr
              (ht (N + d) (Nat.le_add_right N d))
          _ = S.R N := ih (Nat.le_add_right N d)

/-- `R` is bounded exactly when the lift digits are eventually zero. -/
theorem bounded_iff_eventuallyZero (S : LiftSystem) :
    Bounded S.R ↔ EventuallyZero S.liftDigit := by
  rw [monotone_bounded_iff_eventuallyConstant S.R (realizer_monotone S)]
  exact eventuallyConstant_iff_eventuallyZero S

/-- Mixed-radix reconstruction: from `R 0 = 1`,
`R m = 1 + sum_{j < m} liftDigit j * 2^(K j + 1)`. -/
theorem mixedRadix_reconstruction
    (S : LiftSystem) (hR0 : S.R 0 = 1) (m : ℕ) :
    S.R m =
      1 + ∑ j ∈ Finset.range m, S.liftDigit j * 2 ^ (S.K j + 1) := by
  induction m with
  | zero => simpa using hR0
  | succ m ih =>
      rw [S.lift_step m, ih]
      simp [Finset.sum_range_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

end Problems.Collatz

import Problems.Collatz.Arithmetic
import Core.Basic

namespace Problems.Collatz

open Core.Basic

/-- An odd endpoint turns the exact endpoint equation into the expected
congruence modulo the next power of two. -/
theorem endpoint_congruence_factor
    (m K R C x : ℕ)
    (hEndpoint : 3 ^ m * R + C = 2 ^ K * x)
    (hOdd : Odd x) :
    ∃ q, 3 ^ m * R + C = 2 ^ K + 2 ^ (K + 1) * q := by
  obtain ⟨q, hq⟩ := hOdd
  refine ⟨q, ?_⟩
  rw [hEndpoint, hq, pow_succ]
  ring

theorem endpoint_modEq
    (m K R C x : ℕ)
    (hEndpoint : 3 ^ m * R + C = 2 ^ K * x)
    (hOdd : Odd x) :
    Nat.ModEq (2 ^ (K + 1)) (3 ^ m * R + C) (2 ^ K) := by
  obtain ⟨q, hq⟩ :=
    endpoint_congruence_factor m K R C x hEndpoint hOdd
  simp [Nat.ModEq, hq]

theorem endpoint_congruence_zmod
    (m K R C x : ℕ)
    (hEndpoint : 3 ^ m * R + C = 2 ^ K * x)
    (hOdd : Odd x) :
    ((3 ^ m * R + C : ℕ) : ZMod (2 ^ (K + 1))) =
      ((2 ^ K : ℕ) : ZMod (2 ^ (K + 1))) := by
  obtain ⟨q, hq⟩ :=
    endpoint_congruence_factor m K R C x hEndpoint hOdd
  rw [hq]
  simp

/-- The affine endpoint equation gives Kramer's exact 3-adic endpoint
congruence `2^K * x = C (mod 3^m)`. -/
theorem kramer_endpoint_congruence_zmod
    (m K R C x : ℕ)
    (hEndpoint : 3 ^ m * R + C = 2 ^ K * x) :
    ((2 ^ K * x : ℕ) : ZMod (3 ^ m)) =
      ((C : ℕ) : ZMod (3 ^ m)) := by
  rw [← hEndpoint]
  simp

/-- Refining `R` by one lift block changes the canonical endpoint by the
exact amount `2 * 3^m * t`. -/
theorem refined_endpoint_reduction
    (m K R C x t refinedR : ℕ)
    (hEndpoint : 3 ^ m * R + C = 2 ^ K * x)
    (hRefined : refinedR = R + t * 2 ^ (K + 1)) :
    3 ^ m * refinedR + C =
      2 ^ K * (x + 2 * 3 ^ m * t) := by
  calc
    3 ^ m * refinedR + C =
        3 ^ m * (R + t * 2 ^ (K + 1)) + C := by rw [hRefined]
    _ = (3 ^ m * R + C) + 2 ^ K * (2 * 3 ^ m * t) := by
      rw [pow_succ]
      ring
    _ = 2 ^ K * (x + 2 * 3 ^ m * t) := by
      rw [hEndpoint]
      ring

/-- The closed successor equation written as an exact signed drift balance.
No sign or contraction claim is implicit in this identity. -/
theorem exact_endpoint_drift
    (m k : ℕ) (q t x child : ℤ)
    (hChild :
      q + 3 ^ (m + 1) * t = 2 ^ (k - 1) * child) :
    2 ^ (k - 1) * (child - x) =
      q + 3 ^ (m + 1) * t - 2 ^ (k - 1) * x := by
  calc
    2 ^ (k - 1) * (child - x) =
        2 ^ (k - 1) * child - 2 ^ (k - 1) * x := by ring
    _ = q + 3 ^ (m + 1) * t - 2 ^ (k - 1) * x := by rw [← hChild]

def liftBlock (S : LiftSystem) (m : ℕ) : ℕ :=
  S.liftDigit m * 2 ^ S.K m

theorem liftBlock_eq_zero_iff (S : LiftSystem) (m : ℕ) :
    liftBlock S m = 0 ↔ S.liftDigit m = 0 := by
  simp [liftBlock]

/-- The lift blocks are precisely the mixed-radix digits of `(R m - 1) / 2`. -/
theorem liftBlock_reconstruction
    (S : LiftSystem) (hR0 : S.R 0 = 1) (m : ℕ) :
    S.R m =
      1 + 2 * ∑ j ∈ Finset.range m, liftBlock S j := by
  rw [mixedRadix_reconstruction S hR0 m]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [liftBlock, pow_succ]
  ring

theorem half_realizer_mixedRadix
    (S : LiftSystem) (hR0 : S.R 0 = 1) (m : ℕ) :
    (S.R m - 1) / 2 =
      ∑ j ∈ Finset.range m, liftBlock S j := by
  rw [liftBlock_reconstruction S hR0 m]
  omega

theorem eventuallyZero_liftBlock_iff (S : LiftSystem) :
    EventuallyZero (liftBlock S) ↔ EventuallyZero S.liftDigit := by
  constructor
  · rintro ⟨N, hN⟩
    exact ⟨N, fun m hm => (liftBlock_eq_zero_iff S m).mp (hN m hm)⟩
  · rintro ⟨N, hN⟩
    exact ⟨N, fun m hm => (liftBlock_eq_zero_iff S m).mpr (hN m hm)⟩

/-- Existing stabilization theory, expressed directly in terms of the
mixed-radix lift blocks. -/
theorem bounded_iff_eventuallyZero_liftBlock (S : LiftSystem) :
    Bounded S.R ↔ EventuallyZero (liftBlock S) := by
  rw [eventuallyZero_liftBlock_iff S]
  exact bounded_iff_eventuallyZero S

end Problems.Collatz

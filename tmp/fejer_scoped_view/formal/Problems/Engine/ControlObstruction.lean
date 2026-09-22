import Mathlib.Data.Int.Basic
import Mathlib.Tactic
import Problems.Engine.ControlWord

namespace Problems.Engine

/-!
Generic integer obstructions for a cleared cycle constraint
``(A - B) x = C``. This is not a Collatz theorem.
-/

theorem exists_mul_eq_iff_dvd (a b : ℤ) :
    (∃ x : ℤ, a * x = b) ↔ a ∣ b := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, hx.symm⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, hx.symm⟩

theorem cycle_constraint_dvd {A B C x : ℤ}
    (h : A * x = B * x + C) :
    (A - B) ∣ C := by
  exact (exists_mul_eq_iff_dvd (A - B) C).1 ⟨x, cycle_of_composed h⟩

theorem not_dvd_of_abs_gt {a b : ℤ} (hb : b ≠ 0) (h : |b| < |a|) :
    ¬ a ∣ b := by
  rintro ⟨k, rfl⟩
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hb
  have hge : (1 : ℤ) ≤ |k| := by
    have := abs_pos.mpr hk0
    omega
  have : |a| ≤ |a * k| := by
    calc
      |a| = |a| * 1 := by ring
      _ ≤ |a| * |k| := by nlinarith [abs_nonneg a]
      _ = |a * k| := (abs_mul a k).symm
  exact (not_le.mpr h) this

/-- After a prefix `A y = B x + C`, one more step `a z = p y + r` has
remainder `p C + r A`, independent of the last multiplier `a`. -/
theorem last_step_remainder
    {A B C p r a x y z : ℤ}
    (h0 : A * y = B * x + C)
    (h1 : a * z = p * y + r) :
    A * a * z = p * B * x + (p * C + r * A) := by
  have h := compose_two_affine h0 h1
  convert h using 1
  ring

/-- Two-step remainder for a power-family step. Independent of `k1`. -/
theorem two_step_remainder
    {b p r : ℤ} {k0 k1 : ℕ} {x0 x1 x2 : ℤ}
    (h0 : b ^ k0 * x1 = p * x0 + r)
    (h1 : b ^ k1 * x2 = p * x1 + r) :
    b ^ k0 * b ^ k1 * x2 = p * p * x0 + (p * r + r * b ^ k0) :=
  last_step_remainder h0 h1

/-- If `|C| < |A - B|` and `C ≠ 0`, the cycle constraint has no integer `x`. -/
theorem cycle_abs_obstruction
    {A B C x : ℤ}
    (hne : C ≠ 0)
    (hbound : |C| < |A - B|)
    (h : A * x = B * x + C) :
    False :=
  not_dvd_of_abs_gt hne hbound (cycle_constraint_dvd h)

/-- Length-2 remainder elimination for a power-family step. Independent of `k0`. -/
theorem two_step_elimination (b p r : ℤ) (k0 k1 : ℕ) :
    b ^ k1 * (r * (p + b ^ k0)) - r * (b ^ k0 * b ^ k1 - p * p) =
      r * p * (b ^ k1 + p) := by
  ring

/-- If the two-step remainder is divisible by `D`, then `D` divides the
constant `r p (b^{k1} + p)`. Magnitude of `D` versus `C` is not used. -/
theorem dvd_constant_of_dvd_remainder
    {b p r : ℤ} {k0 k1 : ℕ}
    (h : (b ^ k0 * b ^ k1 - p * p) ∣ (r * (p + b ^ k0))) :
    (b ^ k0 * b ^ k1 - p * p) ∣ (r * p * (b ^ k1 + p)) := by
  set D := b ^ k0 * b ^ k1 - p * p
  set C := r * (p + b ^ k0)
  have hmul : D ∣ b ^ k1 * C := h.mul_left (b ^ k1)
  have hrd : D ∣ r * D := by
    rw [mul_comm]
    exact dvd_mul_right D r
  have hsub : D ∣ b ^ k1 * C - r * D := dvd_sub hmul hrd
  simpa [C, D, two_step_elimination b p r k0 k1] using hsub

theorem two_step_not_dvd_of_not_dvd_constant
    {b p r : ℤ} {k0 k1 : ℕ}
    (hK : ¬ (b ^ k0 * b ^ k1 - p * p) ∣ (r * p * (b ^ k1 + p))) :
    ¬ (b ^ k0 * b ^ k1 - p * p) ∣ (r * (p + b ^ k0)) :=
  mt dvd_constant_of_dvd_remainder hK

end Problems.Engine

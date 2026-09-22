import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

namespace Problems.Engine

/-!
Generic arithmetic of exact exponent selection.

If `b^k y = q` and `b` does not divide `y`, then the `b`-adic valuation
of `q` is `k`, and conversely a cofactor exists. This is integer
arithmetic. It is not a map theorem and not a Collatz identity.
-/

theorem padicValInt_pow_self {b k : ℕ} [hp : Fact b.Prime] :
    padicValInt b ((b : ℤ) ^ k) = k := by
  rw [← Int.natCast_pow, padicValInt.of_nat, padicValNat.prime_pow]

/-- `b^k y = q` and `b ∤ y` if and only if `v_b(q) = k`, for prime `b`
and `q ≠ 0`. -/
theorem mul_pow_eq_iff_padicValInt
    {b : ℕ} [hp : Fact b.Prime] {q : ℤ} {k : ℕ} (hq : q ≠ 0) :
    (∃ y : ℤ, (b : ℤ) ^ k * y = q ∧ ¬ (b : ℤ) ∣ y) ↔ padicValInt b q = k := by
  constructor
  · rintro ⟨y, rfl, hnd⟩
    have hy : y ≠ 0 := by
      rintro rfl
      simp at hq
    have hb : (b : ℤ) ^ k ≠ 0 :=
      pow_ne_zero _ (Int.natCast_ne_zero.mpr hp.out.ne_zero)
    rw [padicValInt.mul hb hy, padicValInt_pow_self, padicValInt.eq_zero_of_not_dvd hnd, add_zero]
  · intro hv
    have hdvd : (b : ℤ) ^ k ∣ q := by
      rw [padicValInt_dvd_iff]
      exact Or.inr (le_of_eq hv.symm)
    obtain ⟨y, hy⟩ := hdvd
    refine ⟨y, hy.symm, ?_⟩
    intro hdiv
    obtain ⟨z, hz⟩ := hdiv
    have hsucc : (b : ℤ) ^ (k + 1) ∣ q := by
      rw [hy, hz, ← mul_assoc, ← pow_succ]
      exact dvd_mul_right _ _
    have hle : k + 1 ≤ padicValInt b q := by
      have hiff := (padicValInt_dvd_iff (k + 1) q).mp hsucc
      exact hiff.resolve_left hq
    rw [hv] at hle
    exact (Nat.not_succ_le_self k) hle

theorem padicValInt_eq_of_mul_pow
    {b : ℕ} [hp : Fact b.Prime] {q y : ℤ} {k : ℕ}
    (hq : q ≠ 0) (heq : (b : ℤ) ^ k * y = q) (hnd : ¬ (b : ℤ) ∣ y) :
    padicValInt b q = k :=
  (mul_pow_eq_iff_padicValInt hq).1 ⟨y, heq, hnd⟩

end Problems.Engine

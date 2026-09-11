import Problems.Juggler.Dynamics

/-!
# Elementary integer root cells

Prescribed branch formulas and root inequalities, independent of cycle or
fate hypotheses. Existing public namespaces are retained for callers.
-/

namespace Problems.Juggler

/-- Exact form of `⌊√⌊√N⌋⌋ = m`: the fourth-power cell. -/
theorem sqrt_sqrt_eq_iff {N m : ℕ} :
    (N.sqrt).sqrt = m ↔ m ^ 4 ≤ N ∧ N < (m + 1) ^ 4 := by
  constructor
  · intro h
    have h' := Nat.eq_sqrt.mp h.symm
    obtain ⟨h1, h2⟩ := h'
    have h1' : (m * m) * (m * m) ≤ N := Nat.le_sqrt.mp h1
    have h2' : N < ((m + 1) * (m + 1)) * ((m + 1) * (m + 1)) := Nat.sqrt_lt.mp h2
    constructor
    · calc m ^ 4 = (m * m) * (m * m) := by ring
        _ ≤ N := h1'
    · calc N < ((m + 1) * (m + 1)) * ((m + 1) * (m + 1)) := h2'
        _ = (m + 1) ^ 4 := by ring
  · rintro ⟨h1, h2⟩
    symm
    apply Nat.eq_sqrt.mpr
    constructor
    · apply Nat.le_sqrt.mpr
      calc (m * m) * (m * m) = m ^ 4 := by ring
        _ ≤ N := h1
    · apply Nat.sqrt_lt.mpr
      calc N < (m + 1) ^ 4 := h2
        _ = ((m + 1) * (m + 1)) * ((m + 1) * (m + 1)) := by ring

namespace CubicReturn

def O (x : ℕ) : ℕ := (x ^ 3).sqrt

theorem O_sq_le (x : ℕ) : O x ^ 2 ≤ x ^ 3 := by
  simpa [O, pow_two] using Nat.sqrt_le (x ^ 3)

theorem lt_O_succ_sq (x : ℕ) : x ^ 3 < (O x + 1) ^ 2 := by
  simpa [O, pow_two] using Nat.lt_succ_sqrt (x ^ 3)

theorem sqrt_mul_le_O (x : ℕ) : x.sqrt * x ≤ O x := by
  apply Nat.le_sqrt.mpr
  have h := Nat.mul_le_mul_right (x ^ 2) (Nat.sqrt_le x)
  nlinarith

theorem sq_le_OO {x : ℕ} (hx : 3 ≤ x) : x ^ 2 ≤ O (O x) := by
  by_cases hx4 : x < 4
  · have he : x = 3 := by omega
    subst x
    decide +kernel
  let k := x.sqrt
  have hk : 2 ≤ k := Nat.le_sqrt.mpr (by omega)
  have hcell : x < (k + 1) ^ 2 := by
    simpa [k, pow_two] using Nat.lt_succ_sqrt x
  have hkx : x ≤ k ^ 3 := by
    have hprod : 0 ≤ k * (k - 2) * (k + 1) := Nat.zero_le _
    have hk2 : k - 2 + 2 = k := Nat.sub_add_cancel hk
    nlinarith
  have hmul := sqrt_mul_le_O x
  have hpow := Nat.pow_le_pow_left hmul 3
  have hxp := Nat.mul_le_mul_right (x ^ 3) hkx
  apply Nat.le_sqrt.mpr
  dsimp [k] at *
  nlinarith [show (x.sqrt * x) ^ 3 = x.sqrt ^ 3 * x ^ 3 by ring]

theorem ooe_gt {x : ℕ} (hx : 5 ≤ x) : x < (O (O x)).sqrt := by
  by_cases hx9 : x < 9
  · interval_cases x <;> decide +kernel
  let k := x.sqrt
  have hk : 3 ≤ k := Nat.le_sqrt.mpr (by omega)
  have hcell : x < (k + 1) ^ 2 := by
    simpa [k, pow_two] using Nat.lt_succ_sqrt x
  have hkx : x + 12 ≤ k ^ 3 := by
    have hk3 : k - 3 + 3 = k := Nat.sub_add_cancel hk
    have hp : 0 ≤ (k - 3) * (k ^ 2 + 2 * k + 4) := Nat.zero_le _
    nlinarith
  have hmul := sqrt_mul_le_O x
  have hpow := Nat.pow_le_pow_left hmul 3
  have hxp := Nat.mul_le_mul_right (x ^ 3) hkx
  have hg : (x + 1) ^ 4 ≤ O x ^ 3 := by
    have hp : 0 ≤ (x - 9) * x ^ 2 := Nat.zero_le _
    have hxsub : x - 9 + 9 = x := Nat.sub_add_cancel (by omega)
    have hid : (x.sqrt * x) ^ 3 = x.sqrt ^ 3 * x ^ 3 := by ring
    dsimp [k] at *
    nlinarith [sq_nonneg (x : ℤ)]
  have hfirst : (x + 1) ^ 2 ≤ O (O x) := by
    apply Nat.le_sqrt.mpr
    nlinarith
  have hsecond := Nat.le_sqrt.mpr (show (x + 1) * (x + 1) ≤ O (O x) by
    simpa [pow_two] using hfirst)
  omega

end CubicReturn

end Problems.Juggler

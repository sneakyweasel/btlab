/-
Place values for Γ_NP: `q₀ = 1`, `q₁ = 2`, `q₂ = 5`, and
`q_{n+3} = 2 q_{n+2} + q_{n+1} + 3 q_n`, matching Python
`research.ostrowski.system.place_value`.
-/

import Mathlib.Data.Int.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Ostrowski.NP

/-- Place-value sequence. -/
def q : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | 2 => 5
  | n + 3 => 2 * q (n + 2) + q (n + 1) + 3 * q n

theorem q_zero : q 0 = 1 := rfl
theorem q_one : q 1 = 2 := rfl
theorem q_two : q 2 = 5 := rfl

/-- The MSD recurrence of `Γ_NP`: `q (n+3) = 2 q (n+2) + q (n+1) + 3 q n`.
Equivalently the word `B* = (1, -2, -1, -3)` has consumed sum zero at every start
remaining `n + 4`. -/
theorem q_rec (n : ℕ) : q (n + 3) = 2 * q (n + 2) + q (n + 1) + 3 * q n :=
  rfl

/-- The `3 q n` term drops modulo 3. -/
theorem q_mod_three (n : ℕ) :
    (q (n + 3) : ZMod 3) = 2 * (q (n + 2) : ZMod 3) + (q (n + 1) : ZMod 3) := by
  rw [q_rec]
  push_cast
  have h3 : (3 : ZMod 3) = 0 := rfl
  simp [h3]

theorem q_pos : ∀ n, (0 : ℤ) < q n
  | 0 => by decide
  | 1 => by decide
  | 2 => by decide
  | n + 3 => by
    have h0 := q_pos n
    have h1 := q_pos (n + 1)
    have h2 := q_pos (n + 2)
    have : (0 : ℤ) < 2 * q (n + 2) + q (n + 1) + 3 * q n := by nlinarith
    simpa [q_rec] using this

theorem q_ne_zero (n : ℕ) : q n ≠ 0 :=
  ne_of_gt (q_pos n)

/-- The triple `(q n, q (n+1), q (n+2))` in `(ℤ/3ℤ)³` has period 8. -/
theorem q_triple_mod3_period8 (n : ℕ) :
    ((q (n + 8) : ZMod 3), (q (n + 9) : ZMod 3), (q (n + 10) : ZMod 3)) =
      ((q n : ZMod 3), (q (n + 1) : ZMod 3), (q (n + 2) : ZMod 3)) := by
  induction n with
  | zero =>
    native_decide
  | succ n ih =>
    have hA : (q (n + 8) : ZMod 3) = (q n : ZMod 3) := congrArg Prod.fst ih
    have hB : (q (n + 9) : ZMod 3) = (q (n + 1) : ZMod 3) :=
      congrArg (fun p : ZMod 3 × ZMod 3 × ZMod 3 => p.2.1) ih
    have hC : (q (n + 10) : ZMod 3) = (q (n + 2) : ZMod 3) :=
      congrArg (fun p : ZMod 3 × ZMod 3 × ZMod 3 => p.2.2) ih
    have hNext :
        (q (n + 11) : ZMod 3) = (q (n + 3) : ZMod 3) := by
      have h8 : (q ((n + 8) + 3) : ZMod 3) =
          2 * (q ((n + 8) + 2) : ZMod 3) + (q ((n + 8) + 1) : ZMod 3) :=
        q_mod_three (n + 8)
      have h0 : (q (n + 3) : ZMod 3) =
          2 * (q (n + 2) : ZMod 3) + (q (n + 1) : ZMod 3) :=
        q_mod_three n
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at h8 h0 hB hC ⊢
      rw [h8, hC, hB, h0]
    simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at hB hC hNext ⊢
    exact ⟨hB, hC, hNext⟩

theorem q_mod3_period8 (n : ℕ) : (q (n + 8) : ZMod 3) = (q n : ZMod 3) :=
  congrArg Prod.fst (q_triple_mod3_period8 n)

theorem q_emod_three_period8 (n : ℕ) : q (n + 8) % 3 = q n % 3 := by
  have h := q_mod3_period8 n
  simpa using (ZMod.intCast_eq_intCast_iff' (q (n + 8)) (q n) 3).mp h

private lemma q_mod3_add_eight_mul (k r : ℕ) :
    (q (8 * k + r) : ZMod 3) = (q r : ZMod 3) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hrewrite : 8 * (k + 1) + r = 8 * k + r + 8 := by ring
    rw [hrewrite, q_mod3_period8, ih]

theorem q_mod3_of_mod8 (n : ℕ) : (q n : ZMod 3) = (q (n % 8) : ZMod 3) := by
  calc
    (q n : ZMod 3) = (q (8 * (n / 8) + n % 8) : ZMod 3) := by
      congr 2
      exact (Nat.div_add_mod n 8).symm
    _ = (q (n % 8) : ZMod 3) := q_mod3_add_eight_mul (n / 8) (n % 8)

/-- `q n ≡ 0 (mod 3)` iff `n ≡ 3 or 7 (mod 8)`. -/
theorem q_dvd_three_iff (n : ℕ) :
    (3 : ℤ) ∣ q n ↔ n % 8 = 3 ∨ n % 8 = 7 := by
  have hcast : (3 : ℤ) ∣ q n ↔ (q n : ZMod 3) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (q n) 3).symm
  rw [hcast, q_mod3_of_mod8]
  have : n % 8 < 8 := Nat.mod_lt n (by decide)
  interval_cases n % 8 <;> native_decide

/-- Linear three-register recursor; equals `(q n, q (n+1), q (n+2))`. -/
def qTriple : ℕ → ℤ × ℤ × ℤ
  | 0 => (1, 2, 5)
  | n + 1 =>
    match qTriple n with
    | (a, b, c) => (b, c, 2 * c + b + 3 * a)

theorem qTriple_eq (n : ℕ) : qTriple n = (q n, q (n + 1), q (n + 2)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [qTriple, ih]
    simp [q_rec]

theorem q_eq_triple_fst (n : ℕ) : q n = (qTriple n).1 := by
  rw [qTriple_eq]

theorem q_mod_nine (n : ℕ) :
    (q (n + 3) : ZMod 9) =
      2 * (q (n + 2) : ZMod 9) + (q (n + 1) : ZMod 9) + 3 * (q n : ZMod 9) := by
  rw [q_rec]
  push_cast
  rfl

/-- The triple `(q n, q (n+1), q (n+2))` in `(ℤ/9ℤ)³` has period 24. -/
theorem q_triple_mod9_period24 (n : ℕ) :
    ((q (n + 24) : ZMod 9), (q (n + 25) : ZMod 9), (q (n + 26) : ZMod 9)) =
      ((q n : ZMod 9), (q (n + 1) : ZMod 9), (q (n + 2) : ZMod 9)) := by
  induction n with
  | zero =>
    have h0 : (q 24 : ZMod 9) = (q 0 : ZMod 9) := by
      rw [q_eq_triple_fst 24, q_eq_triple_fst 0]
      native_decide
    have h1 : (q 25 : ZMod 9) = (q 1 : ZMod 9) := by
      rw [q_eq_triple_fst 25, q_eq_triple_fst 1]
      native_decide
    have h2 : (q 26 : ZMod 9) = (q 2 : ZMod 9) := by
      rw [q_eq_triple_fst 26, q_eq_triple_fst 2]
      native_decide
    exact Prod.ext h0 (Prod.ext h1 h2)
  | succ n ih =>
    have hB : (q (n + 25) : ZMod 9) = (q (n + 1) : ZMod 9) :=
      congrArg (fun p : ZMod 9 × ZMod 9 × ZMod 9 => p.2.1) ih
    have hC : (q (n + 26) : ZMod 9) = (q (n + 2) : ZMod 9) :=
      congrArg (fun p : ZMod 9 × ZMod 9 × ZMod 9 => p.2.2) ih
    have hA' : (q (n + 24) : ZMod 9) = (q n : ZMod 9) := congrArg Prod.fst ih
    have hNext : (q (n + 27) : ZMod 9) = (q (n + 3) : ZMod 9) := by
      have h24 : (q ((n + 24) + 3) : ZMod 9) =
          2 * (q ((n + 24) + 2) : ZMod 9) + (q ((n + 24) + 1) : ZMod 9) +
            3 * (q (n + 24) : ZMod 9) :=
        q_mod_nine (n + 24)
      have h0 : (q (n + 3) : ZMod 9) =
          2 * (q (n + 2) : ZMod 9) + (q (n + 1) : ZMod 9) + 3 * (q n : ZMod 9) :=
        q_mod_nine n
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at h24 h0 hA' hB hC ⊢
      rw [h24, hC, hB, hA', h0]
    simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at hB hC hNext ⊢
    exact ⟨hB, hC, hNext⟩

theorem q_mod9_period24 (n : ℕ) : (q (n + 24) : ZMod 9) = (q n : ZMod 9) :=
  congrArg Prod.fst (q_triple_mod9_period24 n)

theorem q_mod9_add_mul (k r : ℕ) :
    (q (24 * k + r) : ZMod 9) = (q r : ZMod 9) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hrewrite : 24 * (k + 1) + r = 24 * k + r + 24 := by ring
    rw [hrewrite, q_mod9_period24, ih]

theorem q_mod9_of_mod24 (n : ℕ) : (q n : ZMod 9) = (q (n % 24) : ZMod 9) := by
  calc
    (q n : ZMod 9) = (q (24 * (n / 24) + n % 24) : ZMod 9) := by
      congr 2
      exact (Nat.div_add_mod n 24).symm
    _ = (q (n % 24) : ZMod 9) := q_mod9_add_mul (n / 24) (n % 24)

end Ostrowski.NP

import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic

namespace Problems.Juggler

/-!
# One-step Juggler map

`floorPower` is the entire dynamics. This file names one-step
evaluation and the two-step odd-state directions. It does not mention
words, drift, certificates, or termination.
-/

/-- Even `n` maps to `Nat.sqrt n`; odd `n` maps to `Nat.sqrt (n^3)`. -/
def floorPower (n : ℕ) : ℕ :=
  if n % 2 = 0 then n.sqrt else (n ^ 3).sqrt

theorem floorPower_even_eq {n : ℕ} (heven : n % 2 = 0) :
    floorPower n = n.sqrt :=
  if_pos heven

theorem floorPower_odd_eq {n : ℕ} (hodd : n % 2 = 1) :
    floorPower n = (n ^ 3).sqrt := by
  have hodd0 : n % 2 ≠ 0 := by omega
  simp [floorPower, hodd0]

theorem floorPower_pos {n : ℕ} (hn : 1 ≤ n) : 1 ≤ floorPower n := by
  cases Nat.mod_two_eq_zero_or_one n with
  | inl heven =>
      rw [floorPower_even_eq heven]
      exact Nat.le_sqrt.mpr (by simpa [pow_two] using hn)
  | inr hodd =>
      rw [floorPower_odd_eq hodd]
      have h3 : 1 ≤ n ^ 3 :=
        Nat.succ_le_of_lt (pow_pos (lt_of_lt_of_le (by decide : 0 < 1) hn) 3)
      exact Nat.le_sqrt.mpr (by simpa [pow_two] using h3)

/-- Integer obstruction: `k^4 ≤ n^3` and `n ≥ 2` forbid `k ≥ n`.
This is iterated `Nat.sqrt` of `n^3`, not `T^2` on the odd-to-odd branch. -/
theorem sqrt_sqrt_n_cubed_lt {n : ℕ} (hn : 2 ≤ n) :
    ((n ^ 3).sqrt).sqrt < n := by
  set m := (n ^ 3).sqrt
  set k := m.sqrt
  have hk : k * k ≤ m := Nat.sqrt_le m
  have hm : m * m ≤ n ^ 3 := Nat.sqrt_le (n ^ 3)
  have hk4 : k * k * (k * k) ≤ m * m := Nat.mul_le_mul hk hk
  have hk4n : k ^ 4 ≤ n ^ 3 := by
    have : k * k * k * k ≤ n ^ 3 := by
      simpa [mul_assoc] using (le_trans hk4 hm)
    simpa [pow_succ, pow_zero, mul_assoc] using this
  refine Nat.lt_of_not_ge fun hkn => ?_
  have hn4 : n ^ 4 ≤ k ^ 4 := by
    have h2 := Nat.mul_le_mul hkn hkn
    have h4 := Nat.mul_le_mul h2 h2
    simpa [pow_succ, pow_zero, mul_assoc] using h4
  have hle : n ^ 4 ≤ n ^ 3 := le_trans hn4 hk4n
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
  have hn3 : 0 < n ^ 3 := pow_pos hn0 3
  have hmul : n * n ^ 3 ≤ 1 * n ^ 3 := by
    simpa [pow_succ, pow_zero, mul_assoc] using hle
  have : n ≤ 1 := Nat.le_of_mul_le_mul_right hmul hn3
  omega

/-- On the odd-to-even branch, `T^2(n) < n`. Not a halt theorem for the full map. -/
theorem floorPower_odd_even_two_step_lt
    {n : ℕ} (hn : 2 ≤ n) (hodd : n % 2 = 1)
    (heven : (n ^ 3).sqrt % 2 = 0) :
    floorPower (floorPower n) < n := by
  have step1 : floorPower n = (n ^ 3).sqrt := floorPower_odd_eq hodd
  have step2 : floorPower (floorPower n) = ((n ^ 3).sqrt).sqrt := by
    rw [step1]
    exact floorPower_even_eq heven
  rw [step2]
  exact sqrt_sqrt_n_cubed_lt hn

/-- Integer comparison: `(n+1)^2 ≤ n^3` for `n ≥ 3`. Threshold for odd-branch growth. -/
theorem succ_sq_le_cube {n : ℕ} (hn : 3 ≤ n) : (n + 1) ^ 2 ≤ n ^ 3 := by
  zify
  nlinarith

/-- On the odd branch, `n ≥ 3` implies `T(n) > n`. Independent of the parity of `T(n)`. -/
theorem floorPower_odd_gt {n : ℕ} (hn : 3 ≤ n) (hodd : n % 2 = 1) :
    n < floorPower n := by
  rw [floorPower_odd_eq hodd]
  have hsq : (n + 1) ^ 2 ≤ n ^ 3 := succ_sq_le_cube hn
  have : n + 1 ≤ (n ^ 3).sqrt := Nat.le_sqrt.mpr (by simpa [pow_two] using hsq)
  omega

/-- The odd branch is nondecreasing: `k ≤ T(k)` when `k` is odd and positive. -/
theorem floorPower_odd_nondecreasing {k : ℕ} (hk : 1 ≤ k) (hodd : k % 2 = 1) :
    k ≤ floorPower k := by
  rw [floorPower_odd_eq hodd]
  have h1 : k ^ 2 ≤ k ^ 3 := by
    have : 1 ≤ k := hk
    simpa [pow_succ, pow_two, pow_zero, mul_assoc] using
      Nat.mul_le_mul_left (k * k) this
  exact Nat.le_sqrt.mpr (by simpa [pow_two] using h1)

/-- On the odd-to-odd branch with `n ≥ 3`, `T^2(n) > n`. Dual of
`floorPower_odd_even_two_step_lt`. Not a divergence theorem. -/
theorem floorPower_odd_odd_two_step_gt
    {n : ℕ} (hn : 3 ≤ n) (hodd : n % 2 = 1)
    (hodd1 : (n ^ 3).sqrt % 2 = 1) :
    n < floorPower (floorPower n) := by
  have step1 : floorPower n = (n ^ 3).sqrt := floorPower_odd_eq hodd
  have hkpos : 1 ≤ floorPower n := by
    have : n < floorPower n := floorPower_odd_gt hn hodd
    omega
  have hoddT : floorPower n % 2 = 1 := by
    simpa [step1] using hodd1
  have hmono : floorPower n ≤ floorPower (floorPower n) :=
    floorPower_odd_nondecreasing hkpos hoddT
  have hgt : n < floorPower n := floorPower_odd_gt hn hodd
  omega

/-- Combined odd-state two-step direction for `n ≥ 3`. Not a
macro-transition law, not a halt theorem, and not a divergence theorem.
The case `n = 1` is excluded: `floorPower 1 = 1`. -/
theorem floorPower_odd_macro_direction
    {n : ℕ} (hn : 3 ≤ n) (hodd : n % 2 = 1) :
    ((n ^ 3).sqrt % 2 = 0 → floorPower (floorPower n) < n) ∧
    ((n ^ 3).sqrt % 2 = 1 → n < floorPower (floorPower n)) := by
  refine ⟨?he, ?ho⟩
  · intro heven
    have hn2 : 2 ≤ n := le_trans (by decide : 2 ≤ 3) hn
    exact floorPower_odd_even_two_step_lt hn2 hodd heven
  · intro hodd1
    exact floorPower_odd_odd_two_step_gt hn hodd hodd1

/-- Even branch: `T(n)^2 ≤ n`. Exact floor bound, not a real square root. -/
theorem floorPower_even_sq_le {n : ℕ} (heven : n % 2 = 0) :
    floorPower n ^ 2 ≤ n := by
  rw [floorPower_even_eq heven]
  simpa [pow_two] using Nat.sqrt_le n

/-- Odd branch: `T(n)^2 ≤ n^3`. Exact floor bound, not a real 3/2-power. -/
theorem floorPower_odd_sq_le_cube {n : ℕ} (hodd : n % 2 = 1) :
    floorPower n ^ 2 ≤ n ^ 3 := by
  rw [floorPower_odd_eq hodd]
  have hle : (n ^ 3).sqrt * (n ^ 3).sqrt ≤ n ^ 3 := Nat.sqrt_le (n ^ 3)
  simpa [pow_two] using hle

/-- Odd squares attain the one-step envelope: odd `m` implies `T(m^2)^2 = (m^2)^3`. -/
theorem floorPower_odd_sq_eq_cube_of_sq {m : ℕ} (hodd : m % 2 = 1) :
    floorPower (m ^ 2) ^ 2 = (m ^ 2) ^ 3 := by
  have nne : (m ^ 2) % 2 = 1 := by
    rw [Nat.pow_two, Nat.mul_mod, hodd]
  rw [floorPower_odd_eq nne]
  have hcube : (m ^ 2) ^ 3 = (m ^ 3) ^ 2 := by ring
  rw [hcube, Nat.sqrt_eq']

/-- Smallest mixed-equality witness: word `O` at `n=9`. -/
theorem floorPower_nine_odd_eq : floorPower 9 ^ 2 = 9 ^ 3 := by
  have h : floorPower ((3 : ℕ) ^ 2) ^ 2 = ((3 : ℕ) ^ 2) ^ 3 :=
    floorPower_odd_sq_eq_cube_of_sq (by decide)
  simpa using h

theorem floorPower_even_lt {n : ℕ} (hn : 2 ≤ n) (he : n % 2 = 0) :
    floorPower n < n := by
  have hsq : floorPower n ^ 2 ≤ n := floorPower_even_sq_le he
  refine Nat.lt_of_not_ge fun hge => ?_
  have : n ^ 2 ≤ n := le_trans (Nat.pow_le_pow_left hge 2) hsq
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hn
  have : n ≤ 1 :=
    Nat.le_of_mul_le_mul_right (by simpa [pow_two] using this) hn0
  omega

theorem floorPower_one : floorPower 1 = 1 := by
  decide +kernel

theorem floorPower_two : floorPower 2 = 1 := by
  decide +kernel

theorem floorPower_four : floorPower 4 = 2 := by
  decide +kernel

theorem floorPower_six : floorPower 6 = 2 := by
  decide +kernel

theorem floorPower_seven : floorPower 7 = 18 := by
  decide +kernel

theorem floorPower_eight : floorPower 8 = 2 := by
  decide +kernel

/-- Packet seed: `T(13) = 46`. -/
theorem floorPower_thirteen_step : floorPower 13 = 46 := by
  decide +kernel

theorem floorPower_eighteen : floorPower 18 = 4 := by
  decide +kernel

theorem floorPower_even_mono {n m : ℕ}
    (hn : n % 2 = 0) (hm : m % 2 = 0) (hle : n ≤ m) :
    floorPower n ≤ floorPower m := by
  rw [floorPower_even_eq hn, floorPower_even_eq hm]
  exact Nat.sqrt_le_sqrt hle

theorem floorPower_odd_mono {n m : ℕ}
    (hn : n % 2 = 1) (hm : m % 2 = 1) (hle : n ≤ m) :
    floorPower n ≤ floorPower m := by
  rw [floorPower_odd_eq hn, floorPower_odd_eq hm]
  exact Nat.sqrt_le_sqrt (pow_le_pow_left' hle 3)

end Problems.Juggler

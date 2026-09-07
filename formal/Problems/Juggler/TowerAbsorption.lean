import Mathlib.Logic.Function.Iterate
import Problems.Juggler.Dynamics

namespace Problems.Juggler

/-!
# Tower absorption: even steps never deepen the floor tower

Iterating `Nat.sqrt` `j` times is the integer `2^j`-th root: the
intermediate floors are transparent. Applied to the Juggler map this
says that an odd step followed by `j` even steps lands exactly on the
integer `2^(j+1)`-th root of `n^3`, i.e. on `⌊n^{3/2^(j+1)}⌋`, so the
nested-floor tower of an orbit value has one level per *odd* letter and
the even runs only change the exponent of the last level. This is the
`EXACT` clause of `juggler_effective_tower_height`.
-/

/-- `j` iterated integer square roots of `x` equal `s` exactly when
`s^(2^j) ≤ x < (s+1)^(2^j)`: the intermediate floors are transparent. -/
theorem sqrt_iter_eq_iff (j : ℕ) {x s : ℕ} :
    Nat.sqrt^[j] x = s ↔ s ^ 2 ^ j ≤ x ∧ x < (s + 1) ^ 2 ^ j := by
  induction j generalizing x with
  | zero =>
      simp only [Function.iterate_zero, id_eq, pow_zero, pow_one]
      omega
  | succ j ih =>
      rw [Function.iterate_succ_apply, ih]
      have hs : s ^ 2 ^ (j + 1) = s ^ 2 ^ j * s ^ 2 ^ j := by
        rw [pow_succ, pow_mul, sq]
      have hs1 : (s + 1) ^ 2 ^ (j + 1) = (s + 1) ^ 2 ^ j * (s + 1) ^ 2 ^ j := by
        rw [pow_succ, pow_mul, sq]
      rw [hs, hs1, Nat.le_sqrt, Nat.sqrt_lt]

/-- On an even run the Juggler map is iterated `Nat.sqrt`. -/
theorem floorPower_iter_of_even {m j : ℕ}
    (heven : ∀ i < j, Nat.sqrt^[i] m % 2 = 0) :
    floorPower^[j] m = Nat.sqrt^[j] m := by
  induction j with
  | zero => rfl
  | succ j ih =>
      have ih' : floorPower^[j] m = Nat.sqrt^[j] m :=
        ih (fun i hi => heven i (Nat.lt_succ_of_lt hi))
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih',
        floorPower_even_eq (heven j (Nat.lt_succ_self j))]

/-- An odd step followed by `j` even steps is the integer `2^(j+1)`-th
root of `n^3`: the value `⌊n^{3/2^(j+1)}⌋`, one floor, no nesting. -/
theorem floorPower_odd_even_run {n j : ℕ} (hodd : n % 2 = 1)
    (heven : ∀ i < j, Nat.sqrt^[i] ((n ^ 3).sqrt) % 2 = 0) :
    floorPower^[j + 1] n = Nat.sqrt^[j + 1] (n ^ 3) := by
  rw [Function.iterate_succ_apply, floorPower_odd_eq hodd,
    floorPower_iter_of_even heven, Function.iterate_succ_apply]

/-- The cell of the value after `O E^j`: `s^(2^(j+1)) ≤ n^3 < (s+1)^(2^(j+1))`. -/
theorem floorPower_odd_even_run_eq_iff {n j s : ℕ} (hodd : n % 2 = 1)
    (heven : ∀ i < j, Nat.sqrt^[i] ((n ^ 3).sqrt) % 2 = 0) :
    floorPower^[j + 1] n = s ↔
      s ^ 2 ^ (j + 1) ≤ n ^ 3 ∧ n ^ 3 < (s + 1) ^ 2 ^ (j + 1) := by
  rw [floorPower_odd_even_run hodd heven, sqrt_iter_eq_iff]

/-- The `OE` fiber of `FateContagion` is the case `j = 1`. -/
theorem floorPower_oe_eq_iff {n s : ℕ} (hodd : n % 2 = 1)
    (heven : (n ^ 3).sqrt % 2 = 0) :
    floorPower (floorPower n) = s ↔ s ^ 4 ≤ n ^ 3 ∧ n ^ 3 < (s + 1) ^ 4 := by
  have h := floorPower_odd_even_run_eq_iff (n := n) (j := 1) (s := s) hodd
    (fun i hi => by
      have : i = 0 := by omega
      subst this
      simpa using heven)
  simpa using h

end Problems.Juggler

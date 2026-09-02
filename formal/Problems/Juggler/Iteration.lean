import Problems.Juggler.Dynamics

namespace Problems.Juggler

/-!
# Iteration of the one-step map

`floorPower^[k]` and the addition law. No parity, no itineraries.
-/

theorem iterate_cons (n : ℕ) (k : ℕ) :
    floorPower^[k + 1] n = floorPower^[k] (floorPower n) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply, ih, ← Function.iterate_succ_apply]

theorem iterate_add_right (n k r : ℕ) :
    floorPower^[k + r] n = floorPower^[r] (floorPower^[k] n) := by
  rw [Nat.add_comm, Function.iterate_add_apply]

theorem floorPower_iterate_pos {n : ℕ} (hn : 1 ≤ n) : ∀ k, 1 ≤ floorPower^[k] n
  | 0 => hn
  | k + 1 => by
      have ih := floorPower_iterate_pos (floorPower_pos hn) k
      simpa [iterate_cons] using ih

end Problems.Juggler

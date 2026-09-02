import Problems.Juggler.LandingParity

namespace Problems.Juggler

/-!
# Iterated odd-landing sets

`oddLanding y` is one odd-to-odd step. `oddRun r y` is the nested
set `P_r`: the first `r+1` images of `y` remain odd after an odd
start. The exact recursion is

```
oddRun (r+1) y  ↔  y odd ∧ oddRun r (T(y))
```

An odd floor cell has at most one integer, so the backward
“cylinder” of a landing is empty or a singleton. This is the
existing `odd_preimage_unique` law, not a shrinking-interval calculus.

This file does not claim a density law, a finite odd-run bound, or
that every start reaches `1`.
-/

abbrev oddLanding (y : ℕ) : Prop :=
  y % 2 = 1 ∧ landingParity y = 1

def oddRun : ℕ → ℕ → Prop
  | 0, y => oddLanding y
  | r + 1, y => oddLanding y ∧ oddRun r (floorPower y)

def oddRunLength : ℕ → ℕ → ℕ
  | _, 0 => 0
  | y, cap + 1 =>
      if y % 2 = 1 ∧ landingParity y = 1 then
        oddRunLength (floorPower y) cap + 1
      else 0

theorem oddLanding_iff {y : ℕ} :
    oddLanding y ↔ y % 2 = 1 ∧ floorPower y % 2 = 1 :=
  Iff.rfl

theorem oddLanding_cell {y : ℕ} (hodd : y % 2 = 1) :
    oddLanding y ↔
      ∃ m, m % 2 = 1 ∧ m ^ 2 ≤ y ^ 3 ∧ y ^ 3 < (m + 1) ^ 2 := by
  constructor
  · intro h
    exact (landingParity_odd_iff hodd).mp h.2
  · intro h
    exact ⟨hodd, (landingParity_odd_iff hodd).mpr h⟩

theorem oddRun_zero (y : ℕ) :
    oddRun 0 y ↔ oddLanding y :=
  Iff.rfl

theorem oddRun_succ (r y : ℕ) :
    oddRun (r + 1) y ↔ oddLanding y ∧ oddRun r (floorPower y) :=
  Iff.rfl

theorem oddRun_start_odd {r y : ℕ} (h : oddRun r y) : y % 2 = 1 := by
  cases r with
  | zero => exact h.1
  | succ _ => exact h.1.1

/-- Exact set recursion: `P_{r+1} = {y odd : T(y) ∈ P_r}`. -/
theorem oddRun_recursive {r y : ℕ} :
    oddRun (r + 1) y ↔ y % 2 = 1 ∧ oddRun r (floorPower y) := by
  constructor
  · intro ⟨hland, hrun⟩
    exact ⟨hland.1, hrun⟩
  · intro ⟨hodd, hrun⟩
    have hz : floorPower y % 2 = 1 := oddRun_start_odd hrun
    exact ⟨⟨hodd, hz⟩, hrun⟩

/-- The odd-landing cylinder of `m` contains at most one integer. -/
theorem oddLanding_preimage_unique {y z m : ℕ}
    (hy : y % 2 = 1) (hz : z % 2 = 1)
    (hyT : floorPower y = m) (hzT : floorPower z = m) :
    y = z :=
  odd_preimage_unique
    ((floorPower_odd_eq_iff_cube_interval hy).mp hyT)
    ((floorPower_odd_eq_iff_cube_interval hz).mp hzT)

end Problems.Juggler

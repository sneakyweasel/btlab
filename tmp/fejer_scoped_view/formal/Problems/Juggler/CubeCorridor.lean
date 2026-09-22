import Problems.Juggler.Corridor

namespace Problems.Juggler

/-!
# Cube-band arithmetic geometry

Pure scale geometry of the cell \(n^2\le x<n^3\). This file does
not know `AboveAnchor`, `CycleMin`, or `MinimalNonTerm`.
`FiniteProgress` bridges from these cells live in `Progress`.

`EnvelopeState` remains the one-sided upper envelope.
`PowerCorridor` remains the two-sided scale interval.
-/

/-- Even cube-not-square landing resets into the square cell. -/
theorem even_cube_not_square {x n : ℕ} (hn : 2 ≤ n) (he : x % 2 = 0)
    (hge : n ^ 2 ≤ x) (hlt : x < n ^ 3) :
    n ≤ floorPower x ∧ floorPower x < n ^ 2 := by
  have hc : PowerCorridor n x 2 3 := ⟨hge, hlt⟩
  refine ⟨?_, even_below_cube_preimage hn he hc.upper⟩
  have hnot : ¬floorPower x < n := by
    intro hdrop
    exact (not_le_of_gt ((even_below_square_iff he).mp hdrop)) hc.lower
  exact Nat.le_of_not_gt hnot

/-- Odd cube-not-square landing lifts to at least `n^3`.
Companion of `odd_ge_succ_sq_floorPower_ge_cube`, with floor `n^2`. -/
theorem odd_ge_sq_floor_ge_cube {x n : ℕ} (hodd : x % 2 = 1)
    (hge : n ^ 2 ≤ x) : n ^ 3 ≤ floorPower x := by
  rw [floorPower_odd_eq hodd]
  refine Nat.le_sqrt.mpr ?_
  have hpow : (n ^ 2) ^ 3 ≤ x ^ 3 := Nat.pow_le_pow_left hge 3
  have hexp : (n ^ 3) ^ 2 = (n ^ 2) ^ 3 := by simp [← Nat.pow_mul]
  have : (n ^ 3) ^ 2 ≤ x ^ 3 := by rwa [hexp]
  simpa [pow_two] using this

/-- Odd cube-band state: the leftover of `even_cube_not_square`. -/
def CubeOddLanding (n x : ℕ) : Prop :=
  n ^ 2 ≤ x ∧ x < n ^ 3 ∧ x % 2 = 1

theorem CubeOddLanding.corridor {n x : ℕ} (h : CubeOddLanding n x) :
    PowerCorridor n x 2 3 :=
  ⟨h.1, h.2.1⟩

theorem cube_odd_landing_two_le {x n : ℕ} (hn : 2 ≤ n)
    (h : CubeOddLanding n x) : 2 ≤ x := by
  have h4 : (2 : ℕ) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hn 2
  have : (4 : ℕ) ≤ n ^ 2 := by simpa using h4
  exact le_trans (by decide : (2 : ℕ) ≤ 4) (le_trans this h.1)

theorem cube_odd_landing_three_le {x n : ℕ} (hn : 2 ≤ n)
    (h : CubeOddLanding n x) : 3 ≤ x := by
  have h4 : (2 : ℕ) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hn 2
  have : (4 : ℕ) ≤ n ^ 2 := by simpa using h4
  exact le_trans (by decide : (3 : ℕ) ≤ 4) (le_trans this h.1)

/-- Generic odd-lift envelope from the cube cell: `T(x)^2 < n^9`. -/
theorem odd_lt_cube_floor_sq_lt_nine {x n : ℕ}
    (hodd : x % 2 = 1) (hlt : x < n ^ 3) :
    floorPower x ^ 2 < n ^ 9 := by
  have hle : floorPower x ^ 2 ≤ x ^ 3 := floorPower_odd_sq_le_cube hodd
  have hx : x ^ 3 < (n ^ 3) ^ 3 :=
    Nat.pow_lt_pow_left hlt (by decide : (3 : ℕ) ≠ 0)
  have h9 : (n ^ 3) ^ 3 = n ^ 9 := (Nat.pow_mul n 3 3).symm
  have : x ^ 3 < n ^ 9 := by rwa [h9] at hx
  exact lt_of_le_of_lt hle this

/-- Weak integer form of `T(x) < n^{9/2}`: `T(x) < n^5`. -/
theorem odd_lt_cube_floor_lt_five {x n : ℕ} (hn : 2 ≤ n)
    (hodd : x % 2 = 1) (hlt : x < n ^ 3) :
    floorPower x < n ^ 5 := by
  have hy2 : floorPower x ^ 2 < n ^ 9 := odd_lt_cube_floor_sq_lt_nine hodd hlt
  have h9 : n ^ 9 < n ^ 10 := pow_lt_of_two_le hn (by decide : (9 : ℕ) < 10)
  have h10 : n ^ 10 = (n ^ 5) ^ 2 := Nat.pow_mul n 5 2
  have : floorPower x ^ 2 < (n ^ 5) ^ 2 := lt_trans hy2 (h10 ▸ h9)
  exact (Nat.pow_lt_pow_iff_left (by decide : (2 : ℕ) ≠ 0)).1 this

/-- Odd cube landing lifts into `[n^3, n^5)`. -/
theorem cube_odd_lift {x n : ℕ} (hn : 2 ≤ n) (h : CubeOddLanding n x) :
    n ^ 3 ≤ floorPower x ∧ floorPower x < n ^ 5 :=
  ⟨odd_ge_sq_floor_ge_cube h.2.2 h.1, odd_lt_cube_floor_lt_five hn h.2.2 h.2.1⟩

/-- Even return after an odd cube lift is strictly below the source.
This is `floorPower_odd_even_two_step_lt` on the cube-band state, plus
the square-trap converse `T^2(x) ≥ n`. Not a claim that `T^2(x) < n^2`. -/
theorem cube_lift_even_reset {x n : ℕ} (hn : 2 ≤ n)
    (h : CubeOddLanding n x) (he : floorPower x % 2 = 0) :
    n ≤ floorPower (floorPower x) ∧ floorPower (floorPower x) < x := by
  have hx2 := cube_odd_landing_two_le hn h
  have hsqrt : (x ^ 3).sqrt % 2 = 0 := by
    simpa [floorPower_odd_eq h.2.2] using he
  have hzlt := floorPower_odd_even_two_step_lt hx2 h.2.2 hsqrt
  have hy := odd_ge_sq_floor_ge_cube h.2.2 h.1
  have hn2n3 : n ^ 2 ≤ n ^ 3 :=
    Nat.pow_le_pow_right (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hn)
      (by decide : (2 : ℕ) ≤ 3)
  have hyn2 : n ^ 2 ≤ floorPower x := le_trans hn2n3 hy
  have hzge : n ≤ floorPower (floorPower x) := by
    refine Nat.le_of_not_gt fun hdrop => ?_
    exact (not_le_of_gt ((even_below_square_iff he).mp hdrop)) hyn2
  exact ⟨hzge, hzlt⟩

/-- Even reset after an odd cube lift re-enters the cube-or-below corridor. -/
theorem cube_lift_even_reset_lt_cube {x n : ℕ} (hn : 2 ≤ n)
    (h : CubeOddLanding n x) (he : floorPower x % 2 = 0) :
    floorPower (floorPower x) < n ^ 3 :=
  lt_trans (cube_lift_even_reset hn h he).2 h.2.1

/-- Scale form of the even return: `T^2(x)^4 < n^9`, i.e. below `n^{9/4}`. -/
theorem cube_lift_even_reset_fourth {x n : ℕ}
    (h : CubeOddLanding n x) (he : floorPower x % 2 = 0) :
    floorPower (floorPower x) ^ 4 < n ^ 9 := by
  have hsq : floorPower (floorPower x) ^ 2 ≤ floorPower x :=
    floorPower_even_sq_le he
  have hy2 : floorPower x ^ 2 < n ^ 9 :=
    odd_lt_cube_floor_sq_lt_nine h.2.2 h.2.1
  have hz4 : floorPower (floorPower x) ^ 4 =
      (floorPower (floorPower x) ^ 2) ^ 2 :=
    Nat.pow_mul _ 2 2
  calc
    floorPower (floorPower x) ^ 4
        = (floorPower (floorPower x) ^ 2) ^ 2 := hz4
    _ ≤ floorPower x ^ 2 := Nat.pow_le_pow_left hsq 2
    _ < n ^ 9 := hy2

/-- Mixed OE cell: an odd cube step followed by an even square
step is the eighth-power comparison. This is strictly sharper
than composing `x < n^3` into `T^2(x) < n^{9/4}`. Not a
one-step envelope and not a defect restriction. -/
theorem odd_even_eighth_lt_sq {x n : ℕ}
    (hodd : x % 2 = 1) (he : floorPower x % 2 = 0) :
    floorPower (floorPower x) < n ^ 2 ↔ x ^ 3 < n ^ 8 := by
  have hy2 : floorPower x ^ 2 ≤ x ^ 3 := floorPower_odd_sq_le_cube hodd
  have hxlt : x ^ 3 < (floorPower x + 1) ^ 2 := by
    rw [floorPower_odd_eq hodd]
    simpa [pow_two, Nat.succ_eq_add_one] using Nat.lt_succ_sqrt (x ^ 3)
  constructor
  · intro hz
    have hy : floorPower x < n ^ 4 := (even_below_fourth he).mp hz
    have hle : (floorPower x + 1) ^ 2 ≤ n ^ 8 := by
      have : floorPower x + 1 ≤ n ^ 4 := Nat.succ_le_of_lt hy
      have hsq : (floorPower x + 1) ^ 2 ≤ (n ^ 4) ^ 2 :=
        Nat.pow_le_pow_left this 2
      have h8 : (n ^ 4) ^ 2 = n ^ 8 := (Nat.pow_mul n 4 2).symm
      rwa [h8] at hsq
    exact lt_of_lt_of_le hxlt hle
  · intro hx
    have hy : floorPower x < n ^ 4 := by
      have : floorPower x ^ 2 < n ^ 8 := lt_of_le_of_lt hy2 hx
      have h8 : n ^ 8 = (n ^ 4) ^ 2 := Nat.pow_mul n 4 2
      exact (Nat.pow_lt_pow_iff_left (by decide : (2 : ℕ) ≠ 0)).1
        (by rwa [h8] at this)
    exact (even_below_fourth he).mpr hy

/-- Odd continuation after an odd cube lift rises above the source. -/
theorem cube_lift_odd_continues {x n : ℕ} (hn : 2 ≤ n)
    (h : CubeOddLanding n x) (hodd1 : floorPower x % 2 = 1) :
    x < floorPower (floorPower x) := by
  have hx3 := cube_odd_landing_three_le hn h
  have hsqrt : (x ^ 3).sqrt % 2 = 1 := by
    simpa [floorPower_odd_eq h.2.2] using hodd1
  exact floorPower_odd_odd_two_step_gt hx3 h.2.2 hsqrt

/-- Odd continuation from a cube-band lift is at least `n^4`. -/
theorem cube_lift_odd_ge_fourth {x n : ℕ} (hn : 2 ≤ n)
    (h : CubeOddLanding n x) (hodd1 : floorPower x % 2 = 1) :
    n ^ 4 ≤ floorPower (floorPower x) := by
  have hy := odd_ge_sq_floor_ge_cube h.2.2 h.1
  rw [floorPower_odd_eq hodd1]
  refine Nat.le_sqrt.mpr ?_
  have hpow : (n ^ 3) ^ 3 ≤ (floorPower x) ^ 3 := Nat.pow_le_pow_left hy 3
  have h9 : (n ^ 3) ^ 3 = n ^ 9 := (Nat.pow_mul n 3 3).symm
  have h8 : (n ^ 4) ^ 2 = n ^ 8 := (Nat.pow_mul n 4 2).symm
  have h89 : n ^ 8 ≤ n ^ 9 :=
    Nat.pow_le_pow_right (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hn)
      (by decide : (8 : ℕ) ≤ 9)
  have : (n ^ 4) ^ 2 ≤ (floorPower x) ^ 3 :=
    le_trans (h8 ▸ h89) (h9 ▸ hpow)
  simpa [pow_two] using this

end Problems.Juggler

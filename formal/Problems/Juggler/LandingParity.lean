import Problems.Juggler.Preimages
import Problems.Juggler.ExpandingGrammar

namespace Problems.Juggler

/-!
# Landing cells and threshold position

A Juggler step lands in a consecutive-square cell:

```
T(x) = m  ↔  m^2 ≤ F(x) < (m+1)^2
```

with `F(x) = x` on the even branch and `F(x) = x^3` on the odd
branch. The normalized gap `θ = ρ / (2T+1)` is the position inside
that cell. Persistence at an odd landing is exactly
`landingParity y = 1`.

These identities package the existing inverse-floor cells. They do
not claim that `θ` occupies a proper subinterval of `[0,1]` on
odd-to-odd states, and they do not claim that every start reaches `1`.
-/

def landingIndex (x : ℕ) : ℕ :=
  floorPower x

def landingSource (x : ℕ) : ℕ :=
  if x % 2 = 0 then x else x ^ 3

def landingCell (x m : ℕ) : Prop :=
  m ^ 2 ≤ landingSource x ∧ landingSource x < (m + 1) ^ 2

def landingGap (x : ℕ) : ℕ :=
  if x % 2 = 0 then localDefectEven x else localDefectOdd x

def landingWidth (x : ℕ) : ℕ :=
  2 * floorPower x + 1

/-- Normalized threshold coordinate as the pair `(ρ, 2T+1)`. -/
def normalizedLandingGap (x : ℕ) : ℕ × ℕ :=
  (landingGap x, landingWidth x)

def landingParity (x : ℕ) : ℕ :=
  floorPower x % 2

theorem landingCell_iff {x m : ℕ} :
    landingIndex x = m ↔ landingCell x m := by
  cases Nat.mod_two_eq_zero_or_one x with
  | inl h =>
      simp [landingIndex, landingCell, landingSource, h]
      exact floorPower_even_eq_iff_sq_interval h
  | inr h =>
      have hne : x % 2 ≠ 0 := by omega
      simp [landingIndex, landingCell, landingSource, hne]
      exact floorPower_odd_eq_iff_cube_interval h

theorem landingParity_odd_iff {x : ℕ} (hodd : x % 2 = 1) :
    landingParity x = 1 ↔
      ∃ m, m % 2 = 1 ∧ m ^ 2 ≤ x ^ 3 ∧ x ^ 3 < (m + 1) ^ 2 := by
  constructor
  · intro h
    refine ⟨floorPower x, h, ?_⟩
    exact (floorPower_odd_eq_iff_cube_interval hodd).mp rfl
  · intro ⟨m, hm, hle, hlt⟩
    have hT : floorPower x = m :=
      (floorPower_odd_eq_iff_cube_interval hodd).mpr ⟨hle, hlt⟩
    simpa [landingParity, hT] using hm

theorem landingParity_even_iff {x : ℕ} (heven : x % 2 = 0) :
    landingParity x = 1 ↔
      ∃ m, m % 2 = 1 ∧ m ^ 2 ≤ x ∧ x < (m + 1) ^ 2 := by
  constructor
  · intro h
    refine ⟨floorPower x, h, ?_⟩
    exact (floorPower_even_eq_iff_sq_interval heven).mp rfl
  · intro ⟨m, hm, hle, hlt⟩
    have hT : floorPower x = m :=
      (floorPower_even_eq_iff_sq_interval heven).mpr ⟨hle, hlt⟩
    simpa [landingParity, hT] using hm

theorem landingGap_bound (x : ℕ) :
    landingGap x < landingWidth x := by
  cases Nat.mod_two_eq_zero_or_one x with
  | inl h =>
      rw [landingGap, if_pos h, landingWidth]
      exact localDefectEven_lt_succ h
  | inr h =>
      have hne : x % 2 ≠ 0 := by omega
      rw [landingGap, if_neg hne, landingWidth]
      exact localDefectOdd_lt_succ h

theorem landingGap_add_even {x : ℕ} (heven : x % 2 = 0) :
    landingIndex x ^ 2 + landingGap x = landingSource x := by
  simp [landingIndex, landingGap, landingSource, heven]
  exact localDefectEven_add heven

theorem landingGap_add_odd {x : ℕ} (hodd : x % 2 = 1) :
    landingIndex x ^ 2 + landingGap x = landingSource x := by
  have hne : x % 2 ≠ 0 := by omega
  simp [landingIndex, landingGap, landingSource, hne]
  exact localDefectOdd_add hodd

/-- Persistence at `y` is exactly an odd-to-odd landing. -/
theorem persistent_landing_constraint {x y : ℕ}
    (h : PersistentOddResidual x y) :
    y % 2 = 1 ∧ landingParity y = 1 :=
  ⟨h.2.2.1, h.2.2.2⟩

end Problems.Juggler

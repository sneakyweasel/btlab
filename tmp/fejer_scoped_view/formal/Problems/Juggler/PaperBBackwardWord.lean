/-
# The backward word, and why `R`'s jump set is the rotation orbit

`J-boundary-fraction-is-a-step-function-on-the-orbit` rests on one observation: the `j`-th
letter of the backward word,

  `w_j (phi) = 1 { fract (phi - (j+1) * b) >= 1 - b }`,

is written against the anchor `(j+1) * b` but is really the indicator of an arc anchored at
`j * b`.  Once that is proved the rest of the row is immediate — a length-`K` word can only
flip at `{k * b : k <= K}`, so the profile computed from the word is constant between those
points, and `R` is a step function whose jump set is the orbit.

* `backWord_iff_fract_lt` — the arc form: `w_j (phi)` holds exactly when
  `fract (phi - j * b) < b`.  This is the whole content; the two statements below are
  corollaries of it and are stated because they are what the row actually uses.
* `backWord_of_mem_arc` / `not_backWord_of_mem_gap` — the letter is constant on `[j*b, (j+1)*b)`
  and constant on `[(j+1)*b, j*b + 1)`, which are the two arcs the orbit cuts.
* `backWord_shift` — `w_(j+1) (phi + b) = w_j (phi)`.  Shifting the phase by `b` shifts the
  word one place, which is the relation `J-phase-shift-is-one-update-and-R-halves` turns into
  a cocycle; its other half, that a non-rising step halves the boundary value, is already
  `PaperBBarrierStep.update_false_at_zero`.

What this does not say.  Nothing here asserts that the quasi-stationary profile exists, so
nothing here states the cocycle itself.  These are facts about the word, which is the input to
that construction and the part that is exact.  The convergence remains the open obligation
recorded in `J-boundary-fraction-is-the-clean-coordinate`.
-/

import Mathlib.Tactic
import Mathlib.Algebra.Order.Floor.Ring
import Problems.Juggler.PaperBTilt

namespace Problems.Juggler

namespace PaperBBackwardWord

variable {b : ℝ}

/-- The `j`-th letter of the backward word at phase `phi`: the barrier rises `j` steps back. -/
def backWord (b : ℝ) (j : ℕ) (phi : ℝ) : Prop :=
  1 - b ≤ Int.fract (phi - ((j : ℝ) + 1) * b)

/-- Subtracting a sub-unit amount that the fractional part cannot absorb wraps once. -/
private theorem fract_sub_wrap (h1 : b < 1) {x : ℝ} (h : Int.fract x < b) :
    Int.fract (x - b) = Int.fract x - b + 1 := by
  have h0' := Int.fract_nonneg x
  rw [Int.fract_eq_iff]
  refine ⟨by linarith, by linarith, ⟨⌊x⌋ - 1, ?_⟩⟩
  push_cast
  simp only [Int.fract]
  ring

/-- And absorbs it otherwise. -/
private theorem fract_sub_stay (h0 : 0 < b) {x : ℝ} (h : b ≤ Int.fract x) :
    Int.fract (x - b) = Int.fract x - b := by
  have h1' := Int.fract_lt_one x
  rw [Int.fract_eq_iff]
  refine ⟨by linarith, by linarith, ⟨⌊x⌋, ?_⟩⟩
  simp only [Int.fract]
  ring

/-- **The letter is an arc anchored at `j * b`.**  Written against `(j+1) * b`, the condition
`fract (phi - (j+1) * b) >= 1 - b` says exactly that `phi` lies within `b` of `j * b`.  This is
why the flips sit on the orbit rather than anywhere else. -/
theorem backWord_iff_fract_lt (h0 : 0 < b) (h1 : b < 1) (phi : ℝ) (j : ℕ) :
    backWord b j phi ↔ Int.fract (phi - (j : ℝ) * b) < b := by
  have hx : phi - ((j : ℝ) + 1) * b = (phi - (j : ℝ) * b) - b := by ring
  simp only [backWord, hx]
  rcases lt_or_ge (Int.fract (phi - (j : ℝ) * b)) b with h | h
  · rw [fract_sub_wrap h1 h]
    have hnn := Int.fract_nonneg (phi - (j : ℝ) * b)
    exact ⟨fun _ => h, fun _ => by linarith⟩
  · rw [fract_sub_stay h0 h]
    have := Int.fract_lt_one (phi - (j : ℝ) * b)
    constructor
    · intro hc; linarith
    · intro hc; linarith

/-- **Constant on the arc.**  Between `j * b` and `(j+1) * b` the letter is on. -/
theorem backWord_of_mem_arc (h0 : 0 < b) (h1 : b < 1) (j : ℕ) {x : ℝ}
    (hx : (j : ℝ) * b ≤ x) (hx' : x < (j : ℝ) * b + b) : backWord b j x := by
  rw [backWord_iff_fract_lt h0 h1]
  rw [Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
  linarith

/-- **Constant on the gap.**  Between `(j+1) * b` and the next orbit point the letter is off. -/
theorem not_backWord_of_mem_gap (h0 : 0 < b) (h1 : b < 1) (j : ℕ) {x : ℝ}
    (hx : (j : ℝ) * b + b ≤ x) (hx' : x < (j : ℝ) * b + 1) : ¬ backWord b j x := by
  rw [backWord_iff_fract_lt h0 h1, not_lt]
  rw [Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩]
  linarith

/-- **The letter depends on the phase only through its position relative to the anchor.** -/
theorem backWord_congr (h0 : 0 < b) (h1 : b < 1) (j : ℕ) {x y : ℝ}
    (h : Int.fract (x - (j : ℝ) * b) = Int.fract (y - (j : ℝ) * b)) :
    backWord b j x ↔ backWord b j y := by
  rw [backWord_iff_fract_lt h0 h1, backWord_iff_fract_lt h0 h1, h]

/-- **Shifting the phase shifts the word.**  `w_(j+1) (phi + b) = w_j (phi)`, which is the
relation the cocycle of `J-phase-shift-is-one-update-and-R-halves` is built from. -/
theorem backWord_shift (b phi : ℝ) (j : ℕ) :
    backWord b (j + 1) (phi + b) ↔ backWord b j phi := by
  simp only [backWord]
  push_cast
  rw [show phi + b - ((j : ℝ) + 1 + 1) * b = phi - ((j : ℝ) + 1) * b by ring]

end PaperBBackwardWord

end Problems.Juggler

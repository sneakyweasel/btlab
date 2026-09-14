import Representation.Words

namespace Operators.Shift

open Representation.Words

/-- Append a trailing zero: the word form of `S(n)=3n` before canonicalizing `0`. -/
def shiftWord (w : List Trit) : List Trit :=
  w ++ [Trit.zero]

theorem eval_shiftWord (w : List Trit) :
    evalMSD (shiftWord w) = 3 * evalMSD w :=
  evalMSD_append_zero w

/-- Digitwise negation is an involution. -/
theorem mapNeg_involutive (w : List Trit) : mapNeg (mapNeg w) = w := by
  induction w with
  | nil => rfl
  | cons d rest ih =>
      simp [mapNeg] at ih ⊢
      simp [ih]

theorem eval_mapNeg_involutive (w : List Trit) :
    evalMSD (mapNeg (mapNeg w)) = evalMSD w := by
  simp [mapNeg_involutive]

theorem N_commutes_S_word (w : List Trit) :
    mapNeg (shiftWord w) = shiftWord (mapNeg w) := by
  simp [shiftWord, mapNeg, Trit.negate]

theorem eval_N_commutes_S (w : List Trit) :
    evalMSD (mapNeg (shiftWord w)) = evalMSD (shiftWord (mapNeg w)) := by
  rw [N_commutes_S_word]

/-- `W ∘ S = W` at word level: trailing zeros are stripped by reverse. -/
theorem W_after_S (w : List Trit) :
    warpWord (shiftWord w) = warpWord w := by
  simpa [shiftWord] using warpWord_append_zeros w 1

end Operators.Shift

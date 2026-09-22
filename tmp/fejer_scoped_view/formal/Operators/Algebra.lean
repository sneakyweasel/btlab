import Operators.DigitDerivative

namespace Operators.Algebra

open Representation.Words
open Operators.Shift
open Operators.DigitDerivative

/-- `D ∘ S = id` on words. -/
theorem DS_identity (w : List Trit) : dropLSD (shiftWord w) = w :=
  D_after_S w

/-- `N ∘ S = S ∘ N` on words. -/
theorem NS_commute (w : List Trit) :
    mapNeg (shiftWord w) = shiftWord (mapNeg w) :=
  N_commutes_S_word w

/-- `N ∘ D = D ∘ N` on words. -/
theorem ND_commute (w : List Trit) :
    mapNeg (dropLSD w) = dropLSD (mapNeg w) :=
  N_commutes_D w

/-- `W ∘ S = W` on words. -/
theorem WS_identity (w : List Trit) :
    warpWord (shiftWord w) = warpWord w :=
  W_after_S w

/-- `N` is an involution. -/
theorem N_involution (w : List Trit) : mapNeg (mapNeg w) = w :=
  mapNeg_involutive w

/-- `W` is not an involution: `W(3)=1`. Word `+0` evaluates to 3 and warps to `+`. -/
def wordThree : List Trit := [Trit.plus, Trit.zero]

theorem eval_wordThree : evalMSD wordThree = 3 := by
  simp [wordThree, evalMSD, Trit.toInt]

theorem warp_wordThree : warpWord wordThree = [Trit.plus] := by
  unfold warpWord canonicalize dropLeadingZeros wordThree
  simp [List.reverse_cons, List.reverse_nil, List.dropWhile]

theorem eval_warp_wordThree : evalMSD (warpWord wordThree) = 1 := by
  rw [warp_wordThree]
  simp [evalMSD, Trit.toInt]

theorem W_not_involution_on_three :
    evalMSD (warpWord wordThree) ≠ evalMSD wordThree := by
  rw [eval_warp_wordThree, eval_wordThree]
  decide

end Operators.Algebra

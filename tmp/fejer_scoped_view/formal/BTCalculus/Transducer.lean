import Operators.DigitDerivative
import BTCalculus.Integral

namespace BTCalculus

open Representation.Words
open Operators.DigitDerivative
open Operators.Shift

/-- Algebraic word facts only. No Mealy-machine theory is formalized here. -/
theorem D_is_dropLSD (w : List Trit) : dropLSD w = w.dropLast := rfl

theorem I_is_appendLSD (a : Trit) (w : List Trit) :
    integralWord a w = w ++ [a] := rfl

theorem S_is_append_zero (w : List Trit) :
    shiftWord w = w ++ [Trit.zero] := rfl

theorem D_after_S_word (w : List Trit) : dropLSD (shiftWord w) = w :=
  D_after_S w

theorem D_after_I_word (a : Trit) (w : List Trit) :
    dropLSD (integralWord a w) = w :=
  D_after_integralWord a w

end BTCalculus

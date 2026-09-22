import BTCalculus.Integral

namespace BTCalculus

open Representation.Words
open Operators.DigitDerivative

theorem decode_derivative (w : List Trit) (hw : w ≠ []) :
    evalMSD (dropLSD w) = DZ (evalMSD w) := by
  have hexp := evalMSD_dropLSD w hw
  have hlsd : lsdZ (evalMSD w) = (w.getLast hw).toInt := by
    apply lsdZ_unique (trit_toInt_is_trit (w.getLast hw))
    have hmod : evalMSD w % 3 = (w.getLast hw).toInt % 3 := by
      calc
        evalMSD w % 3
            = ((w.getLast hw).toInt + 3 * evalMSD (dropLSD w)) % 3 := by
              rw [hexp]
          _ = ((w.getLast hw).toInt % 3 + (3 * evalMSD (dropLSD w)) % 3) % 3 :=
              Int.add_emod _ _ 3
          _ = ((w.getLast hw).toInt % 3 + 0) % 3 := by
              have h0 : (3 * evalMSD (dropLSD w)) % 3 = 0 :=
                Int.mul_emod_right 3 _
              rw [h0]
          _ = (w.getLast hw).toInt % 3 := by
              simp
    exact hmod
  unfold DZ
  rw [hlsd]
  have : evalMSD w - (w.getLast hw).toInt = 3 * evalMSD (dropLSD w) := by
    linarith [hexp]
  rw [this]
  exact (Int.mul_ediv_cancel_left (evalMSD (dropLSD w))
    (by decide : (3 : ℤ) ≠ 0)).symm

theorem decode_integral (a : Trit) (w : List Trit) :
    evalMSD (integralWord a w) = IZ a (evalMSD w) :=
  eval_integralWord a w

end BTCalculus

import BTCalculus.Derivative

namespace BTCalculus

open Representation.Words
open Operators.DigitDerivative

def IZ (a : Trit) (x : ℤ) : ℤ :=
  a.toInt + 3 * x

def PZ (a : Trit) (n : ℤ) : ℤ :=
  IZ a (DZ n)

theorem trit_toInt_is_trit (a : Trit) :
    a.toInt = -1 ∨ a.toInt = 0 ∨ a.toInt = 1 := by
  cases a <;> simp [Trit.toInt]

theorem IZ_mod (a : Trit) (x : ℤ) : IZ a x ≡ a.toInt [ZMOD 3] := by
  unfold IZ
  change (a.toInt + 3 * x) % 3 = a.toInt % 3
  have : (3 * x) % 3 = 0 := by simp
  rw [Int.add_emod, this, add_zero, Int.emod_emod]

theorem lsdZ_IZ (a : Trit) (x : ℤ) : lsdZ (IZ a x) = a.toInt :=
  lsdZ_unique (trit_toInt_is_trit a) (IZ_mod a x)

theorem D_after_I (a : Trit) (x : ℤ) : DZ (IZ a x) = x := by
  unfold DZ
  have hlsd := lsdZ_IZ a x
  unfold IZ at hlsd ⊢
  rw [hlsd]
  have : a.toInt + 3 * x - a.toInt = 3 * x := by ring
  rw [this]
  exact Int.mul_ediv_cancel_left x (by decide : (3 : ℤ) ≠ 0)

theorem I_after_D_iff (a : Trit) (n : ℤ) :
    IZ a (DZ n) = n ↔ lsdZ n = a.toInt := by
  constructor
  · intro h
    have := congrArg lsdZ h
    rw [lsdZ_IZ] at this
    exact this.symm
  · intro h
    unfold IZ
    have hd := decomp n
    rw [h] at hd
    linarith

theorem P_left_zero (a b : Trit) (n : ℤ) : PZ a (PZ b n) = PZ a n := by
  unfold PZ
  rw [D_after_I]

theorem P_idem (a : Trit) (n : ℤ) : PZ a (PZ a n) = PZ a n :=
  P_left_zero a a n

theorem D_after_P (a : Trit) (n : ℤ) : DZ (PZ a n) = DZ n := by
  unfold PZ
  exact D_after_I a (DZ n)

theorem P_after_D (a : Trit) (n : ℤ) : PZ a (DZ n) = IZ a (DZ (DZ n)) := rfl

def integralWord (a : Trit) (w : List Trit) : List Trit :=
  w ++ [a]

theorem eval_integralWord (a : Trit) (w : List Trit) :
    evalMSD (integralWord a w) = IZ a (evalMSD w) := by
  unfold integralWord IZ
  simpa [appendLSD, add_comm] using evalMSD_appendLSD w a

theorem D_after_integralWord (a : Trit) (w : List Trit) :
    dropLSD (integralWord a w) = w :=
  dropLSD_snoc a w

end BTCalculus

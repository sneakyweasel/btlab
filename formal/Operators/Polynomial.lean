import Representation.Words

namespace Operators.Polynomial

open Representation.Words

/-- Horner evaluation of an LSD-first coefficient list: `a0 + x (a1 + x (a2 + ⋯))`. -/
def evalPoly (coeffs : List Trit) (x : ℤ) : ℤ :=
  coeffs.foldr (fun d acc => d.toInt + x * acc) 0

/-- The empty word evaluates to `0`. -/
theorem evalPoly_nil (x : ℤ) : evalPoly [] x = 0 := rfl

/-- Horner step: `evalPoly (d :: rest) x = d + x * evalPoly rest x`. -/
theorem evalPoly_cons (d : Trit) (rest : List Trit) (x : ℤ) :
    evalPoly (d :: rest) x = d.toInt + x * evalPoly rest x := rfl

/-- MSD Horner at a general base. -/
def evalAt (w : List Trit) (x : ℤ) : ℤ :=
  w.foldl (fun acc d => x * acc + d.toInt) 0

/-- Evaluating a word at `3` returns its most-significant-digit value:
`evalAt w 3 = evalMSD w`. -/
theorem evalAt_three (w : List Trit) : evalAt w 3 = evalMSD w := rfl

private theorem foldl_horner_from (x : ℤ) :
    ∀ (w : List Trit) (init : ℤ),
      w.foldl (fun acc d => d.toInt + x * acc) init =
        w.foldl (fun acc d => x * acc + d.toInt) init
  | [], _ => rfl
  | d :: rest, init => by
      have h : d.toInt + x * init = x * init + d.toInt := add_comm _ _
      simp only [List.foldl_cons, h]
      exact foldl_horner_from x rest (x * init + d.toInt)

/-- `P(3)=n` for the LSD polynomial of an MSD word. -/
theorem evalPoly_reverse_three (w : List Trit) :
    evalPoly w.reverse 3 = evalMSD w := by
  unfold evalPoly evalMSD
  rw [List.foldr_reverse, foldl_horner_from]

private theorem foldl_sum_from :
    ∀ (w : List Trit) (init : ℤ),
      w.foldl (fun acc d => acc + d.toInt) init = init + (w.map Trit.toInt).sum
  | [], init => by simp
  | d :: rest, init => by
      simp [List.foldl_cons, foldl_sum_from rest, add_assoc]

/-- Evaluating the reversed word at `1` returns the digit sum. -/
theorem evalPoly_reverse_one (w : List Trit) :
    evalPoly w.reverse 1 = digitSum w := by
  unfold evalPoly digitSum
  rw [List.foldr_reverse, foldl_horner_from 1]
  simp only [one_mul]
  simpa using foldl_sum_from w 0

end Operators.Polynomial

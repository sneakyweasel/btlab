import Operators.Shift

namespace Operators.DigitDerivative

open Representation.Words
open Operators.Shift

/-- Drop the least-significant trit. The empty word is left empty. -/
def dropLSD (w : List Trit) : List Trit :=
  w.dropLast

theorem dropLast_snoc {α : Type*} (w : List α) (d : α) :
    (w ++ [d]).dropLast = w := by
  induction w with
  | nil => simp
  | cons x xs ih =>
      simp [List.dropLast, ih]

theorem eq_dropLast_append_getLast {α : Type*} :
    ∀ (w : List α) (hw : w ≠ []), w.dropLast ++ [w.getLast hw] = w
  | [], hw => (hw rfl).elim
  | [x], _ => by simp [List.getLast]
  | x :: y :: xs, hw => by
      have htail : y :: xs ≠ [] := List.cons_ne_nil _ _
      have ih := eq_dropLast_append_getLast (y :: xs) htail
      have hlast : (x :: y :: xs).getLast hw = (y :: xs).getLast htail := by
        simp [List.getLast]
      simp [List.dropLast, hlast, ih]

/-- The integer identity `n = lsd(n) + 3 D(n)` on a nonempty word. -/
theorem evalMSD_dropLSD (w : List Trit) (hw : w ≠ []) :
    evalMSD w = (w.getLast hw).toInt + 3 * evalMSD (dropLSD w) := by
  unfold dropLSD
  calc
    evalMSD w
        = evalMSD (w.dropLast ++ [w.getLast hw]) := by
            rw [eq_dropLast_append_getLast w hw]
      _ = 3 * evalMSD w.dropLast + (w.getLast hw).toInt :=
            evalMSD_appendLSD _ _
      _ = (w.getLast hw).toInt + 3 * evalMSD w.dropLast := by
            ring

/-- `D ∘ S = id` on words: dropping a freshly appended zero restores `w`. -/
theorem D_after_S (w : List Trit) : dropLSD (shiftWord w) = w := by
  simp [dropLSD, shiftWord]

theorem eval_D_after_S (w : List Trit) :
    evalMSD (dropLSD (shiftWord w)) = evalMSD w := by
  simp [D_after_S]

theorem map_dropLast {α β : Type*} (f : α → β) :
    ∀ w : List α, (w.dropLast).map f = (w.map f).dropLast
  | [] => rfl
  | [_] => by simp [List.dropLast]
  | _ :: _ :: _ => by simp [List.dropLast, map_dropLast f]

/-- Negation commutes with dropping the LSD. -/
theorem N_commutes_D (w : List Trit) :
    mapNeg (dropLSD w) = dropLSD (mapNeg w) := by
  simp [dropLSD, mapNeg]

theorem dropLSD_snoc (d : Trit) (w : List Trit) :
    dropLSD (w ++ [d]) = w :=
  dropLast_snoc w d

theorem reconstruct_step (d : Trit) (w : List Trit) :
    evalMSD (w ++ [d]) = d.toInt + 3 * evalMSD w := by
  simpa [appendLSD, add_comm] using evalMSD_appendLSD w d

theorem reverse_reverse (w : List Trit) : w.reverse.reverse = w :=
  List.reverse_reverse w

end Operators.DigitDerivative

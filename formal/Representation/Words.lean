import Mathlib

namespace Representation.Words

/-- Balanced ternary digits `-1`, `0`, `+1`. -/
inductive Trit where
  | minus
  | zero
  | plus
  deriving DecidableEq, Repr, Inhabited

namespace Trit

def toInt : Trit → ℤ
  | .minus => -1
  | .zero => 0
  | .plus => 1

def negate : Trit → Trit
  | .minus => .plus
  | .zero => .zero
  | .plus => .minus

@[simp] theorem negate_negate (d : Trit) : d.negate.negate = d := by
  cases d <;> rfl

@[simp] theorem toInt_negate (d : Trit) : d.negate.toInt = -d.toInt := by
  cases d <;> simp [toInt, negate]

theorem toInt_eq_zero_iff (d : Trit) : d.toInt = 0 ↔ d = .zero := by
  cases d <;> simp [toInt]

theorem negate_eq_zero_iff (d : Trit) : d.negate = .zero ↔ d = .zero := by
  cases d <;> simp [negate]

end Trit

/-- MSD-first evaluation: `(((d_{k-1})*3 + d_{k-2})*3 + ... ) + d_0`. -/
def evalMSD (w : List Trit) : ℤ :=
  w.foldl (fun acc d => 3 * acc + d.toInt) 0

def digitSum (w : List Trit) : ℤ :=
  (w.map Trit.toInt).sum

def appendLSD (w : List Trit) (d : Trit) : List Trit :=
  w ++ [d]

theorem evalMSD_nil : evalMSD [] = 0 := rfl

theorem evalMSD_appendLSD (w : List Trit) (d : Trit) :
    evalMSD (appendLSD w d) = 3 * evalMSD w + d.toInt := by
  simp [evalMSD, appendLSD, List.foldl_append]

theorem evalMSD_append_zero (w : List Trit) :
    evalMSD (w ++ [Trit.zero]) = 3 * evalMSD w := by
  simpa [appendLSD, Trit.toInt] using evalMSD_appendLSD w Trit.zero

theorem evalMSD_append_zeros (w : List Trit) :
    ∀ m, evalMSD (w ++ List.replicate m Trit.zero) = evalMSD w * 3 ^ m
  | 0 => by simp [evalMSD]
  | m + 1 => by
      rw [List.replicate_succ', ← List.append_assoc, evalMSD_append_zero,
          evalMSD_append_zeros w m, pow_succ]
      ring

theorem digitSum_appendLSD (w : List Trit) (d : Trit) :
    digitSum (appendLSD w d) = digitSum w + d.toInt := by
  simp [digitSum, appendLSD]

/-- Signed digit sum after appending a trailing `+`, the word form of
`s₃(3n+1) = s₃(n)+1`. -/
theorem digitSum_append_plus (w : List Trit) :
    digitSum (appendLSD w .plus) = digitSum w + 1 := by
  simp [digitSum_appendLSD, Trit.toInt]

theorem evalMSD_append_plus (w : List Trit) :
    evalMSD (appendLSD w .plus) = 3 * evalMSD w + 1 := by
  simp [evalMSD_appendLSD, Trit.toInt]

theorem length_appendLSD (w : List Trit) (d : Trit) :
    (appendLSD w d).length = w.length + 1 := by
  simp [appendLSD]

theorem length_append_plus (w : List Trit) :
    (appendLSD w .plus).length = w.length + 1 :=
  length_appendLSD w .plus

def dropLeadingZeros (w : List Trit) : List Trit :=
  w.dropWhile (fun d => d = Trit.zero)

def canonicalize (w : List Trit) : List Trit :=
  match dropLeadingZeros w with
  | [] => [Trit.zero]
  | t => t

def warpWord (w : List Trit) : List Trit :=
  canonicalize w.reverse

def mapNeg (w : List Trit) : List Trit :=
  w.map Trit.negate

private theorem foldl_mapNeg (acc : ℤ) :
    ∀ w : List Trit,
      (w.map Trit.negate).foldl (fun a d => 3 * a + d.toInt) acc =
        - w.foldl (fun a d => 3 * a + d.toInt) (-acc)
  | [] => by simp
  | d :: rest => by
      simp [Trit.toInt_negate]
      rw [foldl_mapNeg (3 * acc + -d.toInt) rest]
      congr 1
      ring

theorem evalMSD_mapNeg (w : List Trit) : evalMSD (mapNeg w) = - evalMSD w := by
  simpa [evalMSD, mapNeg] using foldl_mapNeg 0 w

theorem mapNeg_reverse (w : List Trit) :
    mapNeg w.reverse = (mapNeg w).reverse := by
  simp [mapNeg, List.map_reverse]

theorem dropLeadingZeros_mapNeg (w : List Trit) :
    dropLeadingZeros (mapNeg w) = mapNeg (dropLeadingZeros w) := by
  induction w with
  | nil => simp [dropLeadingZeros, mapNeg]
  | cons d rest ih =>
      cases d with
      | minus => simp [dropLeadingZeros, mapNeg, List.dropWhile, Trit.negate]
      | zero =>
          simp [dropLeadingZeros, mapNeg, List.dropWhile, Trit.negate]
          exact ih
      | plus => simp [dropLeadingZeros, mapNeg, List.dropWhile, Trit.negate]

theorem canonicalize_mapNeg (w : List Trit) :
    canonicalize (mapNeg w) = mapNeg (canonicalize w) := by
  unfold canonicalize
  rw [dropLeadingZeros_mapNeg]
  cases dropLeadingZeros w with
  | nil => simp [mapNeg, Trit.negate]
  | cons d rest => simp [mapNeg]

theorem warpWord_mapNeg (w : List Trit) :
    warpWord (mapNeg w) = mapNeg (warpWord w) := by
  calc
    warpWord (mapNeg w) = canonicalize (mapNeg w).reverse := rfl
    _ = canonicalize (mapNeg w.reverse) := by rw [← mapNeg_reverse]
    _ = mapNeg (canonicalize w.reverse) := canonicalize_mapNeg _
    _ = mapNeg (warpWord w) := rfl

/-- Word-level `W(-n) = -W(n)`. -/
theorem evalMSD_warpWord_mapNeg (w : List Trit) :
    evalMSD (warpWord (mapNeg w)) = - evalMSD (warpWord w) := by
  rw [warpWord_mapNeg, evalMSD_mapNeg]

theorem dropLeadingZeros_replicate_zero_append (m : ℕ) (w : List Trit) :
    dropLeadingZeros (List.replicate m Trit.zero ++ w) = dropLeadingZeros w := by
  induction m with
  | zero => simp [dropLeadingZeros]
  | succ m ih =>
      simp [List.replicate_succ, dropLeadingZeros]

theorem warpWord_append_zeros (w : List Trit) (m : ℕ) :
    warpWord (w ++ List.replicate m Trit.zero) = warpWord w := by
  unfold warpWord canonicalize
  simp [List.reverse_append, List.reverse_replicate, dropLeadingZeros_replicate_zero_append]

theorem dropLeadingZeros_of_head_ne_zero
    {d : Trit} {rest : List Trit} (hd : d ≠ Trit.zero) :
    dropLeadingZeros (d :: rest) = d :: rest := by
  simp [dropLeadingZeros, List.dropWhile, hd]

/-- If the LSD is nonzero, reverse has no leading zero, so `warpWord` is
involutive up to `canonicalize`. -/
theorem warpWord_involutive_of_last_ne_zero
    (w : List Trit) (hw : w ≠ [])
    (hlast : w.getLast hw ≠ Trit.zero) :
    warpWord (warpWord w) = canonicalize w := by
  have hne : w.reverse ≠ [] := List.reverse_ne_nil_iff.mpr hw
  obtain ⟨d, rest, hr⟩ := List.exists_cons_of_ne_nil hne
  have hd : d = w.getLast hw := by
    apply Option.some.inj
    calc
      some d = w.reverse.head? := by simp [hr]
      _ = w.getLast? := List.head?_reverse
      _ = some (w.getLast hw) := List.getLast?_eq_some_getLast hw
  have hdrop : dropLeadingZeros w.reverse = w.reverse := by
    rw [hr, hd]
    exact dropLeadingZeros_of_head_ne_zero hlast
  have hcan : canonicalize w.reverse = w.reverse := by
    unfold canonicalize
    rw [hdrop]
    cases hrev : w.reverse with
    | nil => exact (hne hrev).elim
    | cons _ _ => rfl
  unfold warpWord
  rw [hcan, List.reverse_reverse]

end Representation.Words

import Problems.Juggler.ReturnWordLoss
import Problems.Juggler.ReturnCells

namespace Problems.Juggler.ReturnWordBounds

open ReturnWordLoss


def wordA : List Branch := [.odd, .odd, .even]
def wordB : List Branch := [.odd, .even]
def wordC : List Branch := wordA ++ wordA ++ wordB
def wordD : List Branch := wordA ++ wordC ++ wordC
def wordW : List Branch := wordD ++ wordD ++ wordD ++ wordC
def wordV : List Branch := wordD ++ wordD ++ wordD ++ wordD ++ wordC

theorem exponent_A : exponent wordA = (9 : ℝ) / 8 := by
  norm_num [wordA, exponent, alpha, branchExp]

theorem exponent_B : exponent wordB = (3 : ℝ) / 4 := by
  norm_num [wordB, exponent, alpha, branchExp]

theorem exponent_C : exponent wordC = (243 : ℝ) / 256 := by
  norm_num [wordC, exponent_append, exponent_A, exponent_B]

theorem exponent_D : exponent wordD = (531441 : ℝ) / 524288 := by
  norm_num [wordD, exponent_append, exponent_A, exponent_C]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem exponent_W : exponent wordW = (3 : ℝ) ^ 41 / 2 ^ 65 := by
  norm_num [wordW, exponent_append, exponent_D, exponent_C]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem exponent_V : exponent wordV = (3 : ℝ) ^ 53 / 2 ^ 84 := by
  norm_num [wordV, exponent_append, exponent_D, exponent_C]

theorem eval_A (x : ℕ) : eval wordA x = ReturnCells.ooe x := by
  simp [wordA, eval, step, branchExp, ReturnCells.ooe, ReturnCells.oe]
theorem eval_B (x : ℕ) : eval wordB x = ReturnCells.oe x := by
  simp [wordB, eval, step, branchExp, ReturnCells.oe]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem c_tails : ConcaveTails wordC := by
  norm_num [wordC, wordA, wordB, ConcaveTails, exponent, alpha, branchExp]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem d_tails : ConcaveTails wordD := by
  norm_num [wordD, wordC, wordA, wordB, ConcaveTails, exponent, alpha, branchExp]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem ac_tails : ConcaveTails (wordA ++ wordC) := by
  norm_num [wordC, wordA, wordB, ConcaveTails, exponent, alpha, branchExp]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem w_tails : ConcaveTails wordW := by
  norm_num [wordW, wordD, wordC, wordA, wordB, ConcaveTails, exponent, alpha, branchExp]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem v_tails : ConcaveTails wordV := by
  norm_num [wordV, wordD, wordC, wordA, wordB, ConcaveTails, exponent, alpha, branchExp]

theorem ac_grows {x : ℕ} (hx : 2 ^ 24 ≤ x) :
    x < eval (wordA ++ wordC) x := by
  apply grows_of_unit_loss (k := 24) (by decide) ac_tails (by exact_mod_cast hx)
  · norm_num [exponent_append, exponent_A, exponent_C]
  · norm_num [exponent_append, exponent_A, exponent_C]
  · have hx' : (2 : ℝ) ^ 24 ≤ x := by exact_mod_cast hx
    norm_num [wordA, wordC, wordB] at *
    linarith

theorem d_grows {x : ℕ} (hx : 2 ^ 24 ≤ x) : x < eval wordD x := by
  apply grows_of_unit_loss (k := 24) (by decide) d_tails (by exact_mod_cast hx)
  · rw [exponent_D]; norm_num
  · rw [exponent_D]; norm_num
  · have hx' : (2 : ℝ) ^ 24 ≤ x := by exact_mod_cast hx
    norm_num [wordD, wordA, wordC, wordB] at *
    linarith

theorem v_grows {x : ℕ} (hx : 2 ^ 128 ≤ x) : x < eval wordV x := by
  apply grows_of_unit_loss (k := 128) (by decide) v_tails (by exact_mod_cast hx)
  · rw [exponent_V]; norm_num
  · rw [exponent_V]; norm_num
  · have hx' : (2 : ℝ) ^ 128 ≤ x := by exact_mod_cast hx
    norm_num [wordV, wordW, wordD, wordA, wordC, wordB] at *
    linarith

theorem odd_step_ge (x : ℕ) : x ≤ step .odd x := by
  by_cases hx : x = 0
  · simp [hx, step]
  · apply Nat.le_sqrt.mpr
    simpa [step, branchExp, pow_two] using
      Nat.pow_le_pow_right (Nat.pos_of_ne_zero hx) (by decide : 2 ≤ 3)

theorem a_ge {x : ℕ} (hx : 3 ≤ x) : x ≤ eval wordA x := by
  have hh := CubicReturn.sq_le_OO hx
  apply Nat.le_sqrt.mpr
  simpa [wordA, eval, step, branchExp, CubicReturn.O, pow_two] using hh

theorem a_innerAbove (x : ℕ) : InnerAbove (x : ℝ) x wordA := by
  have h₁ := odd_step_ge x
  have h₂ := h₁.trans (odd_step_ge (step .odd x))
  simp only [wordA, InnerAbove, ne_eq, reduceCtorEq, not_false_eq_true,
    not_true_eq_false, false_implies, forall_const, and_true]
  exact ⟨by exact_mod_cast h₁, by exact_mod_cast h₂⟩

theorem b_innerAbove (x : ℕ) : InnerAbove (x : ℝ) x wordB := by
  simp only [wordB, InnerAbove, ne_eq, reduceCtorEq, not_false_eq_true,
    not_true_eq_false, false_implies, forall_const, and_true]
  exact_mod_cast odd_step_ge x

theorem c_innerAbove {x : ℕ} (hx : 3 ≤ x) : InnerAbove (x : ℝ) x wordC := by
  have h := innerAbove_repeat_append (m := 3) wordA wordB
    (fun y _ => a_innerAbove y) (fun _ hy => a_ge hy)
    (fun y _ => b_innerAbove y) 2 x hx
  simpa [wordC, List.replicate_succ, List.append_assoc] using h

theorem ac_innerAbove {x : ℕ} (hx : 3 ≤ x) :
    InnerAbove (x : ℝ) x (wordA ++ wordC) := by
  have h₁ := a_ge hx
  have h₁' : (x : ℝ) ≤ eval wordA x := by exact_mod_cast h₁
  exact innerAbove_append wordA wordC x (a_innerAbove x)
    (innerAbove_mono h₁' (c_innerAbove (hx.trans h₁))) (fun _ => h₁')

theorem d_innerAbove {x : ℕ} (hx : 2 ^ 24 ≤ x) :
    InnerAbove (x : ℝ) x wordD := by
  have hx3 : 3 ≤ x := by omega
  have hg := ac_grows hx
  have hg' : (x : ℝ) ≤ eval (wordA ++ wordC) x := by exact_mod_cast hg.le
  have hh := innerAbove_append (wordA ++ wordC) wordC x (ac_innerAbove hx3)
    (innerAbove_mono hg' (c_innerAbove (hx3.trans hg.le))) (fun _ => hg')
  simpa only [wordD, List.append_assoc] using hh

theorem w_innerAbove {x : ℕ} (hx : 2 ^ 24 ≤ x) :
    InnerAbove (x : ℝ) x wordW := by
  have h := innerAbove_repeat_append (m := 2 ^ 24) wordD wordC
    (fun _ hy => d_innerAbove hy) (fun _ hy => (d_grows hy).le)
    (fun _ hy => c_innerAbove (by omega)) 3 x hx
  simpa [wordW, List.replicate_succ, List.append_assoc] using h

end Problems.Juggler.ReturnWordBounds

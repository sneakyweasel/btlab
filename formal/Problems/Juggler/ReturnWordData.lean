import Problems.Juggler.ReturnWordLoss
import Problems.Juggler.CubicReturn

namespace Problems.Juggler.ReturnWordBounds

open ReturnWordLoss

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

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

theorem exponent_W : exponent wordW = (3 : ℝ) ^ 41 / 2 ^ 65 := by
  norm_num [wordW, exponent_append, exponent_D, exponent_C]

theorem exponent_V : exponent wordV = (3 : ℝ) ^ 53 / 2 ^ 84 := by
  norm_num [wordV, exponent_append, exponent_D, exponent_C]

theorem eval_A (x : ℕ) : eval wordA x = ReturnCells.ooe x := by
  simp [wordA, eval, step, branchExp, ReturnCells.ooe, ReturnCells.oe]
theorem eval_B (x : ℕ) : eval wordB x = ReturnCells.oe x := by
  simp [wordB, eval, step, branchExp, ReturnCells.oe]

theorem c_tails : ConcaveTails wordC := by
  norm_num [wordC, wordA, wordB, ConcaveTails, exponent, alpha, branchExp]

theorem d_tails : ConcaveTails wordD := by
  norm_num [wordD, wordC, wordA, wordB, ConcaveTails, exponent, alpha, branchExp]

theorem ac_tails : ConcaveTails (wordA ++ wordC) := by
  norm_num [wordC, wordA, wordB, ConcaveTails, exponent, alpha, branchExp]

theorem w_tails : ConcaveTails wordW := by
  norm_num [wordW, wordD, wordC, wordA, wordB, ConcaveTails, exponent, alpha, branchExp]

theorem v_tails : ConcaveTails wordV := by
  norm_num [wordV, wordD, wordC, wordA, wordB, ConcaveTails, exponent, alpha, branchExp]

theorem innerAbove_mono {m n : ℝ} (hmn : m ≤ n) {x : ℕ} {w : List Branch}
    (h : InnerAbove n x w) : InnerAbove m x w := by
  induction w generalizing x with
  | nil => trivial
  | cons b w ih => exact ⟨fun hn => hmn.trans (h.1 hn), ih h.2⟩

theorem innerAbove_one (w : List Branch) {x : ℕ} (hx : 0 < x) :
    InnerAbove 1 x w := by
  induction w generalizing x with
  | nil => trivial
  | cons b w ih =>
    have hy := step_pos b hx
    exact ⟨fun _ => by exact_mod_cast hy, ih hy⟩

theorem budget_one_le_length (w : List Branch) (ht : ConcaveTails w) :
    budget 1 w ≤ w.length := by
  induction w with
  | nil => simp [budget]
  | cons b w ih =>
    have hh := ih ht.2
    simp only [budget, Real.one_rpow, mul_one, List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith [ht.1]

theorem unit_loss_lt_length {w : List Branch} (hw : w ≠ [])
    (ht : ConcaveTails w) {x : ℕ} (hx : 0 < x) :
    (x : ℝ) ^ exponent w - eval w x < w.length :=
  (loss_lt_budget (by norm_num) hw hx ht (innerAbove_one w hx)).trans_le
    (budget_one_le_length w ht)

theorem grows_of_unit_loss {w : List Branch} (hw : w ≠ []) (ht : ConcaveTails w)
    {x k : ℕ} (hx : (2 : ℝ) ^ k ≤ x) (hp : 1 < exponent w)
    (he : (1 : ℝ) ≤ k * (exponent w - 1) * 4)
    (hl : (8 : ℝ) * w.length < x) : x < eval w x := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (by positivity) hx
  have hn : 0 < x := by exact_mod_cast hx0
  have hpow := dyadic_rpow_lower (q := exponent w - 1) (c := (9 : ℝ) / 8)
    (a := 1) (b := 4) hx (by linarith) (by simpa using he) (by norm_num)
  have hid : (x : ℝ) ^ exponent w = (x : ℝ) ^ (exponent w - 1) * x := by
    nth_rw 1 [show exponent w = (exponent w - 1) + 1 by ring]
    rw [Real.rpow_add_one hx0.ne']
  have hh := mul_lt_mul_of_pos_right hpow hx0
  have hb := unit_loss_lt_length hw ht hn
  rw [← hid] at hh
  have hlt : (x : ℝ) < eval w x := by linarith
  exact_mod_cast hlt

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
  have h₁ := a_ge hx
  have h₂ := a_ge (hx.trans h₁)
  have h₁' : (x : ℝ) ≤ eval wordA x := by exact_mod_cast h₁
  have h₂' : (x : ℝ) ≤ eval wordA (eval wordA x) := by exact_mod_cast h₁.trans h₂
  unfold wordC
  apply innerAbove_append wordA (wordA ++ wordB) x (a_innerAbove x)
  · apply innerAbove_append wordA wordB (eval wordA x)
    · exact innerAbove_mono h₁' (a_innerAbove _)
    · exact innerAbove_mono h₂' (b_innerAbove _)
    · intro _; exact h₂'
  · intro _; exact h₁'

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
  have h₁ := d_grows hx
  have h₂ := d_grows (hx.trans h₁.le)
  have h₃ := d_grows ((hx.trans h₁.le).trans h₂.le)
  have h₁' : (x : ℝ) ≤ eval wordD x := by exact_mod_cast h₁.le
  have h₂' : (x : ℝ) ≤ eval wordD (eval wordD x) := by exact_mod_cast h₁.le.trans h₂.le
  have h₃' : (x : ℝ) ≤ eval wordD (eval wordD (eval wordD x)) := by
    exact_mod_cast (h₁.le.trans h₂.le).trans h₃.le
  unfold wordW
  apply innerAbove_append wordD (wordD ++ wordD ++ wordC) x (d_innerAbove hx)
  · apply innerAbove_append wordD (wordD ++ wordC) (eval wordD x)
    · exact innerAbove_mono h₁' (d_innerAbove (hx.trans h₁.le))
    · apply innerAbove_append wordD wordC (eval wordD (eval wordD x))
      · exact innerAbove_mono h₂' (d_innerAbove ((hx.trans h₁.le).trans h₂.le))
      · exact innerAbove_mono h₃' (c_innerAbove (by omega))
      · intro _; exact h₃'
    · intro _; exact h₂'
  · intro _; exact h₁'

end Problems.Juggler.ReturnWordBounds

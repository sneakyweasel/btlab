/-
# Paper A Theorem 3.31: the even-count floor, its arithmetic core

Appendix A listed this row as "enumeration in `run_suffix_law.closure`; not yet Lean".  That
backtick is a *Python* probe (`src/research/juggler_sequence/branch_index.py`), not a Lean
name, so until now the row had no Lean at all --- the coverage count above it said otherwise
only because the classifier never checked its backticks against the index.

Theorem 3.31 has two halves and they are not alike.

* The **per-run cap** and the **period floor** are arithmetic.  Both are here, kernel-checked.
* The **enumeration** --- 16, 186, 2037, 25353 and 325452 canonical forms for `e = 3,…,7`, each
  closed by Theorem 3.29 --- is a certified computation, and stays one.

Lean:

* `runCapConst` --- the constant `log 2 / log(3/2)` of the displayed cap
  `aᵢ ≤ ⌊(e−i)·log 2/log(3/2)⌋`.
* `runCapConst_gt`, `runCapConst_lt` --- `5/3 < runCapConst < 12/7`.  Both are integer power
  comparisons in disguise: the lower bound is `3^5 < 2^8` (243 < 256) and the upper is
  `2^19 < 3^12` (524288 < 531441).  The upper one is tight for what follows --- it is exactly
  the inequality that pins the `e = 7` cap at 11 rather than 12.
* `runCap`, `runCap_eq_floor` --- Paper A's table *is* that floor.  All seven values follow
  from the two bounds alone; no further logarithm is needed.
* `runCap_tuple_three` … `runCap_tuple_seven` --- the tuples the proof quotes, `(5,3,1)`
  through `(11,10,8,6,5,3,1)`, read off the same table.
* `runCap_antitone` --- the caps fall as the suffix shortens, which is why the proof may take
  them run by run.
* `period_ge_22_of_even_count` --- the second half.  Eight even letters and formal expansion
  `2^L < 3^o` force `L ≥ 22`.
* `expansion_holds_at_22`, `expansion_fails_below_22` --- and 22 is the first such length, so
  the bound is sharp for this argument.

Not attempted: the enumeration.  It is a search over 353044 canonical forms, and it belongs
with Paper A's other certified computations, not here.
-/

import Problems.Juggler.RunTypePacking
import Mathlib.Tactic

namespace Problems.Juggler

/-- The per-run constant of Theorem 3.31: a run of `m` odd letters costs `(3/2)^m`, and a
suffix with `k` even letters can pay `2^k`, so `m ≤ k · log 2/log(3/2)`. -/
noncomputable def runCapConst : ℝ := Real.log 2 / Real.log (3 / 2)

theorem log_three_halves_pos : (0:ℝ) < Real.log (3 / 2) :=
  Real.log_pos (by norm_num)

theorem log_three_halves_eq : Real.log ((3:ℝ) / 2) = Real.log 3 - Real.log 2 :=
  Real.log_div (by norm_num) (by norm_num)

/-- `5/3 < runCapConst`, which is `3^5 < 2^8` — that is, `243 < 256`. -/
theorem runCapConst_gt : (5:ℝ) / 3 < runCapConst := by
  have h : Real.log ((3:ℝ) ^ 5) < Real.log ((2:ℝ) ^ 8) :=
    Real.log_lt_log (by positivity) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  push_cast at h
  rw [runCapConst, lt_div_iff₀ log_three_halves_pos, log_three_halves_eq]
  linarith

/-- `runCapConst < 12/7`, which is `2^19 < 3^12` — that is, `524288 < 531441`.  This is the
inequality that pins the `e = 7` cap at 11: `7 · runCapConst < 12`. -/
theorem runCapConst_lt : runCapConst < 12 / 7 := by
  have h : Real.log ((2:ℝ) ^ 19) < Real.log ((3:ℝ) ^ 12) :=
    Real.log_lt_log (by positivity) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  push_cast at h
  rw [runCapConst, div_lt_iff₀ log_three_halves_pos, log_three_halves_eq]
  linarith

/-- Paper A's table of run bounds: the cap on a run whose suffix carries `k` even letters. -/
def runCap : ℕ → ℤ
  | 1 => 1
  | 2 => 3
  | 3 => 5
  | 4 => 6
  | 5 => 8
  | 6 => 10
  | 7 => 11
  | _ => 0

/-- **The table is the floor.**  For every suffix length the paper uses,
`runCap k = ⌊k · log 2/log(3/2)⌋`. -/
theorem runCap_eq_floor {k : ℕ} (h1 : 1 ≤ k) (h7 : k ≤ 7) :
    ⌊(k : ℝ) * runCapConst⌋ = runCap k := by
  have hg := runCapConst_gt
  have hl := runCapConst_lt
  interval_cases k <;>
    · rw [runCap, Int.floor_eq_iff]
      constructor <;> push_cast <;> linarith

/-- The caps fall as the suffix shortens, so the proof may apply them run by run. -/
theorem runCap_antitone {j k : ℕ} (h1 : 1 ≤ j) (hjk : j ≤ k) (h7 : k ≤ 7) :
    runCap j ≤ runCap k := by
  have hj7 : j ≤ 7 := le_trans hjk h7
  interval_cases j <;> interval_cases k <;> decide

theorem runCap_tuple_three : [runCap 3, runCap 2, runCap 1] = [5, 3, 1] := by decide

theorem runCap_tuple_four : [runCap 4, runCap 3, runCap 2, runCap 1] = [6, 5, 3, 1] := by decide

theorem runCap_tuple_five :
    [runCap 5, runCap 4, runCap 3, runCap 2, runCap 1] = [8, 6, 5, 3, 1] := by decide

theorem runCap_tuple_six :
    [runCap 6, runCap 5, runCap 4, runCap 3, runCap 2, runCap 1] = [10, 8, 6, 5, 3, 1] := by
  decide

theorem runCap_tuple_seven :
    [runCap 7, runCap 6, runCap 5, runCap 4, runCap 3, runCap 2, runCap 1] =
      [11, 10, 8, 6, 5, 3, 1] := by decide

/-- **Formal expansion first holds at length 22.**  `2^22 < 3^14`. -/
theorem expansion_holds_at_22 : (2:ℕ) ^ 22 < 3 ^ (22 - 8) := by norm_num

/-- And at no shorter length: `2^L < 3^(L−8)` fails for every `L < 22`. -/
theorem expansion_fails_below_22 {L : ℕ} (h : L < 22) : ¬ (2:ℕ) ^ L < 3 ^ (L - 8) := by
  interval_cases L <;> norm_num

/-- **Theorem 3.31's second half.**  A cycle with at least eight even letters and formal
expansion `2^L < 3^o` has period at least twenty-two. -/
theorem period_ge_22_of_even_count {o e L : ℕ} (he : 8 ≤ e) (hL : L = o + e)
    (hexp : (2:ℕ) ^ L < 3 ^ o) : 22 ≤ L := by
  rcases Nat.lt_or_ge L 22 with hcon | h
  · have h1 : (3:ℕ) ^ o ≤ 3 ^ (L - 8) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact absurd (lt_of_lt_of_le hexp h1) (expansion_fails_below_22 hcon)
  · exact h

end Problems.Juggler

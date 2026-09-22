/-
# Paper A Theorem 4.7: the run-type packing, its arithmetic core

Appendix A listed this row as "run-type packing; human proof, not Lean" — with Lemma 4.4b, one
of the two rows in that table with no Lean at all.  What is formalized here is the theorem's
*arithmetic*; what stays human is its *dynamics*, and the line between them is worth stating
because it is not the usual one.

Lean:

* `packing_counts` — the packing is consistent.  `o − e` copies of `OOE` together with `2e − o`
  circuits of `OE` use exactly `o` odd letters and `e` even letters.  This is the counting the
  theorem's "largest number of `n`-scale valleys compatible with the even cap" rests on.
* `odd_excess_lt_even` — the theorem's `o − e < e` is exactly `3o < 2L`.
* `three_mul_lt_two_mul_of_omin` — and that holds at the least admissible odd count.
  Minimality gives `3^(o−1) ≤ 2^L`; the certified sandwich bounds `log 2/log 3` above by
  `10590737/16785921`, which turns it into `o ≤ 1 + L·(log 2/log 3)` and hence `3o < 2L` once
  `L ≥ 28`.  The threshold is sharp for this argument: the certified bound gives `L > 27.98`.
* `log_two_div_log_three_lt` — the bound just used, from `lower_lt_walkTheta` and
  `walkTheta = 1 − log 2/log 3`.

Human, and not attempted here: the displayed six-term bound on `Σ 1/(xᵢ log xᵢ)`.  That is a
statement about where an actual cycle's iterates sit — one cheap valley at `n`, the rest at
`n+2`, the expensive ones at `v`, one internal odd at `t`, the rest at `J(n+2)`, every even at
`n²` — and it needs Theorem 3.2 and the orbit, not arithmetic.  Formalizing the core moves this
row from "no Lean" to "Lean with a stated gap"; it does not close it.
-/

import Problems.Juggler.OstrowskiSandwich
import Mathlib.Tactic

namespace Problems.Juggler

/-- `log 2 / log 3` is below the certified sandwich endpoint, since
`walkTheta = log(3/2)/log 3 = 1 − log 2/log 3`. -/
theorem log_two_div_log_three_lt :
    Real.log 2 / Real.log 3 < (10590737 : ℝ) / 16785921 := by
  have h3 : (0:ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hw : walkTheta = 1 - Real.log 2 / Real.log 3 := by
    unfold walkTheta
    rw [show (3:ℝ)/2 = 3/2 by norm_num, Real.log_div (by norm_num) (by norm_num)]
    field_simp
  have h := lower_lt_walkTheta
  rw [hw] at h
  linarith

/-- **The packing is consistent.**  `o − e` copies of `OOE` and `2e − o` circuits of `OE`
use exactly `o` odd letters and `e` even letters. -/
theorem packing_counts (o e : ℕ) (h1 : e ≤ o) (h2 : o ≤ 2 * e) :
    2 * (o - e) + (2 * e - o) = o ∧ (o - e) + (2 * e - o) = e := by
  omega

/-- **`o − e < e` is `3o < 2L`.** -/
theorem odd_excess_lt_even {L o : ℕ} (h : o ≤ L) :
    o - (L - o) < L - o ↔ 3 * o < 2 * L := by
  omega

/-- **At the least admissible odd count, `3o < 2L`.**  Minimality gives `3^(o−1) ≤ 2^L`, and
the certified bound on `log 2/log 3` turns that into `o ≤ 1 + L·(log 2/log 3)`, whence
`3o < 2L` as soon as `L ≥ 28`. -/
theorem three_mul_lt_two_mul_of_omin {L o : ℕ} (hL : 28 ≤ L) (ho : 1 ≤ o)
    (hmin : (3:ℝ) ^ (o - 1) ≤ 2 ^ L) :
    3 * o < 2 * L := by
  have h3 : (0:ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have h2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : ((o : ℝ) - 1) * Real.log 3 ≤ (L : ℝ) * Real.log 2 := by
    have h := Real.log_le_log (by positivity) hmin
    rw [Real.log_pow, Real.log_pow, Nat.cast_sub ho] at h
    push_cast at h
    linarith
  have hb := log_two_div_log_three_lt
  have hoR : (o : ℝ) ≤ 1 + (L : ℝ) * ((10590737 : ℝ) / 16785921) := by
    have hstep : (o : ℝ) - 1 ≤ (L : ℝ) * (Real.log 2 / Real.log 3) := by
      rw [← mul_div_assoc, le_div_iff₀ h3]
      linarith
    nlinarith [hstep, hb, Nat.cast_nonneg (α := ℝ) L]
  have hLR : (28:ℝ) ≤ (L:ℝ) := by exact_mod_cast hL
  have : (3:ℝ) * o < 2 * L := by nlinarith [hoR, hLR]
  exact_mod_cast this

end Problems.Juggler

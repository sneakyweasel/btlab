import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Problems.Juggler.GapTransfer

namespace Problems.Juggler

/-!
# A power-budget instance of the gap transfer, and the closure threshold

`Problems.Juggler.GapTransfer` proves the floor-free transfer
`n log n * min (L, 1) <= 2 L` for the linear form `o log 3 - L log 2`, and
instantiates it at Rhin's printed measure `e^{-6.1256} L^{-13.3}`
(`cycleMin_length_of_rhin`, Paper A Corollary 4.11). Rhin is not the
sharpest recorded input. Wu-Wang (2014) give, for every positive `eps` and
all large `H = max (|b|, |c|)`,

  `|a + b log 2 + c log 3| >= H^{-4.1163051-eps}` ,

and the cycle substitution `(a, b, c) = (0, -L, o)` of Corollary 4.11 has
`H = max (L, o) = L`. That is the same substitution, at a smaller exponent.

This file states the transfer once, parametrically in the Diophantine
exponent `p`, and reads off three consequences.

* `cycleMin_length_of_gap_power` — a budget `C * L^{-p}` gives
  `n log n <= (2/C) * L^{p+1}`. At `p = 13.3` this is Corollary 4.11; at
  `p = 4.1163051` it is the Wu-Wang instance, exponent `5.1163051`.
* `cycleMin_period_ge` — the same inequality read as a *period lower
  bound growing with the minimum*, `L >= (C n log n / 2)^{1/(p+1)}`.
  Floor-free: no descent floor enters.
* `no_cycleMin_of_gap_and_minimum` — the closure threshold. A matching
  lower bound `n log n > (2/C) L^{p+1}` on cycle minima leaves no
  nontrivial cycle. At `p = 4.1163051` the required lower bound is
  `n >> L^{5.1163051}`; since `p >= 1` for every irrational, no instance
  of this scheme ever asks for less than `n >> L^{2}`.

Every transcendence input is a hypothesis, exactly as in `GapTransfer`;
the transfer and the threshold are proved. Wu-Wang's constant is
`C_eps`-implied, so the sharpened instance is asymptotic where Rhin's is
effective — the two are companions, not replacements. This is a
reduction, not a kill: at every certified floor the bound is far weaker
than the finance table. Not a halt theorem.
-/

/-- The Diophantine budget `C * L^{-p}` fed to `cycleMin_length_of_gap`. -/
noncomputable def gapBudget (C p : ℝ) (L : ℕ) : ℝ :=
  C * (L : ℝ) ^ (-p)

theorem gapBudget_pos {C p : ℝ} {L : ℕ} (hC : 0 < C) (hL : 0 < L) :
    0 < gapBudget C p L := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  unfold gapBudget
  positivity

/-- For `L >= 1`, `C <= 1` and `p >= 0` the budget is at most one, which is
what `cycleMin_length_of_gap` needs. -/
theorem gapBudget_le_one {C p : ℝ} {L : ℕ}
    (hC1 : C ≤ 1) (hp : 0 ≤ p) (hL : 0 < L) :
    gapBudget C p L ≤ 1 := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (Nat.succ_le_of_lt hL)
  have hpow : (L : ℝ) ^ (-p) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hL1 (neg_nonpos.mpr hp)
  unfold gapBudget
  exact mul_le_one₀ hC1 (Real.rpow_nonneg (by exact_mod_cast hL.le) _) hpow

/-- **Power-budget gap transfer.** A Diophantine lower bound
`C * L^{-p} <= o log 3 - L log 2` on a cycle gives the floor-free length
bound `n log n <= (2/C) * L^{p+1}`.

Instances: `p = 13.3`, `C = e^{-6.1256}` is Paper A Corollary 4.11
(Rhin, effective). `p = 4.1163051` is the Wu-Wang instance, exponent
`5.1163051`, with `C = C_eps` implied. -/
theorem cycleMin_length_of_gap_power {n : ℕ} {w : List Branch} {C p : ℝ}
    (hn : 2 ≤ n) (h : CycleMin n w) (hL : 0 < w.length)
    (hC0 : 0 < C) (hC1 : C ≤ 1) (hp : 0 ≤ p)
    (hgap : C * (w.length : ℝ) ^ (-p) ≤
              (oddCount w : ℝ) * Real.log 3 - (w.length : ℝ) * Real.log 2) :
    (n : ℝ) * Real.log n ≤ 2 / C * (w.length : ℝ) ^ (p + 1) := by
  have hLpos : (0 : ℝ) < (w.length : ℝ) := by exact_mod_cast hL
  have hε1 : gapBudget C p w.length ≤ 1 := gapBudget_le_one hC1 hp hL
  have hεΛ : gapBudget C p w.length ≤
      (oddCount w : ℝ) * Real.log 3 - (w.length : ℝ) * Real.log 2 := hgap
  have hgapT := cycleMin_length_of_gap hn h hε1 hεΛ
  have hεpos : 0 < gapBudget C p w.length := gapBudget_pos hC0 hL
  have hP : (n : ℝ) * Real.log n ≤ 2 * (w.length : ℝ) / gapBudget C p w.length :=
    (le_div_iff₀ hεpos).mpr (by linarith [hgapT])
  have hrewrite : 2 * (w.length : ℝ) / gapBudget C p w.length
      = 2 / C * (w.length : ℝ) ^ (p + 1) := by
    have hpow : (w.length : ℝ) ^ (p + 1) = (w.length : ℝ) ^ p * (w.length : ℝ) := by
      rw [Real.rpow_add hLpos, Real.rpow_one]
    have hneg : (w.length : ℝ) ^ (-p) = ((w.length : ℝ) ^ p)⁻¹ :=
      Real.rpow_neg hLpos.le p
    have hppos : (0 : ℝ) < (w.length : ℝ) ^ p := Real.rpow_pos_of_pos hLpos p
    unfold gapBudget
    rw [hneg, hpow]
    field_simp
  exact hP.trans_eq hrewrite

/-- **The same inequality read as a period lower bound.** Under the same
Diophantine budget, a nontrivial cycle of minimum `n` has period at least
`(C * n log n / 2)^{1/(p+1)}`. No descent floor enters: the bound grows
with the minimum, which is the one direction the finite tables cannot
supply.

At `p = 13.3` (Rhin) the exponent in `n` is `1/14.3 = 0.0699...`; at
`p = 4.1163051` (Wu-Wang) it is `1/5.1163051 = 0.1954...`. -/
theorem cycleMin_period_ge {n : ℕ} {w : List Branch} {C p : ℝ}
    (hn : 2 ≤ n) (h : CycleMin n w) (hL : 0 < w.length)
    (hC0 : 0 < C) (hC1 : C ≤ 1) (hp : 0 ≤ p)
    (hgap : C * (w.length : ℝ) ^ (-p) ≤
              (oddCount w : ℝ) * Real.log 3 - (w.length : ℝ) * Real.log 2) :
    (C / 2 * ((n : ℝ) * Real.log n)) ^ (1 / (p + 1)) ≤ (w.length : ℝ) := by
  have hLpos : (0 : ℝ) < (w.length : ℝ) := by exact_mod_cast hL
  have hp1 : (0 : ℝ) < p + 1 := by linarith
  have hmain := cycleMin_length_of_gap_power hn h hL hC0 hC1 hp hgap
  have hC2 : (0 : ℝ) < C / 2 := by linarith
  have hstep : C / 2 * ((n : ℝ) * Real.log n) ≤ (w.length : ℝ) ^ (p + 1) := by
    have hmul := mul_le_mul_of_nonneg_left hmain hC2.le
    calc C / 2 * ((n : ℝ) * Real.log n)
        ≤ C / 2 * (2 / C * (w.length : ℝ) ^ (p + 1)) := hmul
      _ = (w.length : ℝ) ^ (p + 1) := by field_simp
  have hbase : 0 ≤ C / 2 * ((n : ℝ) * Real.log n) := by
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hlog : 0 ≤ (n : ℝ) * Real.log n :=
      mul_nonneg (by positivity) (Real.log_nonneg h1)
    positivity
  have hmono :
      (C / 2 * ((n : ℝ) * Real.log n)) ^ (1 / (p + 1))
        ≤ ((w.length : ℝ) ^ (p + 1)) ^ (1 / (p + 1)) :=
    Real.rpow_le_rpow hbase hstep (by positivity)
  have hcollapse : ((w.length : ℝ) ^ (p + 1)) ^ (1 / (p + 1)) = (w.length : ℝ) := by
    rw [← Real.rpow_mul hLpos.le, mul_one_div_cancel hp1.ne', Real.rpow_one]
  exact hmono.trans_eq hcollapse

/-- **The closure threshold.** If the Diophantine budget holds on every
nontrivial cycle and cycle minima obey the matching lower bound
`n log n > (2/C) L^{p+1}`, then every cycle word based at a minimum
`n >= 2` is empty: there is no nontrivial cycle.

This is the numerical content of the standing reopen condition "a lower
bound on the cycle minimum in terms of the period"
(`docs/problems/juggler_cycle_method_ceilings.md`). Neither hypothesis is
proved here. The Wu-Wang instance `p = 4.1163051` sets the unconditional
target at `n >> L^{5.1163051}`; since `p >= 1` for every irrational, no
instance of this scheme can ask for less than `n >> L^{2}`. -/
theorem no_cycleMin_of_gap_and_minimum {C p : ℝ}
    (hC0 : 0 < C) (hC1 : C ≤ 1) (hp : 0 ≤ p)
    (hgap : ∀ (m : ℕ) (v : List Branch), 2 ≤ m → CycleMin m v → 0 < v.length →
      C * (v.length : ℝ) ^ (-p) ≤
        (oddCount v : ℝ) * Real.log 3 - (v.length : ℝ) * Real.log 2)
    (hmin : ∀ (m : ℕ) (v : List Branch), 2 ≤ m → CycleMin m v → 0 < v.length →
      2 / C * (v.length : ℝ) ^ (p + 1) < (m : ℝ) * Real.log m)
    {n : ℕ} {w : List Branch} (hn : 2 ≤ n) (h : CycleMin n w) :
    w.length = 0 := by
  by_contra hne
  have hL : 0 < w.length := Nat.pos_of_ne_zero hne
  exact absurd
    (cycleMin_length_of_gap_power hn h hL hC0 hC1 hp (hgap n w hn h hL))
    (not_le.mpr (hmin n w hn h hL))

/-- **Wu-Wang instance of the transfer.** `C * L^{-4.1163051} <= Lambda`
gives `n log n <= (2/C) L^{5.1163051}`, against Corollary 4.11's
`L^{14.3}`. -/
theorem cycleMin_length_of_wuWang {n : ℕ} {w : List Branch} {C : ℝ}
    (hn : 2 ≤ n) (h : CycleMin n w) (hL : 0 < w.length)
    (hC0 : 0 < C) (hC1 : C ≤ 1)
    (hWW : C * (w.length : ℝ) ^ (-(4.1163051 : ℝ)) ≤
             (oddCount w : ℝ) * Real.log 3 - (w.length : ℝ) * Real.log 2) :
    (n : ℝ) * Real.log n ≤ 2 / C * (w.length : ℝ) ^ (5.1163051 : ℝ) := by
  have h51 : (4.1163051 : ℝ) + 1 = 5.1163051 := by norm_num
  have hmain := cycleMin_length_of_gap_power hn h hL hC0 hC1 (by norm_num) hWW
  rwa [h51] at hmain

/-- **Wu-Wang period lower bound.** Every nontrivial cycle has
`L >= (C n log n / 2)^{1/5.1163051}`, floor-free. -/
theorem cycleMin_period_ge_wuWang {n : ℕ} {w : List Branch} {C : ℝ}
    (hn : 2 ≤ n) (h : CycleMin n w) (hL : 0 < w.length)
    (hC0 : 0 < C) (hC1 : C ≤ 1)
    (hWW : C * (w.length : ℝ) ^ (-(4.1163051 : ℝ)) ≤
             (oddCount w : ℝ) * Real.log 3 - (w.length : ℝ) * Real.log 2) :
    (C / 2 * ((n : ℝ) * Real.log n)) ^ (1 / (5.1163051 : ℝ)) ≤ (w.length : ℝ) := by
  have h51 : (4.1163051 : ℝ) + 1 = 5.1163051 := by norm_num
  have hmain := cycleMin_period_ge hn h hL hC0 hC1 (by norm_num) hWW
  rwa [h51] at hmain

end Problems.Juggler

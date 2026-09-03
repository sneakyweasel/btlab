import Problems.Juggler.CycleFinance

namespace Problems.Juggler

/-!
# Gap transfer and the short-cycle reduction (Paper A Theorem 4.10)

Theorem 4.4 bounds the relative surplus `θ = 1 − 2^L/3^o` of a
minimum-based cycle by `L/(n log n)`. The linear form
`Λ = o log 3 − L log 2 = −log(1 − θ)` is what transcendence theory
bounds from below. The two are tied by the elementary inequality
`log(1/(1−θ)) ≤ θ/(1−θ)`, which gives the floor-free transfer

`n log n · min(Λ, 1) ≤ 2 L`

(`cycleMin_gap_transfer`). Any lower bound `ε ≤ 1` on `Λ` therefore
becomes a length bound `n log n · ε ≤ 2 L` (`cycleMin_length_of_gap`).
With Rhin's effective measure `Λ > e^{−13.3(0.46057 + log L)}` this is
Corollary 4.11: every nontrivial cycle satisfies
`n log n ≤ 2 e^{6.1256} L^{14.3}`, so the no-cycle problem is exactly
the exclusion of long cycles `L^{14.3} > n log n / 914.9`. The
transcendence input is classical and stays a hypothesis here; the
transfer itself is fully proved.

This is a reduction, not a kill: at every certified floor the bound is
weaker than the finance table (the REFUTED Baker transfer of
`docs/problems/juggler_cycle_gap_baker.md` is the floor-level
statement). Not a halt theorem.
-/

/-- Gap transfer (Theorem 4.10): with `Λ = o log 3 − L log 2`,
`n log n · min(Λ, 1) ≤ 2 L` for every cycle minimum `n ≥ 2`. -/
theorem cycleMin_gap_transfer {n : ℕ} {w : List Branch}
    (hn : 2 ≤ n) (h : CycleMin n w) :
    (n : ℝ) * Real.log n *
        min ((oddCount w : ℝ) * Real.log 3 - (w.length : ℝ) * Real.log 2) 1 ≤
      2 * (w.length : ℝ) := by
  have hfin := cycleMin_finance hn h
  set A : ℝ := (3 : ℝ) ^ oddCount w with hA
  set B : ℝ := (2 : ℝ) ^ w.length with hB
  set P : ℝ := (n : ℝ) * Real.log n with hP
  have hApos : 0 < A := by positivity
  have hBpos : 0 < B := by positivity
  have hP0 : 0 ≤ P := by
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    exact mul_nonneg (by positivity) (Real.log_nonneg h1)
  have hL0 : (0 : ℝ) ≤ w.length := by positivity
  have hΛ : (oddCount w : ℝ) * Real.log 3 - (w.length : ℝ) * Real.log 2
      = Real.log (A / B) := by
    rw [Real.log_div hApos.ne' hBpos.ne', hA, hB, Real.log_pow, Real.log_pow]
  rw [hΛ]
  rcases le_or_gt A B with hAB | hAB
  · -- Λ ≤ 0: the left side is nonpositive.
    have hlog : Real.log (A / B) ≤ 0 :=
      Real.log_nonpos (by positivity) ((div_le_one hBpos).mpr hAB)
    have hmin : min (Real.log (A / B)) 1 ≤ 0 := le_trans (min_le_left _ _) hlog
    have := mul_le_mul_of_nonneg_left hmin hP0
    linarith
  · rcases le_or_gt (2 * B) A with h2 | h2
    · -- θ ≥ 1/2: finance alone gives P ≤ 2L.
      have hmin : min (Real.log (A / B)) 1 ≤ 1 := min_le_right _ _
      have hP2 : P ≤ 2 * w.length := by
        have hPB : P * B ≤ P * (A / 2) := by
          apply mul_le_mul_of_nonneg_left _ hP0
          linarith
        have : P * A ≤ 2 * w.length * A := by nlinarith
        exact le_of_mul_le_mul_right this hApos
      calc P * min (Real.log (A / B)) 1 ≤ P * 1 := mul_le_mul_of_nonneg_left hmin hP0
        _ = P := mul_one P
        _ ≤ 2 * w.length := hP2
    · -- θ < 1/2: Λ ≤ A/B − 1 = (A − B)/B and P (A − B) ≤ L A ≤ 2 L B.
      have hlog : Real.log (A / B) ≤ A / B - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      have hmin : min (Real.log (A / B)) 1 ≤ A / B - 1 :=
        le_trans (min_le_left _ _) hlog
      have hstep : P * (A / B - 1) ≤ 2 * w.length := by
        have heq : A / B - 1 = (A - B) / B := by
          field_simp
        rw [heq, ← mul_div_assoc, div_le_iff₀ hBpos]
        have hLA : (w.length : ℝ) * A ≤ (w.length : ℝ) * (2 * B) :=
          mul_le_mul_of_nonneg_left h2.le hL0
        nlinarith
      calc P * min (Real.log (A / B)) 1 ≤ P * (A / B - 1) :=
            mul_le_mul_of_nonneg_left hmin hP0
        _ ≤ 2 * w.length := hstep

/-- Any lower bound `ε ≤ 1` on the linear form `o log 3 − L log 2`
transfers to the floor-free length bound `n log n · ε ≤ 2 L`. With
Rhin's effective measure `ε = e^{−13.3(0.46057 + log L)}` (a hypothesis
here, classical in the literature) this is Paper A Corollary 4.11. -/
theorem cycleMin_length_of_gap {n : ℕ} {w : List Branch} {ε : ℝ}
    (hn : 2 ≤ n) (h : CycleMin n w) (hε : ε ≤ 1)
    (hgap : ε ≤ (oddCount w : ℝ) * Real.log 3 - (w.length : ℝ) * Real.log 2) :
    (n : ℝ) * Real.log n * ε ≤ 2 * (w.length : ℝ) := by
  have ht := cycleMin_gap_transfer hn h
  have hmin : ε ≤ min ((oddCount w : ℝ) * Real.log 3 - (w.length : ℝ) * Real.log 2) 1 :=
    le_min hgap hε
  have hP0 : 0 ≤ (n : ℝ) * Real.log n := by
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    exact mul_nonneg (by positivity) (Real.log_nonneg h1)
  calc (n : ℝ) * Real.log n * ε
      ≤ (n : ℝ) * Real.log n *
          min ((oddCount w : ℝ) * Real.log 3 - (w.length : ℝ) * Real.log 2) 1 :=
        mul_le_mul_of_nonneg_left hmin hP0
    _ ≤ 2 * (w.length : ℝ) := ht

end Problems.Juggler

/-
# Paper B, Appendix A: the threshold certificate

Three things this session established about
`docs/theory/juggler_parity_discrepancy_note.md` that are finite enough to prove
rather than compute:

1. the **raised-threshold device** of Step 5b, which replaced the comparison
   `V ≥ 10|f'' - Λ|` (Section 1 below) — a purely logical statement about
   sublevel sets, and the one genuinely new structural move of the session;
2. the **threshold rows** of the Appendix A certificate, which the probe solves
   by floating-point bisection (Section 2).  Every exponent in the paper lies in
   `(1/96)ℤ`, so substituting `P = t^n` for a suitable `n` turns each row into a
   polynomial inequality in `t` and removes `Real.rpow` entirely;
3. the **sharpness of `|G - δ| ≤ 1`** in Lemma 5.2b step (i), and the claim that
   recentring the interpolant cannot improve it (Section 3).

What is *not* here, and cannot reasonably be: Lemma 5.2, Theorem 5.3, and every
analytic input they use (van der Corput, Vaaler, Erdős–Turán, the `A`-process).
Those are hypotheses to the statements below, not conclusions.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Problems.Juggler

section RaisedThreshold

/-- **Step 5b, the raised-threshold device.**  Lemma 3.9 is applied to the global
interpolant `Λ` at threshold `W = V + E`, where `E` bounds `|f - Λ|`.  Off the
sublevel set `{|Λ| ≤ W}` this returns control of `f` itself: `|f| ≥ V`, and `f`
carries the sign of `Λ`.

This is what makes the former comparison `V ≥ 10 |f - Λ|` unnecessary.  The
factor `10` was not merely margin: it forced `V` upward exactly where the Lemma
3.9 hypothesis `V ≤ c₇S/2` forced it down, so the two pinned the normalisation
`κ` near `1/3`.  With this lemma `κ` falls to `1/12`, and both `P₀` and the
non-vacuity point `P₁` improve together. -/
theorem sublevel_raised_threshold
    (f Λ : ℝ → ℝ) (E V x : ℝ)
    (hV : 0 ≤ V) (hE : |f x - Λ x| ≤ E)
    (hx : V + E < |Λ x|) :
    V ≤ |f x| ∧ (0 < Λ x → 0 < f x) ∧ (Λ x < 0 → f x < 0) := by
  obtain ⟨h₁, h₂⟩ := abs_le.mp hE
  have hEnn : 0 ≤ E := le_trans (abs_nonneg _) hE
  refine ⟨?_, ?_, ?_⟩
  · -- |f| ≥ |Λ| - |f - Λ| > (V + E) - E = V
    have : |Λ x| - |f x - Λ x| ≤ |f x| := by
      have := abs_sub_abs_le_abs_sub (Λ x) (f x)
      rw [abs_sub_comm (Λ x) (f x)] at this
      linarith
    linarith
  · intro hpos
    have : V + E < Λ x := by rwa [abs_of_pos hpos] at hx
    linarith
  · intro hneg
    have : V + E < -Λ x := by rwa [abs_of_neg hneg] at hx
    linarith

/-- The device is sound for *any* nonnegative `V`, in particular for the small
`V` that the old comparison forbade.  Stated separately because it is the whole
point: the admissible range of `V` is `[0, c₇S/2 - E]`, not `[10E, c₇S/2]`. -/
theorem raised_threshold_admissible (E S c₇ : ℝ) (_hE : 0 ≤ E)
    (_hfeas : E ≤ c₇ * S / 2) :
    ∀ V, 0 ≤ V → V ≤ c₇ * S / 2 - E → V + E ≤ c₇ * S / 2 := by
  intro V _ hV2; linarith

end RaisedThreshold

section CertificateRows

/-! ### Appendix A rows as polynomial inequalities

Each row is stated in the substituted variable.  The paper's `P` is recovered as
`t ^ n`; the substitution is recorded in each docstring, and no `rpow` appears.
-/

/-- **Row `s3s1-Bsmall`** (Theorem 4.1, Stage 3(s1)): `2.25 P^(-1/16) < 1/2`,
i.e. `P > 4.5^16 = 2.83·10^10`.  Substitution `P = t^16`. -/
theorem row_s3s1_Bsmall (t : ℝ) (ht : 4.5 < t) : 2.25 / t < 1 / 2 := by
  rw [div_lt_iff₀ (by linarith)]
  linarith

/-- **Row `s3s2-window`** (Theorem 4.1, Stage 3(s2)): the Lemma 3.7 hypothesis
`P^(1/2) ≥ 8(1 + 2.25 P^(1/4))`.  Substitution `P = t^4`, so the row reads
`t^2 ≥ 8 + 18t`, first true at `t = 9 + √89 = 18.434`; the paper prints
`P^(1/4) ≥ 19`. -/
theorem row_s3s2_window (t : ℝ) (ht : 19 ≤ t) : 8 * (1 + 2.25 * t) ≤ t ^ 2 := by
  nlinarith [sq_nonneg (t - 19)]

/-- **Row `st6D1-window`** (Theorem 5.3, Stage 6(D1)): `P^(1/2) ≥ 8(1 + 7P^(1/4))`,
i.e. `t^2 ≥ 8 + 56t` under `P = t^4`; the paper prints `P^(1/4) ≥ 56`. -/
theorem row_st6D1_window (t : ℝ) (ht : 57 ≤ t) : 8 * (1 + 7 * t) ≤ t ^ 2 := by
  nlinarith [sq_nonneg (t - 57)]

/-- **Row `5b-Npieces`** (Theorem 5.3, Step 5b): the common refinement has at
most `3.5 P^(13/24)` pieces.  Substitution `P = t^48`: gap cells contribute
`3 t^26 + 2`, anchor runs `22 t^15`, sawtooth windows `5 t^16`, against
`3.5 t^26`.  First true near `t^48 = 5·10^7`. -/
theorem row_5b_Npieces (t : ℝ) (ht : 2.4 ≤ t) :
    3 * t ^ 26 + 2 + 22 * t ^ 15 + 5 * t ^ 16 ≤ 3.5 * t ^ 26 := by
  have ht0 : (0:ℝ) < t := by linarith
  have h16 : (1:ℝ) ≤ t ^ 16 := one_le_pow₀ (by linarith)
  have h1516 : t ^ 15 ≤ t ^ 16 := by
    have : t ^ 16 = t ^ 15 * t := by ring
    nlinarith [pow_pos ht0 15]
  -- 22t^15 + 5t^16 + 2 ≤ 29 t^16, and 58 ≤ t^10 gives 29 t^16 ≤ 0.5 t^26
  have h10 : (58:ℝ) ≤ t ^ 10 := by
    have h : (2.4:ℝ) ^ 10 ≤ t ^ 10 := by gcongr
    have : (58:ℝ) ≤ (2.4:ℝ) ^ 10 := by norm_num
    linarith
  have hkey : 29 * t ^ 16 ≤ 0.5 * t ^ 26 := by
    have e : t ^ 26 = t ^ 16 * t ^ 10 := by ring
    nlinarith [pow_pos ht0 16]
  linarith

/-- **The binding row, `5b-W<=c7S`** (Theorem 5.3, Step 5b): the single Lemma 3.9
hypothesis `W = V + E ≤ c₇S/2` at the lower end `S = 0.35 P^(-5/8)`, with
`V = (1/12) S^(1/2) P^(-11/24)` and `E = 105.6 P^(-25/24) + 0.11 P^(-5/6)`.

Multiplying by `P^(5/8)` and substituting `P = t^48` gives
`a t^13 + 0.11 t^10 + 105.6 ≤ b t^20` with `a = (1/12)√0.35 ≤ 0.04931` and
`b = 0.35/464 = 7/9280`.  This is `P₀`; the probe's bisection reports
`8.93·10^13`, and `t = 1.96` here is the rational threshold `1.07·10^14`. -/
theorem row_5b_binding (t : ℝ) (ht : 1.96 ≤ t) :
    0.04931 * t ^ 13 + 0.11 * t ^ 10 + 105.6 ≤ (7 / 9280) * t ^ 20 := by
  have ht0 : (0:ℝ) < t := by linarith
  have h7 : (111:ℝ) ≤ t ^ 7 := by
    have h : (1.96:ℝ) ^ 7 ≤ t ^ 7 := by gcongr
    have : (111:ℝ) ≤ (1.96:ℝ) ^ 7 := by norm_num
    linarith
  have h10 : (836:ℝ) ≤ t ^ 10 := by
    have h : (1.96:ℝ) ^ 10 ≤ t ^ 10 := by gcongr
    have : (836:ℝ) ≤ (1.96:ℝ) ^ 10 := by norm_num
    linarith
  -- the three terms are each a fixed fraction of t^20, and 4.4423 + 1.3158 + 1.5115 < 7.5431
  have k1 : 111 * t ^ 13 ≤ t ^ 20 := by
    have e : t ^ 20 = t ^ 13 * t ^ 7 := by ring
    nlinarith [pow_pos ht0 13]
  have k2 : 836 * t ^ 10 ≤ t ^ 20 := by
    have e : t ^ 20 = t ^ 10 * t ^ 10 := by ring
    nlinarith [pow_pos ht0 10]
  have k3 : (698896:ℝ) ≤ t ^ 20 := by
    have e : t ^ 20 = t ^ 10 * t ^ 10 := by ring
    nlinarith [pow_pos ht0 10]
  -- 0.04931/111 = 4.44234e-4, so 4.45e-4 is safe; 0.11/836 and 105.6/698896 likewise
  have b1 : 0.04931 * t ^ 13 ≤ 0.000445 * t ^ 20 := by linarith
  have b2 : 0.11 * t ^ 10 ≤ 0.00013158 * t ^ 20 := by linarith
  have b3 : (105.6:ℝ) ≤ 0.00015115 * t ^ 20 := by linarith
  -- 4.450 + 1.3158 + 1.5115 = 7.2773 < 7.5431 = 7/9280 (in units of 1e-4)
  linarith

end CertificateRows

section GapSharpness

/-- **Lemma 5.2b, step (i).**  The frozen gap satisfies `G = ⌊δ⌋ + κ` with
`κ ∈ {0,1}`, so `|G - δ| = |κ - Int.fract δ| ≤ 1`.  This is the bound that
produces the `52.3 k(h₁+h₂)P^(-9/8)` of the interpolant error. -/
theorem gap_error_le_one (δ : ℝ) (κ : ℤ) (hκ : κ = 0 ∨ κ = 1) :
    |((⌊δ⌋ + κ : ℤ) : ℝ) - δ| ≤ 1 := by
  have hf := Int.fract_nonneg δ
  have hf' := Int.fract_lt_one δ
  have hfe : Int.fract δ = δ - ⌊δ⌋ := rfl
  rcases hκ with h | h <;> subst h <;> push_cast <;> rw [abs_le] <;>
    constructor <;> linarith

/-- The bound `1` is **attained**: at `δ` an integer and `κ = 1`. -/
theorem gap_error_one_attained : |((⌊(0:ℝ)⌋ + 1 : ℤ) : ℝ) - 0| = 1 := by norm_num

/-- **Recentring cannot halve it.**  The error `κ - Int.fract δ` ranges over a set
of diameter `> 1` — it contains `1` (at `κ = 1`, `δ = 0`) and `-3/4` (at `κ = 0`,
`δ = 3/4`) — so no constant shift `θ` of the interpolant brings every value
within `1/2`.  This is why the paper's `1` is not replaced by `1/2`, and why
`κ_i = 1` exactly when `{ν^(3/2)} + {δ} ≥ 1` matters: both values occur. -/
theorem gap_error_not_halved_by_recentring (θ : ℝ) :
    1 / 2 < |1 - θ| ∨ 1 / 2 < |(-3 / 4 : ℝ) - θ| := by
  -- the two attainable errors are 7/4 apart, so no single θ is within 1/2 of both
  rcases le_or_gt θ (1 / 8) with h | h
  · left
    rw [abs_of_nonneg (by linarith)]
    linarith
  · right
    rw [abs_of_nonpos (by linarith)]
    linarith

end GapSharpness

end Problems.Juggler

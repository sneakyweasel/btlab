import Mathlib.Analysis.SpecialFunctions.Exp
import Problems.Juggler.RateFreeDensity

namespace Problems.Juggler

open Finset

/-!
# The tilted odd share and the pressure telescoping

Paper C Proposition 9.3 on the word-weight framework of
`RateFreeDensity`: with `x = e^θ`, the tilted generating function
`weightGen μ x d = Σ_{|w|=d} μ(w) x^{o(w)}` grows by at most the factor
`1 + (x-1) s_d` per depth, where `s_d` is the *tilted odd share* — the
tilted mass of the odd continuations over the tilted mass at depth `d`.
Each factor is at most `a_q exp(c_q (s_d - q)^+)` with
`a_q = 1 + (x-1) q` and `c_q = (x-1)/a_q`, so the depth-`d` tilted mass
is `weightGen μ x 0 · a_q^d · exp(c_q Σ_{t<d} (s_t - q)^+)`, and with
`weight_markov` the mass of words with at least `k` odd letters is that
over `x^k`. This is the reduction from the no-momentum hypothesis
`M_{θ,q}` to the Tao-type count, kernel-checked; the only Juggler input
is `WeightSplit`, i.e. that a word's two children carry at most the
parent's weight, which the live counts satisfy.
-/

/-- Tilted mass of the odd continuations at depth `d`:
`Σ_{|w|=d} μ(w ++ [O]) x^{o(w)}`. -/
noncomputable def oddMass (μ : List Branch → ℝ) (x : ℝ) (d : ℕ) : ℝ :=
  ∑ w ∈ allWords d, μ (w ++ [.odd]) * x ^ oddCount w

/-- The tilted odd share `s_θ(d)` with `x = e^θ`: odd continuations over
the whole tilted mass at depth `d` (Lean's `a / 0 = 0` when no mass). -/
noncomputable def tiltedShare (μ : List Branch → ℝ) (x : ℝ) (d : ℕ) : ℝ :=
  oddMass μ x d / weightGen μ x d

theorem weightGen_nonneg (μ : List Branch → ℝ) (x : ℝ) (hμ : ∀ w, 0 ≤ μ w)
    (hx : 0 ≤ x) (d : ℕ) : 0 ≤ weightGen μ x d :=
  Finset.sum_nonneg (fun w _ => mul_nonneg (hμ w) (pow_nonneg hx _))

theorem oddMass_nonneg (μ : List Branch → ℝ) (x : ℝ) (hμ : ∀ w, 0 ≤ μ w)
    (hx : 0 ≤ x) (d : ℕ) : 0 ≤ oddMass μ x d :=
  Finset.sum_nonneg (fun _w _ => mul_nonneg (hμ _) (pow_nonneg hx _))

/-- Odd continuations carry at most the parents' tilted mass. -/
theorem oddMass_le_weightGen (μ : List Branch → ℝ) (x : ℝ)
    (hsplit : WeightSplit μ) (hx : 0 ≤ x) (d : ℕ) :
    oddMass μ x d ≤ weightGen μ x d := by
  unfold oddMass weightGen
  apply Finset.sum_le_sum
  intro w _
  obtain ⟨he, _ho, hsum⟩ := hsplit w
  have h : μ (w ++ [.odd]) ≤ μ w := by linarith
  exact mul_le_mul_of_nonneg_right h (pow_nonneg hx _)

/-- One depth: `Z_{d+1} ≤ Z_d + (x-1)·oddMass_d`. -/
theorem weightGen_succ_le (μ : List Branch → ℝ) (x : ℝ)
    (hsplit : WeightSplit μ) (hx : 1 ≤ x) (d : ℕ) :
    weightGen μ x (d + 1) ≤ weightGen μ x d + (x - 1) * oddMass μ x d := by
  rw [weightGen_succ]
  unfold weightGen oddMass
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro w _
  obtain ⟨_he, _ho, hsum⟩ := hsplit w
  have hp : 0 ≤ x ^ oddCount w := pow_nonneg (by linarith) _
  have hsplit_term :
      μ (w ++ [.even]) * x ^ oddCount w + μ (w ++ [.odd]) * x ^ (oddCount w + 1)
        = (μ (w ++ [.even]) + μ (w ++ [.odd])) * x ^ oddCount w
          + (x - 1) * (μ (w ++ [.odd]) * x ^ oddCount w) := by
    rw [pow_succ]
    ring
  rw [hsplit_term]
  have h2 : (μ (w ++ [.even]) + μ (w ++ [.odd])) * x ^ oddCount w
      ≤ μ w * x ^ oddCount w :=
    mul_le_mul_of_nonneg_right hsum hp
  linarith

/-- One depth in share form: `Z_{d+1} ≤ Z_d (1 + (x-1) s_d)`. -/
theorem weightGen_succ_le_share (μ : List Branch → ℝ) (x : ℝ)
    (hμ : ∀ w, 0 ≤ μ w) (hsplit : WeightSplit μ) (hx : 1 ≤ x) (d : ℕ) :
    weightGen μ x (d + 1) ≤ weightGen μ x d * (1 + (x - 1) * tiltedShare μ x d) := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have h := weightGen_succ_le μ x hsplit hx d
  by_cases hz : weightGen μ x d = 0
  · have hom : oddMass μ x d = 0 :=
      le_antisymm (hz ▸ oddMass_le_weightGen μ x hsplit hx0 d) (oddMass_nonneg μ x hμ hx0 d)
    rw [hz, hom] at h
    rw [hz]
    linarith
  · have hrepr : oddMass μ x d = tiltedShare μ x d * weightGen μ x d := by
      unfold tiltedShare
      rw [div_mul_cancel₀ _ hz]
    rw [hrepr] at h
    calc weightGen μ x (d + 1)
        ≤ weightGen μ x d + (x - 1) * (tiltedShare μ x d * weightGen μ x d) := h
      _ = weightGen μ x d * (1 + (x - 1) * tiltedShare μ x d) := by ring

/-- The per-depth factor is dominated by `a_q exp(c_q (s - q)^+)`. -/
theorem one_add_le_exp_excess (x q s : ℝ) (hx : 1 ≤ x) (hq : 0 ≤ q) :
    1 + (x - 1) * s ≤
      (1 + (x - 1) * q) * Real.exp ((x - 1) / (1 + (x - 1) * q) * max (s - q) 0) := by
  have ha0 : 0 < 1 + (x - 1) * q := by nlinarith
  have hc : 0 ≤ (x - 1) / (1 + (x - 1) * q) := div_nonneg (by linarith) ha0.le
  have hac : (1 + (x - 1) * q) * ((x - 1) / (1 + (x - 1) * q)) = x - 1 :=
    mul_div_cancel₀ _ ha0.ne'
  have key : 1 + (x - 1) * s
      = (1 + (x - 1) * q) * (1 + (x - 1) / (1 + (x - 1) * q) * (s - q)) := by
    have : (1 + (x - 1) * q) * (1 + (x - 1) / (1 + (x - 1) * q) * (s - q))
        = (1 + (x - 1) * q) + ((1 + (x - 1) * q) * ((x - 1) / (1 + (x - 1) * q))) * (s - q) := by
      ring
    rw [this, hac]
    ring
  rw [key]
  apply mul_le_mul_of_nonneg_left _ ha0.le
  calc 1 + (x - 1) / (1 + (x - 1) * q) * (s - q)
      = (x - 1) / (1 + (x - 1) * q) * (s - q) + 1 := by ring
    _ ≤ Real.exp ((x - 1) / (1 + (x - 1) * q) * (s - q)) := Real.add_one_le_exp _
    _ ≤ Real.exp ((x - 1) / (1 + (x - 1) * q) * max (s - q) 0) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left (le_max_left _ _) hc

/-- Proposition 9.3: the tilted mass at depth `d` is at most
`Z_0 · a_q^d · exp(c_q Σ_{t<d} (s_t - q)^+)`. -/
theorem weightGen_le_pressure (μ : List Branch → ℝ) (x q : ℝ)
    (hμ : ∀ w, 0 ≤ μ w) (hsplit : WeightSplit μ) (hx : 1 ≤ x) (hq : 0 ≤ q) (d : ℕ) :
    weightGen μ x d ≤
      weightGen μ x 0 * (1 + (x - 1) * q) ^ d *
        Real.exp ((x - 1) / (1 + (x - 1) * q) *
          ∑ t ∈ Finset.range d, max (tiltedShare μ x t - q) 0) := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have ha0 : 0 ≤ 1 + (x - 1) * q := by nlinarith
  induction d with
  | zero => simp
  | succ d ih =>
      have hstep := weightGen_succ_le_share μ x hμ hsplit hx d
      have hexp := one_add_le_exp_excess x q (tiltedShare μ x d) hx hq
      have hW : 0 ≤ weightGen μ x d := weightGen_nonneg μ x hμ hx0 d
      have hfac : 0 ≤ (1 + (x - 1) * q) *
          Real.exp ((x - 1) / (1 + (x - 1) * q) * max (tiltedShare μ x d - q) 0) :=
        mul_nonneg ha0 (Real.exp_pos _).le
      rw [Finset.sum_range_succ, mul_add, Real.exp_add, pow_succ]
      calc weightGen μ x (d + 1)
          ≤ weightGen μ x d * (1 + (x - 1) * tiltedShare μ x d) := hstep
        _ ≤ weightGen μ x d * ((1 + (x - 1) * q) *
              Real.exp ((x - 1) / (1 + (x - 1) * q) * max (tiltedShare μ x d - q) 0)) :=
            mul_le_mul_of_nonneg_left hexp hW
        _ ≤ (weightGen μ x 0 * (1 + (x - 1) * q) ^ d *
              Real.exp ((x - 1) / (1 + (x - 1) * q) *
                ∑ t ∈ Finset.range d, max (tiltedShare μ x t - q) 0)) *
            ((1 + (x - 1) * q) *
              Real.exp ((x - 1) / (1 + (x - 1) * q) * max (tiltedShare μ x d - q) 0)) :=
            mul_le_mul_of_nonneg_right ih hfac
        _ = weightGen μ x 0 * ((1 + (x - 1) * q) ^ d * (1 + (x - 1) * q)) *
              (Real.exp ((x - 1) / (1 + (x - 1) * q) *
                ∑ t ∈ Finset.range d, max (tiltedShare μ x t - q) 0) *
               Real.exp ((x - 1) / (1 + (x - 1) * q) * max (tiltedShare μ x d - q) 0)) := by
            ring

/-- Theorem 9.2 with Proposition 9.3: the mass of words with at least
`k` odd letters is at most `Z_0 a_q^d exp(c_q Σ (s_t - q)^+) / x^k`. -/
theorem count_le_pressure (μ : List Branch → ℝ) (x q : ℝ)
    (hμ : ∀ w, 0 ≤ μ w) (hsplit : WeightSplit μ) (hx : 1 ≤ x) (hq : 0 ≤ q) (d k : ℕ) :
    (∑ w ∈ (allWords d).filter (fun w => k ≤ oddCount w), μ w) ≤
      weightGen μ x 0 * (1 + (x - 1) * q) ^ d *
        Real.exp ((x - 1) / (1 + (x - 1) * q) *
          ∑ t ∈ Finset.range d, max (tiltedShare μ x t - q) 0) / x ^ k := by
  have hxk : 0 ≤ x ^ k := pow_nonneg (by linarith) k
  calc (∑ w ∈ (allWords d).filter (fun w => k ≤ oddCount w), μ w)
      ≤ weightGen μ x d / x ^ k := weight_markov μ x d k hx hμ
    _ ≤ _ := div_le_div_of_nonneg_right (weightGen_le_pressure μ x q hμ hsplit hx hq d) hxk

/-- The no-momentum hypothesis at one scale and depth: the tilted odd
share exceeds `q` by at most `δ d` in total over the depths below `d`. -/
def NoMomentum (μ : List Branch → ℝ) (x q δ : ℝ) (d : ℕ) : Prop :=
  (∑ t ∈ Finset.range d, max (tiltedShare μ x t - q) 0) ≤ δ * d

/-- Under no momentum the mass of words with at least `k` odd letters
is at most `Z_0 · a_q^d · exp(c_q δ d) / x^k`: the Tao-type count with
its Chernoff-form exponent, kernel-checked. -/
theorem count_le_of_noMomentum (μ : List Branch → ℝ) (x q δ : ℝ)
    (hμ : ∀ w, 0 ≤ μ w) (hsplit : WeightSplit μ) (hx : 1 ≤ x) (hq : 0 ≤ q)
    (d k : ℕ) (hM : NoMomentum μ x q δ d) :
    (∑ w ∈ (allWords d).filter (fun w => k ≤ oddCount w), μ w) ≤
      weightGen μ x 0 * (1 + (x - 1) * q) ^ d *
        Real.exp ((x - 1) / (1 + (x - 1) * q) * (δ * d)) / x ^ k := by
  have ha0 : 0 < 1 + (x - 1) * q := by nlinarith
  have hc : 0 ≤ (x - 1) / (1 + (x - 1) * q) := div_nonneg (by linarith) ha0.le
  have hZ0 : 0 ≤ weightGen μ x 0 := weightGen_nonneg μ x hμ (by linarith) 0
  have hpow : 0 ≤ (1 + (x - 1) * q) ^ d := pow_nonneg ha0.le d
  have hxk : 0 ≤ x ^ k := pow_nonneg (by linarith) k
  have hexp : Real.exp ((x - 1) / (1 + (x - 1) * q) *
        ∑ t ∈ Finset.range d, max (tiltedShare μ x t - q) 0)
      ≤ Real.exp ((x - 1) / (1 + (x - 1) * q) * (δ * d)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hM hc
  calc (∑ w ∈ (allWords d).filter (fun w => k ≤ oddCount w), μ w)
      ≤ weightGen μ x 0 * (1 + (x - 1) * q) ^ d *
          Real.exp ((x - 1) / (1 + (x - 1) * q) *
            ∑ t ∈ Finset.range d, max (tiltedShare μ x t - q) 0) / x ^ k :=
        count_le_pressure μ x q hμ hsplit hx hq d k
    _ ≤ weightGen μ x 0 * (1 + (x - 1) * q) ^ d *
          Real.exp ((x - 1) / (1 + (x - 1) * q) * (δ * d)) / x ^ k := by
        apply div_le_div_of_nonneg_right _ hxk
        exact mul_le_mul_of_nonneg_left hexp (mul_nonneg hZ0 hpow)

/-- At the re-centring tilt `x = p(1-q)/(q(1-p))` the per-step exponent is
the relative entropy: `p log x - log(1 + (x-1) q) = D(p ‖ q)`. -/
theorem tilt_exponent_eq_kl (p q : ℝ) (hq0 : 0 < q) (hqp : q < p) (hp1 : p < 1) :
    p * Real.log (p * (1 - q) / (q * (1 - p))) -
        Real.log (1 + (p * (1 - q) / (q * (1 - p)) - 1) * q) =
      p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q)) := by
  have hp0 : 0 < p := lt_trans hq0 hqp
  have h1p : 0 < 1 - p := by linarith
  have h1q : 0 < 1 - q := by linarith
  have hden : q * (1 - p) ≠ 0 := by positivity
  have ha : 1 + (p * (1 - q) / (q * (1 - p)) - 1) * q = (1 - q) / (1 - p) := by
    field_simp
    ring
  have h1 : Real.log (p * (1 - q) / (q * (1 - p)))
      = Real.log p + Real.log (1 - q) - (Real.log q + Real.log (1 - p)) := by
    rw [Real.log_div (by positivity) hden, Real.log_mul hp0.ne' h1q.ne',
      Real.log_mul hq0.ne' h1p.ne']
  have h2 : Real.log ((1 - q) / (1 - p)) = Real.log (1 - q) - Real.log (1 - p) :=
    Real.log_div h1q.ne' h1p.ne'
  have h3 : Real.log (p / q) = Real.log p - Real.log q := Real.log_div hp0.ne' hq0.ne'
  have h4 : Real.log ((1 - p) / (1 - q)) = Real.log (1 - p) - Real.log (1 - q) :=
    Real.log_div h1p.ne' h1q.ne'
  rw [ha, h1, h2, h3, h4]
  ring

end Problems.Juggler

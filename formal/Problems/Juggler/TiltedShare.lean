import Mathlib.Analysis.Convex.SpecificFunctions.Basic
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

/-- AM–GM in the form used below: a product of `d` positive reals is at
most the `d`-th power of their mean (Jensen for `Real.log`). -/
theorem prod_le_mean_pow (d : ℕ) (hd : 0 < d) (z : ℕ → ℝ)
    (hz : ∀ t ∈ Finset.range d, 0 < z t) :
    ∏ t ∈ Finset.range d, z t ≤ ((∑ t ∈ Finset.range d, z t) / d) ^ d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := hdR.ne'
  have hw : ∀ t ∈ Finset.range d, (0 : ℝ) ≤ 1 / d := fun _ _ => by positivity
  have hw1 : ∑ t ∈ Finset.range d, (1 / (d : ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  have hmem : ∀ t ∈ Finset.range d, z t ∈ Set.Ioi (0 : ℝ) := fun t ht => hz t ht
  have hJ := (strictConcaveOn_log_Ioi.concaveOn).le_map_sum hw hw1 hmem
  simp only [smul_eq_mul] at hJ
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hJ
  have hprod : 0 < ∏ t ∈ Finset.range d, z t := Finset.prod_pos hz
  have hsum : 0 < ∑ t ∈ Finset.range d, z t :=
    Finset.sum_pos hz (Finset.nonempty_range_iff.mpr hd.ne')
  have hmean : 0 < (∑ t ∈ Finset.range d, z t) / d := div_pos hsum hdR
  rw [← Real.log_le_log_iff hprod (pow_pos hmean d), Real.log_pow,
    Real.log_prod (fun t ht => (hz t ht).ne')]
  have hrepr : (∑ t ∈ Finset.range d, z t) / d = 1 / d * ∑ t ∈ Finset.range d, z t := by
    ring
  rw [hrepr]
  calc (∑ t ∈ Finset.range d, Real.log (z t))
      = d * (1 / d * ∑ t ∈ Finset.range d, Real.log (z t)) := by
        field_simp
    _ ≤ d * Real.log (1 / d * ∑ t ∈ Finset.range d, z t) :=
        mul_le_mul_of_nonneg_left hJ hdR.le

/-- The product form of the telescoping: `Z_d ≤ Z_0 ∏_{t<d} (1 + (x-1) s_t)`. -/
theorem weightGen_le_prod (μ : List Branch → ℝ) (x : ℝ)
    (hμ : ∀ w, 0 ≤ μ w) (hsplit : WeightSplit μ) (hx : 1 ≤ x) (d : ℕ) :
    weightGen μ x d ≤
      weightGen μ x 0 * ∏ t ∈ Finset.range d, (1 + (x - 1) * tiltedShare μ x t) := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  induction d with
  | zero => simp
  | succ d ih =>
      have hstep := weightGen_succ_le_share μ x hμ hsplit hx d
      have hs : 0 ≤ tiltedShare μ x d :=
        div_nonneg (oddMass_nonneg μ x hμ hx0 d) (weightGen_nonneg μ x hμ hx0 d)
      have hfac : 0 ≤ 1 + (x - 1) * tiltedShare μ x d := by nlinarith
      rw [Finset.prod_range_succ]
      calc weightGen μ x (d + 1)
          ≤ weightGen μ x d * (1 + (x - 1) * tiltedShare μ x d) := hstep
        _ ≤ (weightGen μ x 0 * ∏ t ∈ Finset.range d, (1 + (x - 1) * tiltedShare μ x t)) *
              (1 + (x - 1) * tiltedShare μ x d) := mul_le_mul_of_nonneg_right ih hfac
        _ = _ := by ring

/-- The mean-share hypothesis: the tilted odd share averages at most `q`
over the depths below `d`.  No positive part: depths with share below
`q` compensate depths with share above it. -/
def MeanShare (μ : List Branch → ℝ) (x q : ℝ) (d : ℕ) : Prop :=
  (∑ t ∈ Finset.range d, tiltedShare μ x t) ≤ q * d

/-- No momentum against `q` with slack `δ` gives mean share at most `q + δ`. -/
theorem meanShare_of_noMomentum (μ : List Branch → ℝ) (x q δ : ℝ) (d : ℕ)
    (hM : NoMomentum μ x q δ d) : MeanShare μ x (q + δ) d := by
  unfold MeanShare
  unfold NoMomentum at hM
  have h : ∑ t ∈ Finset.range d, tiltedShare μ x t ≤
      ∑ t ∈ Finset.range d, (q + max (tiltedShare μ x t - q) 0) := by
    apply Finset.sum_le_sum
    intro t _
    linarith [le_max_left (tiltedShare μ x t - q) 0]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  linarith

/-- Under the mean-share hypothesis the depth-`d` tilted mass is at most
`Z_0 a_q^d`, with no exponential slack: AM–GM on the product form. -/
theorem weightGen_le_of_meanShare (μ : List Branch → ℝ) (x q : ℝ)
    (hμ : ∀ w, 0 ≤ μ w) (hsplit : WeightSplit μ) (hx : 1 ≤ x) (_hq : 0 ≤ q) (d : ℕ)
    (hM : MeanShare μ x q d) :
    weightGen μ x d ≤ weightGen μ x 0 * (1 + (x - 1) * q) ^ d := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    simp
  · have hx0 : (0 : ℝ) ≤ x := by linarith
    have hZ0 : 0 ≤ weightGen μ x 0 := weightGen_nonneg μ x hμ hx0 0
    have hpos : ∀ t ∈ Finset.range d, 0 < 1 + (x - 1) * tiltedShare μ x t := by
      intro t _
      have hs : 0 ≤ tiltedShare μ x t :=
        div_nonneg (oddMass_nonneg μ x hμ hx0 t) (weightGen_nonneg μ x hμ hx0 t)
      nlinarith
    have hamgm := prod_le_mean_pow d hd (fun t => 1 + (x - 1) * tiltedShare μ x t) hpos
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    have hmean0 : 0 ≤ (∑ t ∈ Finset.range d, (1 + (x - 1) * tiltedShare μ x t)) / d :=
      div_nonneg (Finset.sum_nonneg (fun t ht => (hpos t ht).le)) hdR.le
    have hmean : (∑ t ∈ Finset.range d, (1 + (x - 1) * tiltedShare μ x t)) / d ≤
        1 + (x - 1) * q := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        ← Finset.mul_sum, div_le_iff₀ hdR]
      have h := mul_le_mul_of_nonneg_left hM (by linarith : (0 : ℝ) ≤ x - 1)
      unfold MeanShare at hM
      nlinarith
    calc weightGen μ x d
        ≤ weightGen μ x 0 * ∏ t ∈ Finset.range d, (1 + (x - 1) * tiltedShare μ x t) :=
          weightGen_le_prod μ x hμ hsplit hx d
      _ ≤ weightGen μ x 0 *
            ((∑ t ∈ Finset.range d, (1 + (x - 1) * tiltedShare μ x t)) / d) ^ d :=
          mul_le_mul_of_nonneg_left hamgm hZ0
      _ ≤ weightGen μ x 0 * (1 + (x - 1) * q) ^ d :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hmean0 hmean d) hZ0

/-- The Tao-type count under the mean-share hypothesis:
`#{o_d ≥ k} ≤ Z_0 a_q^d / x^k`, with no exponential slack. -/
theorem count_le_of_meanShare (μ : List Branch → ℝ) (x q : ℝ)
    (hμ : ∀ w, 0 ≤ μ w) (hsplit : WeightSplit μ) (hx : 1 ≤ x) (hq : 0 ≤ q) (d k : ℕ)
    (hM : MeanShare μ x q d) :
    (∑ w ∈ (allWords d).filter (fun w => k ≤ oddCount w), μ w) ≤
      weightGen μ x 0 * (1 + (x - 1) * q) ^ d / x ^ k := by
  have hxk : 0 ≤ x ^ k := pow_nonneg (by linarith) k
  calc (∑ w ∈ (allWords d).filter (fun w => k ≤ oddCount w), μ w)
      ≤ weightGen μ x d / x ^ k := weight_markov μ x d k hx hμ
    _ ≤ _ := div_le_div_of_nonneg_right
      (weightGen_le_of_meanShare μ x q hμ hsplit hx hq d hM) hxk

/-! ## Exceptional depths are free

Paper C section 9.3(a) says in prose that any `o(log log y)` set of depths
costs nothing, because a single letter multiplies the tilted moment by at
most `x`.  The theorems below are that sentence: the mean-share hypothesis
need only hold away from an exceptional set `E`, and the price is exactly
`x^{|E|}`.  With `E` an initial segment this says every fixed-depth split,
the depth-five one included, is irrelevant to the reduction.
-/

/-- The tilted odd share is a share: it never exceeds `1`. -/
theorem tiltedShare_le_one (μ : List Branch → ℝ) (x : ℝ)
    (hμ : ∀ w, 0 ≤ μ w) (hsplit : WeightSplit μ) (hx : 0 ≤ x) (d : ℕ) :
    tiltedShare μ x d ≤ 1 := by
  unfold tiltedShare
  rcases eq_or_lt_of_le (weightGen_nonneg μ x hμ hx d) with h | h
  · rw [← h, div_zero]; norm_num
  · rw [div_le_one h]
    exact oddMass_le_weightGen μ x hsplit hx d

/-- AM–GM over an arbitrary finite index set. -/
theorem prod_le_mean_pow_finset (s : Finset ℕ) (hs : s.Nonempty) (z : ℕ → ℝ)
    (hz : ∀ t ∈ s, 0 < z t) :
    ∏ t ∈ s, z t ≤ ((∑ t ∈ s, z t) / s.card) ^ s.card := by
  have hcard : 0 < s.card := Finset.card_pos.mpr hs
  have hcR : (0 : ℝ) < s.card := by exact_mod_cast hcard
  have hc0 : (s.card : ℝ) ≠ 0 := hcR.ne'
  have hw : ∀ t ∈ s, (0 : ℝ) ≤ 1 / s.card := fun _ _ => by positivity
  have hw1 : ∑ _t ∈ s, (1 / (s.card : ℝ)) = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    field_simp
  have hmem : ∀ t ∈ s, z t ∈ Set.Ioi (0 : ℝ) := fun t ht => hz t ht
  have hJ := (strictConcaveOn_log_Ioi.concaveOn).le_map_sum hw hw1 hmem
  simp only [smul_eq_mul] at hJ
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hJ
  have hprod : 0 < ∏ t ∈ s, z t := Finset.prod_pos hz
  have hsum : 0 < ∑ t ∈ s, z t := Finset.sum_pos hz hs
  have hmean : 0 < (∑ t ∈ s, z t) / s.card := div_pos hsum hcR
  rw [← Real.log_le_log_iff hprod (pow_pos hmean _), Real.log_pow,
    Real.log_prod (fun t ht => (hz t ht).ne')]
  have hrepr : (∑ t ∈ s, z t) / s.card = 1 / s.card * ∑ t ∈ s, z t := by ring
  rw [hrepr]
  calc (∑ t ∈ s, Real.log (z t))
      = s.card * (1 / s.card * ∑ t ∈ s, Real.log (z t)) := by field_simp
    _ ≤ s.card * Real.log (1 / s.card * ∑ t ∈ s, z t) :=
        mul_le_mul_of_nonneg_left hJ hcR.le

/-- The mean-share hypothesis away from an exceptional set of depths `E`.
Nothing at all is assumed on `E`. -/
def MeanShareOff (μ : List Branch → ℝ) (x q : ℝ) (d : ℕ) (E : Finset ℕ) : Prop :=
  (∑ t ∈ Finset.range d \ E, tiltedShare μ x t) ≤ q * (Finset.range d \ E).card

/-- With no exceptional depths this is `MeanShare`. -/
theorem meanShareOff_empty (μ : List Branch → ℝ) (x q : ℝ) (d : ℕ) :
    MeanShareOff μ x q d ∅ ↔ MeanShare μ x q d := by
  simp [MeanShareOff, MeanShare]

/-- **Exceptional depths cost a factor `x` each, and nothing more.**  Under
`MeanShareOff` the depth-`d` tilted mass is at most
`Z_0 · x^{|E ∩ [0,d)|} · a_q^{|[0,d) \ E|}`. -/
theorem weightGen_le_of_meanShareOff (μ : List Branch → ℝ) (x q : ℝ)
    (hμ : ∀ w, 0 ≤ μ w) (hsplit : WeightSplit μ) (hx : 1 ≤ x) (hq : 0 ≤ q)
    (d : ℕ) (E : Finset ℕ) (hM : MeanShareOff μ x q d E) :
    weightGen μ x d ≤
      weightGen μ x 0 * (x ^ (Finset.range d ∩ E).card *
        (1 + (x - 1) * q) ^ (Finset.range d \ E).card) := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hZ0 : 0 ≤ weightGen μ x 0 := weightGen_nonneg μ x hμ hx0 0
  have hs0 : ∀ t, 0 ≤ tiltedShare μ x t := fun t =>
    div_nonneg (oddMass_nonneg μ x hμ hx0 t) (weightGen_nonneg μ x hμ hx0 t)
  have hs1 : ∀ t, tiltedShare μ x t ≤ 1 := fun t =>
    tiltedShare_le_one μ x hμ hsplit hx0 t
  have hpos : ∀ t, 0 < 1 + (x - 1) * tiltedShare μ x t := by
    intro t; nlinarith [hs0 t]
  have hfx : ∀ t, 1 + (x - 1) * tiltedShare μ x t ≤ x := by
    intro t; nlinarith [hs1 t]
  -- split the product over the exceptional and the good depths
  have hsplit_prod :
      (∏ t ∈ Finset.range d ∩ E, (1 + (x - 1) * tiltedShare μ x t)) *
        (∏ t ∈ Finset.range d \ E, (1 + (x - 1) * tiltedShare μ x t))
      = ∏ t ∈ Finset.range d, (1 + (x - 1) * tiltedShare μ x t) := by
    rw [Finset.sdiff_eq_filter, ← Finset.filter_mem_eq_inter]
    exact Finset.prod_filter_mul_prod_filter_not _ _ _
  have hbad :
      (∏ t ∈ Finset.range d ∩ E, (1 + (x - 1) * tiltedShare μ x t))
        ≤ x ^ (Finset.range d ∩ E).card := by
    calc (∏ t ∈ Finset.range d ∩ E, (1 + (x - 1) * tiltedShare μ x t))
        ≤ ∏ _t ∈ Finset.range d ∩ E, x :=
          Finset.prod_le_prod (fun i _ => (hpos i).le) (fun i _ => hfx i)
      _ = x ^ (Finset.range d ∩ E).card := by rw [Finset.prod_const]
  have hgood :
      (∏ t ∈ Finset.range d \ E, (1 + (x - 1) * tiltedShare μ x t))
        ≤ (1 + (x - 1) * q) ^ (Finset.range d \ E).card := by
    rcases Finset.eq_empty_or_nonempty (Finset.range d \ E) with hE | hE
    · simp [hE]
    · have hamgm := prod_le_mean_pow_finset _ hE
        (fun t => 1 + (x - 1) * tiltedShare μ x t) (fun t _ => hpos t)
      have hcR : (0 : ℝ) < (Finset.range d \ E).card := by
        exact_mod_cast Finset.card_pos.mpr hE
      have hmean0 : 0 ≤ (∑ t ∈ Finset.range d \ E, (1 + (x - 1) * tiltedShare μ x t))
          / (Finset.range d \ E).card :=
        div_nonneg (Finset.sum_nonneg fun t _ => (hpos t).le) hcR.le
      have hmean : (∑ t ∈ Finset.range d \ E, (1 + (x - 1) * tiltedShare μ x t))
          / (Finset.range d \ E).card ≤ 1 + (x - 1) * q := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum,
          div_le_iff₀ hcR]
        unfold MeanShareOff at hM
        nlinarith
      exact le_trans hamgm (pow_le_pow_left₀ hmean0 hmean _)
  have hprodpos : 0 ≤ ∏ t ∈ Finset.range d ∩ E, (1 + (x - 1) * tiltedShare μ x t) :=
    Finset.prod_nonneg (fun i _ => (hpos i).le)
  have haq : 0 ≤ (1 + (x - 1) * q) ^ (Finset.range d \ E).card :=
    pow_nonneg (by nlinarith) _
  calc weightGen μ x d
      ≤ weightGen μ x 0 * ∏ t ∈ Finset.range d, (1 + (x - 1) * tiltedShare μ x t) :=
        weightGen_le_prod μ x hμ hsplit hx d
    _ = weightGen μ x 0 *
          ((∏ t ∈ Finset.range d ∩ E, (1 + (x - 1) * tiltedShare μ x t)) *
            (∏ t ∈ Finset.range d \ E, (1 + (x - 1) * tiltedShare μ x t))) := by
        rw [hsplit_prod]
    _ ≤ weightGen μ x 0 * (x ^ (Finset.range d ∩ E).card *
          (1 + (x - 1) * q) ^ (Finset.range d \ E).card) := by
        apply mul_le_mul_of_nonneg_left _ hZ0
        exact mul_le_mul hbad hgood
          (Finset.prod_nonneg (fun i _ => (hpos i).le)) (pow_nonneg (by linarith) _)

/-- The Tao-type count with an exceptional set of depths. -/
theorem count_le_of_meanShareOff (μ : List Branch → ℝ) (x q : ℝ)
    (hμ : ∀ w, 0 ≤ μ w) (hsplit : WeightSplit μ) (hx : 1 ≤ x) (hq : 0 ≤ q)
    (d k : ℕ) (E : Finset ℕ) (hM : MeanShareOff μ x q d E) :
    (∑ w ∈ (allWords d).filter (fun w => k ≤ oddCount w), μ w) ≤
      weightGen μ x 0 * (x ^ (Finset.range d ∩ E).card *
        (1 + (x - 1) * q) ^ (Finset.range d \ E).card) / x ^ k := by
  have hxk : 0 ≤ x ^ k := pow_nonneg (by linarith) k
  calc (∑ w ∈ (allWords d).filter (fun w => k ≤ oddCount w), μ w)
      ≤ weightGen μ x d / x ^ k := weight_markov μ x d k hx hμ
    _ ≤ _ := div_le_div_of_nonneg_right
      (weightGen_le_of_meanShareOff μ x q hμ hsplit hx hq d E hM) hxk

/-- **Every bounded prefix of depths is free.**  Taking the exceptional set to
be the first `k` depths, no assumption whatever on those depths costs more
than the constant factor `x^k`.  This is Paper C section 9.3(a): the
depth-five split, and every split to any fixed depth, cannot bear on the
reduction. -/
theorem initial_depths_are_free (μ : List Branch → ℝ) (x q : ℝ)
    (hμ : ∀ w, 0 ≤ μ w) (hsplit : WeightSplit μ) (hx : 1 ≤ x) (hq : 0 ≤ q)
    (d k : ℕ) (hk : k ≤ d) (hM : MeanShareOff μ x q d (Finset.range k)) :
    weightGen μ x d ≤ weightGen μ x 0 * (x ^ k * (1 + (x - 1) * q) ^ (d - k)) := by
  have hsub : Finset.range k ⊆ Finset.range d := fun t ht =>
    Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp ht) hk)
  have hinter : Finset.range d ∩ Finset.range k = Finset.range k :=
    Finset.inter_eq_right.mpr hsub
  have hcard : (Finset.range d \ Finset.range k).card = d - k := by
    rw [Finset.card_sdiff, Finset.card_range, Finset.inter_eq_left.mpr hsub,
      Finset.card_range]
  have h := weightGen_le_of_meanShareOff μ x q hμ hsplit hx hq d (Finset.range k) hM
  rwa [hinter, Finset.card_range, hcard] at h

/-! ## Tower tolerance

Paper C section 9.3(b): an all-odd tower splitting with odd share `β` at every
level carries tilted weight `(βx/a_q)^t` relative to the fair total, so it
costs a bounded total exactly when `βx < a_q`.  The threshold is `a_q/x`, and
at `q = 1/2` that is `(1+x)/(2x) = (1 + e^{-θ})/2`.
-/

/-- A tower biased below `a_q/x` has geometrically decaying relative weight. -/
theorem tower_ratio_lt_one (β x q : ℝ) (hx : 0 < x) (ha : 0 < 1 + (x - 1) * q)
    (hlt : β < (1 + (x - 1) * q) / x) :
    β * x / (1 + (x - 1) * q) < 1 := by
  rw [div_lt_one ha]
  rw [lt_div_iff₀ hx] at hlt
  linarith

/-- At `q = 1/2` the tower tolerance is `(1+x)/(2x)`. -/
theorem tower_tolerance_half (x : ℝ) (hx : x ≠ 0) :
    (1 + (x - 1) * (1 / 2 : ℝ)) / x = (1 + x) / (2 * x) := by
  field_simp
  ring

end Problems.Juggler

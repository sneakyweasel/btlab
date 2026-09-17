/-
# The exact-rate asymptotic skeleton of the survivor count

Companion to `PaperBSurvivorDecay`, which machine-checked the upper bound
`N_d / 2^d ≤ θ(β)^d` and the decay `N_d / 2^d → 0`.  The measured truth is sharper
(`J-paper-b-meander-prefactor-is-almost-periodic`, COMPUTATIONALLY VERIFIED):

  `N_d / 2^d ~ ψ(frac(d·β)) · θ(β)^d · d^(-3/2)`,

with the prefactor `ψ` an almost-periodic, non-convergent function of `frac(d·β)`
(measured range `10.3685 … 10.9968`, spread `1.07` over twenty consecutive depths at
`d ≈ 1000–4000`, so the limit `C` of a naive constant-prefactor target does not exist).
This module states that shape exactly, as Lean propositions over a candidate `ψ`,
proves the one identity the ledger quoted numerically, and proves that once the shape
holds with `ψ` bounded on both sides of `0`, the proved upper bound is sharp up to the
polynomial `d^(3/2)` — nothing more is left to find at the exponential scale.

* `theta_beta_eq_rho` — the ledger's `ρ = θ(β)`, recorded as a `1.1e-16` numerical
  agreement, is `rfl` between `PaperBChernoff.theta` and `PaperBTilt.rho`.  So the
  crude tilt forfeits no exponential rate against the measured truth; the whole gap is
  the polynomial `d^(3/2)` and the almost-periodic prefactor.
* `MeanderShape` — the asymptotic itself, stated as a `Tendsto` against a candidate
  `ψ`.  Nothing here asserts it holds: the open obligation is a local limit theorem for
  a lattice walk against a Sturmian barrier (`PaperBTilt.sturmian_step` is why the
  barrier is Sturmian rather than straight), which no module of the laboratory proves.
* `PrefactorBounds` — `ψ` bounded above and bounded below away from zero on `(0,1)`.
  The measured band satisfies this with `(10.4, 11)`; the constants are hypotheses.
* `isBigO_truth_of_shape` — under the shape and the prefactor bounds, the survivor
  density is a big-Theta of the model `θ(β)^d · d^(-3/2)`: the two-sided comparison
  that turns "the upper bound is sharp up to the polynomial" from a reading of a plot
  into a theorem.
* `theta_bound_is_sharp_up_to_poly` — that Theta, packaged next to the proved upper
  bound `survivorDensity d ≤ rateBase^d` of `PaperBSurvivorDecay`, so the ledger row
  cites one symbol for the claim "the crude tilt is sharp up to `d^(3/2)`".

What this does NOT do.  It does not prove `MeanderShape` for any `ψ` — that is the
missing local limit theorem.  It does not change any proved density bound:
`PaperBSurvivorDecay.neverNegCount_div_pow_le_theta` is untouched, and the paper's
conditional Theorem 6.1 is unchanged.  Nothing here is a halt theorem.
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Asymptotics.Theta
import Problems.Juggler.PaperBSurvivorDecay
import Problems.Juggler.PaperBTilt

namespace Problems.Juggler

namespace PaperBSurvivorAsymptotic

open Filter Topology Real Asymptotics

/-- The survivor density `N_d / 2^d` as a real sequence. -/
noncomputable def survivorDensity (d : ℕ) : ℝ := (neverNegCount d : ℝ) / 2 ^ d

/-- The rate base: `PaperBChernoff.theta` at `PaperBThreshold.beta`. -/
noncomputable def rateBase : ℝ := PaperBChernoff.theta PaperBThreshold.beta

theorem rateBase_pos : 0 < rateBase := by
  have h0 : (0 : ℝ) < PaperBThreshold.beta := by
    linarith [PaperBThreshold.beta_gt_five_eighths]
  exact PaperBChernoff.theta_pos h0 PaperBThreshold.beta_lt_one

theorem rateBase_lt_one : rateBase < 1 := by
  have h0 : (0 : ℝ) < PaperBThreshold.beta := by
    linarith [PaperBThreshold.beta_gt_five_eighths]
  have hne : PaperBThreshold.beta ≠ 1 / 2 := by
    linarith [PaperBThreshold.beta_gt_five_eighths]
  exact PaperBChernoff.theta_lt_one h0 PaperBThreshold.beta_lt_one hne

/-- **The rate is an identity, not a measurement.**  The ledger's `ρ = θ(β)`,
recorded as a `1.1e-16` numerical agreement in
`J-theorem-six-one-threshold-is-slack`, is `rfl` between the two definitions. -/
theorem theta_beta_eq_rho :
    PaperBChernoff.theta PaperBThreshold.beta = PaperBTilt.rho PaperBTilt.beta := rfl

/-- The measured model sequence: `θ(β)^d · d^(-3/2)`. -/
noncomputable def model (d : ℕ) : ℝ := rateBase ^ d * (d : ℝ) ^ (-(3 : ℝ) / 2)

theorem model_pos {d : ℕ} (hd : 1 ≤ d) : 0 < model d := by
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  exact mul_pos (pow_pos rateBase_pos d) (Real.rpow_pos_of_pos hd' _)

/-- The measured asymptotic shape, as a predicate on the prefactor: the ratio of the
truth to `ψ(frac(d·β)) · θ(β)^d · d^(-3/2)` tends to `1`.  Stated, not proved: the
proof obligation is a local limit theorem for a lattice walk against a Sturmian
barrier, open in the laboratory. -/
def MeanderShape (psi : ℝ → ℝ) : Prop :=
  Tendsto
    (fun d : ℕ =>
      survivorDensity d /
        (model d * psi (Int.fract ((d : ℝ) * PaperBThreshold.beta))))
    atTop (𝓝 1)

/-- The prefactor hypotheses the comparisons need: `ψ` bounded above, and bounded
below away from zero, on `(0,1)`.  The measured band satisfies this with
`(10.4, 11)`; the constants stay hypotheses, because no theorem here fixes which `ψ`
the truth carries. -/
structure PrefactorBounds (psi : ℝ → ℝ) where
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  upper_pos : 0 < upper
  upper_le : ∀ x ∈ Set.Ioo 0 1, psi x ≤ upper
  lower_le : ∀ x ∈ Set.Ioo 0 1, lower ≤ psi x

/-- **Once the shape holds, the truth is a big-Theta of the model.**  With `ψ`
bounded on both sides of `0`, `survivorDensity = Θ(model)` along `atTop`: the ratio
tends to `1`, hence sits in `(1/2, 3/2)` eventually, and the bounded prefactor turns
that into the two linear comparisons of a Theta.  This is the formal content of "the
proved upper bound `θ(β)^d` is sharp up to the polynomial `d^(3/2)`": the model IS
`θ(β)^d · d^(-3/2)`, and bound and truth differ from it by the bounded prefactor
alone. -/
theorem isBigO_truth_of_shape {psi : ℝ → ℝ} (hshape : MeanderShape psi)
    (hb : PrefactorBounds psi)
    (hfrac : ∀ᶠ d : ℕ in atTop,
      Int.fract ((d : ℝ) * PaperBThreshold.beta) ∈ Set.Ioo 0 1) :
    survivorDensity =Θ[atTop] model := by
  have hlim : Tendsto
      (fun d : ℕ => survivorDensity d /
        (model d * psi (Int.fract ((d : ℝ) * PaperBThreshold.beta)))) atTop (𝓝 1) :=
    hshape
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨D, hD⟩ := hlim (1 / 2 : ℝ) (by norm_num)
  constructor
  · -- survivorDensity = O(model), with constant 3/2 * upper.
    refine isBigO_iff.mpr ⟨3 / 2 * hb.upper, ?_⟩
    filter_upwards [eventually_ge_atTop (max D 1), hfrac] with d hd hfd
    have hdge : d ≥ D := le_trans (le_max_left D 1) hd
    have hd1 : 1 ≤ d := le_trans (le_max_right D 1) hd
    have hdist := hD d hdge
    rw [Real.dist_eq, abs_lt] at hdist
    have hlow := hb.lower_le _ hfd
    have hupp := hb.upper_le _ hfd
    have hpsi_pos : (0 : ℝ) < psi (Int.fract ((d : ℝ) * PaperBThreshold.beta)) :=
      lt_of_lt_of_le hb.lower_pos hlow
    have hmodel_pos : (0 : ℝ) < model d := model_pos hd1
    have hden : (0 : ℝ) < model d * psi (Int.fract ((d : ℝ) * PaperBThreshold.beta)) :=
      mul_pos hmodel_pos hpsi_pos
    have hsd_nn : (0 : ℝ) ≤ survivorDensity d :=
      div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) d)
    rw [Real.norm_eq_abs, abs_of_nonneg hsd_nn,
      Real.norm_eq_abs, abs_of_nonneg hmodel_pos.le]
    have hlt := hdist.2
    have h1 : survivorDensity d <
        (3 / 2) * (model d * psi (Int.fract ((d : ℝ) * PaperBThreshold.beta))) := by
      have h2 : survivorDensity d /
          (model d * psi (Int.fract ((d : ℝ) * PaperBThreshold.beta))) < 3 / 2 := by
        linarith [hlt]
      exact (div_lt_iff₀ hden).mp h2
    calc survivorDensity d
        ≤ (3 / 2) * (model d * psi (Int.fract ((d : ℝ) * PaperBThreshold.beta))) :=
          le_of_lt h1
      _ ≤ (3 / 2) * (model d * hb.upper) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_left hupp hmodel_pos.le
      _ = (3 * hb.upper) * model d := by
          -- `ring` normalises `3/2` to `2⁻¹ * 3` on one side and not the other; use a
          -- field_simp on the goal to clear the denominator first.
          have h : (3 / 2 : ℝ) * (model d * hb.upper) = (3 * hb.upper) * model d := by
            field_simp
            ring
          exact h
  · -- model = O(survivorDensity), with constant 2 / lower.
    refine isBigO_iff.mpr ⟨2 / hb.lower, ?_⟩
    filter_upwards [eventually_ge_atTop (max D 1), hfrac] with d hd hfd
    have hdge : d ≥ D := le_trans (le_max_left D 1) hd
    have hd1 : 1 ≤ d := le_trans (le_max_right D 1) hd
    have hdist := hD d hdge
    rw [Real.dist_eq, abs_lt] at hdist
    have hlow := hb.lower_le _ hfd
    have hpsi_pos : (0 : ℝ) < psi (Int.fract ((d : ℝ) * PaperBThreshold.beta)) :=
      lt_of_lt_of_le hb.lower_pos hlow
    have hmodel_pos : (0 : ℝ) < model d := model_pos hd1
    have hden : (0 : ℝ) < model d * psi (Int.fract ((d : ℝ) * PaperBThreshold.beta)) :=
      mul_pos hmodel_pos hpsi_pos
    have hsd_pos : (0 : ℝ) < survivorDensity d := by
      have h1 := PaperBSurvivorDecay.one_le_neverNegCount d
      have h2 : (0 : ℝ) < (neverNegCount d : ℝ) := by exact_mod_cast h1
      exact div_pos h2 (by positivity)
    rw [Real.norm_eq_abs, abs_of_nonneg hmodel_pos.le,
      Real.norm_eq_abs, abs_of_nonneg hsd_pos.le]
    -- From the ratio > 1/2: survivorDensity > (1/2) * model * psi ≥ (1/2) * model *
    -- lower, hence model ≤ (2 / lower) * survivorDensity ≤ (3 / lower) * survivorDensity.
    have hgt := hdist.1
    have h1 : (1 / 2 : ℝ) * (model d * psi (Int.fract ((d : ℝ) * PaperBThreshold.beta))) <
        survivorDensity d := by
      have h2 : (1 / 2 : ℝ) < survivorDensity d /
          (model d * psi (Int.fract ((d : ℝ) * PaperBThreshold.beta))) := by
        linarith [hgt]
      exact (lt_div_iff₀ hden).mp h2
    have hstep : model d * hb.lower ≤ 2 * survivorDensity d := by
      have h3 : model d * hb.lower ≤
          model d * psi (Int.fract ((d : ℝ) * PaperBThreshold.beta)) :=
        mul_le_mul_of_nonneg_left hlow hmodel_pos.le
      linarith [h1, h3]
    calc model d
        = (model d * hb.lower) / hb.lower := by
          rw [mul_div_cancel_right₀ _ (ne_of_gt hb.lower_pos)]
      _ ≤ (2 * survivorDensity d) / hb.lower :=
          div_le_div_of_nonneg_right hstep hb.lower_pos.le
      _ = (2 / hb.lower) * survivorDensity d := by ring

/-- **The proved upper bound is sharp up to the polynomial.**  The laboratory's
`neverNegCount_div_pow_le_theta` says `survivorDensity ≤ rateBase^d` for every `d`;
the model is `rateBase^d · d^(-3/2)`.  Under the meander shape the truth is Theta of
the model, so the proved bound overshoots by exactly `d^(3/2)` times a bounded
prefactor — packaged here next to the bound itself, one symbol for the ledger. -/
theorem theta_bound_is_sharp_up_to_poly {psi : ℝ → ℝ} (hshape : MeanderShape psi)
    (hb : PrefactorBounds psi)
    (hfrac : ∀ᶠ d : ℕ in atTop,
      Int.fract ((d : ℝ) * PaperBThreshold.beta) ∈ Set.Ioo 0 1) :
    (survivorDensity =Θ[atTop] model) ∧ (∀ d : ℕ, survivorDensity d ≤ rateBase ^ d) :=
  ⟨isBigO_truth_of_shape hshape hb hfrac,
    fun d => PaperBSurvivorDecay.neverNegCount_div_pow_le_theta d⟩

end PaperBSurvivorAsymptotic

end Problems.Juggler

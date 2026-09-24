import Problems.Juggler.BeattyFiniteOccupation
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# A primitive for the tilted-profile occupation formula

The primitive of `g(y)/y` is differentiated only at positive arguments.
Its local Lipschitz bound provides summable domination of jump increments.
-/

namespace Problems.Juggler.BeattyPhase

open Filter Topology Set MeasureTheory Finset
open scoped BoundedContinuousFunction

/-- A primitive of the logarithmic occupation kernel, based at one. -/
noncomputable def occupationPrimitive (g : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ x in 1..y, g x / x

private theorem kernel_intervalIntegrable {g : ℝ → ℝ} (hg : Continuous g)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun y => g y / y) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply hg.continuousOn.div continuousOn_id
  intro y hy
  exact (lt_of_lt_of_le (lt_min ha hb) hy.1).ne'

/-- The occupation primitive has the expected derivative at every positive value. -/
theorem occupationPrimitive_hasDerivAt {g : ℝ → ℝ} (hg : Continuous g)
    {y : ℝ} (hy : 0 < y) :
    HasDerivAt (occupationPrimitive g) (g y / y) y := by
  exact intervalIntegral.integral_hasDerivAt_right
    (kernel_intervalIntegrable hg zero_lt_one hy)
    (hg.measurable.div measurable_id).stronglyMeasurable.stronglyMeasurableAtFilter
    (hg.continuousAt.div continuousAt_id hy.ne')

/-- Differences of primitive values are ordinary logarithmic kernel integrals. -/
theorem occupationPrimitive_sub {g : ℝ → ℝ} (hg : Continuous g)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    occupationPrimitive g b - occupationPrimitive g a = ∫ y in a..b, g y / y := by
  unfold occupationPrimitive
  exact (intervalIntegral.integral_add_adjacent_intervals
    (kernel_intervalIntegrable hg zero_lt_one ha) (kernel_intervalIntegrable hg ha hb)).symm
    |> fun h => by linarith

/-- A positive lower bound on the value interval controls every primitive
increment by its length, uniformly for bounded continuous observables. -/
theorem occupationPrimitive_sub_bound (g : ℝ →ᵇ ℝ) {q a b : ℝ}
    (hq : 0 < q) (ha : q ≤ a) (hb : q ≤ b) :
    ‖occupationPrimitive g b - occupationPrimitive g a‖ ≤ ‖g‖ / q * |b-a| := by
  rw [occupationPrimitive_sub g.continuous (hq.trans_le ha) (hq.trans_le hb)]
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro y hy
  have hqy : q ≤ y := le_trans (le_min ha hb) hy.1.le
  have hypos := hq.trans_le hqy
  rw [norm_div, Real.norm_eq_abs y, abs_of_pos hypos]
  exact div_le_div₀ (norm_nonneg g) (g.norm_coe_le_norm y) hq hqy

/-- Exact finite-cutoff occupation identity, with its endpoint correction.
No total-mass or periodic-endpoint hypothesis is used. -/
theorem finiteJumpProfile_occupation {phase w : ℕ → ℝ}
    (hi : Function.Injective phase) (hw : ∀ i, 0 ≤ w i)
    {q : ℝ} (hq : 0 < q) (g : ℝ →ᵇ ℝ) (s : Finset ℕ)
    (hp : ∀ i ∈ s, phase i ∈ Ioo (0 : ℝ) 1) :
    (-Real.log q) * (∫ t in (0 : ℝ)..1, g (q^t * finiteJumpProfile s phase w 1 t)) =
      (∑ i ∈ s, (occupationPrimitive g (q^(phase i) *
          (finiteJumpProfile s phase w 1 (phase i) + w i)) -
        occupationPrimitive g (q^(phase i) * finiteJumpProfile s phase w 1 (phase i)))) +
      occupationPrimitive g 1 - occupationPrimitive g (q * (1 + ∑ i ∈ s, w i)) := by
  let P := fun t c : ℝ => occupationPrimitive g (q^t*c)
  let D := fun t c : ℝ => Real.log q*g (q^t*c)
  have hD (c : ℝ) (_ : 0 < c) : Continuous (fun t => D t c) :=
    (g.continuous.comp ((Real.continuous_const_rpow hq.ne').mul continuous_const)).const_mul _
  have hP (c : ℝ) (hc : 0 < c) (t : ℝ) : HasDerivAt (fun t => P t c) (D t c) t := by
    have hpos : 0 < q^t*c := mul_pos (Real.rpow_pos_of_pos hq t) hc
    have h := (occupationPrimitive_hasDerivAt g.continuous hpos).comp t
      (((hasDerivAt_id t).const_rpow hq).mul_const c)
    convert h using 1 <;> first | rfl | (dsimp [P, D]; field_simp)
  have h := (finiteJumpProfile_integral_chain hi hw hD hP s zero_lt_one zero_le_one hp).2
  dsimp only [P, D] at h
  rw [intervalIntegral.integral_const_mul] at h
  simp only [Real.rpow_zero, one_mul, Real.rpow_one] at h
  linarith

end Problems.Juggler.BeattyPhase

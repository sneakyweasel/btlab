import Problems.Juggler.BeattyOccupationPrimitive
import Problems.Juggler.BeattyPhaseTransfer
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The occupation identity for a summable dense jump profile

Finite cutoffs converge under a summable bound on the primitive increments.
The endpoint term disappears precisely when `q * (1 + sum w) = 1`.
The phases may be dense; no continuity of the jump profile is assumed.
-/

namespace Problems.Juggler.BeattyPhase

open Filter Topology Set MeasureTheory Finset
open scoped BoundedContinuousFunction

/-- Finite chronological cutoffs converge at every phase, including atoms. -/
theorem finiteJumpProfile_tendsto {phase w : ℕ → ℝ} (hw : Summable w)
    (hn : ∀ i, 0 ≤ w i) (t : ℝ) :
    Tendsto (fun N => finiteJumpProfile (Finset.range N) phase w 1 t)
      atTop (𝓝 (jumpProfile phase w t)) := by
  have hs : Summable (fun i => if phase i < t then w i else 0) :=
    hw.of_norm_bounded (fun i => by
      split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg (hn i), hn i])
  exact hs.hasSum.tendsto_sum_nat.const_add 1

private theorem tilted_lower {q z t : ℝ} (hq : 0 < q) (hq1 : q ≤ 1)
    (ht : t ≤ 1) (hz : 1 ≤ z) : q ≤ q^t*z := by
  have hpow : q ≤ q^t := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hq hq1 ht
  exact hpow.trans (le_mul_of_one_le_right (Real.rpow_pos_of_pos hq t).le hz)

private theorem increment_bound (g : ℝ →ᵇ ℝ) {q t z v : ℝ}
    (hq : 0 < q) (hq1 : q ≤ 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hz : 1 ≤ z) (hv : 0 ≤ v) :
    ‖occupationPrimitive g (q^t*(z+v)) - occupationPrimitive g (q^t*z)‖ ≤
      (‖g‖/q)*v := by
  have hpowpos := (Real.rpow_pos_of_pos hq t).le
  have hpowle : q^t ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_ge hq hq1 ht.1
  have hlo := tilted_lower hq hq1 ht.2 hz
  have hhi : q ≤ q^t*(z+v) := hlo.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hv) hpowpos)
  have h := occupationPrimitive_sub_bound g hq hlo hhi
  have he : q^t*(z+v)-q^t*z = q^t*v := by ring
  rw [he, abs_of_nonneg (mul_nonneg hpowpos hv)] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (mul_le_of_le_one_left hv hpowle) (div_nonneg (norm_nonneg _) hq.le))

/-- The logarithmic primitive increments form the exact occupation law.
Summability and the endpoint mass identity suffice, even for dense phases. -/
theorem jumpProfile_occupation_hasSum {phase w : ℕ → ℝ}
    (hi : Function.Injective phase) (hw : Summable w) (hn : ∀ i, 0 ≤ w i)
    (hp : ∀ i, phase i ∈ Ioo (0 : ℝ) 1)
    {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (hmass : q*(1+∑' i, w i) = 1)
    (g : ℝ →ᵇ ℝ) :
    HasSum (fun i => occupationPrimitive g (q^(phase i)*(jumpProfile phase w (phase i)+w i)) -
      occupationPrimitive g (q^(phase i)*jumpProfile phase w (phase i)))
      ((-Real.log q)*(∫ t in (0 : ℝ)..1, g (q^t*jumpProfile phase w t))) := by
  classical
  let F (N : ℕ) (t : ℝ) := finiteJumpProfile (Finset.range N) phase w 1 t
  let J (f : ℝ → ℝ) (i : ℕ) := occupationPrimitive g (q^(phase i)*(f (phase i)+w i)) -
    occupationPrimitive g (q^(phase i)*f (phase i))
  let K (N i : ℕ) := if i < N then J (F N) i else 0
  have hF (t : ℝ) : Tendsto (fun N => F N t) atTop (𝓝 (jumpProfile phase w t)) :=
    finiteJumpProfile_tendsto hw hn t
  have hJ (i : ℕ) : Tendsto (fun N => J (F N) i) atTop (𝓝 (J (jumpProfile phase w) i)) := by
    have hpos : 0 < q^(phase i)*jumpProfile phase w (phase i) :=
      mul_pos (Real.rpow_pos_of_pos hq _) (zero_lt_one.trans_le (jumpProfile_bounds hw hn _).1)
    have hpos' : 0 < q^(phase i)*(jumpProfile phase w (phase i)+w i) :=
      mul_pos (Real.rpow_pos_of_pos hq _)
        (lt_of_lt_of_le (zero_lt_one.trans_le (jumpProfile_bounds hw hn _).1)
          (le_add_of_nonneg_right (hn i)))
    exact ((occupationPrimitive_hasDerivAt g.continuous hpos').continuousAt.tendsto.comp
      (((hF (phase i)).add_const (w i)).const_mul _)).sub
        ((occupationPrimitive_hasDerivAt g.continuous hpos).continuousAt.tendsto.comp
          ((hF (phase i)).const_mul _))
  have hK (i : ℕ) : Tendsto (fun N => K N i) atTop (𝓝 (J (jumpProfile phase w) i)) := by
    apply (hJ i).congr'
    filter_upwards [eventually_gt_atTop i] with N hN
    simp [K, hN]
  have hb (N i : ℕ) : ‖K N i‖ ≤ (‖g‖/q)*w i := by
    dsimp [K]
    split_ifs
    · exact increment_bound g hq hq1 ⟨(hp i).1.le, (hp i).2.le⟩
        (finiteJumpProfile_bounds hn _ 1 _).1 (hn i)
    · simpa only [norm_zero, abs_zero] using mul_nonneg (div_nonneg (norm_nonneg g) hq.le) (hn i)
  have hsum := tendsto_tsum_of_dominated_convergence (hw.mul_left (‖g‖/q)) hK
    (Eventually.of_forall hb)
  have heq (N : ℕ) : (∑' i, K N i) = ∑ i ∈ Finset.range N, J (F N) i := by
    rw [tsum_eq_sum (s := Finset.range N) (fun i hi' => by
      simp only [Finset.mem_range] at hi'
      simp [K, hi'])]
    apply Finset.sum_congr rfl
    intro i hi'
    simp [K, Finset.mem_range.mp hi']
  simp only [heq] at hsum
  have hmeas (N : ℕ) : Measurable (fun t => g (q^t*F N t)) :=
    g.continuous.measurable.comp ((Real.continuous_const_rpow hq.ne').measurable.mul
      (finiteJumpProfile_monotone hn (Finset.range N) 1).measurable)
  have hint : Tendsto (fun N => ∫ t in (0 : ℝ)..1, g (q^t*F N t)) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, g (q^t*jumpProfile phase w t))) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => ‖g‖)
    · exact Eventually.of_forall fun N => (hmeas N).aestronglyMeasurable
    · exact Eventually.of_forall fun N => Eventually.of_forall fun t _ => g.norm_coe_le_norm _
    · exact intervalIntegrable_const
    · exact Eventually.of_forall fun t _ => g.continuous.continuousAt.tendsto.comp
        ((hF t).const_mul (q^t))
  have hend : Tendsto (fun N => occupationPrimitive g (q*(1+∑ i ∈ Finset.range N, w i)))
      atTop (𝓝 (occupationPrimitive g 1)) := by
    have h := (occupationPrimitive_hasDerivAt g.continuous zero_lt_one).continuousAt.tendsto
    apply h.comp
    simpa only [hmass] using (hw.hasSum.tendsto_sum_nat.const_add 1).const_mul q
  have hfinite (N : ℕ) : (∑ i ∈ Finset.range N, J (F N) i) =
      (-Real.log q)*(∫ t in (0 : ℝ)..1, g (q^t*F N t)) - occupationPrimitive g 1 +
        occupationPrimitive g (q*(1+∑ i ∈ Finset.range N, w i)) := by
    have h := finiteJumpProfile_occupation hi hn hq g (Finset.range N) (fun i _ => hp i)
    dsimp [F, J]
    linarith
  have hlim := ((hint.const_mul (-Real.log q)).sub_const (occupationPrimitive g 1)).add hend
  simp only [sub_add_cancel, ← hfinite] at hlim
  have hjb (i : ℕ) : ‖J (jumpProfile phase w) i‖ ≤ (‖g‖/q)*w i :=
    increment_bound g hq hq1 ⟨(hp i).1.le, (hp i).2.le⟩ (jumpProfile_bounds hw hn _).1 (hn i)
  have hsj : Summable (J (jumpProfile phase w)) := (hw.mul_left (‖g‖/q)).of_norm_bounded hjb
  have hvalue := tendsto_nhds_unique hsum hlim
  exact hvalue ▸ hsj.hasSum

/-- Integral form of the occupation identity, with the actual rescaled
jump intervals as summands. -/
theorem jumpProfile_kernel_occupation_hasSum {phase w : ℕ → ℝ}
    (hi : Function.Injective phase) (hw : Summable w) (hn : ∀ i, 0 ≤ w i)
    (hp : ∀ i, phase i ∈ Ioo (0 : ℝ) 1)
    {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (hmass : q*(1+∑' i, w i) = 1)
    (g : ℝ →ᵇ ℝ) :
    HasSum (fun i => ∫ y in (q^(phase i)*jumpProfile phase w (phase i))..
      (q^(phase i)*(jumpProfile phase w (phase i)+w i)), g y/y)
      ((-Real.log q)*(∫ t in (0 : ℝ)..1, g (q^t*jumpProfile phase w t))) := by
  convert jumpProfile_occupation_hasSum hi hw hn hp hq hq1 hmass g using 1
  funext i
  have hpos := zero_lt_one.trans_le (jumpProfile_bounds (phase := phase) hw hn (phase i)).1
  exact (occupationPrimitive_sub g.continuous
    (mul_pos (Real.rpow_pos_of_pos hq _) hpos)
    (mul_pos (Real.rpow_pos_of_pos hq _) (lt_of_lt_of_le hpos
      (le_add_of_nonneg_right (hn i))))).symm

end Problems.Juggler.BeattyPhase

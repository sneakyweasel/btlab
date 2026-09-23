import Problems.Juggler.BeattyWeakConvergence
import Problems.Juggler.BeattyCertificateCluster
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Equidistribution of the certificate phases

Irrational linear phases have vanishing nonconstant Fourier averages. Weyl's
criterion gives Haar measure on the circle; the almost-everywhere continuous
choice of representative then gives uniform measure on the real unit interval.
-/

namespace Problems.Juggler.BeattyPhase

open Filter Topology Set Finset
open MeasureTheory hiding average
open scoped ENNReal
open BTCalculus.WeylDifferencing UnitAddTorus

/-- An irrational real angle is not a root of the exponential phase at one. -/
theorem phase_ne_one_of_irrational {a : ℝ} (ha : Irrational a) : phase a ≠ 1 := by
  intro he
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 he
  have hi := congrArg Complex.im hm
  simp [Complex.mul_im, Complex.mul_re] at hi
  have he' : a = (m : ℝ) := by nlinarith [Real.pi_pos]
  exact ha.ne_rational m 1 (by simpa using he')

/-- Every irrational linear exponential phase has zero limiting average.
The geometric sum is bounded uniformly in its length. -/
theorem tendsto_irrational_phase_average {a : ℝ} (ha : Irrational a) :
    Tendsto (average (fun n => phase ((n : ℝ)*a))) atTop (𝓝 0) := by
  have he (n : ℕ) : phase ((n : ℝ)*a) = phase a ^ n := by
    unfold phase
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hb (N : ℕ) : ‖∑ n ∈ range N, phase ((n : ℝ)*a)‖ ≤ 2 / ‖phase a - 1‖ := by
    simp_rw [he]
    rw [geom_sum_eq (phase_ne_one_of_irrational ha), norm_div]
    apply div_le_div_of_nonneg_right _ (norm_nonneg _)
    calc
      ‖phase a ^ N - 1‖ ≤ ‖phase a ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by norm_num [norm_pow, phase_norm]
  apply squeeze_zero_norm (a := fun N : ℕ => (2 / ‖phase a - 1‖) / (N : ℝ))
    _ (tendsto_const_div_atTop_nhds_zero_nat _)
  intro N
  simpa only [average, norm_div, Complex.norm_natCast] using
    div_le_div_of_nonneg_right (hb N) (Nat.cast_nonneg N : (0 : ℝ) ≤ N)

/-- Uniform probability measure on the real unit phase interval. -/
noncomputable def unitPhaseLaw : ProbabilityMeasure ℝ :=
  ⟨volume.restrict (Ioc 0 1), by constructor; simp⟩

private noncomputable def circleLaw : ProbabilityMeasure UnitAddCircle :=
  ⟨AddCircle.haarAddCircle, inferInstance⟩

private theorem irrational_circle_empirical {a : ℝ} (ha : Irrational a) :
    Tendsto (empiricalLaw (fun n => ((n : ℝ)*a : UnitAddCircle))) atTop
      (𝓝 circleLaw) := by
  let : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
  let : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
    inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
  let x : ℕ → UnitAddTorus Unit := fun n _ => ↑((n : ℝ)*a)
  have hx : ∀ k : Unit → ℤ, k ≠ 0 →
      Tendsto (average (fun n => mFourier k (x n))) atTop (𝓝 0) := by
    intro k hk
    have hk' : k () ≠ 0 := by
      intro he
      apply hk
      funext i
      cases i
      exact he
    have h := tendsto_irrational_phase_average (ha.intCast_mul hk')
    simpa only [x, BTCalculus.FourierBoxRecurrence.mFourier_real_eq_phase,
      Fintype.sum_unique, mul_left_comm] using h
  have ht := BTCalculus.FourierBoxCounting.tendsto_empirical x hx
  have hm := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    _ _ ht (continuous_apply ())
  have hp := measurePreserving_eval (fun _ : Unit => (volume : Measure UnitAddCircle)) ()
  have hl : ProbabilityMeasure.map (⟨volume, inferInstance⟩ : ProbabilityMeasure (UnitAddTorus Unit))
      (continuous_apply ()).measurable.aemeasurable = circleLaw := by
    apply Subtype.ext
    exact hp.map_eq
  change Tendsto (fun N => (empiricalLaw x N).map
    (continuous_apply ()).measurable.aemeasurable) _ _ at hm
  simpa only [empiricalLaw_map _ (continuous_apply ()).measurable, hl, x] using hm

private noncomputable def circleRepresentative (x : UnitAddCircle) : ℝ :=
  (AddCircle.equivIoc (1 : ℝ) 0 x : ℝ)

private theorem measurable_circleRepresentative : Measurable circleRepresentative :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIoc (1 : ℝ) 0).measurable

private theorem circleRepresentative_preserves :
    MeasurePreserving circleRepresentative (circleLaw : Measure UnitAddCircle)
      (unitPhaseLaw : Measure ℝ) := by
  change MeasurePreserving (Subtype.val ∘ AddCircle.equivIoc (1 : ℝ) 0)
    AddCircle.haarAddCircle (volume.restrict (Ioc (0 : ℝ) 1))
  have h := (measurePreserving_subtype_coe (measurableSet_Ioc (a := (0 : ℝ)) (b := 0+1))).comp
    (AddCircle.measurePreserving_equivIoc (1 : ℝ) (a := 0))
  simpa only [AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul,
    zero_add] using h

private theorem circleRepresentative_ae_continuous :
    ∀ᵐ x ∂(circleLaw : Measure UnitAddCircle), ContinuousAt circleRepresentative x := by
  have hz : (circleLaw : Measure UnitAddCircle) {0} = 0 := by
    have h := AddCircle.volume_closedBall (T := 1) (x := 0) 0
    simpa only [Metric.closedBall_zero, AddCircle.volume_eq_smul_haarAddCircle,
      ENNReal.ofReal_one, one_smul, mul_zero, min_eq_right zero_le_one,
      ENNReal.ofReal_zero, circleLaw, ProbabilityMeasure.coe_mk] using h
  have hzero : ∀ᵐ x ∂(circleLaw : Measure UnitAddCircle), x ≠ 0 := by
    simpa only [ae_iff, not_not, Set.ofPred_eq_eq_singleton] using hz
  filter_upwards [hzero] with x hx
  exact continuous_subtype_val.continuousAt.comp
    (AddCircle.continuousAt_equivIoc (1 : ℝ) 0 (by simpa using hx))

/-- The exact certificate phases have the uniform empirical limiting law. -/
theorem certificatePhase_equidistributed :
    Tendsto (empiricalLaw certificatePhase) atTop (𝓝 unitPhaseLaw) := by
  have hm := tendsto_probability_map_of_ae_continuous
    (irrational_circle_empirical certificateSlope_irrational)
    measurable_circleRepresentative circleRepresentative_ae_continuous
  have hl : circleLaw.map measurable_circleRepresentative.aemeasurable = unitPhaseLaw := by
    apply Subtype.ext
    exact circleRepresentative_preserves.map_eq
  simp only [empiricalLaw_map _ measurable_circleRepresentative, hl] at hm
  apply empiricalLaw_tendsto_of_sub_tendsto_zero hm
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hp : certificatePhase n ∈ Ioc (0 : ℝ) (0+1) :=
    ⟨certificatePhase_pos hn, by linarith [(certificatePhase_mem_Ico n).2]⟩
  have he : (certificatePhase n : UnitAddCircle) = ↑((n : ℝ)*(1/PaperBThreshold.beta)) := by
    rw [certificatePhase_eq_fract, AddCircle.coe_fract]
    congr 1
    ring
  simp only [circleRepresentative, ← he, AddCircle.equivIoc_coe_eq hp,
    sub_self]

end Problems.Juggler.BeattyPhase

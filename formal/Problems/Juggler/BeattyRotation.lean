import Problems.Juggler.BeattyWeakConvergence
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Recurrence and equidistribution of irrational rotations

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

/-- Every positive multiple of an irrational angle has fractional part
strictly inside the unit interval. -/
theorem irrational_rotation_fract_pos {a : ℝ} (ha : Irrational a) {n : ℕ} (hn : 0 < n) :
    0 < Int.fract ((n : ℝ)*a) := by
  apply lt_of_le_of_ne (Int.fract_nonneg _)
  intro he
  apply (ha.natCast_mul (by omega : n ≠ 0)).ne_int ⌊(n : ℝ)*a⌋
  have hf := Int.floor_add_fract ((n : ℝ)*a)
  linarith

/-- Every open unit subinterval is visited arbitrarily late by the
fractional parts of the nonnegative multiples of any irrational angle. -/
theorem irrational_rotation_recurrent {a : ℝ} (ha : Irrational a)
    (u v : ℝ) (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ 1) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ Int.fract ((n : ℝ)*a) ∈ Ioo u v := by
  let slope : AddCircle (1 : ℝ) := ↑a
  have hd : DenseRange (fun n : ℤ => n • slope) :=
    AddCircle.denseRange_zsmul_coe_iff.2 (by simpa using ha)
  obtain ⟨x, hux, hxv⟩ := exists_between huv
  have hc : MapClusterPt (↑x : AddCircle (1 : ℝ)) atTop (fun n : ℕ => n • slope) :=
    (mapClusterPt_atTop_nsmul_tfae (↑x : AddCircle (1 : ℝ)) slope).out 3 0 |>.mp
      (hd (↑x))
  let U : Set (AddCircle (1 : ℝ)) := (fun x : ℝ => (↑x : AddCircle (1 : ℝ))) '' Ioo u v
  have hU : IsOpen U := QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  have hxU : (↑x : AddCircle (1 : ℝ)) ∈ U := ⟨x, ⟨hux, hxv⟩, rfl⟩
  obtain ⟨n, hn, hnU⟩ := frequently_atTop.1 (hc.frequently (hU.mem_nhds hxU)) N
  obtain ⟨y, hy, he⟩ := hnU
  have hphase : (↑(Int.fract ((n : ℝ)*a)) : AddCircle (1 : ℝ)) = n • slope := by
    rw [AddCircle.coe_fract, ← AddCircle.coe_nsmul, nsmul_eq_mul]
  have hny : Int.fract ((n : ℝ)*a) = y := by
    apply AddCircle.coe_eq_coe_iff_of_mem_Ico
      (p := (1 : ℝ)) (a := 0)
      (by simpa using And.intro (Int.fract_nonneg ((n : ℝ)*a)) (Int.fract_lt_one ((n : ℝ)*a)))
      (by constructor <;> linarith [hy.1, hy.2]) |>.1
    exact hphase.trans he.symm
  exact ⟨n, hn, hny.symm ▸ hy⟩

/-- Fractional parts of the multiples of every irrational real angle have
uniform limiting empirical law on the unit interval. -/
theorem irrational_rotation_equidistributed {a : ℝ} (ha : Irrational a) :
    Tendsto (empiricalLaw (fun n : ℕ => Int.fract ((n : ℝ)*a))) atTop (𝓝 unitPhaseLaw) := by
  have hm := tendsto_probability_map_of_ae_continuous
    (irrational_circle_empirical ha)
    measurable_circleRepresentative circleRepresentative_ae_continuous
  have hl : circleLaw.map measurable_circleRepresentative.aemeasurable = unitPhaseLaw := by
    apply Subtype.ext
    exact circleRepresentative_preserves.map_eq
  simp only [empiricalLaw_map _ measurable_circleRepresentative, hl] at hm
  apply empiricalLaw_tendsto_of_sub_tendsto_zero hm
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hp : Int.fract ((n : ℝ)*a) ∈ Ioc (0 : ℝ) (0+1) :=
    ⟨irrational_rotation_fract_pos ha hn, by linarith [Int.fract_lt_one ((n : ℝ)*a)]⟩
  simp only [circleRepresentative, ← AddCircle.coe_fract ((n : ℝ)*a),
    AddCircle.equivIoc_coe_eq hp, sub_self]

end Problems.Juggler.BeattyPhase

import Problems.Juggler.BeattySlopeCantor
import Problems.Juggler.BeattySlopeDistribution
import Problems.Juggler.BeattyDiophantineHitting

/-!
# Hausdorff measure of the cluster set for every irrational slope

The cube-root tube bound gives finite two-thirds Hausdorff measure for every
irrational boundary in `(0,1)`. Polynomial phase hitting, and hence a uniform
Diophantine lower bound for the slope `1/β`, gives Hölder regularity of the
limiting distribution function and positive Hausdorff measure at the matching
exponent. The arithmetic premises are explicit arguments.
-/

namespace Problems.Juggler.BeattySlope

open Filter Topology Set MeasureTheory BeattyPhase
open scoped NNReal ENNReal

variable {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ : Irrational β)

include hβ0 hβ1 hβ

/-- Every family cluster set has finite two-thirds Hausdorff measure. -/
theorem passageCluster_hausdorff_ne_top :
    Measure.hausdorffMeasure (2/3 : ℝ) (passageClusterSet β) ≠ ⊤ := by
  obtain ⟨c,C,_,_,h⟩ := passageClusterSet_tube_bounds hβ0 hβ1 hβ
  exact hausdorffMeasure_two_thirds_ne_top_of_tube_bound (isCompact_passageClusterSet hβ0 hβ1 hβ)
    (fun ε hε hsmall => (h ε hε hsmall).2)

/-- Every family cluster set has Hausdorff dimension at most two-thirds. -/
theorem passageCluster_dimH_le : dimH (passageClusterSet β) ≤ (2/3 : ℝ≥0∞) := by
  simpa using dimH_le_of_hausdorffMeasure_ne_top
    (d := (2/3 : ℝ≥0)) (passageCluster_hausdorff_ne_top hβ0 hβ1 hβ)

/-- The continuous distribution function of the family passage law. -/
noncomputable def passageCdf (y : ℝ) : ℝ :=
  ((passageLaw hβ0 hβ1 hβ : ProbabilityMeasure ℝ) : Measure ℝ).real (Iic y)

/-- The family distribution function is monotone. -/
theorem passageCdf_monotone : Monotone (passageCdf hβ0 hβ1 hβ) :=
  fun _ _ h => measureReal_mono (Iic_subset_Iic.2 h)

/-- The family distribution function takes values in the unit interval. -/
theorem passageCdf_bounds (y : ℝ) : passageCdf hβ0 hβ1 hβ y ∈ Icc (0 : ℝ) 1 := by
  refine ⟨measureReal_nonneg, ?_⟩
  simp [passageCdf]

/-- The distribution function inverts the profile on the unit interval. -/
theorem passageCdf_profile {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    passageCdf hβ0 hβ1 hβ (passageProfile β t) = t := by
  simp only [passageCdf, Measure.real, passageLaw_Iic_profile hβ0 hβ1 hβ ht,
    ENNReal.toReal_ofReal ht.1]

/-- The distribution function is constant on each closed gap. -/
theorem passageCdf_gap (n : ℕ) {y : ℝ}
    (hy : y ∈ Icc (passageProfile β (passagePhase β (n+1)))
      (passageProfile β (passagePhase β (n+1))+passageJumpWeight β (n+1))) :
    passageCdf hβ0 hβ1 hβ y = passagePhase β (n+1) := by
  simp only [passageCdf, Measure.real, passageLaw_Iic_gap hβ0 hβ1 hβ n hy,
    ENNReal.toReal_ofReal (passagePhase_mem_Ico hβ0 _).1]

/-- The distribution function maps the cluster set onto the unit interval. -/
theorem passageCdf_image_cluster :
    passageCdf hβ0 hβ1 hβ '' passageClusterSet β = Icc (0 : ℝ) 1 := by
  apply Subset.antisymm
  · rintro _ ⟨y,_,rfl⟩
    exact passageCdf_bounds hβ0 hβ1 hβ y
  · intro t ht
    refine ⟨passageProfile β t, ?_, passageCdf_profile hβ0 hβ1 hβ ht⟩
    rw [passageClusterSet_eq_closure_range hβ0 hβ1 hβ]
    exact subset_closure (mem_range_self t)

private theorem gap_between_cdf {x y : ℝ} {n : ℕ}
    (hn : passagePhase β (n+1) ∈
      Ioo (passageCdf hβ0 hβ1 hβ x) (passageCdf hβ0 hβ1 hβ y)) :
    passageJumpWeight β (n+1) ≤ y-x := by
  have hI : passagePhase β (n+1) ∈ Icc (0 : ℝ) 1 :=
    ⟨(passagePhase_mem_Ico hβ0 _).1, (passagePhase_mem_Ico hβ0 _).2.le⟩
  have hl : x < passageProfile β (passagePhase β (n+1)) := by
    by_contra h
    have hm := passageCdf_monotone hβ0 hβ1 hβ (le_of_not_gt h)
    rw [passageCdf_profile hβ0 hβ1 hβ hI] at hm
    exact (not_lt_of_ge hm) hn.1
  have hu : passageProfile β (passagePhase β (n+1))+passageJumpWeight β (n+1) < y := by
    by_contra h
    have hm := passageCdf_monotone hβ0 hβ1 hβ (le_of_not_gt h)
    rw [passageCdf_gap hβ0 hβ1 hβ n
      ⟨by linarith [passageJumpWeight_nonneg hβ0 hβ1 (n+1)], le_rfl⟩] at hm
    exact (not_lt_of_ge hm) hn.2
  linarith

private theorem weight_power_lower :
    ∃ A : ℝ, 0 < A ∧ ∀ n : ℕ,
      A ≤ ((n : ℝ)+1)*passageJumpWeight β (n+1)^(2/3 : ℝ) := by
  obtain ⟨a,b,ha,_,hw⟩ := passageWeight_three_halves hβ0 hβ1 hβ
  refine ⟨a^(2/3 : ℝ), Real.rpow_pos_of_pos ha _, fun n => ?_⟩
  have h := Real.rpow_le_rpow (by positivity : 0 ≤ a/((n : ℝ)+1)^(3/2 : ℝ))
    (hw n).1 (by norm_num : (0 : ℝ) ≤ 2/3)
  rw [Real.div_rpow ha.le (Real.rpow_nonneg (by positivity) _),
    ← Real.rpow_mul (by positivity : 0 ≤ (n : ℝ)+1)] at h
  norm_num at h
  exact (div_le_iff₀ (by positivity : 0 < (n : ℝ)+1)).1 h |>.trans_eq (mul_comm _ _)

/-- Polynomial phase hitting with exponent `τ` gives a global Hölder bound
of exponent `2/(3τ)` for the family distribution function. -/
theorem passageCdf_holder {H τ : ℝ} (hH : 0 < H) (hτ : 0 < τ)
    (hh : PhaseHittingBound (fun n => passagePhase β (n+1)) H τ) :
    ∃ C : ℝ≥0, HolderWith C ⟨(2/3 : ℝ)/τ, by positivity⟩ (passageCdf hβ0 hβ1 hβ) := by
  obtain ⟨A,hA,hw⟩ := weight_power_lower hβ0 hβ1 hβ
  let G := passageCdf hβ0 hβ1 hβ
  let C : ℝ≥0 := ⟨(H/A)^(1/τ), Real.rpow_nonneg (div_nonneg hH.le hA.le) _⟩
  have hc (x y : ℝ) (hxy : x ≤ y) : G y-G x ≤ (C : ℝ)*(y-x)^((2/3 : ℝ)/τ) := by
    by_cases he : G x = G y
    · rw [he, sub_self]
      positivity
    have hp : 0 < G y-G x :=
      sub_pos.2 (lt_of_le_of_ne (passageCdf_monotone hβ0 hβ1 hβ hxy) he)
    obtain ⟨n,hn,hindex⟩ := hh _ _ (passageCdf_bounds hβ0 hβ1 hβ x).1
      (sub_pos.1 hp) (passageCdf_bounds hβ0 hβ1 hβ y).2
    have hgap := gap_between_cdf hβ0 hβ1 hβ hn
    have hpτ : 0 ≤ (G y-G x)^τ := Real.rpow_nonneg hp.le _
    have hw0 := passageJumpWeight_nonneg hβ0 hβ1 (n+1)
    have hpow := Real.rpow_le_rpow hw0 hgap (by norm_num : (0 : ℝ) ≤ 2/3)
    have hprod : A*(G y-G x)^τ ≤ H*(y-x)^(2/3 : ℝ) := by
      calc
        _ ≤ (((n : ℝ)+1)*passageJumpWeight β (n+1)^(2/3 : ℝ))*(G y-G x)^τ :=
          mul_le_mul_of_nonneg_right (hw n) hpτ
        _ = (((n : ℝ)+1)*(G y-G x)^τ)*passageJumpWeight β (n+1)^(2/3 : ℝ) := by ring
        _ ≤ H*passageJumpWeight β (n+1)^(2/3 : ℝ) :=
          mul_le_mul_of_nonneg_right hindex (Real.rpow_nonneg hw0 _)
        _ ≤ _ := mul_le_mul_of_nonneg_left hpow hH.le
    have hdiv : (G y-G x)^τ ≤ (H/A)*(y-x)^(2/3 : ℝ) := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hA).2
      simpa only [mul_comm] using hprod
    have hr := Real.rpow_le_rpow hpτ hdiv (by positivity : 0 ≤ 1/τ)
    rw [← Real.rpow_mul hp.le, Real.mul_rpow (div_nonneg hH.le hA.le)
      (Real.rpow_nonneg (sub_nonneg.2 hxy) _),
      ← Real.rpow_mul (sub_nonneg.2 hxy)] at hr
    change _ ≤ (H/A)^(1/τ)*(y-x)^((2/3 : ℝ)/τ)
    simpa [hτ.ne', div_eq_mul_inv] using hr
  have hmono : Monotone G := passageCdf_monotone hβ0 hβ1 hβ
  refine ⟨C, ?_⟩
  intro x y
  have hd : dist (G x) (G y) ≤ (C : ℝ)*dist x y^((2/3 : ℝ)/τ) := by
    rcases le_total x y with hxy | hyx
    · rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.2 (hmono hxy)),
        abs_of_nonpos (sub_nonpos.2 hxy), neg_sub, neg_sub]
      exact hc x y hxy
    · rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.2 (hmono hyx)),
        abs_of_nonneg (sub_nonneg.2 hyx)]
      exact hc y x hyx
  change edist (G x) (G y) ≤ (C : ℝ≥0∞)*edist x y^((2/3 : ℝ)/τ)
  simpa only [ENNReal.ofReal_mul C.coe_nonneg,
    ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_rpow_of_nonneg (dist_nonneg : 0 ≤ dist x y)
      (by positivity : 0 ≤ (2/3 : ℝ)/τ), ← edist_dist] using ENNReal.ofReal_le_ofReal hd

/-- Phase hitting gives positive Hausdorff measure at exponent `2/(3τ)`. -/
theorem passageCluster_hausdorff_pos {H τ : ℝ} (hH : 0 < H) (hτ : 0 < τ)
    (hh : PhaseHittingBound (fun n => passagePhase β (n+1)) H τ) :
    Measure.hausdorffMeasure ((2/3 : ℝ)/τ) (passageClusterSet β) ≠ 0 := by
  obtain ⟨C,hC⟩ := passageCdf_holder hβ0 hβ1 hβ hH hτ hh
  let r : ℝ≥0 := ⟨(2/3 : ℝ)/τ, by positivity⟩
  have hr : 0 < r := by change (0 : ℝ) < (2/3 : ℝ)/τ; positivity
  change HolderWith C r (passageCdf hβ0 hβ1 hβ) at hC
  have h := (hC.holderOnWith (passageClusterSet β)).hausdorffMeasure_image_le hr
    (d := 1) (by norm_num)
  rw [passageCdf_image_cluster, hausdorffMeasure_real, Real.volume_Icc] at h
  norm_num only [sub_zero, ENNReal.ofReal_one, ENNReal.rpow_one, mul_one] at h
  change (1 : ℝ≥0∞) ≤ (C : ℝ≥0∞)*
    Measure.hausdorffMeasure ((2/3 : ℝ)/τ) (passageClusterSet β) at h
  intro hz
  rw [hz, mul_zero] at h
  exact (not_le_of_gt zero_lt_one) h

/-- Phase hitting gives the Hausdorff dimension lower bound `2/(3τ)`. -/
theorem passageCluster_dimH_ge {H τ : ℝ} (hH : 0 < H) (hτ : 0 < τ)
    (hh : PhaseHittingBound (fun n => passagePhase β (n+1)) H τ) :
    ENNReal.ofReal ((2/3 : ℝ)/τ) ≤ dimH (passageClusterSet β) := by
  obtain ⟨C,hC⟩ := passageCdf_holder hβ0 hβ1 hβ hH hτ hh
  let r : ℝ≥0 := ⟨(2/3 : ℝ)/τ, by positivity⟩
  have hr : 0 < r := by change (0 : ℝ) < (2/3 : ℝ)/τ; positivity
  change HolderWith C r (passageCdf hβ0 hβ1 hβ) at hC
  have h := hC.dimH_image_le hr (passageClusterSet β)
  rw [passageCdf_image_cluster] at h
  have hI : dimH (Icc (0 : ℝ) 1) = 1 := by
    simpa only [segment_eq_Icc (by norm_num : (0 : ℝ) ≤ 1)] using
      (Real.dimH_segment (by norm_num : (0 : ℝ) ≠ 1))
  rw [hI] at h
  have hh' := (ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.coe_ne_zero.2 hr.ne'))
    (Or.inl ENNReal.coe_ne_top)).1 h
  rw [one_mul, ← ENNReal.ofReal_coe_nnreal] at hh'
  exact hh'

omit hβ1 hβ in
/-- A uniform Diophantine lower bound for the slope `1/β` supplies phase
hitting with the same exponent. -/
theorem passagePhase_hitting {c τ : ℝ} (hc : 0 < c) (hτ : 0 < τ)
    (hdio : DiophantineLowerBound (1/β) c τ) :
    PhaseHittingBound (fun n => passagePhase β (n+1)) (4^τ/c+1) τ := by
  have h := phaseHittingBound_of_diophantineLowerBound hc hτ hdio
  simpa only [PhaseHittingBound, passagePhase_eq_fract hβ0, mul_one_div] using h

/-- A uniform Diophantine lower bound gives positive Hausdorff measure at
exponent `2/(3τ)` for the actual cluster set. -/
theorem passageCluster_hausdorff_dio {c τ : ℝ} (hc : 0 < c) (hτ : 0 < τ)
    (hdio : DiophantineLowerBound (1/β) c τ) :
    Measure.hausdorffMeasure ((2/3 : ℝ)/τ) (passageClusterSet β) ≠ 0 :=
  passageCluster_hausdorff_pos hβ0 hβ1 hβ (by positivity) hτ
    (passagePhase_hitting hβ0 hc hτ hdio)

/-- Bad approximability of `1/β` gives positive finite two-thirds measure. -/
theorem passageCluster_hausdorff_bad {c : ℝ} (hc : 0 < c)
    (hdio : DiophantineLowerBound (1/β) c 1) :
    0 < Measure.hausdorffMeasure (2/3 : ℝ) (passageClusterSet β) ∧
    Measure.hausdorffMeasure (2/3 : ℝ) (passageClusterSet β) < ⊤ := by
  refine ⟨pos_iff_ne_zero.2 ?_, lt_top_iff_ne_top.2 (passageCluster_hausdorff_ne_top hβ0 hβ1 hβ)⟩
  simpa only [div_one] using passageCluster_hausdorff_dio hβ0 hβ1 hβ hc zero_lt_one hdio

/-- Diophantine bounds at every exponent above one give dimension `2/3`. -/
theorem passageCluster_dimH_eq
    (hdio : ∀ τ : ℝ, 1 < τ → ∃ c : ℝ, 0 < c ∧ DiophantineLowerBound (1/β) c τ) :
    dimH (passageClusterSet β) = (2/3 : ℝ≥0∞) := by
  apply le_antisymm (passageCluster_dimH_le hβ0 hβ1 hβ)
  have hcont : ContinuousAt (fun τ : ℝ => ENNReal.ofReal ((2/3 : ℝ)/τ)) 1 :=
    ENNReal.continuous_ofReal.continuousAt.comp
      (continuousAt_const.div continuousAt_id (by norm_num))
  have hlim := hcont.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (1 : ℝ) ≤ 𝓝 1)
  have hle : ENNReal.ofReal ((2/3 : ℝ)/1) ≤ dimH (passageClusterSet β) := by
    apply le_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    obtain ⟨c,hc,hbound⟩ := hdio τ hτ
    exact passageCluster_dimH_ge hβ0 hβ1 hβ (by positivity) (zero_lt_one.trans hτ)
      (passagePhase_hitting hβ0 hc (zero_lt_one.trans hτ) hbound)
  simpa only [div_one, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3),
    ENNReal.ofReal_ofNat] using hle

end Problems.Juggler.BeattySlope

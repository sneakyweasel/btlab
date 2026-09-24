import Problems.Juggler.BeattySlopeGammaConcentration
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# Subcritical integrability of the Gamma density for every slope

Layer cake turns the weak three-halves tail estimate into finite density
power integrals below that exponent, at every irrational `0<β<1`. This is
integrability of the density, not the real-power moments of the law.
-/

namespace Problems.Juggler.BeattySlope

open Filter Topology Set MeasureTheory
open scoped ENNReal

variable {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ : Irrational β)

include hβ0 hβ1 hβ

/-- The canonical density vanishes pointwise outside its positive compact
envelope, including points that are not covered by any rescaled jump. -/
theorem passageGammaDensity_envelope {y : ℝ}
    (hy : y ∉ Icc (1-β) (1/(1-β))) : passageGammaDensity β y = 0 := by
  unfold passageGammaDensity
  apply ENNReal.tsum_eq_zero.mpr
  intro r
  apply indicator_of_notMem
  intro hr
  exact hy ⟨(passageGammaJump_bounds hβ0 hβ1 hβ r).1.trans hr.1.le,
    hr.2.le.trans (passageGammaJump_bounds hβ0 hβ1 hβ r).2⟩

omit hβ0 hβ1 hβ in
private theorem real_density_superlevel_le {T : ℝ} (hT : 0 < T) :
    volume {y | T < (passageGammaDensity β y).toReal} ≤
      volume {y | ENNReal.ofReal T < passageGammaDensity β y} := by
  apply measure_mono
  intro y hy
  exact (ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨hy,hT.trans hy⟩).trans_le
    ENNReal.ofReal_toReal_le

private theorem real_density_superlevel_envelope {T : ℝ} (hT : 0 < T) :
    volume {y | T < (passageGammaDensity β y).toReal} ≤
      volume (Icc (1-β) (1/(1-β))) := by
  apply measure_mono
  intro y hy
  change T < (passageGammaDensity β y).toReal at hy
  by_contra hn
  rw [passageGammaDensity_envelope hβ0 hβ1 hβ hn, ENNReal.toReal_zero] at hy
  exact (hT.trans hy).false

private theorem power_integral_lt_top {p : ℝ} (hp : 1 ≤ p) (hp' : p < 3/2) :
    (∫⁻ y, ENNReal.ofReal ((passageGammaDensity β y).toReal^p)) < ∞ := by
  obtain ⟨D,hD,hd⟩ := passageGammaDensity_weak_three hβ0 hβ1 hβ
  let f : ℝ → ℝ≥0∞ := fun t => volume {y | t < (passageGammaDensity β y).toReal} *
    ENNReal.ofReal (t^(p-1))
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  rw [lintegral_rpow_eq_lintegral_meas_lt_mul volume
    (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
    (passageGammaDensity_measurable β).ennreal_toReal.aemeasurable hp0]
  apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
  change ∫⁻ t in Ioi 0, f t < ∞
  have hsmall : ∫⁻ t in Ioc (0 : ℝ) 1, f t < ∞ := by
    have hbound : ∫⁻ t in Ioc (0 : ℝ) 1, f t ≤
        volume (Icc (1-β) (1/(1-β)))*volume (Ioc (0 : ℝ) 1) := by
      rw [← setLIntegral_const]
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht0 : 0 < t := ht.1
      have hpow : ENNReal.ofReal (t^(p-1)) ≤ 1 := by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (Real.rpow_le_one ht0.le ht.2 (by linarith))
      exact (mul_le_mul' (real_density_superlevel_envelope hβ0 hβ1 hβ ht0) hpow).trans_eq (mul_one _)
    exact hbound.trans_lt (ENNReal.mul_lt_top (by simp) (by simp))
  have hlarge : ∫⁻ t in Ioi (1 : ℝ), f t < ∞ := by
    have hbound : ∫⁻ t in Ioi (1 : ℝ), f t ≤
        ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (D*t^(p-5/2 : ℝ)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := lt_trans zero_lt_one ht
      calc
        f t ≤ ENNReal.ofReal (D*t^(-3/2 : ℝ))*ENNReal.ofReal (t^(p-1)) :=
          mul_le_mul' ((real_density_superlevel_le ht0).trans (hd t ht0)) le_rfl
        _ = _ := by
          rw [← ENNReal.ofReal_mul (by positivity), mul_assoc, ← Real.rpow_add ht0]
          rw [show (-3/2 : ℝ)+(p-1) = p-5/2 by ring]
    apply hbound.trans_lt
    exact ((integrableOn_Ioi_rpow_of_lt (by linarith : p-5/2 < -1) zero_lt_one).const_mul D).lintegral_lt_top
  have he : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := by ext t; simp only [mem_Ioi, mem_union, mem_Ioc]; grind
  rw [he, lintegral_union measurableSet_Ioi (by
    rw [disjoint_left]; intro t ht ht'; exact (not_lt_of_ge ht.2) ht')]
  exact ENNReal.add_lt_top.mpr ⟨hsmall,hlarge⟩

/-- Every density power below three-halves and at least one has finite
Lebesgue integral. Infinite values on the null exceptional set are retained;
no endpoint or supercritical integrability claim is made. -/
theorem passageGammaDensity_rpow_lt_top {p : ℝ}
    (hp : 1 ≤ p) (hp' : p < 3/2) :
    (∫⁻ y, passageGammaDensity β y^p) < ∞ := by
  have he : (fun y => passageGammaDensity β y^p) =ᵐ[volume]
      (fun y => ENNReal.ofReal ((passageGammaDensity β y).toReal^p)) := by
    filter_upwards [passageGammaDensity_ae_lt_top hβ0 hβ1 hβ] with y hy
    exact (ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (zero_le_one.trans hp)).symm.trans
      (by rw [ENNReal.ofReal_toReal hy.ne]) |>.symm
  rw [lintegral_congr_ae he]
  exact power_integral_lt_top hβ0 hβ1 hβ hp hp'

/-- The almost-everywhere finite real representative of the density belongs
to `L^p` for every `1 ≤ p < 3/2`. Its zero values at infinite-density points
only choose a representative on a null set. -/
theorem passageGammaDensity_memLp {p : ℝ} (hp : 1 ≤ p) (hp' : p < 3/2) :
    MemLp (fun y => (passageGammaDensity β y).toReal) (ENNReal.ofReal p) volume := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  refine ⟨(passageGammaDensity_measurable β).ennreal_toReal.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp0.le]
  have he : (fun y => ‖(passageGammaDensity β y).toReal‖ₑ^p) =ᵐ[volume]
      (fun y => passageGammaDensity β y^p) := by
    filter_upwards [passageGammaDensity_ae_lt_top hβ0 hβ1 hβ] with y hy
    rw [Real.enorm_eq_ofReal ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hy.ne]
  rw [lintegral_congr_ae he]
  exact passageGammaDensity_rpow_lt_top hβ0 hβ1 hβ hp hp'

end Problems.Juggler.BeattySlope

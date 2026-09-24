import Problems.Juggler.BeattySlopeContinuity
import Problems.Juggler.BeattySlopeGammaLaw

/-!
# Slope continuity of the Gamma-normalized law

The Gamma amplitude `(1-β)^t F_β(t)` converges at every non-atom phase as
irrational boundaries approach an irrational boundary, so every bounded
continuous phase average converges: the absolutely continuous Gamma laws
depend weakly continuously on the slope, like the singular binomial laws.
-/

namespace Problems.Juggler.BeattySlope

open Filter Topology Set MeasureTheory
open scoped BoundedContinuousFunction

/-- The Gamma amplitude converges at every non-atom phase along irrational
boundaries approaching an irrational boundary. -/
theorem passageGammaAmp_tendsto {β₀ : ℝ} (hβ0 : 0 < β₀) (hβ1 : β₀ < 1) (hβ : Irrational β₀)
    {t : ℝ} (ht : ∀ r : ℕ, passagePhase β₀ (r+1) ≠ t) :
    Tendsto (fun β => passageGammaAmp β t) (irrNhds β₀) (𝓝 (passageGammaAmp β₀ t)) := by
  unfold passageGammaAmp
  have hq : Tendsto (fun β : ℝ => (1-β)^t) (𝓝 β₀) (𝓝 ((1-β₀)^t)) :=
    ((Real.continuousAt_rpow_const _ _ (Or.inl (by linarith))).tendsto).comp
      (tendsto_const_nhds.sub tendsto_id)
  exact (hq.mono_left nhdsWithin_le_nhds).mul (passageProfile_tendsto hβ0 hβ1 hβ ht)

/-- The Gamma-normalized laws converge weakly as irrational boundaries
approach an irrational boundary: bounded continuous phase averages converge. -/
theorem passageGammaLaw_slope_cont {β₀ : ℝ} (hβ0 : 0 < β₀) (hβ1 : β₀ < 1)
    (hβ : Irrational β₀) (g : ℝ →ᵇ ℝ) :
    Tendsto (fun β => ∫ t in Ioc (0 : ℝ) 1, g (passageGammaAmp β t)) (irrNhds β₀)
      (𝓝 (∫ t in Ioc (0 : ℝ) 1, g (passageGammaAmp β₀ t))) := by
  have h1 : ∀ᶠ β in 𝓝 β₀, 0 < β ∧ β < 1 := (eventually_gt_nhds hβ0).and (eventually_lt_nhds hβ1)
  have hu : ∀ᶠ β in irrNhds β₀, 0 < β ∧ β < 1 ∧ Irrational β := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds h1, self_mem_nhdsWithin]
      with β hb hi
    exact ⟨hb.1, hb.2, hi⟩
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => ‖g‖) ?_ ?_ ?_ ?_
  · filter_upwards [hu] with β h
    exact (g.continuous.measurable.comp
      (passageGammaAmp_measurable h.1 h.2.1 h.2.2)).aestronglyMeasurable
  · exact Eventually.of_forall fun β => Eventually.of_forall fun t => g.norm_coe_le_norm _
  · exact integrableOn_const (hs := measure_Ioc_lt_top.ne)
  · have hc : (range (fun r : ℕ => passagePhase β₀ (r+1))).Countable := countable_range _
    filter_upwards [ae_restrict_of_ae (hc.ae_notMem volume)] with t ht
    exact (g.continuous.tendsto _).comp
      (passageGammaAmp_tendsto hβ0 hβ1 hβ (fun r hr => ht ⟨r, hr⟩))

end Problems.Juggler.BeattySlope

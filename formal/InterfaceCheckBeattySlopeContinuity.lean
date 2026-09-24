import Problems.Juggler.BeattySlopeContinuity

/-! Expanded consumers of the slope-continuity theorems. The weights are
written through the original integer first-passage counts, and the content
through its explicit amplitude and profile integral. -/

namespace Problems.Juggler.BeattySlopeContinuityChecks

open BeattySlope Filter Topology MeasureTheory Set
open scoped BoundedContinuousFunction

/-- Each actual integer first-passage count is locally constant in the
boundary at every irrational boundary. -/
theorem actual_count_locally_constant (β₀ : ℝ) (hβ : Irrational β₀) (n : ℕ) :
    ∀ᶠ β in 𝓝 β₀, passageCount β n = passageCount β₀ n :=
  passageCount_eventually hβ n

/-- The actual Bernoulli-weighted counts converge in `ℓ¹` along irrational
boundaries, with no uniform bound assumed. -/
theorem actual_weights_l1 (β₀ : ℝ) (hβ0 : 0 < β₀) (hβ1 : β₀ < 1) (hβ : Irrational β₀) :
    Tendsto (fun β => ∑' r : ℕ,
      |(passageCount β (⌊((r+1 : ℕ) : ℝ)/β⌋₊+1) : ℝ)*β^(r+1)*(1-β)^(⌊((r+1 : ℕ) : ℝ)/β⌋₊-(r+1)) -
        (passageCount β₀ (⌊((r+1 : ℕ) : ℝ)/β₀⌋₊+1) : ℝ)*β₀^(r+1)*
          (1-β₀)^(⌊((r+1 : ℕ) : ℝ)/β₀⌋₊-(r+1))|)
      (𝓝[{β | Irrational β}] β₀) (𝓝 0) := by
  have h := passageJumpWeight_l1 hβ0 hβ1 hβ
  have hev : ∀ᶠ β in 𝓝[{β | Irrational β}] β₀, 0 < β ∧ β < 1 :=
    eventually_nhdsWithin_of_eventually_nhds ((eventually_gt_nhds hβ0).and (eventually_lt_nhds hβ1))
  refine h.congr' (hev.mono fun β hb => ?_)
  simp only [passageJumpWeight_eq hb.1 hb.2, passageJumpWeight_eq hβ0 hβ1, passageIndex]

/-- The exact Minkowski content, with amplitude and profile integral written
out, is continuous along irrational slopes at every irrational slope above one. -/
theorem actual_content_continuous (α₀ : ℝ) (h1 : 1 < α₀) (hα : Irrational α₀) :
    Tendsto (fun α => 3*(2 : ℝ)^(1/3 : ℝ)*((1/Real.sqrt (2*Real.pi*α*(α-1)))^(2/3 : ℝ)*
        ∫ t in (0 : ℝ)..1, (passageProfile (1/α) t)^(2/3 : ℝ)))
      (𝓝[{α | Irrational α}] α₀)
      (𝓝 (3*(2 : ℝ)^(1/3 : ℝ)*((1/Real.sqrt (2*Real.pi*α₀*(α₀-1)))^(2/3 : ℝ)*
        ∫ t in (0 : ℝ)..1, (passageProfile (1/α₀) t)^(2/3 : ℝ)))) := by
  have hexp (α : ℝ) (h1 : 1 < α) (hα : Irrational α) : passageMinkowskiContent (1/α) =
      3*(2 : ℝ)^(1/3 : ℝ)*((1/Real.sqrt (2*Real.pi*α*(α-1)))^(2/3 : ℝ)*
        ∫ t in (0 : ℝ)..1, (passageProfile (1/α) t)^(2/3 : ℝ)) := by
    have h0 : 0 < α := by linarith
    rw [passageMinkowskiContent, passageGapMoment_eq_profile (one_div_pos.mpr h0)
      ((div_lt_one h0).mpr h1) (by simpa using hα.inv), passageAmplitude_reciprocal h1]
  have h := passageContent_slope_tendsto h1 hα
  rw [hexp α₀ h1 hα] at h
  have hev : ∀ᶠ α in 𝓝[{α | Irrational α}] α₀, 1 < α ∧ Irrational α := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds h1),
      self_mem_nhdsWithin] with α ha hi
    exact ⟨ha, hi⟩
  exact h.congr' (hev.mono fun α ha => hexp α ha.1 ha.2)

/-- The limiting laws of the actual ratios converge weakly along irrational
slopes, in the explicit phase-average form. -/
theorem actual_law_continuous (α₀ : ℝ) (h1 : 1 < α₀) (hα : Irrational α₀) (g : ℝ →ᵇ ℝ) :
    Tendsto (fun α => ∫ t in Ioc (0 : ℝ) 1, g (passageProfile (1/α) t))
      (𝓝[{α | Irrational α}] α₀) (𝓝 (∫ t in Ioc (0 : ℝ) 1, g (passageProfile (1/α₀) t))) :=
  passageLaw_slope_cont h1 hα g

#print axioms actual_count_locally_constant
#print axioms actual_weights_l1
#print axioms actual_content_continuous
#print axioms actual_law_continuous

end Problems.Juggler.BeattySlopeContinuityChecks

import Problems.Juggler.BeattyTwoScaleExact
import Problems.Juggler.BeattySlopeExactDim
import Problems.Juggler.BeattySlopeMeasureDim

/-!
# Two-scale slopes in the low regime

For `ν > 1` and `1 ≤ ρ ≤ 1 + 3/ν` the two-scale quadratic
`3(ρν-1)s² + 4(ρ-1)s - 4(ρ-1)` is positive for every `s > 2/(2+ν)`, so the
two-scale covering beats every exponent above the Diophantine-class bound.
An isolated slope whose good denominators satisfy `Q_(g(j+1)) ≤ Q_(g j + 1)^ρ'`
eventually for every `ρ' > ρ` therefore has `dim_H K_α = 2/(2+ν)`. The
two-scale slopes of `twoScale_dims` exist for every such `ρ`, with class
exactly `ν`. At `ρ = 1 + 3/ν` the two formulas agree: `S(ν, 1 + 3/ν) = 2/(2+ν)`.
-/

namespace Problems.Juggler.BeattySlope

open Filter Topology Set MeasureTheory BeattyPhase

/-- **The low regime.** For `ν > 1` and `1 ≤ ρ ≤ 1 + 3/ν`, the two-scale
quadratic is positive for every `s > 2/(2+ν)`. -/
theorem twoScaleQuad_pos_low {ν ρ s : ℝ} (hν : 1 < ν) (hρ1 : 1 ≤ ρ) (hρ : ρ ≤ 1 + 3 / ν)
    (hs : 2 / (2 + ν) < s) : 0 < twoScaleQuad ν ρ s := by
  have hν0 : 0 < ν := by linarith
  have hR : ρ * ν ≤ ν + 3 := by
    have h : ρ - 1 ≤ 3 / ν := by linarith
    rw [le_div_iff₀ hν0] at h
    nlinarith
  have hR1 : 0 < ρ * ν - 1 := by nlinarith
  set a := 2 / (2 + ν) with ha
  have ha0 : 0 < a := by positivity
  -- `Q(2/(2+ν)) (2+ν)² = 4(ν-1)(ν+3-ρν) ≥ 0`
  have hQa : 0 ≤ twoScaleQuad ν ρ a := by
    have key : twoScaleQuad ν ρ a * (2 + ν) ^ 2 = 4 * (ν - 1) * (ν + 3 - ρ * ν) := by
      unfold twoScaleQuad; rw [ha]; field_simp; ring
    have hk : 0 ≤ 4 * (ν - 1) * (ν + 3 - ρ * ν) :=
      mul_nonneg (by linarith) (by linarith)
    by_contra hc
    push Not at hc
    have : twoScaleQuad ν ρ a * (2 + ν) ^ 2 < 0 := mul_neg_of_neg_of_pos hc (by positivity)
    linarith
  -- `Q(s) - Q(a) = (s - a)(3(ρν-1)(s+a) + 4(ρ-1))`
  have hdiff : twoScaleQuad ν ρ s - twoScaleQuad ν ρ a =
      (s - a) * (3 * (ρ * ν - 1) * (s + a) + 4 * (ρ - 1)) := by
    unfold twoScaleQuad; ring
  have hf : 0 < 3 * (ρ * ν - 1) * (s + a) + 4 * (ρ - 1) := by
    have : 0 < 3 * (ρ * ν - 1) * (s + a) := mul_pos (by linarith) (by linarith)
    linarith
  have := mul_pos (sub_pos.2 hs) hf
  linarith

/-- **The boundary.** `S(ν, 1 + 3/ν) = 2/(2+ν)`. -/
theorem twoScaleDim_boundary {ν : ℝ} (hν : 0 < ν) :
    twoScaleDim ν (1 + 3 / ν) = 2 / (2 + ν) := by
  have hsq : Real.sqrt ((1 + 3 / ν - 1) * (3 * ((1 + 3 / ν) * ν) + (1 + 3 / ν) - 4)) =
      3 * (ν + 1) / ν := by
    rw [Real.sqrt_eq_iff_mul_self_eq (by
      have : 0 < 3 / ν := by positivity
      apply mul_nonneg (by linarith)
      field_simp; nlinarith) (by positivity)]
    field_simp; ring
  have h2 : 2 + ν ≠ 0 := by positivity
  unfold twoScaleDim
  rw [hsq]
  have hν3 : (1 + 3 / ν) * ν = ν + 3 := by field_simp
  rw [hν3, div_eq_div_iff (by nlinarith) h2]
  field_simp
  ring

/-- **Exact dimension of two-scale slopes in the low regime.** Let `ν > 1`,
`1 ≤ ρ ≤ 1 + 3/ν`, and let the good denominators of an isolated slope satisfy,
for every `ρ' > ρ`, `Q_(g(j+1)) ≤ Q_(g j + 1)^ρ'` from some level on. Then
`dim_H K_α = 2/(2+ν)`. No lower growth condition is needed: the lower bound
comes from the Diophantine class alone. -/
theorem twoScale_dimH_low {ν B ρ : ℝ} {G : ℕ → Prop} [DecidablePred G]
    (Lv : IsoLevels ν G B) (hν : 1 < ν) (hρ1 : 1 ≤ ρ) (hρ : ρ ≤ 1 + 3 / ν)
    (hup : ∀ ρ', ρ < ρ' → ∃ j1, ∀ j, j1 ≤ j →
      (isoDen ν G (Lv.g (j + 1)) : ℝ) ≤ (isoDen ν G (Lv.g j + 1) : ℝ) ^ ρ') :
    dimH (passageClusterSet (1 / isoSlope ν G)) = ENNReal.ofReal (2 / (2 + ν)) := by
  have hν0 : 0 < ν := by linarith
  have ha0 : 0 < 2 / (2 + ν) := by positivity
  have hhi : 2 / (2 + ν) < 2 / 3 := div_lt_div_of_pos_left (by norm_num) (by norm_num)
    (by linarith)
  apply le_antisymm
  · -- upper bound: `dim ≤ s` for every `s ∈ (2/(2+ν), 2/3)`
    apply le_of_forall_gt
    intro c hc
    obtain ⟨s, hs1, hs2⟩ : ∃ s : ℝ, 2 / (2 + ν) < s ∧ s < 2 / 3 ∧ ENNReal.ofReal s < c := by
      by_cases hct : c = ⊤
      · obtain ⟨s, h1, h2⟩ := exists_between hhi
        exact ⟨s, h1, h2, by rw [hct]; exact ENNReal.ofReal_lt_top⟩
      · have hc' : 2 / (2 + ν) < c.toReal := by
          rw [← ENNReal.ofReal_toReal hct] at hc
          exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha0.le).1 hc
        obtain ⟨s, h1, h2⟩ := exists_between (lt_min hc' hhi)
        refine ⟨s, h1, h2.trans_le (min_le_right _ _), ?_⟩
        rw [← ENNReal.ofReal_toReal hct]
        exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2
          (h2.trans_le (min_le_left _ _))
    obtain ⟨hs23, hsc⟩ := hs2
    obtain ⟨t, ht0, hQ'⟩ := twoScaleQuad_pos_right (twoScaleQuad_pos_low hν hρ1 hρ hs1)
    obtain ⟨j1, hj1⟩ := hup (ρ + t) (by linarith)
    have hzero := twoScale_iso_hausdorff_zero Lv hν (by linarith) ⟨j1, hj1⟩ hs1 hs23 hQ'
    have hle : dimH (passageClusterSet (1 / isoSlope ν G)) ≤ ENNReal.ofReal s := by
      have hs0 : 0 ≤ s := by linarith
      have hne : Measure.hausdorffMeasure ((s.toNNReal : NNReal) : ℝ)
          (passageClusterSet (1 / isoSlope ν G)) ≠ ⊤ := by
        rw [Real.coe_toNNReal _ hs0, hzero]; exact ENNReal.zero_ne_top
      exact dimH_le_of_hausdorffMeasure_ne_top hne
    exact hle.trans_lt hsc
  · -- lower bound: the slope has Diophantine class exactly `ν`
    have hcls := isoSlope_diophClass hν Lv.frequent
    exact cluster_dimH_ge_class (one_lt_isoSlope ν G) (isoSlope_irrational ν G) hν0.le
      fun τ hτ => dioph_lower_of_class (isoSlope_irrational ν G) hcls hτ

open Classical in
/-- **Two-scale slopes in the low regime.** For every `ν > 1` and
`1 ≤ ρ ≤ 1 + 3/ν` the two-scale slope has Diophantine class exactly `ν` and
`dim_H K_α = 2/(2+ν)`. -/
theorem twoScale_dims_low {ν ρ : ℝ} (hν : 1 < ν) (hρ1 : 1 ≤ ρ) (hρ : ρ ≤ 1 + 3 / ν) :
    DiophClass (isoSlope ν (TwoScaleGood ν (ρ * ν))) ν ∧
    dimH (passageClusterSet (1 / isoSlope ν (TwoScaleGood ν (ρ * ν)))) =
      ENNReal.ofReal (2 / (2 + ν)) := by
  set Lv := twoScaleLevels ν (ρ * ν) hν.le
  exact ⟨isoSlope_diophClass hν Lv.frequent,
    twoScale_dimH_low Lv hν hρ1 hρ (twoScale_up_rpow hν.le hρ1)⟩

end Problems.Juggler.BeattySlope

import Problems.Juggler.BeattyTwoScaleUpper

/-!
# Exact dimension of two-scale slopes

For `ν > 1` and `ρ > 1 + 3/ν`, put `R = ρν` and
`S(ν, ρ) = 2(√((ρ-1)(3R+ρ-4)) - (ρ-1))/(3(R-1))`, the positive root of
`3(R-1)s² + 4(ρ-1)s - 4(ρ-1) = 0`. An isolated slope whose good denominators
grow with `Q_(g(j+1)) ≥ Q_(g j)^R` from some level on, and with
`Q_(g(j+1)) ≤ Q_(g j + 1)^ρ'` eventually for every `ρ' > ρ`, has
`dim_H K_α = S(ν, ρ)`.
-/

namespace Problems.Juggler.BeattySlope

open Filter Topology Set MeasureTheory BeattyPhase

/-- The two-scale dimension `S(ν, ρ)`. -/
noncomputable def twoScaleDim (ν ρ : ℝ) : ℝ :=
  2 * (Real.sqrt ((ρ - 1) * (3 * (ρ * ν) + ρ - 4)) - (ρ - 1)) / (3 * (ρ * ν - 1))

/-- The two-scale quadratic `3(ρν-1)s² + 4(ρ-1)s - 4(ρ-1)`. -/
def twoScaleQuad (ν ρ s : ℝ) : ℝ := 3 * (ρ * ν - 1) * s ^ 2 + 4 * (ρ - 1) * s - 4 * (ρ - 1)

/-- **The root.** For `ν > 1` and `ρ > 1 + 3/ν`, `S(ν, ρ)` lies strictly between
`2/(2+ν)` and `2/3`, and the quadratic is negative below it and positive above it,
on positive `s`. -/
theorem twoScaleDim_props {ν ρ : ℝ} (hν : 1 < ν) (hρ : 1 + 3 / ν < ρ) :
    2 / (2 + ν) < twoScaleDim ν ρ ∧ twoScaleDim ν ρ < 2 / 3 ∧
      (∀ s, 0 < s → s < twoScaleDim ν ρ → twoScaleQuad ν ρ s < 0) ∧
      (∀ s, twoScaleDim ν ρ < s → 0 < twoScaleQuad ν ρ s) := by
  have hν0 : 0 < ν := by linarith
  have hρ1 : 0 < ρ - 1 := by
    have : 0 < 3 / ν := by positivity
    linarith
  have hR : ν + 3 < ρ * ν := by
    have : 3 / ν < ρ - 1 := by linarith
    rw [div_lt_iff₀ hν0] at this
    nlinarith
  have hR1 : 0 < ρ * ν - 1 := by linarith
  set D := (ρ - 1) * (3 * (ρ * ν) + ρ - 4) with hD
  have hD0 : 0 ≤ D := by rw [hD]; apply mul_nonneg hρ1.le; nlinarith
  set r := Real.sqrt D with hr
  have hr2 : r ^ 2 = D := Real.sq_sqrt hD0
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  set S := twoScaleDim ν ρ with hS
  have hSdef : S = 2 * (r - (ρ - 1)) / (3 * (ρ * ν - 1)) := rfl
  -- `Q(S) = 0`
  have hQS : twoScaleQuad ν ρ S = 0 := by
    unfold twoScaleQuad
    rw [hSdef]
    field_simp
    nlinarith [hr2]
  -- factorization `Q(s) - Q(S) = (s - S)(3(R-1)(s+S) + 4(ρ-1))`
  have hfac : ∀ s, twoScaleQuad ν ρ s =
      (s - S) * (3 * (ρ * ν - 1) * (s + S) + 4 * (ρ - 1)) := by
    intro s
    have := hQS
    unfold twoScaleQuad at this ⊢
    nlinarith [this]
  -- `S > 0`: `r > ρ - 1` since `D > (ρ-1)²`
  have hrρ : ρ - 1 < r := by
    have : (ρ - 1) ^ 2 < D := by rw [hD]; nlinarith
    rw [hr]
    exact Real.lt_sqrt_of_sq_lt this
  have hS0 : 0 < S := by rw [hSdef]; apply div_pos (by linarith) (by positivity)
  have hpos : ∀ s, 0 < s → 0 < 3 * (ρ * ν - 1) * (s + S) + 4 * (ρ - 1) := by
    intro s hs; positivity
  -- `Q(2/(2+ν)) < 0` and `Q(2/3) > 0`
  have hQlo : twoScaleQuad ν ρ (2 / (2 + ν)) < 0 := by
    unfold twoScaleQuad
    have key : (3 * (ρ * ν - 1) * (2 / (2 + ν)) ^ 2 + 4 * (ρ - 1) * (2 / (2 + ν)) -
        4 * (ρ - 1)) * (2 + ν) ^ 2 = 4 * (ν - 1) * (ν + 3 - ρ * ν) := by
      field_simp; ring
    have : 4 * (ν - 1) * (ν + 3 - ρ * ν) < 0 := by
      have : 0 < ν - 1 := by linarith
      nlinarith
    rw [← key] at this
    by_contra hc
    push Not at hc
    have : 0 ≤ (3 * (ρ * ν - 1) * (2 / (2 + ν)) ^ 2 + 4 * (ρ - 1) * (2 / (2 + ν)) -
        4 * (ρ - 1)) * (2 + ν) ^ 2 := mul_nonneg hc (by positivity)
    linarith
  have hQhi : 0 < twoScaleQuad ν ρ (2 / 3) := by
    unfold twoScaleQuad; nlinarith
  have hlo : 2 / (2 + ν) < S := by
    by_contra hc
    push Not at hc
    have := hfac (2 / (2 + ν))
    have h1 : 0 ≤ (2 / (2 + ν) - S) := by linarith
    have := mul_nonneg h1 (hpos (2 / (2 + ν)) (by positivity)).le
    linarith
  have hhi : S < 2 / 3 := by
    by_contra hc
    push Not at hc
    have := hfac (2 / 3)
    have h1 : (2 / 3 - S) ≤ 0 := by linarith
    have := mul_nonpos_of_nonpos_of_nonneg h1 (hpos (2 / 3) (by norm_num)).le
    linarith
  refine ⟨hlo, hhi, fun s hs hsS => ?_, fun s hsS => ?_⟩
  · rw [hfac s]
    exact mul_neg_of_neg_of_pos (by linarith) (hpos s hs)
  · rw [hfac s]
    exact mul_pos (by linarith) (hpos s (hS0.trans hsS))

/-- **Two-scale upper bound for isolated slopes.** If `Q_(g(j+1)) ≤ Q_(g j + 1)^ρ`
from some level on, then `H^s(K_α) = 0` whenever `2/(2+ν) < s < 2/3` and the
two-scale quadratic is positive at `s`. -/
theorem twoScale_iso_hausdorff_zero {ν B ρ s : ℝ} {G : ℕ → Prop} [DecidablePred G]
    (Lv : IsoLevels ν G B) (hν : 1 < ν) (hρ : 1 ≤ ρ)
    (hup : ∃ j1, ∀ j, j1 ≤ j →
      (isoDen ν G (Lv.g (j + 1)) : ℝ) ≤ (isoDen ν G (Lv.g j + 1) : ℝ) ^ ρ)
    (hs : 2 / (2 + ν) < s) (hs23 : s < 2 / 3) (hQ : 0 < twoScaleQuad ν ρ s) :
    Measure.hausdorffMeasure s (passageClusterSet (1 / isoSlope ν G)) = 0 := by
  have ha := isoQuot_succ_ge ν G
  have hG := cf_goodConvergents ha
  have hq : ∀ m, cfDen (isoQuot ν G) (m + 1) = isoDen ν G (m + 1) := fun m =>
    cfDen_isoQuot ν G (m + 1)
  have hmono : Monotone (fun m => cfDen (isoQuot ν G) (m + 1)) :=
    monotone_nat_of_le_succ fun m => cfDen_le_succ ha (m + 1)
  have htend : Tendsto (fun m => cfDen (isoQuot ν G) (m + 1)) atTop atTop :=
    (cfDen_tendsto ha).comp (tendsto_add_atTop_nat 1)
  have hg1 : ∀ j, 1 ≤ Lv.g j := Lv.one_le_g
  set n : ℕ → ℕ := fun j => Lv.g j - 1 with hn
  have hn1 : ∀ j, n j + 1 = Lv.g j := fun j => by simp only [hn]; have := hg1 j; omega
  have hnm : StrictMono n := by
    intro a b hab
    have := Lv.mono hab
    have := hg1 a
    simp only [hn]; omega
  have hgrow : ∀ᶠ j in atTop, ((fun m => cfDen (isoQuot ν G) (m + 1)) (n j) : ℝ) ^ ν ≤
      (fun m => cfDen (isoQuot ν G) (m + 1)) (n j + 1) := by
    refine Eventually.of_forall fun j => ?_
    simp only [cfDen_isoQuot, hn1]
    exact (isoDen_good_growth hν.le (hg1 j) (Lv.good j)).1
  obtain ⟨j1, hup⟩ := hup
  have hup' : ∀ᶠ j in atTop, ((fun m => cfDen (isoQuot ν G) (m + 1)) (n (j + 1)) : ℝ) ≤
      ((fun m => cfDen (isoQuot ν G) (m + 1)) (n j + 1) : ℝ) ^ ρ := by
    refine eventually_atTop.2 ⟨j1, fun j hj => ?_⟩
    simp only [cfDen_isoQuot, hn1]
    exact hup j hj
  have hQ' : 0 < 3 * (ν * ρ - 1) * s ^ 2 + 4 * (ρ - 1) * s - 4 * (ρ - 1) := by
    have := hQ; unfold twoScaleQuad at this; rwa [mul_comm ν ρ]
  exact twoScale_hausdorff_zero (one_lt_isoSlope ν G) (isoSlope_irrational ν G) hG hmono htend
    hnm hν.le hρ hgrow hup' hs hs23 hQ'

/-- **Exact dimension of two-scale slopes.** Let `ν > 1`, `ρ > 1 + 3/ν`, and let the
good denominators of an isolated slope satisfy `Q_(g(j+1)) ≥ Q_(g j)^(ρν)` from some
level on and, for every `ρ' > ρ`, `Q_(g(j+1)) ≤ Q_(g j + 1)^ρ'` from some level on.
Then `dim_H K_α = S(ν, ρ)`. -/
theorem twoScale_dimH_eq {ν B ρ : ℝ} {G : ℕ → Prop} [DecidablePred G]
    (Lv : IsoLevels ν G B) (hν : 1 < ν) (hρ : 1 + 3 / ν < ρ)
    (hlow : ∃ j1, ∀ j, j1 ≤ j →
      (isoDen ν G (Lv.g j) : ℝ) ^ (ρ * ν) ≤ isoDen ν G (Lv.g (j + 1)))
    (hup : ∀ ρ', ρ < ρ' → ∃ j1, ∀ j, j1 ≤ j →
      (isoDen ν G (Lv.g (j + 1)) : ℝ) ≤ (isoDen ν G (Lv.g j + 1) : ℝ) ^ ρ') :
    dimH (passageClusterSet (1 / isoSlope ν G)) = ENNReal.ofReal (twoScaleDim ν ρ) := by
  obtain ⟨hlo, hhi, hneg, hposQ⟩ := twoScaleDim_props hν hρ
  have hS0 : 0 < twoScaleDim ν ρ := lt_trans (by positivity) hlo
  have hν0 : 0 < ν := by linarith
  have hρ1 : 1 ≤ ρ := by have : 0 < 3 / ν := by positivity
                         linarith
  apply le_antisymm
  · -- upper bound: `dim ≤ s` for every `s ∈ (S, 2/3)`
    apply le_of_forall_gt
    intro c hc
    have hcT : ENNReal.ofReal (twoScaleDim ν ρ) < c := hc
    -- choose `s` with `S < s < min(c, 2/3)`
    obtain ⟨s, hs1, hs2⟩ : ∃ s : ℝ, twoScaleDim ν ρ < s ∧ s < 2 / 3 ∧ ENNReal.ofReal s < c := by
      by_cases hct : c = ⊤
      · obtain ⟨s, h1, h2⟩ := exists_between hhi
        exact ⟨s, h1, h2, by rw [hct]; exact ENNReal.ofReal_lt_top⟩
      · have hc' : twoScaleDim ν ρ < c.toReal := by
          rw [← ENNReal.ofReal_toReal hct] at hcT
          exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hS0.le).1 hcT
        obtain ⟨s, h1, h2⟩ := exists_between (lt_min hc' hhi)
        refine ⟨s, h1, h2.trans_le (min_le_right _ _), ?_⟩
        rw [← ENNReal.ofReal_toReal hct]
        exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2
          (h2.trans_le (min_le_left _ _))
    obtain ⟨hs23, hsc⟩ := hs2
    have hQs := hposQ s hs1
    -- a slightly larger `ρ'` keeps the quadratic positive
    set c1 := 3 * ν * s ^ 2 + 4 * s - 4 with hc1
    set t := twoScaleQuad ν ρ s / (2 * (|c1| + 1)) with ht
    have ht0 : 0 < t := by positivity
    have hQ' : 0 < twoScaleQuad ν (ρ + t) s := by
      have e : twoScaleQuad ν (ρ + t) s = twoScaleQuad ν ρ s + t * c1 := by
        unfold twoScaleQuad; rw [hc1]; ring
      have hb : t * |c1| ≤ twoScaleQuad ν ρ s / 2 := by
        rw [ht, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [abs_nonneg c1]
      rw [e]
      nlinarith [neg_abs_le c1]
    obtain ⟨j1, hj1⟩ := hup (ρ + t) (by linarith)
    have hzero := twoScale_iso_hausdorff_zero Lv hν (by linarith) ⟨j1, hj1⟩
      (hlo.trans hs1) hs23 hQ'
    have hle : dimH (passageClusterSet (1 / isoSlope ν G)) ≤ ENNReal.ofReal s := by
      have hs0 : 0 ≤ s := by linarith
      have hne : Measure.hausdorffMeasure ((s.toNNReal : NNReal) : ℝ)
          (passageClusterSet (1 / isoSlope ν G)) ≠ ⊤ := by
        rw [Real.coe_toNNReal _ hs0, hzero]; exact ENNReal.zero_ne_top
      exact dimH_le_of_hausdorffMeasure_ne_top hne
    exact hle.trans_lt hsc
  · -- lower bound: `dim ≥ s` for every `s ∈ [2/(2+ν), S)`
    apply le_of_forall_lt
    intro c hc
    have hcT : c ≠ ⊤ := ne_top_of_lt hc
    have hc' : c.toReal < twoScaleDim ν ρ := by
      rw [← ENNReal.ofReal_toReal hcT] at hc
      exact (ENNReal.ofReal_lt_ofReal_iff hS0).1 hc
    obtain ⟨s, hs1, hs2⟩ := exists_between (max_lt hc' hlo)
    have hs0 : 2 / (2 + ν) ≤ s := ((le_max_right _ _).trans_lt hs1).le
    have hspos : 0 < s := lt_of_lt_of_le (by positivity) hs0
    have hQ := hneg s hspos hs2
    unfold twoScaleQuad at hQ
    have hge := twoScale_dimH_ge Lv hν hρ hlow hs0 hQ
    calc c = ENNReal.ofReal c.toReal := (ENNReal.ofReal_toReal hcT).symm
      _ < ENNReal.ofReal s :=
          (ENNReal.ofReal_lt_ofReal_iff hspos).2 ((le_max_left _ _).trans_lt hs1)
      _ ≤ _ := hge

end Problems.Juggler.BeattySlope

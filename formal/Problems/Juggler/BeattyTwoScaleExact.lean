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

/-- A positive two-scale quadratic stays positive for a slightly larger `ρ`. -/
theorem twoScaleQuad_pos_right {ν ρ s : ℝ} (hQ : 0 < twoScaleQuad ν ρ s) :
    ∃ t, 0 < t ∧ 0 < twoScaleQuad ν (ρ + t) s := by
  set c1 := 3 * ν * s ^ 2 + 4 * s - 4 with hc1
  set t := twoScaleQuad ν ρ s / (2 * (|c1| + 1)) with ht
  have ht0 : 0 < t := by positivity
  refine ⟨t, ht0, ?_⟩
  have e : twoScaleQuad ν (ρ + t) s = twoScaleQuad ν ρ s + t * c1 := by
    unfold twoScaleQuad; rw [hc1]; ring
  have hb : t * |c1| ≤ twoScaleQuad ν ρ s / 2 := by
    rw [ht, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [abs_nonneg c1]
  rw [e]
  nlinarith [neg_abs_le c1]

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
    -- a slightly larger `ρ'` keeps the quadratic positive
    obtain ⟨t, ht0, hQ'⟩ := twoScaleQuad_pos_right (hposQ s hs1)
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

/-- `isoDen ν G k` depends only on which indices below `k` are good. -/
theorem isoDen_congr {ν : ℝ} {G G' : ℕ → Prop} [DecidablePred G] [DecidablePred G'] :
    ∀ k, (∀ i < k, (G i ↔ G' i)) → isoDen ν G k = isoDen ν G' k
  | 0, _ => rfl
  | 1, _ => rfl
  | k + 2, h => by
    have h1 := isoDen_congr (ν := ν) (G := G) (G' := G') (k + 1) (fun i hi => h i (by omega))
    have h0 := isoDen_congr (ν := ν) (G := G) (G' := G') k (fun i hi => h i (by omega))
    have hk := h (k + 1) (by omega)
    show (if G (k + 1) then ⌈(isoDen ν G (k + 1) : ℝ) ^ (ν - 1)⌉₊ + 1 else 1) *
        isoDen ν G (k + 1) + isoDen ν G k =
      (if G' (k + 1) then ⌈(isoDen ν G' (k + 1) : ℝ) ^ (ν - 1)⌉₊ + 1 else 1) *
        isoDen ν G' (k + 1) + isoDen ν G' k
    rw [h1, h0]
    by_cases hg : G (k + 1)
    · rw [if_pos hg, if_pos (hk.1 hg)]
    · rw [if_neg hg, if_neg (fun h' => hg (hk.2 h'))]

/-- Some index beyond `g + 3` has denominator at least `Q_g^R` (for the good set `S`). -/
theorem twoScale_next_exists (ν R : ℝ) (S : Finset ℕ) (g : ℕ) :
    ∃ k, g + 3 ≤ k ∧ (isoDen ν (· ∈ S) g : ℝ) ^ R ≤ isoDen ν (· ∈ S) k := by
  set x := (isoDen ν (· ∈ S) g : ℝ) ^ R
  refine ⟨max (g + 3) (⌈x⌉₊ + 1), le_max_left _ _, ?_⟩
  have h1 := idx_le_isoDen (ν := ν) (G := (· ∈ S)) (max (g + 3) (⌈x⌉₊ + 1))
  have h2 : ⌈x⌉₊ ≤ isoDen ν (· ∈ S) (max (g + 3) (⌈x⌉₊ + 1)) := by
    have := le_max_right (g + 3) (⌈x⌉₊ + 1); omega
  calc x ≤ ⌈x⌉₊ := Nat.le_ceil x
    _ ≤ _ := by exact_mod_cast h2

open Classical in
/-- The next good index after `g`, for the good set `S`. -/
noncomputable def twoScaleNext (ν R : ℝ) (S : Finset ℕ) (g : ℕ) : ℕ :=
  Nat.find (twoScale_next_exists ν R S g)

/-- The chosen good indices after `l` steps and the last of them. -/
noncomputable def twoScaleState (ν R : ℝ) : ℕ → Finset ℕ × ℕ
  | 0 => ({1}, 1)
  | l + 1 =>
    (insert (twoScaleNext ν R (twoScaleState ν R l).1 (twoScaleState ν R l).2)
      (twoScaleState ν R l).1,
     twoScaleNext ν R (twoScaleState ν R l).1 (twoScaleState ν R l).2)

/-- The two-scale good indices. -/
noncomputable def twoScaleIdx (ν R : ℝ) (l : ℕ) : ℕ := (twoScaleState ν R l).2

/-- The two-scale good set. -/
def TwoScaleGood (ν R : ℝ) (k : ℕ) : Prop := ∃ l, twoScaleIdx ν R l = k

/-- The next good index is the search result for the current set. -/
theorem twoScaleIdx_succ (ν R : ℝ) (l : ℕ) :
    twoScaleIdx ν R (l + 1) =
      twoScaleNext ν R (twoScaleState ν R l).1 (twoScaleIdx ν R l) := rfl

/-- Consecutive good indices are at least three apart. -/
theorem twoScaleIdx_step (ν R : ℝ) (l : ℕ) :
    twoScaleIdx ν R l + 3 ≤ twoScaleIdx ν R (l + 1) := by
  classical
  rw [twoScaleIdx_succ]
  exact (Nat.find_spec (twoScale_next_exists ν R _ _)).1

/-- The good indices increase strictly. -/
theorem twoScaleIdx_mono (ν R : ℝ) : StrictMono (twoScaleIdx ν R) :=
  strictMono_nat_of_lt_succ fun l => by have := twoScaleIdx_step ν R l; omega

/-- The chosen set after `l` steps is `{g 0, …, g l}`. -/
theorem mem_twoScaleState (ν R : ℝ) (l k : ℕ) :
    k ∈ (twoScaleState ν R l).1 ↔ ∃ i ≤ l, twoScaleIdx ν R i = k := by
  induction l with
  | zero =>
    simp only [twoScaleState, Finset.mem_singleton, twoScaleIdx]
    constructor
    · rintro rfl; exact ⟨0, le_rfl, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      obtain rfl : i = 0 := by omega
      rfl
  | succ l ih =>
    rw [show (twoScaleState ν R (l + 1)).1 = insert (twoScaleIdx ν R (l + 1))
      (twoScaleState ν R l).1 from rfl, Finset.mem_insert, ih]
    constructor
    · rintro (rfl | ⟨i, hi, rfl⟩)
      · exact ⟨l + 1, le_rfl, rfl⟩
      · exact ⟨i, by omega, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      rcases Nat.eq_or_lt_of_le hi with rfl | hlt
      · exact Or.inl rfl
      · exact Or.inr ⟨i, by omega, rfl⟩

open Classical in
/-- Up to the next good index, the final good set and the chosen set agree. -/
theorem twoScale_agree (ν R : ℝ) (l : ℕ) {k : ℕ} (hk : k ≤ twoScaleIdx ν R (l + 1)) :
    isoDen ν (TwoScaleGood ν R) k = isoDen ν (· ∈ (twoScaleState ν R l).1) k := by
  apply isoDen_congr
  intro i hi
  rw [mem_twoScaleState]
  constructor
  · rintro ⟨j, rfl⟩
    refine ⟨j, ?_, rfl⟩
    by_contra hj
    push Not at hj
    have := (twoScaleIdx_mono ν R).monotone (show l + 1 ≤ j by omega)
    omega
  · rintro ⟨j, -, rfl⟩
    exact ⟨j, rfl⟩

open Classical in
/-- The two-scale enumeration. -/
noncomputable def twoScaleLevels (ν R : ℝ) (hν : 1 ≤ ν) : IsoLevels ν (TwoScaleGood ν R) 1 where
  g := twoScaleIdx ν R
  mono := twoScaleIdx_mono ν R
  one_le := le_rfl
  good_mem l := ⟨l, rfl⟩
  gap l k h1 h2 := by
    rintro ⟨j, rfl⟩
    have a := (twoScaleIdx_mono ν R).lt_iff_lt.1 h1
    have b := (twoScaleIdx_mono ν R).lt_iff_lt.1 h2
    omega
  big := by
    show (1 : ℝ) ≤ isoDen ν (TwoScaleGood ν R) 1
    simp [isoDen]
  step2 l := by
    set g := twoScaleIdx ν R l
    have hstep := twoScaleIdx_step ν R l
    have hmono := isoDen_mono (ν := ν) (G := TwoScaleGood ν R)
    -- `Q_(g+3) ≥ Q_(g+2) + Q_(g+1) ≥ 2 Q_(g+1)`
    have h3 : 2 * isoDen ν (TwoScaleGood ν R) (g + 1) ≤ isoDen ν (TwoScaleGood ν R) (g + 3) := by
      have e : isoDen ν (TwoScaleGood ν R) (g + 3) =
          (if TwoScaleGood ν R (g + 2) then
            ⌈(isoDen ν (TwoScaleGood ν R) (g + 2) : ℝ) ^ (ν - 1)⌉₊ + 1 else 1) *
            isoDen ν (TwoScaleGood ν R) (g + 2) + isoDen ν (TwoScaleGood ν R) (g + 1) := rfl
      have h21 := hmono (show g + 1 ≤ g + 2 by omega)
      have hpos : 1 ≤ (if TwoScaleGood ν R (g + 2) then
            ⌈(isoDen ν (TwoScaleGood ν R) (g + 2) : ℝ) ^ (ν - 1)⌉₊ + 1 else 1) := by
        split_ifs <;> omega
      rw [e]
      nlinarith
    have := hmono (show g + 3 ≤ twoScaleIdx ν R (l + 1) from hstep)
    exact_mod_cast h3.trans this

open Classical in
/-- **Growth of the two-scale denominators.** `Q_(g(l+1)) ≥ Q_(g l)^R`, and
`Q_(g(l+1)) ≤ 4 Q_(g l + 1)^ρ` when `R = ρν`, `ρ ≥ 1`. -/
theorem twoScale_growth {ν ρ : ℝ} (hν : 1 ≤ ν) (hρ : 1 ≤ ρ) (l : ℕ) :
    (isoDen ν (TwoScaleGood ν (ρ * ν)) (twoScaleIdx ν (ρ * ν) l) : ℝ) ^ (ρ * ν) ≤
        isoDen ν (TwoScaleGood ν (ρ * ν)) (twoScaleIdx ν (ρ * ν) (l + 1)) ∧
      (isoDen ν (TwoScaleGood ν (ρ * ν)) (twoScaleIdx ν (ρ * ν) (l + 1)) : ℝ) ≤
        4 * (isoDen ν (TwoScaleGood ν (ρ * ν)) (twoScaleIdx ν (ρ * ν) l + 1) : ℝ) ^ ρ := by
  set R := ρ * ν
  set G := TwoScaleGood ν R
  set S := (twoScaleState ν R l).1
  set g := twoScaleIdx ν R l
  set g' := twoScaleIdx ν R (l + 1)
  have hg' : g' = twoScaleNext ν R S g := twoScaleIdx_succ ν R l
  have hspec := Nat.find_spec (twoScale_next_exists ν R S g)
  have hstep : g + 3 ≤ g' := twoScaleIdx_step ν R l
  have hag : ∀ k, k ≤ g' → isoDen ν G k = isoDen ν (· ∈ S) k :=
    fun k hk => twoScale_agree ν R l hk
  have hgg' : g ≤ g' := by omega
  -- lower growth
  have hlow : (isoDen ν G g : ℝ) ^ R ≤ isoDen ν G g' := by
    rw [hag g hgg', hag g' le_rfl, hg']
    exact hspec.2
  refine ⟨hlow, ?_⟩
  -- the good level `g` gives `Q_g^R ≤ Q_(g+1)^ρ`
  have hg1 : 1 ≤ g := (twoScaleLevels ν R hν).one_le_g l
  have hgood : G g := ⟨l, rfl⟩
  have hgr := (isoDen_good_growth hν hg1 hgood).1
  have hQ0 : (0 : ℝ) ≤ isoDen ν G g := Nat.cast_nonneg _
  have hN1 : (1 : ℝ) ≤ isoDen ν G (g + 1) := by exact_mod_cast isoDen_pos (ν := ν) (G := G) g
  have hR : (isoDen ν G g : ℝ) ^ R ≤ (isoDen ν G (g + 1) : ℝ) ^ ρ := by
    calc (isoDen ν G g : ℝ) ^ R = ((isoDen ν G g : ℝ) ^ ν) ^ ρ := by
          rw [← Real.rpow_mul hQ0, mul_comm ν ρ]
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hgr (by linarith)
  have hNρ : (isoDen ν G (g + 1) : ℝ) ≤ (isoDen ν G (g + 1) : ℝ) ^ ρ := by
    simpa using Real.rpow_le_rpow_of_exponent_le hN1 hρ
  rcases Nat.eq_or_lt_of_le hstep with heq | hlt
  · -- `g' = g + 3`: two dense steps, each at most doubling
    have hng2 : ¬ G (g + 2) := (twoScaleLevels ν R hν).not_good (l := l)
      (show g < g + 2 by omega) (show g + 2 < g' by omega)
    have hng1 : ¬ G (g + 1) := (twoScaleLevels ν R hν).not_good (l := l)
      (show g < g + 1 by omega) (show g + 1 < g' by omega)
    have a1 := isoDen_succ_le_two (ν := ν) (show 1 ≤ g + 2 by omega) hng2
    have a2 := isoDen_succ_le_two (ν := ν) (show 1 ≤ g + 1 by omega) hng1
    rw [← heq]
    calc (isoDen ν G (g + 3) : ℝ) ≤ 2 * isoDen ν G (g + 2) := a1
      _ ≤ 2 * (2 * isoDen ν G (g + 1)) := by linarith
      _ ≤ 4 * (isoDen ν G (g + 1) : ℝ) ^ ρ := by linarith
  · -- `g' > g + 3`: the index before `g'` fails the search, and is not good
    have hmin := Nat.find_min (twoScale_next_exists ν R S g)
      (show g' - 1 < twoScaleNext ν R S g by omega)
    have hfail : (isoDen ν (· ∈ S) (g' - 1) : ℝ) < (isoDen ν (· ∈ S) g : ℝ) ^ R := by
      by_contra hc
      push Not at hc
      exact hmin ⟨by omega, hc⟩
    rw [← hag (g' - 1) (by omega), ← hag g hgg'] at hfail
    have hng : ¬ G (g' - 1) := (twoScaleLevels ν R hν).not_good (l := l)
      (show g < g' - 1 by omega) (show g' - 1 < g' by omega)
    have a := isoDen_succ_le_two (ν := ν) (show 1 ≤ g' - 1 by omega) hng
    rw [show g' - 1 + 1 = g' by omega] at a
    calc (isoDen ν G g' : ℝ) ≤ 2 * isoDen ν G (g' - 1) := a
      _ ≤ 2 * (isoDen ν G g : ℝ) ^ R := by linarith
      _ ≤ 2 * (isoDen ν G (g + 1) : ℝ) ^ ρ := by linarith
      _ ≤ 4 * (isoDen ν G (g + 1) : ℝ) ^ ρ := by
          have : (0 : ℝ) ≤ (isoDen ν G (g + 1) : ℝ) ^ ρ := by positivity
          linarith

open Classical in
/-- **Upper growth of the two-scale denominators.** For `ν, ρ ≥ 1` and every
`ρ' > ρ`, `Q_(g(j+1)) ≤ Q_(g j + 1)^ρ'` from some level on. -/
theorem twoScale_up_rpow {ν ρ : ℝ} (hν : 1 ≤ ν) (hρ1 : 1 ≤ ρ) :
    ∀ ρ', ρ < ρ' → ∃ j1, ∀ j, j1 ≤ j →
      (isoDen ν (TwoScaleGood ν (ρ * ν)) ((twoScaleLevels ν (ρ * ν) hν).g (j + 1)) : ℝ) ≤
        (isoDen ν (TwoScaleGood ν (ρ * ν)) ((twoScaleLevels ν (ρ * ν) hν).g j + 1) : ℝ) ^ ρ' := by
  set Lv := twoScaleLevels ν (ρ * ν) hν
  intro ρ' hρ'
  -- `4 N^ρ ≤ N^ρ'` once `N^(ρ'-ρ) ≥ 4`, and `N ≥ g ≥ j` grows without bound
  set t := ρ' - ρ with ht
  have ht0 : 0 < t := by linarith
  refine ⟨⌈(4 : ℝ) ^ (1 / t)⌉₊ + 1, fun j hj => ?_⟩
  set N := (isoDen ν (TwoScaleGood ν (ρ * ν)) (twoScaleIdx ν (ρ * ν) j + 1) : ℝ) with hN
  have hN1 : 1 ≤ N := by
    have h : 1 ≤ isoDen ν (TwoScaleGood ν (ρ * ν)) (twoScaleIdx ν (ρ * ν) j + 1) :=
      isoDen_pos (ν := ν) (G := TwoScaleGood ν (ρ * ν)) (twoScaleIdx ν (ρ * ν) j)
    rw [hN]; exact_mod_cast h
  have hNj : (j : ℝ) ≤ N := by
    have h1 := idx_le_isoDen (ν := ν) (G := TwoScaleGood ν (ρ * ν)) (twoScaleIdx ν (ρ * ν) j + 1)
    have h2 := Lv.g_ge j
    have : j ≤ isoDen ν (TwoScaleGood ν (ρ * ν)) (twoScaleIdx ν (ρ * ν) j + 1) := by
      show j ≤ _; have : j + 1 ≤ twoScaleIdx ν (ρ * ν) j := h2; omega
    rw [hN]; exact_mod_cast this
  have h4 : 4 ≤ N ^ t := by
    have hc : (4 : ℝ) ^ (1 / t) ≤ N := by
      have h1 : (4 : ℝ) ^ (1 / t) ≤ ⌈(4 : ℝ) ^ (1 / t)⌉₊ := Nat.le_ceil _
      have h3 : ((⌈(4 : ℝ) ^ (1 / t)⌉₊ : ℕ) : ℝ) ≤ j := by
        exact_mod_cast (show ⌈(4 : ℝ) ^ (1 / t)⌉₊ ≤ j by omega)
      linarith
    calc (4 : ℝ) = ((4 : ℝ) ^ (1 / t)) ^ t := by
          rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel ht0.ne', Real.rpow_one]
      _ ≤ N ^ t := Real.rpow_le_rpow (by positivity) hc ht0.le
  have hgr := (twoScale_growth hν hρ1 j).2
  calc (isoDen ν (TwoScaleGood ν (ρ * ν)) (twoScaleIdx ν (ρ * ν) (j + 1)) : ℝ)
      ≤ 4 * N ^ ρ := hgr
    _ ≤ N ^ t * N ^ ρ := by gcongr
    _ = N ^ ρ' := by rw [← Real.rpow_add (by linarith), ht]; ring_nf

open Classical in
/-- **Two-scale slopes exist and attain `S(ν, ρ)`.** For every `ν > 1` and
`ρ > 1 + 3/ν` the two-scale slope has Diophantine class exactly `ν` and
`dim_H K_α = S(ν, ρ)`. -/
theorem twoScale_dims {ν ρ : ℝ} (hν : 1 < ν) (hρ : 1 + 3 / ν < ρ) :
    DiophClass (isoSlope ν (TwoScaleGood ν (ρ * ν))) ν ∧
    dimH (passageClusterSet (1 / isoSlope ν (TwoScaleGood ν (ρ * ν)))) =
      ENNReal.ofReal (twoScaleDim ν ρ) := by
  have hν0 : 0 < ν := by linarith
  have hρ1 : 1 ≤ ρ := by
    have : 0 < 3 / ν := by positivity
    linarith
  set Lv := twoScaleLevels ν (ρ * ν) hν.le
  exact ⟨isoSlope_diophClass hν Lv.frequent,
    twoScale_dimH_eq Lv hν hρ ⟨0, fun j _ => (twoScale_growth hν.le hρ1 j).1⟩
      (twoScale_up_rpow hν.le hρ1)⟩

end Problems.Juggler.BeattySlope

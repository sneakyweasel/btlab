import Problems.Juggler.BeattyIsoExact

/-!
# Two-scale slopes: the lower bound

An isolated slope whose good denominators grow by a fixed exponent,
`Q_(g(j+1)) ≥ Q_(g j)^R` from some level on, carries window masses
`M_(j+1) ≤ Q_j^(-1+η)` for every `η > (γ-1)/(R-1)`. The Frostman bound of
`BeattyIsoFrostman` then gives `H^s(K_α) > 0` whenever the two exponent
conditions hold with such an `η`.

For `ρ > 1 + 3/ν` and `R = ρν`, both conditions can be met at every
`s ≥ 2/(2+ν)` with `3(R-1)s² + 4(ρ-1)s - 4(ρ-1) < 0`: the window exponents
allowed by the two conditions form the interval `(γ₂(s), γ₁(s))`, and
`γ₁ - γ₂` has the sign of `-(3(R-1)s² + 4(ρ-1)s - 4(ρ-1))`.
-/

namespace Problems.Juggler.BeattySlope

open Filter Topology Set MeasureTheory

namespace IsoLevels

variable {ν γ B : ℝ} {G : ℕ → Prop} [DecidablePred G] {Lv : IsoLevels ν G B}
  (P : IsoParams ν γ B)

omit P in
/-- Enumerated good indices grow at least linearly. -/
theorem g_ge (Lv : IsoLevels ν G B) (j : ℕ) : j + 1 ≤ Lv.g j := by
  induction j with
  | zero => exact Lv.one_le
  | succ n ih => have := Lv.mono (Nat.lt_add_one n); omega

omit P in
/-- Good denominators are at least their level. -/
theorem den_ge_level (Lv : IsoLevels ν G B) (j : ℕ) : (j : ℝ) ≤ Lv.den j := by
  have h1 := idx_le_isoDen (ν := ν) (G := G) (Lv.g j)
  have h2 := Lv.g_ge j
  have : j ≤ isoDen ν G (Lv.g j) := by omega
  unfold den
  exact_mod_cast this

include P

/-- One level of window masses: `M_(j+2) Q_(j+1) ≤ 2 Q_j^(γ-1) (M_(j+1) Q_j)`. -/
theorem mass_den_step (j : ℕ) :
    (Lv.grid P).tree.mass (j + 2) * Lv.den (j + 1) ≤
      2 * Lv.den j ^ (γ - 1) * ((Lv.grid P).tree.mass (j + 1) * Lv.den j) := by
  set D := Lv.grid P
  have h := mass_step (Lv := Lv) P (j + 1)
  have hd : D.d (j + 1) = Lv.den j ^ (-γ) := rfl
  have hq2 : (D.q (j + 2) : ℝ) = Lv.den (j + 1) := rfl
  rw [hd, hq2] at h
  have hq := den_pos (Lv := Lv) P j
  have hq1 := den_pos (Lv := Lv) P (j + 1)
  have hdp : 0 < Lv.den j ^ (-γ) := Real.rpow_pos_of_pos hq _
  have hM := D.tree.mass_pos (j + 1)
  have hinv : Lv.den j ^ (-γ) * Lv.den j ^ (γ - 1) * Lv.den j = 1 := by
    rw [← Real.rpow_add hq, ← Real.rpow_add_one hq.ne',
      show -γ + (γ - 1) + 1 = (0 : ℝ) by ring, Real.rpow_zero]
  rw [le_div_iff₀ (mul_pos hdp hq1)] at h
  have : D.tree.mass (j + 2) * Lv.den (j + 1) * (Lv.den j ^ (-γ)) ≤
      2 * D.tree.mass (j + 1) := by nlinarith
  calc D.tree.mass (j + 2) * Lv.den (j + 1)
      = D.tree.mass (j + 2) * Lv.den (j + 1) * (Lv.den j ^ (-γ) * Lv.den j ^ (γ - 1) *
          Lv.den j) := by rw [hinv, mul_one]
    _ = (D.tree.mass (j + 2) * Lv.den (j + 1) * Lv.den j ^ (-γ)) *
          (Lv.den j ^ (γ - 1) * Lv.den j) := by ring
    _ ≤ (2 * D.tree.mass (j + 1)) * (Lv.den j ^ (γ - 1) * Lv.den j) :=
          mul_le_mul_of_nonneg_right this (by positivity)
    _ = _ := by ring

/-- Growth `Q_(j+1) ≥ Q_j^R'` bounds the product of the good denominators:
`(∏_(j1 ≤ i < j) Q_i) Q_(j1)^a ≤ Q_j^a` with `a = 1/(R'-1)`. -/
theorem prod_den_le {R' : ℝ} (hR' : 1 < R') {j1 : ℕ}
    (hg : ∀ j, j1 ≤ j → Lv.den j ^ R' ≤ Lv.den (j + 1)) :
    ∀ j, j1 ≤ j → (∏ i ∈ Finset.Ico j1 j, Lv.den i) * Lv.den j1 ^ (1 / (R' - 1)) ≤
      Lv.den j ^ (1 / (R' - 1)) := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => simp
  | succ j hj ih =>
    rw [Finset.prod_Ico_succ_top hj]
    have hq := den_pos (Lv := Lv) P j
    have ha : 0 < 1 / (R' - 1) := one_div_pos.2 (by linarith)
    have e : Lv.den j ^ (1 / (R' - 1)) * Lv.den j = (Lv.den j ^ R') ^ (1 / (R' - 1)) := by
      rw [← Real.rpow_mul hq.le, ← Real.rpow_add_one hq.ne']
      congr 1
      have : R' - 1 ≠ 0 := by linarith
      field_simp
      ring
    calc (∏ i ∈ Finset.Ico j1 j, Lv.den i) * Lv.den j * Lv.den j1 ^ (1 / (R' - 1))
        = ((∏ i ∈ Finset.Ico j1 j, Lv.den i) * Lv.den j1 ^ (1 / (R' - 1))) * Lv.den j := by
          ring
      _ ≤ Lv.den j ^ (1 / (R' - 1)) * Lv.den j := mul_le_mul_of_nonneg_right ih hq.le
      _ = (Lv.den j ^ R') ^ (1 / (R' - 1)) := e
      _ ≤ Lv.den (j + 1) ^ (1 / (R' - 1)) :=
          Real.rpow_le_rpow (by positivity) (hg j hj) ha.le

/-- Once `2 ≤ Q_j^δ`, window masses satisfy
`M_(j+1) Q_j ≤ (M_(j2+1) Q_(j2)) (∏_(j2 ≤ i < j) Q_i)^(γ-1+δ)`. -/
theorem mass_prod_le {δ : ℝ} (_hδ : 0 < δ) {j2 : ℕ} (h2 : ∀ j, j2 ≤ j → 2 ≤ Lv.den j ^ δ) :
    ∀ j, j2 ≤ j → (Lv.grid P).tree.mass (j + 1) * Lv.den j ≤
      ((Lv.grid P).tree.mass (j2 + 1) * Lv.den j2) *
        (∏ i ∈ Finset.Ico j2 j, Lv.den i) ^ (γ - 1 + δ) := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => simp
  | succ j hj ih =>
    rw [Finset.prod_Ico_succ_top hj]
    have hq := den_pos (Lv := Lv) P j
    have hst := mass_den_step (Lv := Lv) P j
    have hprod : 0 ≤ ∏ i ∈ Finset.Ico j2 j, Lv.den i :=
      Finset.prod_nonneg fun i _ => (den_pos (Lv := Lv) P i).le
    have hM := (Lv.grid P).tree.mass_pos (j + 1)
    rw [Real.mul_rpow hprod hq.le]
    have e : Lv.den j ^ (γ - 1 + δ) = Lv.den j ^ δ * Lv.den j ^ (γ - 1) := by
      rw [← Real.rpow_add hq]; ring_nf
    have hpos : 0 ≤ Lv.den j ^ (γ - 1) := by positivity
    calc (Lv.grid P).tree.mass (j + 1 + 1) * Lv.den (j + 1)
        ≤ 2 * Lv.den j ^ (γ - 1) * ((Lv.grid P).tree.mass (j + 1) * Lv.den j) := hst
      _ ≤ Lv.den j ^ δ * Lv.den j ^ (γ - 1) * (((Lv.grid P).tree.mass (j2 + 1) * Lv.den j2) *
            (∏ i ∈ Finset.Ico j2 j, Lv.den i) ^ (γ - 1 + δ)) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (h2 j hj) hpos) ih (by positivity)
            (by positivity)
      _ = _ := by rw [e]; ring

/-- **Window masses at a growth ratio.** If `Q_(j+1) ≥ Q_j^R'` from some level on,
then `M_(j+1) ≤ Q_j^(-1+η)` from some level on, for every `η > (γ-1)/(R'-1)`. -/
theorem twoScale_mass_eventually {R' η : ℝ} (hR' : 1 < R') {j1 : ℕ}
    (hg : ∀ j, j1 ≤ j → Lv.den j ^ R' ≤ Lv.den (j + 1)) (hη : (γ - 1) / (R' - 1) < η) :
    ∃ j0 : ℕ, ∀ j, j0 ≤ j → (Lv.grid P).tree.mass (j + 1) ≤ Lv.den j ^ (-1 + η) := by
  set a := 1 / (R' - 1) with ha_def
  have ha : 0 < a := one_div_pos.2 (by linarith)
  have hηa : a * (γ - 1) < η := by
    rw [ha_def, one_div_mul_eq_div]; exact hη
  set gap := η - a * (γ - 1) with hgap_def
  have hgap : 0 < gap := by linarith
  set δ := gap / (2 * a) with hδ_def
  have hδ : 0 < δ := by positivity
  set ε := gap / 2 with hε_def
  have hε : 0 < ε := by positivity
  have haδ : a * δ = gap / 2 := by rw [hδ_def]; field_simp
  -- the level from which `2 ≤ Q_j^δ`
  set j2 := max j1 ⌈(2 : ℝ) ^ (1 / δ)⌉₊ with hj2_def
  have h2 : ∀ j, j2 ≤ j → 2 ≤ Lv.den j ^ δ := by
    intro j hj
    have hc : (2 : ℝ) ^ (1 / δ) ≤ Lv.den j := by
      have h1 : (2 : ℝ) ^ (1 / δ) ≤ ⌈(2 : ℝ) ^ (1 / δ)⌉₊ := Nat.le_ceil _
      have h3 : (⌈(2 : ℝ) ^ (1 / δ)⌉₊ : ℝ) ≤ j := by
        exact_mod_cast (le_max_right _ _).trans hj
      exact h1.trans (h3.trans (Lv.den_ge_level j))
    calc (2 : ℝ) = ((2 : ℝ) ^ (1 / δ)) ^ δ := by
          rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hδ.ne', Real.rpow_one]
      _ ≤ Lv.den j ^ δ := Real.rpow_le_rpow (by positivity) hc hδ.le
  set C := (Lv.grid P).tree.mass (j2 + 1) * Lv.den j2 with hC_def
  have hC : 0 < C := mul_pos ((Lv.grid P).tree.mass_pos _) (den_pos (Lv := Lv) P j2)
  refine ⟨max j2 ⌈C ^ (1 / ε)⌉₊, fun j hj => ?_⟩
  have hj2 : j2 ≤ j := (le_max_left _ _).trans hj
  have hq := den_pos (Lv := Lv) P j
  have hq1 := den_one (Lv := Lv) P j
  -- the product bound from level `j2`
  have hg2 : ∀ i, j2 ≤ i → Lv.den i ^ R' ≤ Lv.den (i + 1) :=
    fun i hi => hg i ((le_max_left _ _).trans hi)
  have hp := prod_den_le (Lv := Lv) P hR' hg2 j hj2
  have hprod : 0 ≤ ∏ i ∈ Finset.Ico j2 j, Lv.den i :=
    Finset.prod_nonneg fun i _ => (den_pos (Lv := Lv) P i).le
  have hone : 1 ≤ Lv.den j2 ^ a := Real.one_le_rpow (den_one (Lv := Lv) P j2) ha.le
  have hp' : ∏ i ∈ Finset.Ico j2 j, Lv.den i ≤ Lv.den j ^ a := by
    calc ∏ i ∈ Finset.Ico j2 j, Lv.den i ≤ (∏ i ∈ Finset.Ico j2 j, Lv.den i) * Lv.den j2 ^ a :=
          le_mul_of_one_le_right hprod hone
      _ ≤ _ := hp
  have hm := mass_prod_le (Lv := Lv) P hδ h2 j hj2
  have hγ1 := P.γ1
  have hc0 : 0 ≤ γ - 1 + δ := by linarith
  -- `C ≤ Q_j^ε`
  have hCε : C ≤ Lv.den j ^ ε := by
    have hc : C ^ (1 / ε) ≤ Lv.den j := by
      have h1 : C ^ (1 / ε) ≤ ⌈C ^ (1 / ε)⌉₊ := Nat.le_ceil _
      have h3 : (⌈C ^ (1 / ε)⌉₊ : ℝ) ≤ j := by exact_mod_cast (le_max_right _ _).trans hj
      exact h1.trans (h3.trans (Lv.den_ge_level j))
    calc C = (C ^ (1 / ε)) ^ ε := by
          rw [← Real.rpow_mul hC.le, one_div_mul_cancel hε.ne', Real.rpow_one]
      _ ≤ Lv.den j ^ ε := Real.rpow_le_rpow (by positivity) hc hε.le
  have hbound : (Lv.grid P).tree.mass (j + 1) * Lv.den j ≤ Lv.den j ^ (ε + a * (γ - 1 + δ)) := by
    calc (Lv.grid P).tree.mass (j + 1) * Lv.den j
        ≤ C * (∏ i ∈ Finset.Ico j2 j, Lv.den i) ^ (γ - 1 + δ) := hm
      _ ≤ Lv.den j ^ ε * (Lv.den j ^ a) ^ (γ - 1 + δ) :=
          mul_le_mul hCε (Real.rpow_le_rpow hprod hp' hc0) (by positivity) (by positivity)
      _ = Lv.den j ^ (ε + a * (γ - 1 + δ)) := by
          rw [← Real.rpow_mul hq.le, ← Real.rpow_add hq]
  have hexp : ε + a * (γ - 1 + δ) = η := by
    rw [mul_add, haδ, hε_def, hgap_def]; ring
  rw [hexp] at hbound
  rw [← le_div_iff₀ hq] at hbound
  calc (Lv.grid P).tree.mass (j + 1) ≤ Lv.den j ^ η / Lv.den j := hbound
    _ = Lv.den j ^ (-1 + η) := by
        rw [Real.rpow_add hq, Real.rpow_neg_one]; field_simp

/-- **Two-scale Frostman.** With growth `Q_(j+1) ≥ Q_j^R'` and the exponent
conditions at some `η > (γ-1)/(R'-1)`, the cluster set has positive
`s`-dimensional Hausdorff measure. -/
theorem twoScale_hausdorff (Lv : IsoLevels ν G B) {R' s η : ℝ} (hR' : 1 < R') {j1 : ℕ}
    (hg : ∀ j, j1 ≤ j → Lv.den j ^ R' ≤ Lv.den (j + 1)) (hη : (γ - 1) / (R' - 1) < η)
    (hs : 0 < s) (hs23 : s < 2 / 3)
    (hE1 : γ - 1 + η ≤ ν * (1 - 3 * s / 2)) (hE2 : s * (3 + ν - γ) / 2 ≤ 1 - η) :
    Measure.hausdorffMeasure s (passageClusterSet (1 / isoSlope ν G)) ≠ 0 := by
  obtain ⟨j0, hM⟩ := twoScale_mass_eventually (Lv := Lv) P hR' hg hη
  exact hausdorff_ne_zero P Lv hs hs23 j0 hM hE1 hE2

end IsoLevels

/-- **Exponent choice for two-scale slopes.** Let `ν > 1`, `ρ > 1 + 3/ν`, `R = ρν`,
and `2/(2+ν) ≤ s` with `3(R-1)s² + 4(ρ-1)s - 4(ρ-1) < 0`. Then `s < 2/3`, and some
`γ ∈ (1, ν)` and `η > (γ-1)/(R-1)` satisfy both exponent conditions. -/
theorem twoScale_exponents {ν ρ s : ℝ} (hν : 1 < ν) (hρ : 1 + 3 / ν < ρ)
    (hs0 : 2 / (2 + ν) ≤ s)
    (hQ : 3 * (ρ * ν - 1) * s ^ 2 + 4 * (ρ - 1) * s - 4 * (ρ - 1) < 0) :
    s < 2 / 3 ∧ ∃ γ η : ℝ, 1 < γ ∧ γ < ν ∧ (γ - 1) / (ρ * ν - 1) < η ∧
      γ - 1 + η ≤ ν * (1 - 3 * s / 2) ∧ s * (3 + ν - γ) / 2 ≤ 1 - η := by
  obtain ⟨R, hR⟩ : ∃ R, R = ρ * ν := ⟨_, rfl⟩
  rw [← hR] at hQ ⊢
  have hν0 : 0 < ν := by linarith
  have hρν : ν + 3 < R := by
    have : 3 / ν < ρ - 1 := by linarith
    rw [div_lt_iff₀ hν0] at this
    rw [hR]; nlinarith
  have hR1 : 0 < R - 1 := by linarith
  have hR0 : 0 < R := by linarith
  have hρ1 : 0 < ρ - 1 := by
    have : 0 < 3 / ν := by positivity
    linarith
  have hρ0 : 0 < ρ := by linarith
  have hs_pos : 0 < s := lt_of_lt_of_le (by positivity) hs0
  have hs2 : 2 ≤ s * (2 + ν) := by
    rwa [div_le_iff₀ (by linarith)] at hs0
  have hsR : 2 < s * (R - 1) := by nlinarith
  -- `s < t = 2(R-ν)/(3(R-1))`, since `Q(t) > 0` and `Q` increases
  have hst : 3 * s * (R - 1) < 2 * (R - ν) := by
    by_contra hc
    push Not at hc
    set t := 2 * (R - ν) / (3 * (R - 1)) with ht
    have htle : t ≤ s := by rw [ht, div_le_iff₀ (by positivity)]; linarith
    have ht0 : 0 ≤ t := by
      rw [ht]; apply div_nonneg _ (by positivity); linarith
    have key : (3 * (R - 1) * t ^ 2 + 4 * (ρ - 1) * t - 4 * (ρ - 1)) * (3 * (R - 1)) =
        4 * (ρ - 1) * (ν - 1) * (ρ * ν - ν - 3) := by
      rw [ht]
      have : R - 1 ≠ 0 := hR1.ne'
      field_simp
      rw [hR]
      ring
    have hpos : 0 < 4 * (ρ - 1) * (ν - 1) * (ρ * ν - ν - 3) := by
      have : 0 < ρ * ν - ν - 3 := by rw [← hR]; linarith
      have : 0 < ν - 1 := by linarith
      positivity
    have hQt : 0 < 3 * (R - 1) * t ^ 2 + 4 * (ρ - 1) * t - 4 * (ρ - 1) := by
      rw [← key] at hpos
      exact pos_of_mul_pos_left hpos (by positivity)
    have hmono : 3 * (R - 1) * t ^ 2 + 4 * (ρ - 1) * t - 4 * (ρ - 1) ≤
        3 * (R - 1) * s ^ 2 + 4 * (ρ - 1) * s - 4 * (ρ - 1) := by nlinarith
    linarith
  have hs23 : s < 2 / 3 := by nlinarith
  refine ⟨hs23, ?_⟩
  -- the window interval `(γ₂, γ₁)`
  set D₂ := s * (R - 1) - 2 with hD₂
  have hD₂pos : 0 < D₂ := by rw [hD₂]; linarith
  set γ₁ := 1 + (R - 1) * ν * (1 - 3 * s / 2) / R with hγ₁
  set γ₂ := 1 + (R - 1) * (s * (2 + ν) - 2) / D₂ with hγ₂
  have h12 : γ₂ < γ₁ := by
    have key : (γ₁ - γ₂) * (2 * ρ * D₂) =
        -(3 * (R - 1) * s ^ 2 + 4 * (ρ - 1) * s - 4 * (ρ - 1)) * (R - 1) := by
      rw [hγ₁, hγ₂]
      have h2 : R ≠ 0 := hR0.ne'
      have h3 : D₂ ≠ 0 := hD₂pos.ne'
      field_simp
      rw [hD₂, hR]
      ring
    have hrhs : 0 < -(3 * (R - 1) * s ^ 2 + 4 * (ρ - 1) * s - 4 * (ρ - 1)) * (R - 1) := by
      have : 0 < -(3 * (R - 1) * s ^ 2 + 4 * (ρ - 1) * s - 4 * (ρ - 1)) := by linarith
      positivity
    have hden : 0 < 2 * ρ * D₂ := by positivity
    rw [← key] at hrhs
    exact sub_pos.1 (pos_of_mul_pos_left hrhs hden.le)
  have h2ν : γ₂ < ν := by
    have : (R - 1) * (s * (2 + ν) - 2) / D₂ < ν - 1 := by
      rw [div_lt_iff₀ hD₂pos, hD₂]; nlinarith
    rw [hγ₂]; linarith
  have h21 : 1 ≤ γ₂ := by
    rw [hγ₂]
    have : 0 ≤ (R - 1) * (s * (2 + ν) - 2) / D₂ :=
      div_nonneg (mul_nonneg hR1.le (by linarith)) hD₂pos.le
    linarith
  set m := min γ₁ ν with hm
  have h2m : γ₂ < m := lt_min h12 h2ν
  set γ := (γ₂ + m) / 2 with hγ
  have hγ2 : γ₂ < γ := by rw [hγ]; linarith
  have hγm : γ < m := by rw [hγ]; linarith
  have hγ1 : γ < γ₁ := hγm.trans_le (min_le_left _ _)
  have hγν : γ < ν := hγm.trans_le (min_le_right _ _)
  set η₀ := (γ - 1) / (R - 1) with hη₀
  have hE1 : γ - 1 + η₀ < ν * (1 - 3 * s / 2) := by
    have e : γ - 1 + η₀ = (γ - 1) * R / (R - 1) := by
      rw [hη₀]; field_simp; ring
    rw [e, div_lt_iff₀ hR1]
    have h : (γ - 1) * R < (R - 1) * ν * (1 - 3 * s / 2) := by
      have : γ - 1 < (R - 1) * ν * (1 - 3 * s / 2) / R := by
        have := hγ1; rw [hγ₁] at this; linarith
      rwa [lt_div_iff₀ hR0] at this
    linarith
  have hE2 : s * (3 + ν - γ) / 2 < 1 - η₀ := by
    have h : (R - 1) * (s * (2 + ν) - 2) < (γ - 1) * D₂ := by
      have : (R - 1) * (s * (2 + ν) - 2) / D₂ < γ - 1 := by
        have := hγ2; rw [hγ₂] at this; linarith
      rwa [div_lt_iff₀ hD₂pos] at this
    rw [hD₂] at h
    have e : 1 - η₀ - s * (3 + ν - γ) / 2 =
        ((γ - 1) * (s * (R - 1) - 2) - (R - 1) * (s * (2 + ν) - 2)) / (2 * (R - 1)) := by
      rw [hη₀]; field_simp; ring
    have : 0 < 1 - η₀ - s * (3 + ν - γ) / 2 := by
      rw [e]; apply div_pos (by linarith) (by positivity)
    linarith
  set sl := min (ν * (1 - 3 * s / 2) - (γ - 1 + η₀)) (1 - η₀ - s * (3 + ν - γ) / 2) with hsl
  have hsl0 : 0 < sl := lt_min (by linarith) (by linarith)
  have hsl1 := min_le_left (ν * (1 - 3 * s / 2) - (γ - 1 + η₀)) (1 - η₀ - s * (3 + ν - γ) / 2)
  have hsl2 := min_le_right (ν * (1 - 3 * s / 2) - (γ - 1 + η₀)) (1 - η₀ - s * (3 + ν - γ) / 2)
  refine ⟨γ, η₀ + sl / 2, by linarith, hγν, by rw [hη₀]; linarith, by linarith, by linarith⟩

/-- **Two-scale lower bound.** Let the good levels of an isolated slope grow by the
exponent `R = ρν`, `Q_(g(j+1)) ≥ Q_(g j)^R` from some level on, with `ρ > 1 + 3/ν`.
Then `dim_H K_α ≥ s` for every `s ≥ 2/(2+ν)` with `3(R-1)s² + 4(ρ-1)s - 4(ρ-1) < 0`. -/
theorem twoScale_dimH_ge {ν B ρ s : ℝ} {G : ℕ → Prop} [DecidablePred G]
    (Lv : IsoLevels ν G B) (hν : 1 < ν) (hρ : 1 + 3 / ν < ρ)
    (hg : ∃ j1, ∀ j, j1 ≤ j →
      (isoDen ν G (Lv.g j) : ℝ) ^ (ρ * ν) ≤ isoDen ν G (Lv.g (j + 1)))
    (hs0 : 2 / (2 + ν) ≤ s)
    (hQ : 3 * (ρ * ν - 1) * s ^ 2 + 4 * (ρ - 1) * s - 4 * (ρ - 1) < 0) :
    ENNReal.ofReal s ≤ dimH (passageClusterSet (1 / isoSlope ν G)) := by
  obtain ⟨hs23, γ, η, hγ1, hγν, hη, hE1, hE2⟩ := twoScale_exponents hν hρ hs0 hQ
  obtain ⟨B', P⟩ := exists_isoParams hγ1 hγν
  obtain ⟨k, hk⟩ := Lv.exists_floor_index B'
  obtain ⟨j1, hg⟩ := hg
  have hν0 : 0 < ν := by linarith
  have hR' : 1 < ρ * ν := by
    have : 3 / ν < ρ - 1 := by linarith
    rw [div_lt_iff₀ hν0] at this
    nlinarith
  have hg' : ∀ j, j1 ≤ j → (Lv.shift k B' hk).den j ^ (ρ * ν) ≤ (Lv.shift k B' hk).den (j + 1) := by
    intro j hj
    show (isoDen ν G (Lv.g (j + k)) : ℝ) ^ (ρ * ν) ≤ isoDen ν G (Lv.g (j + 1 + k))
    rw [show j + 1 + k = j + k + 1 by ring]
    exact hg (j + k) (by omega)
  have hs : 0 < s := lt_of_lt_of_le (by positivity) hs0
  have hne := IsoLevels.twoScale_hausdorff P (Lv.shift k B' hk) hR' hg' hη hs hs23 hE1 hE2
  have : ((s.toNNReal : NNReal) : ℝ) = s := Real.coe_toNNReal _ hs.le
  rw [← this] at hne
  exact le_dimH_of_hausdorffMeasure_ne_zero hne

end Problems.Juggler.BeattySlope

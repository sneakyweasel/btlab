import Problems.Juggler.BeattySlopeMeasureDim

/-!
# The packing dimension of the limit law

At a convergent `q` every phase interval longer than `4/q` holds an orbit point
of index below `q`, whose atom weighs at least `A q^(-3/2)`. So at the radius
`r = A q^(-3/2)/3` every ball carries law mass at most `4/q ≍ r^(2/3)`, at every
irrational slope. Counting grid intervals of length `r` then shows that every
set of positive law mass has `r`-neighbourhood volume at least `c r^(1/3)`
along these radii, so its modified upper box (packing) dimension is at least
`2/3`. Hence the limit law has packing dimension `2/3` for every irrational
slope, while its Hausdorff dimension is `2/(1+ω)`: the two agree exactly when
the irrationality exponent is `2`.
-/

namespace Problems.Juggler.BeattySlope

open Filter Topology Set MeasureTheory BeattyPhase
open scoped NNReal ENNReal

/-- A lower tube bound along radii accumulating at zero forces upper box
dimension at least `d`. -/
theorem le_upperBoxDim_of_tube_freq {F : Set ℝ} {c d : ℝ} (hc : 0 < c)
    (h : ∃ᶠ ε in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (c * ε ^ (1 - d)) ≤ volume (Metric.thickening ε F)) :
    ENNReal.ofReal d ≤ upperBoxDim F := by
  refine le_iInf₂ fun s hs => ?_
  rw [← ENNReal.ofReal_coe_nnreal]
  refine ENNReal.ofReal_le_ofReal (not_lt.1 fun hsd => ?_)
  obtain ⟨C, hC⟩ := hs
  have hp : 0 < d - s := sub_pos.2 hsd
  have hsmall : Tendsto (fun ε : ℝ => C * ε ^ (d - s)) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun ε : ℝ => ε ^ (d - s)) (𝓝 0) (𝓝 0) := by
      simpa [Real.zero_rpow hp.ne'] using
        (Real.continuousAt_rpow_const 0 (d - s) (Or.inr hp.le)).tendsto
    simpa using (h0.mono_left nhdsWithin_le_nhds).const_mul C
  obtain ⟨ε, ⟨hlo, hup, hε⟩, hlt⟩ := ((h.and_eventually
    (hC.and self_mem_nhdsWithin)).and_eventually ((tendsto_order.1 hsmall).2 c hc)).exists
  have hε0 : (0 : ℝ) < ε := hε
  have ha : 0 < c * ε ^ (1 - d) := mul_pos hc (Real.rpow_pos_of_pos hε0 _)
  have hle : c * ε ^ (1 - d) ≤ C * ε ^ (1 - (s : ℝ)) := by
    rcases ENNReal.ofReal_le_ofReal_iff'.1 (hlo.trans hup) with h1 | h1
    · exact h1
    · exact absurd h1 (not_le.2 ha)
  have he : C * ε ^ (1 - (s : ℝ)) = (C * ε ^ (d - s)) * ε ^ (1 - d) := by
    rw [mul_assoc, ← Real.rpow_add hε0]; ring_nf
  rw [he] at hle
  have := le_of_mul_le_mul_right hle (Real.rpow_pos_of_pos hε0 _)
  linarith

/-- **Grid counting.** If every ball of radius `r` has `μ`-mass at most `M`,
then `μ(E) r ≤ M λ(E_r)` for every set `E`. -/
theorem measure_mul_le_thickening {μ : Measure ℝ} {r : ℝ} (hr : 0 < r) {M : ℝ≥0∞}
    (hM : ∀ y, μ (Metric.ball y r) ≤ M) (E : Set ℝ) :
    μ E * ENNReal.ofReal r ≤ M * volume (Metric.thickening r E) := by
  classical
  set J : ℤ → Set ℝ := fun i => Ico ((i : ℝ) * r) (((i : ℝ) + 1) * r) with hJ
  set I : Set ℤ := {i | (J i ∩ E).Nonempty}
  have hI : I.Countable := Set.to_countable I
  have hcov : E ⊆ ⋃ i ∈ I, J i := by
    intro x hx
    set i := ⌊x / r⌋
    have h1 : (i : ℝ) ≤ x / r := Int.floor_le _
    have h2 : x / r < (i : ℝ) + 1 := Int.lt_floor_add_one _
    have hxJ : x ∈ J i := by
      refine ⟨?_, ?_⟩
      · have := mul_le_mul_of_nonneg_right h1 hr.le; rwa [div_mul_cancel₀ _ hr.ne'] at this
      · have := mul_lt_mul_of_pos_right h2 hr; rwa [div_mul_cancel₀ _ hr.ne'] at this
    exact mem_iUnion₂.2 ⟨i, ⟨x, hxJ, hx⟩, hxJ⟩
  have hsub : (⋃ i ∈ I, J i) ⊆ Metric.thickening r E := by
    intro y hy
    obtain ⟨i, ⟨x, hxJ, hxE⟩, hyJ⟩ := mem_iUnion₂.1 hy
    refine Metric.mem_thickening_iff.2 ⟨x, hxE, ?_⟩
    rw [Real.dist_eq, abs_lt]
    simp only [hJ, mem_Ico] at hxJ hyJ
    constructor <;> nlinarith [hxJ.1, hxJ.2, hyJ.1, hyJ.2]
  have hdisj : I.PairwiseDisjoint J := by
    intro i _ j _ hij
    refine disjoint_left.2 fun x hxi hxj => hij ?_
    simp only [hJ, mem_Ico] at hxi hxj
    have a1 : (i : ℝ) < (j : ℝ) + 1 := by
      by_contra h; push Not at h; nlinarith [mul_le_mul_of_nonneg_right h hr.le]
    have a2 : (j : ℝ) < (i : ℝ) + 1 := by
      by_contra h; push Not at h; nlinarith [mul_le_mul_of_nonneg_right h hr.le]
    have b1 : i < j + 1 := by exact_mod_cast a1
    have b2 : j < i + 1 := by exact_mod_cast a2
    omega
  have hball (i : ℤ) : J i ⊆ Metric.ball (((i : ℝ) + 1/2) * r) r := by
    intro x hx
    simp only [hJ, mem_Ico] at hx
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> nlinarith
  have hvol : volume (⋃ i ∈ I, J i) = ∑' i : I, ENNReal.ofReal r := by
    rw [measure_biUnion hI hdisj (fun i _ => measurableSet_Ico)]
    congr 1; funext i
    simp only [hJ, Real.volume_Ico]
    ring_nf
  have hμ : μ E ≤ ∑' i : I, M :=
    (measure_mono hcov).trans ((measure_biUnion_le μ hI J).trans
      (ENNReal.tsum_le_tsum fun i => (measure_mono (hball i)).trans (hM _)))
  calc μ E * ENNReal.ofReal r ≤ (∑' i : I, M) * ENNReal.ofReal r := by gcongr
    _ = M * ∑' i : I, ENNReal.ofReal r := by
        rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
    _ = M * volume (⋃ i ∈ I, J i) := by rw [hvol]
    _ ≤ M * volume (Metric.thickening r E) := by gcongr

/-- The radius identity `4/Q · c r^(1/3) = m r` for `r = A Q^(-3/2)/3`. -/
theorem conv_radius_identity {A Q m : ℝ} (hA : 0 < A) (hQ : 0 < Q) :
    4 / Q * (m * (A / 3) ^ (2/3 : ℝ) / 4 * (A / Q ^ (3/2 : ℝ) / 3) ^ (1 - 2/3 : ℝ)) =
      m * (A / Q ^ (3/2 : ℝ) / 3) := by
  have hA3 : 0 < A / 3 := by positivity
  have hr : A / Q ^ (3/2 : ℝ) / 3 = (A / 3) * Q ^ (-(3/2) : ℝ) := by
    rw [Real.rpow_neg hQ.le]; ring
  rw [hr, show (1 : ℝ) - 2/3 = 1/3 by norm_num,
    Real.mul_rpow hA3.le (Real.rpow_nonneg hQ.le _), ← Real.rpow_mul hQ.le]
  have h1 : (A / 3) ^ (2/3 : ℝ) * (A / 3) ^ (1/3 : ℝ) = A / 3 := by
    rw [← Real.rpow_add hA3]; norm_num
  have h2 : Q ^ (-(3/2) * (1/3) : ℝ) = Q ^ (-(1/2) : ℝ) := by norm_num
  have h3 : Q⁻¹ * Q ^ (-(1/2) : ℝ) = Q ^ (-(3/2) : ℝ) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hQ]; norm_num
  rw [h2]
  calc 4 / Q * (m * (A / 3) ^ (2/3 : ℝ) / 4 * ((A / 3) ^ (1/3 : ℝ) * Q ^ (-(1/2) : ℝ)))
      = m * ((A / 3) ^ (2/3 : ℝ) * (A / 3) ^ (1/3 : ℝ)) * (Q⁻¹ * Q ^ (-(1/2) : ℝ)) := by
        field_simp
    _ = _ := by rw [h1, h3]; ring

/-- The packing dimension of a measure on the line: the least modified upper
box dimension of a set of positive mass. -/
noncomputable def lawDimP (μ : Measure ℝ) : ℝ≥0∞ :=
  ⨅ (E : Set ℝ) (_ : 0 < μ E), modUpperBoxDim E

section Passage

variable {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ : Irrational β)

include hβ0 hβ1 hβ

/-- **Uniform small balls at convergent radii.** With `Q` a continued-fraction
denominator of `1/β` and `A` the lower weight constant, every ball of radius
`A Q^(-3/2)/3` has law mass at most `4/Q`. -/
theorem passageLaw_ball_le {A : ℝ} (hA : 0 < A)
    (hwA : ∀ k : ℕ, A / ((k : ℝ) + 1) ^ (3/2 : ℝ) ≤ passageJumpWeight β (k+1)) (n : ℕ) (y : ℝ) :
    (passageLaw hβ0 hβ1 hβ : Measure ℝ)
      (Metric.ball y (A / (cfDen (cfDigits (1/β)) (n + 1) : ℝ) ^ (3/2 : ℝ) / 3)) ≤
      ENNReal.ofReal (4 / (cfDen (cfDigits (1/β)) (n + 1) : ℝ)) := by
  classical
  have hα : Irrational (1/β) := by simpa using hβ.inv
  have h0 : 0 < 1/β := one_div_pos.2 hβ0
  set dg := cfDigits (1/β)
  have hdg : ∀ k, 1 ≤ dg (k + 1) := cfDigits_succ_ge hα
  have hG := irrational_goodConvergents hα h0.le
  set Q := cfDen dg (n + 1)
  have hQ0 : 0 < Q := hG.pos n
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ0
  set r := A / (Q : ℝ) ^ (3/2 : ℝ) / 3 with hrdef
  have hQ32 : 0 < (Q : ℝ) ^ (3/2 : ℝ) := Real.rpow_pos_of_pos hQR _
  have happr : |1/β - ((cfNum dg (n + 1) : ℤ) : ℝ) / Q| ≤ 1 / (Q : ℝ) ^ 2 := by
    have h := hG.approx n
    have hmono : (Q : ℝ) ≤ cfDen dg (n + 1 + 1) := by exact_mod_cast cfDen_le_succ hdg (n + 1)
    have h' : |(Q : ℝ) * (1/β) - ((cfNum dg (n + 1) : ℤ) : ℝ)| ≤ 1 / (Q : ℝ) :=
      h.trans (one_div_le_one_div_of_le hQR hmono)
    have e : 1/β - ((cfNum dg (n + 1) : ℤ) : ℝ) / Q =
        ((Q : ℝ) * (1/β) - ((cfNum dg (n + 1) : ℤ) : ℝ)) / Q := by field_simp
    rw [e, abs_div, abs_of_pos hQR, div_le_iff₀ hQR]
    calc _ ≤ 1 / (Q : ℝ) := h'
      _ = 1 / (Q : ℝ) ^ 2 * Q := by field_simp
  have hcop := hG.coprime n
  have hfr : ∀ k : ℕ, passagePhase β (k+1) = Int.fract (((k : ℝ) + 1) * (1/β)) :=
    passagePhase_succ_fract hβ0
  have hmeas := (passageProfile_monotone hβ0 hβ1 hβ).measurable
  have mono := passageProfile_monotone hβ0 hβ1 hβ
  rw [passageLaw, ProbabilityMeasure.toMeasure_map,
    Measure.map_apply hmeas Metric.isOpen_ball.measurableSet]
  change (volume.restrict (Ioc (0 : ℝ) 1)) _ ≤ _
  rw [Measure.restrict_apply (hmeas Metric.isOpen_ball.measurableSet)]
  refine (Real.volume_le_diam _).trans (Metric.ediam_le fun t₁ ht₁ t₂ ht₂ => ?_)
  rw [edist_dist, Real.dist_eq]
  apply ENNReal.ofReal_le_ofReal
  -- two phases in the preimage are within `4/Q`
  have key (u v : ℝ) (hu : u ∈ passageProfile β ⁻¹' Metric.ball y r ∩ Ioc 0 1)
      (hv : v ∈ passageProfile β ⁻¹' Metric.ball y r ∩ Ioc 0 1) (huv : u ≤ v) :
      v - u ≤ 4 / Q := by
    by_contra hlt
    push Not at hlt
    have hshort := gap_short_of_approx hfr hQ0 hcop happr (c := u) (d := v) hu.2.1.le hv.2.2
    by_cases hno : ∀ k : ℕ, k + 1 < Q → passagePhase β (k+1) ∉ Ioo u v
    · exact absurd (hshort hno) (not_le.2 hlt)
    push Not at hno
    obtain ⟨k, hkQ, hk⟩ := hno
    have h1 : passageProfile β u ≤ passageProfile β (passagePhase β (k+1)) := mono hk.1.le
    have h2 := passageGap_right_le hβ0 hβ1 hβ k hk.2
    have hk1 : ((k : ℝ) + 1) ^ (3/2 : ℝ) ≤ (Q : ℝ) ^ (3/2 : ℝ) := by
      apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
      have : k + 1 ≤ Q := hkQ.le
      exact_mod_cast this
    have hw : A / (Q : ℝ) ^ (3/2 : ℝ) ≤ passageJumpWeight β (k+1) :=
      (div_le_div_of_nonneg_left hA.le (by positivity) hk1).trans (hwA k)
    have hbu := hu.1
    have hbv := hv.1
    simp only [mem_preimage, Metric.mem_ball, Real.dist_eq, abs_lt] at hbu hbv
    have hr : A / (Q : ℝ) ^ (3/2 : ℝ) = 3 * r := by rw [hrdef]; ring
    linarith [hbu.1, hbu.2, hbv.1, hbv.2]
  rcases le_total t₁ t₂ with h | h
  · rw [abs_sub_comm, abs_of_nonneg (by linarith)]; exact key t₁ t₂ ht₁ ht₂ h
  · rw [abs_of_nonneg (by linarith)]; exact key t₂ t₁ ht₂ ht₁ h

/-- **Every set of positive law mass has packing dimension at least `2/3`.**
The lower tube bound `λ(E_r) ≥ c r^(1/3)` holds along the convergent radii. -/
theorem passageLaw_upperBoxDim_ge {E : Set ℝ} (hE : 0 < (passageLaw hβ0 hβ1 hβ : Measure ℝ) E) :
    ENNReal.ofReal (2/3) ≤ upperBoxDim E := by
  classical
  obtain ⟨A, B, hA, hB, hwB⟩ := passageWeight_three_halves hβ0 hβ1 hβ
  have hwA : ∀ k : ℕ, A / ((k : ℝ) + 1) ^ (3/2 : ℝ) ≤ passageJumpWeight β (k+1) :=
    fun k => (hwB k).1
  have hα : Irrational (1/β) := by simpa using hβ.inv
  set dg := cfDigits (1/β)
  have hdg : ∀ k, 1 ≤ dg (k + 1) := cfDigits_succ_ge hα
  set μ := (passageLaw hβ0 hβ1 hβ : Measure ℝ)
  have hfin : μ E ≠ ⊤ := measure_ne_top _ _
  set m := (μ E).toReal
  have hm : 0 < m := ENNReal.toReal_pos hE.ne' hfin
  set c := m * (A / 3) ^ (2/3 : ℝ) / 4
  have hc : 0 < c := by positivity
  set Qf : ℕ → ℝ := fun n => (cfDen dg (n + 1) : ℝ)
  set rf : ℕ → ℝ := fun n => A / Qf n ^ (3/2 : ℝ) / 3
  have hQpos (n : ℕ) : 0 < Qf n := by
    simp only [Qf]; exact_mod_cast cfDen_succ_pos hdg n
  have hrpos (n : ℕ) : 0 < rf n := by
    simp only [rf]; have := Real.rpow_pos_of_pos (hQpos n) (3/2 : ℝ); positivity
  have hQtend : Tendsto Qf atTop atTop :=
    tendsto_natCast_atTop_atTop.comp ((cfDen_tendsto hdg).comp (tendsto_add_atTop_nat 1))
  have hrtend : Tendsto rf atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have h1 : Tendsto (fun n => Qf n ^ (3/2 : ℝ)) atTop atTop :=
        (tendsto_rpow_atTop (by norm_num)).comp hQtend
      have h2 := (h1.inv_tendsto_atTop).const_mul (A / 3)
      simp only [mul_zero] at h2
      refine h2.congr fun n => ?_
      simp only [rf, Pi.inv_apply]; ring
    · exact Eventually.of_forall fun n => hrpos n
  apply le_upperBoxDim_of_tube_freq hc
  refine hrtend.frequently (Eventually.frequently (Eventually.of_forall fun n => ?_))
  -- the lower tube bound at radius `rf n`
  have hball := passageLaw_ball_le hβ0 hβ1 hβ hA hwA n
  have hgrid := measure_mul_le_thickening (hrpos n) hball E
  have hM0 : ENNReal.ofReal (4 / Qf n) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact div_pos (by norm_num) (hQpos n)
  rw [← ENNReal.mul_le_mul_iff_right hM0 ENNReal.ofReal_ne_top]
  refine le_trans (le_of_eq ?_) hgrid
  rw [← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  congr 1
  exact conv_radius_identity hA (hQpos n)

/-- **The packing dimension of the law.** For every irrational boundary the
limit law has packing dimension exactly `2/3`. -/
theorem passageLaw_lawDimP_eq :
    lawDimP (passageLaw hβ0 hβ1 hβ : Measure ℝ) = ENNReal.ofReal (2/3) := by
  apply le_antisymm
  · refine iInf_le_of_le (passageClusterSet β) (iInf_le_of_le ?_
      (passageCluster_modUpperBoxDim hβ0 hβ1 hβ).le)
    rw [passageLaw_cluster hβ0 hβ1 hβ]; exact one_pos
  · refine le_iInf₂ fun E hE => le_iInf₂ fun G hG => ?_
    by_contra hlt
    push Not at hlt
    have hnull : ∀ i, (passageLaw hβ0 hβ1 hβ : Measure ℝ) (G i) = 0 := by
      intro i
      by_contra hne
      have hpos : 0 < (passageLaw hβ0 hβ1 hβ : Measure ℝ) (G i) := pos_iff_ne_zero.2 hne
      exact absurd ((passageLaw_upperBoxDim_ge hβ0 hβ1 hβ hpos).trans
        (le_iSup (fun i => upperBoxDim (G i)) i))
        (not_le.2 hlt)
    have := measure_mono (μ := (passageLaw hβ0 hβ1 hβ : Measure ℝ)) hG
    rw [measure_iUnion_null hnull] at this
    exact absurd (le_antisymm this bot_le) hE.ne'

end Passage

/-- **Hausdorff against packing for the law.** At an irrational slope `α > 1`
of Diophantine class `ν ≥ 1` the limit law has packing dimension `2/3` and
Hausdorff dimension `2/(2+ν)`; they agree exactly when `ν = 1`, that is, when
the irrationality exponent is `2`. -/
theorem passageLaw_dims_eq_iff {α ν : ℝ} (hα1 : 1 < α) (hα : Irrational α) (hν : 1 ≤ ν)
    (hcls : DiophClass α ν) :
    lawDimP (passageLaw (β := 1/α) (one_div_pos.2 (by linarith))
      ((div_lt_one (by linarith)).2 hα1) (by simpa using hα.inv) : Measure ℝ) =
      ENNReal.ofReal (2/3) ∧
    (lawDimH (passageLaw (β := 1/α) (one_div_pos.2 (by linarith))
      ((div_lt_one (by linarith)).2 hα1) (by simpa using hα.inv) : Measure ℝ) =
      lawDimP (passageLaw (β := 1/α) (one_div_pos.2 (by linarith))
        ((div_lt_one (by linarith)).2 hα1) (by simpa using hα.inv) : Measure ℝ) ↔ ν = 1) := by
  have hP := passageLaw_lawDimP_eq (β := 1/α) (one_div_pos.2 (by linarith))
    ((div_lt_one (by linarith)).2 hα1) (by simpa using hα.inv)
  refine ⟨hP, ?_⟩
  rw [hP, passageLaw_lawDimH_eq hα1 hα hν hcls,
    ENNReal.ofReal_eq_ofReal_iff (by positivity) (by norm_num)]
  constructor
  · intro h
    rw [div_eq_div_iff (by linarith) (by norm_num)] at h
    linarith
  · rintro rfl; norm_num

end Problems.Juggler.BeattySlope

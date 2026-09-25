import Problems.Juggler.BeattySlopeCantor
import Problems.Juggler.BeattySlopeLocalCounting
import Problems.Juggler.BeattyLocalVolume
import Problems.Juggler.BeattySlopeIrrExp

/-!
# Universal packing dimension two-thirds

For a set `F ⊆ ℝ` the upper box dimension is read from its neighbourhood
volumes: `F` has tube exponent `s` when `λ(F_ε) ≤ C ε^(1-s)` for small `ε`,
and `upperBoxDim F` is the infimum of such `s`. The modified upper box
dimension `modUpperBoxDim F` is the infimum, over countable covers of `F`, of
the largest upper box dimension of a cover member; for compact sets in `ℝ` it
equals the packing dimension (Falconer, *Fractal Geometry*, §3.3, not
formalized here).

For every irrational boundary every relatively open piece of the cluster set
contains a phase window. Counting the gaps whose phase lies in that window
gives the local tube bound `λ((K ∩ U)_ε) ≥ c ε^(1/3)`. By Baire's theorem
every countable cover has a member whose closure contains such a piece, so
`modUpperBoxDim K_α = 2/3` for every irrational slope. The Hausdorff
dimension, by contrast, takes every value in `[0, 2/3]`.
-/

namespace Problems.Juggler.BeattySlope

open Filter Topology Set MeasureTheory BeattyPhase
open scoped NNReal ENNReal

/-! ### Box dimensions from neighbourhood volumes -/

/-- `F` has tube exponent `s`: `λ(F_ε) ≤ C ε^(1-s)` for all small `ε > 0`. -/
def TubeExponent (F : Set ℝ) (s : ℝ) : Prop :=
  ∃ C : ℝ, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
    volume (Metric.thickening ε F) ≤ ENNReal.ofReal (C * ε ^ (1 - s))

/-- Upper box dimension of a subset of the line, from neighbourhood volumes. -/
noncomputable def upperBoxDim (F : Set ℝ) : ℝ≥0∞ :=
  ⨅ (s : ℝ≥0) (_ : TubeExponent F s), (s : ℝ≥0∞)

/-- Modified upper box dimension: the infimum over countable covers of the
largest upper box dimension of a cover member. -/
noncomputable def modUpperBoxDim (F : Set ℝ) : ℝ≥0∞ :=
  ⨅ (G : ℕ → Set ℝ) (_ : F ⊆ ⋃ i, G i), ⨆ i, upperBoxDim (G i)

/-- Upper box dimension is monotone. -/
theorem upperBoxDim_mono {F G : Set ℝ} (h : F ⊆ G) : upperBoxDim F ≤ upperBoxDim G := by
  refine le_iInf₂ fun s hs => iInf₂_le s ?_
  obtain ⟨C, hC⟩ := hs
  exact ⟨C, hC.mono fun ε hε => (measure_mono (Metric.thickening_subset_of_subset ε h)).trans hε⟩

/-- A set and its closure have the same upper box dimension. -/
theorem upperBoxDim_closure (F : Set ℝ) : upperBoxDim (closure F) = upperBoxDim F := by
  simp only [upperBoxDim, TubeExponent, Metric.thickening_closure]

/-- A tube exponent bounds the upper box dimension. -/
theorem upperBoxDim_le_of_tube {F : Set ℝ} {s : ℝ≥0} (h : TubeExponent F s) :
    upperBoxDim F ≤ s :=
  iInf₂_le s h

/-- A lower tube bound `λ(F_ε) ≥ c ε^(1-d)` forces upper box dimension at least `d`. -/
theorem le_upperBoxDim_of_tube {F : Set ℝ} {c d : ℝ} (hc : 0 < c)
    (h : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ENNReal.ofReal (c * ε ^ (1 - d)) ≤ volume (Metric.thickening ε F)) :
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
  obtain ⟨ε, ⟨⟨hlo, hup⟩, hε⟩, hlt⟩ :=
    (h.and hC |>.and self_mem_nhdsWithin |>.and ((tendsto_order.1 hsmall).2 c hc)).exists
  have hε0 : (0 : ℝ) < ε := hε
  have ha : 0 < c * ε ^ (1 - d) := mul_pos hc (Real.rpow_pos_of_pos hε0 _)
  have hle : c * ε ^ (1 - d) ≤ C * ε ^ (1 - (s : ℝ)) := by
    have := (ENNReal.ofReal_le_ofReal_iff'.1 (hlo.trans hup))
    rcases this with h1 | h1
    · exact h1
    · exact absurd h1 (not_le.2 ha)
  have he : C * ε ^ (1 - (s : ℝ)) = (C * ε ^ (d - s)) * ε ^ (1 - d) := by
    rw [mul_assoc, ← Real.rpow_add hε0]; ring_nf
  rw [he] at hle
  have := le_of_mul_le_mul_right hle (Real.rpow_pos_of_pos hε0 _)
  linarith

/-- The modified upper box dimension is at most the upper box dimension. -/
theorem modUpperBoxDim_le (F : Set ℝ) : modUpperBoxDim F ≤ upperBoxDim F :=
  (iInf₂_le (fun _ : ℕ => F) (by intro x hx; exact mem_iUnion.2 ⟨0, hx⟩)).trans (iSup_le fun _ => le_rfl)

/-! ### The cluster set: local tube bounds -/

variable {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ : Irrational β)

include hβ0 hβ1 hβ

private theorem w_summable : Summable (fun r => passageJumpWeight β (r+1)) :=
  (passage_jump_weights_hasSum hβ0 hβ1 hβ).summable

omit hβ in
private theorem w_nonneg (r : ℕ) : 0 ≤ passageJumpWeight β (r+1) :=
  passageJumpWeight_nonneg hβ0 hβ1 _

private theorem phase_inj : Function.Injective (fun r => passagePhase β (r+1)) :=
  (passagePhase_injective hβ0 hβ1 hβ).comp (add_left_injective 1)

private theorem phase_mem (r : ℕ) : passagePhase β (r+1) ∈ Ioo (0 : ℝ) 1 :=
  ⟨passagePhase_pos hβ0 hβ1 hβ (by omega), (passagePhase_mem_Ico hβ0 _).2⟩

/-- The profile is constant outside the unit phase interval. -/
theorem passageProfile_clamp (x : ℝ) :
    passageProfile β (max 0 (min x 1)) = passageProfile β x := by
  unfold passageProfile jumpProfile
  congr 1
  refine tsum_congr fun n => ?_
  have hp := phase_mem hβ0 hβ1 hβ n
  have hiff : passagePhase β (n+1) < max 0 (min x 1) ↔ passagePhase β (n+1) < x := by
    simp [not_lt.2 hp.1.le, hp.2]
  simp only [hiff]

/-- The right end of a gap lies below the profile at every later phase. -/
theorem passageGap_right_le (n : ℕ) {y : ℝ} (hy : passagePhase β (n+1) < y) :
    passageProfile β (passagePhase β (n+1)) + passageJumpWeight β (n+1) ≤ passageProfile β y := by
  have hw := w_summable hβ0 hβ1 hβ
  have hn := w_nonneg hβ0 hβ1
  have hj := jumpProfile_jump hw hn (phase_inj hβ0 hβ1 hβ) n
  have hr : jumpProfileRight (fun r => passagePhase β (r+1)) (fun r => passageJumpWeight β (r+1))
      (passagePhase β (n+1)) ≤
      jumpProfile (fun r => passagePhase β (r+1)) (fun r => passageJumpWeight β (r+1)) y :=
    le_of_tendsto (jumpProfile_tendsto_right hw hn _)
      (by filter_upwards [Ioo_mem_nhdsGT hy] with x hx
          exact jumpProfile_monotone hw hn hx.2.le)
  unfold passageProfile
  linarith

/-- Every open interval meeting the cluster set contains the profile image of
a nondegenerate phase window. -/
theorem exists_phase_window {u v : ℝ} (hK : (passageClusterSet β ∩ Ioo u v).Nonempty) :
    ∃ t₁ t₂ : ℝ, 0 ≤ t₁ ∧ t₁ < t₂ ∧ t₂ ≤ 1 ∧ ∀ t ∈ Icc t₁ t₂, passageProfile β t ∈ Ioo u v := by
  obtain ⟨y, hyK, hyU⟩ := hK
  have hcl := passageClusterSet_eq_closure_range hβ0 hβ1 hβ
  have h1 : (Ioo u v ∩ range (passageProfile β)).Nonempty := by
    rw [hcl] at hyK; exact mem_closure_iff.1 hyK _ isOpen_Ioo hyU
  obtain ⟨_, hx1U, x1, rfl⟩ := h1
  have h2 : ∃ z ∈ passageClusterSet β, z ∈ Ioo u v ∧ z ≠ passageProfile β x1 := by
    by_cases hy : y = passageProfile β x1
    · obtain ⟨z, ⟨hzU, hzK⟩, hzne⟩ := accPt_iff_nhds.1
        ((perfect_passageClusterSet hβ0 hβ1 hβ).acc y hyK) _ (isOpen_Ioo.mem_nhds hyU)
      exact ⟨z, hzK, hzU, hy ▸ hzne⟩
    · exact ⟨y, hyK, hyU, hy⟩
  obtain ⟨z, hzK, hzU, hzne⟩ := h2
  have h3 : ((Ioo u v \ {passageProfile β x1}) ∩ range (passageProfile β)).Nonempty := by
    rw [hcl] at hzK
    exact mem_closure_iff.1 hzK _ (isOpen_Ioo.sdiff isClosed_singleton) ⟨hzU, hzne⟩
  obtain ⟨_, ⟨hx2U, hx2ne⟩, x2, rfl⟩ := h3
  have e1 := passageProfile_clamp hβ0 hβ1 hβ x1
  have e2 := passageProfile_clamp hβ0 hβ1 hβ x2
  have hI (x : ℝ) : max 0 (min x 1) ∈ Icc (0 : ℝ) 1 :=
    ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
  have hne : max 0 (min x1 1) ≠ max 0 (min x2 1) := fun h =>
    hx2ne (by rw [mem_singleton_iff, ← e2, ← h, e1])
  have mono := passageProfile_monotone hβ0 hβ1 hβ
  rcases lt_or_gt_of_ne hne with h | h
  · refine ⟨_, _, (hI x1).1, h, (hI x2).2, fun t ht => ⟨?_, ?_⟩⟩
    · calc u < passageProfile β x1 := hx1U.1
        _ = _ := e1.symm
        _ ≤ _ := mono ht.1
    · calc passageProfile β t ≤ passageProfile β (max 0 (min x2 1)) := mono ht.2
        _ = _ := e2
        _ < v := hx2U.2
  · refine ⟨_, _, (hI x2).1, h, (hI x1).2, fun t ht => ⟨?_, ?_⟩⟩
    · calc u < passageProfile β x2 := hx2U.1
        _ = _ := e2.symm
        _ ≤ _ := mono ht.1
    · calc passageProfile β t ≤ passageProfile β (max 0 (min x1 1)) := mono ht.2
        _ = _ := e1
        _ < v := hx1U.2

/-- The gap-count density between two profile levels has positive integral. -/
theorem tailDensity_gap_pos {t₁ t₂ : ℝ} (h0 : 0 ≤ t₁) (h12 : t₁ < t₂) (h1 : t₂ ≤ 1) :
    0 < (∫ t in (0 : ℝ)..1, passageTailDensity β (passageProfile β t₁) t) -
      ∫ t in (0 : ℝ)..1, passageTailDensity β (passageProfile β t₂) t := by
  set y₁ := passageProfile β t₁
  set y₂ := passageProfile β t₂
  have hsm := passageProfile_strictMonoOn hβ0 hβ1 hβ
  have mono := passageProfile_monotone hβ0 hβ1 hβ
  have hy : y₁ < y₂ := hsm ⟨h0, h12.le.trans h1⟩ ⟨h0.trans h12.le, h1⟩ h12
  have hκ := passageAmplitude_pos hβ0 hβ1
  have hF1 (t : ℝ) : 1 ≤ passageProfile β t :=
    (jumpProfile_bounds (w_summable hβ0 hβ1 hβ) (w_nonneg hβ0 hβ1) t).1
  set h : ℝ → ℝ := fun t => passageTailDensity β y₁ t - passageTailDensity β y₂ t
  have hint (y : ℝ) (a b : ℝ) : IntervalIntegrable (passageTailDensity β y) volume a b :=
    (passageTailDensity_monotone hβ0 hβ1 hβ y).intervalIntegrable
  have hhint (a b : ℝ) : IntervalIntegrable h volume a b := (hint y₁ a b).sub (hint y₂ a b)
  have hnn (t : ℝ) : 0 ≤ h t := by
    simp only [h, passageTailDensity]
    split_ifs with ha hb hb
    · simp
    · simpa using Real.rpow_nonneg (mul_nonneg hκ.le (zero_le_one.trans (hF1 t))) (2/3 : ℝ)
    · exact absurd (hy.trans hb) ha
    · simp
  have hlow (t : ℝ) (ht : t ∈ Ioo t₁ t₂) : passageAmplitude β ^ (2/3 : ℝ) ≤ h t := by
    have hlt : y₁ < passageProfile β t := hsm ⟨h0, h12.le.trans h1⟩
      ⟨h0.trans ht.1.le, ht.2.le.trans h1⟩ ht.1
    have hle : ¬ y₂ < passageProfile β t := not_lt.2 (mono ht.2.le)
    simp only [h, passageTailDensity, if_pos hlt, if_neg hle, sub_zero]
    exact Real.rpow_le_rpow hκ.le (le_mul_of_one_le_right hκ.le (hF1 t)) (by norm_num)
  rw [← intervalIntegral.integral_sub (hint _ _ _) (hint _ _ _)]
  change 0 < ∫ t in (0 : ℝ)..1, h t
  rw [← intervalIntegral.integral_add_adjacent_intervals (hhint 0 t₁) (hhint t₁ 1),
    ← intervalIntegral.integral_add_adjacent_intervals (hhint t₁ t₂) (hhint t₂ 1)]
  have ha : 0 ≤ ∫ t in (0 : ℝ)..t₁, h t := intervalIntegral.integral_nonneg h0 fun t _ => hnn t
  have hc : 0 ≤ ∫ t in t₂..(1 : ℝ), h t := intervalIntegral.integral_nonneg h1 fun t _ => hnn t
  have hb := intervalIntegral.integral_mono_on_of_le_Ioo h12.le intervalIntegrable_const
    (hhint t₁ t₂) hlow
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hb
  have hpos : 0 < (t₂ - t₁) * passageAmplitude β ^ (2/3 : ℝ) :=
    mul_pos (sub_pos.2 h12) (Real.rpow_pos_of_pos hκ _)
  linarith

/-- **Local tube bound.** Every relatively open piece of the cluster set has
neighbourhood volume at least `c ε^(1/3)`. -/
theorem passageCluster_local_tube {u v : ℝ} (hK : (passageClusterSet β ∩ Ioo u v).Nonempty) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ ε in 𝓝[>] (0 : ℝ), ENNReal.ofReal (c * ε ^ (1 - 2/3 : ℝ)) ≤
      volume (Metric.thickening ε (passageClusterSet β ∩ Ioo u v)) := by
  obtain ⟨t₁, t₂, h0, h12, h1, hwin⟩ := exists_phase_window hβ0 hβ1 hβ hK
  have hsm := passageProfile_strictMonoOn hβ0 hβ1 hβ
  have mono := passageProfile_monotone hβ0 hβ1 hβ
  have h1' : t₁ < (t₁ + t₂)/2 := by linarith
  have h2' : (t₁ + t₂)/2 < t₂ := by linarith
  have hy : passageProfile β t₁ < passageProfile β ((t₁ + t₂)/2) :=
    hsm ⟨h0, h1'.le.trans (h2'.le.trans h1)⟩ ⟨h0.trans h1'.le, h2'.le.trans h1⟩ h1'
  have hy2 : passageProfile β ((t₁ + t₂)/2) < passageProfile β t₂ :=
    hsm ⟨h0.trans h1'.le, h2'.le.trans h1⟩ ⟨h0.trans h12.le, h1⟩ h2'
  set y₁ := passageProfile β t₁
  set y₂ := passageProfile β ((t₁ + t₂)/2)
  have hL := tailDensity_gap_pos hβ0 hβ1 hβ h0 h1' (h2'.le.trans h1)
  set L := (∫ t in (0 : ℝ)..1, passageTailDensity β y₁ t) -
    ∫ t in (0 : ℝ)..1, passageTailDensity β y₂ t
  have hD : Tendsto (fun x : ℝ => x ^ (2/3 : ℝ) * ((gapCount (passageTailWeight β y₁) x : ℝ) -
      gapCount (passageTailWeight β y₂) x)) (𝓝[>] 0) (𝓝 L) :=
    ((passage_tail_gapCount_asymptotic hβ0 hβ1 hβ y₁).sub
      (passage_tail_gapCount_asymptotic hβ0 hβ1 hβ y₂)).congr fun x => by ring
  have hev := (tendsto_order.1 hD).1 (L/2) (by linarith)
  have hdbl : Tendsto (fun ε : ℝ => 2*ε) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · simpa using (tendsto_const_nhds (x := (2 : ℝ))).mul
        (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0))
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact mul_pos (by norm_num : (0 : ℝ) < 2) hε
  refine ⟨(2 : ℝ)^(1/3 : ℝ) * (L/2), by positivity, ?_⟩
  filter_upwards [hdbl.eventually hev, self_mem_nhdsWithin] with ε hε hε0
  have hε0' : (0 : ℝ) < ε := hε0
  have hx : (0 : ℝ) < 2*ε := by positivity
  have hw := w_summable hβ0 hβ1 hβ
  have hfin : {n | 2*ε ≤ passageJumpWeight β (n+1)}.Finite := by
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hw.tendsto_atTop_zero).2 _ hx)
    refine (Set.finite_Iio N).subset fun n hn => ?_
    by_contra hc
    exact absurd hn (not_le.2 (hN n (not_lt.1 hc)))
  have hset (y : ℝ) : {n | 2*ε ≤ passageTailWeight β y n} =
      {n | y < passageProfile β (passagePhase β (n+1)) ∧ 2*ε ≤ passageJumpWeight β (n+1)} := by
    ext n
    simp only [mem_ofPred_eq, passageTailWeight]
    split_ifs with h
    · simp [h]
    · simp [h, not_le.2 hx]
  set D : Set ℕ := {n | y₁ < passageProfile β (passagePhase β (n+1)) ∧
    passageProfile β (passagePhase β (n+1)) ≤ y₂ ∧ 2*ε ≤ passageJumpWeight β (n+1)}
  have hcount : ((gapCount (passageTailWeight β y₁) (2*ε) : ℝ) -
      gapCount (passageTailWeight β y₂) (2*ε)) = D.ncard := by
    unfold gapCount
    rw [hset, hset]
    have hsub : {n | y₂ < passageProfile β (passagePhase β (n+1)) ∧
        2*ε ≤ passageJumpWeight β (n+1)} ⊆ {n | y₁ < passageProfile β (passagePhase β (n+1)) ∧
        2*ε ≤ passageJumpWeight β (n+1)} := fun n hn => ⟨hy.trans hn.1, hn.2⟩
    have hdiff : {n | y₁ < passageProfile β (passagePhase β (n+1)) ∧
        2*ε ≤ passageJumpWeight β (n+1)} \ {n | y₂ < passageProfile β (passagePhase β (n+1)) ∧
        2*ε ≤ passageJumpWeight β (n+1)} = D := by
      ext n
      simp only [Set.mem_sdiff, mem_ofPred_eq, D]
      constructor
      · rintro ⟨⟨a, b⟩, c⟩
        exact ⟨a, not_lt.1 fun h => c ⟨h, b⟩, b⟩
      · rintro ⟨a, b, c⟩
        exact ⟨⟨a, c⟩, fun h => absurd h.1 (not_lt.2 b)⟩
    have := Set.ncard_sdiff_add_ncard_of_subset hsub (hfin.subset fun n hn => hn.2)
    rw [hdiff] at this
    rw [← this]
    push_cast
    ring
  rw [hcount] at hε
  have hDfin : D.Finite := hfin.subset fun n hn => hn.2.2
  set S := passageClusterSet β ∩ Ioo u v
  have hgap (n : ℕ) (hn : n ∈ D) : volume (Metric.thickening ε S ∩
      Ioo (passageProfile β (passagePhase β (n+1)))
        (passageProfile β (passagePhase β (n+1)) + passageJumpWeight β (n+1))) =
      ENNReal.ofReal (2*ε) := by
    have hδ1 : t₁ < passagePhase β (n+1) := by
      by_contra hc
      exact absurd (mono (not_lt.1 hc)) (not_le.2 hn.1)
    have hδ2 : passagePhase β (n+1) < t₂ := by
      by_contra hc
      have := mono (not_lt.1 hc)
      linarith [hn.2.1]
    have hl : passageProfile β (passagePhase β (n+1)) ∈ S :=
      ⟨(passage_gap_endpoints_mem hβ0 hβ1 hβ n).1, hwin _ ⟨hδ1.le, hδ2.le⟩⟩
    have hwpos := passageJumpWeight_pos hβ0 hβ1 (n+1)
    have hr : passageProfile β (passagePhase β (n+1)) + passageJumpWeight β (n+1) ∈ S :=
      ⟨(passage_gap_endpoints_mem hβ0 hβ1 hβ n).2, by linarith [hl.2.1],
        (passageGap_right_le hβ0 hβ1 hβ n hδ2).trans_lt (hwin t₂ ⟨h12.le, le_rfl⟩).2⟩
    have hg : Disjoint (Ioo (passageProfile β (passagePhase β (n+1)))
        (passageProfile β (passagePhase β (n+1)) + passageJumpWeight β (n+1))) S :=
      disjoint_left.2 fun z hz hzS => hzS.1.2 (mem_iUnion.2 ⟨n, hz⟩)
    have hreal := volume_thickening_inter_gap hl hr hg hwpos.le hε0'
    rw [min_eq_right hn.2.2] at hreal
    rw [← hreal, measureReal_def, ENNReal.ofReal_toReal
      (lt_of_le_of_lt (measure_mono inter_subset_right) measure_Ioo_lt_top).ne]
  have hdisj : (hDfin.toFinset : Set ℕ).PairwiseDisjoint (fun n => Metric.thickening ε S ∩
      Ioo (passageProfile β (passagePhase β (n+1)))
        (passageProfile β (passagePhase β (n+1)) + passageJumpWeight β (n+1))) := by
    intro i _ j _ hij
    exact ((jumpProfile_gaps_pairwiseDisjoint hw (w_nonneg hβ0 hβ1) (phase_inj hβ0 hβ1 hβ))
      hij).mono inter_subset_right inter_subset_right
  have hsum := measure_biUnion_finset (μ := volume) hdisj
    (fun n _ => Metric.isOpen_thickening.measurableSet.inter measurableSet_Ioo)
  have hle := measure_mono (μ := volume)
    (iUnion₂_subset fun n (_ : n ∈ hDfin.toFinset) => inter_subset_left (s := Metric.thickening ε S)
      (t := Ioo (passageProfile β (passagePhase β (n+1)))
        (passageProfile β (passagePhase β (n+1)) + passageJumpWeight β (n+1))))
  rw [hsum, Finset.sum_congr rfl (fun n hn => hgap n (hDfin.mem_toFinset.1 hn)),
    Finset.sum_const, nsmul_eq_mul] at hle
  refine le_trans ?_ hle
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  rw [← Set.ncard_eq_toFinset_card D hDfin]
  have hx13 : (2*ε) ^ (1/3 : ℝ) * (2*ε) ^ (2/3 : ℝ) = 2*ε := by
    rw [← Real.rpow_add hx]; norm_num
  calc (2 : ℝ)^(1/3 : ℝ) * (L/2) * ε ^ (1 - 2/3 : ℝ) = (2*ε) ^ (1/3 : ℝ) * (L/2) := by
        rw [show (1 : ℝ) - 2/3 = 1/3 by norm_num, Real.mul_rpow (by norm_num) hε0'.le]; ring
    _ ≤ (2*ε) ^ (1/3 : ℝ) * ((2*ε) ^ (2/3 : ℝ) * D.ncard) :=
        mul_le_mul_of_nonneg_left hε.le (by positivity)
    _ = D.ncard * (2*ε) := by rw [← mul_assoc, hx13]; ring

/-- **Universal packing dimension.** For every irrational boundary the cluster
set has modified upper box (packing) dimension exactly `2/3`. -/
theorem passageCluster_modUpperBoxDim :
    modUpperBoxDim (passageClusterSet β) = ENNReal.ofReal (2/3) := by
  have hcpt := isCompact_passageClusterSet hβ0 hβ1 hβ
  apply le_antisymm
  · refine (modUpperBoxDim_le _).trans ?_
    have hts : TubeExponent (passageClusterSet β) ((2/3 : ℝ).toNNReal) := by
      obtain ⟨c, C, hc, hC, hb⟩ := passageClusterSet_tube_bounds hβ0 hβ1 hβ
      refine ⟨C, ?_⟩
      filter_upwards [self_mem_nhdsWithin, (eventually_le_nhds
        (show (0 : ℝ) < 1/2 by norm_num)).filter_mono nhdsWithin_le_nhds] with ε hε hε2
      rw [Real.coe_toNNReal _ (by norm_num), show (1 : ℝ) - 2/3 = 1/3 by norm_num]
      have hfin : volume (Metric.thickening ε (passageClusterSet β)) ≠ ⊤ :=
        (hcpt.isBounded.thickening.measure_lt_top).ne
      rw [← ENNReal.ofReal_toReal hfin]
      exact ENNReal.ofReal_le_ofReal (hb ε hε hε2).2
    exact upperBoxDim_le_of_tube hts
  · refine le_iInf₂ fun G hG => ?_
    have : CompactSpace (passageClusterSet β) := isCompact_iff_compactSpace.1 hcpt
    have : Nonempty (passageClusterSet β) := (passageClusterSet_nonempty hβ0 hβ1 hβ).to_subtype
    let f : ℕ → Set (passageClusterSet β) := fun i => {x | (x : ℝ) ∈ closure (G i)}
    have hfc (i : ℕ) : IsClosed (f i) := isClosed_closure.preimage continuous_subtype_val
    have hfu : ⋃ i, f i = univ := by
      refine eq_univ_of_forall fun x => ?_
      obtain ⟨i, hi⟩ := mem_iUnion.1 (hG x.2)
      exact mem_iUnion.2 ⟨i, subset_closure hi⟩
    obtain ⟨i, x₀, hx₀⟩ := nonempty_interior_of_iUnion_of_closed hfc hfu
    obtain ⟨V, hVo, hV⟩ := isOpen_induced_iff.1 (isOpen_interior (s := f i))
    have hx₀V : (x₀ : ℝ) ∈ V := by
      have : x₀ ∈ Subtype.val ⁻¹' V := by rw [hV]; exact hx₀
      exact this
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hVo _ hx₀V
    have hsub : passageClusterSet β ∩ Ioo ((x₀ : ℝ) - δ) ((x₀ : ℝ) + δ) ⊆ closure (G i) := by
      rintro z ⟨hzK, hzU⟩
      have hzV : z ∈ V := hball (by rw [Real.ball_eq_Ioo]; exact hzU)
      have hz : (⟨z, hzK⟩ : passageClusterSet β) ∈ interior (f i) := by
        rw [← hV]; exact hzV
      exact (interior_subset hz : (⟨z, hzK⟩ : passageClusterSet β) ∈ f i)
    have hne : (passageClusterSet β ∩ Ioo ((x₀ : ℝ) - δ) ((x₀ : ℝ) + δ)).Nonempty :=
      ⟨x₀, x₀.2, by constructor <;> linarith⟩
    obtain ⟨c, hc, hloc⟩ := passageCluster_local_tube hβ0 hβ1 hβ hne
    calc ENNReal.ofReal (2/3) ≤ upperBoxDim (passageClusterSet β ∩
          Ioo ((x₀ : ℝ) - δ) ((x₀ : ℝ) + δ)) := le_upperBoxDim_of_tube hc hloc
      _ ≤ upperBoxDim (closure (G i)) := upperBoxDim_mono hsub
      _ = upperBoxDim (G i) := upperBoxDim_closure _
      _ ≤ ⨆ i, upperBoxDim (G i) := le_iSup (fun i => upperBoxDim (G i)) i

omit hβ0 hβ1 hβ in
/-- **Packing against Hausdorff.** For every irrational slope `α > 1` the
packing (modified upper box) dimension of the cluster set is `2/3`, and the
Hausdorff dimension is strictly smaller exactly when `α` is Liouville of some
exponent above `2`, that is, when its irrationality exponent exceeds `2`. -/
theorem cluster_dim_gap_iff {α : ℝ} (hα1 : 1 < α) (hα : Irrational α) :
    modUpperBoxDim (passageClusterSet (1/α)) = (2/3 : ℝ≥0∞) ∧
      (dimH (passageClusterSet (1/α)) < modUpperBoxDim (passageClusterSet (1/α)) ↔
        ∃ p > (2 : ℝ), LiouvilleWith p α) := by
  have hα0 : 0 < α := by linarith
  have hb0 : 0 < 1/α := one_div_pos.2 hα0
  have hb1 : 1/α < 1 := (div_lt_one hα0).2 hα1
  have hb : Irrational (1/α) := by simpa using hα.inv
  have he : ENNReal.ofReal (2/3) = (2/3 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
  have hP : modUpperBoxDim (passageClusterSet (1/α)) = (2/3 : ℝ≥0∞) := by
    rw [passageCluster_modUpperBoxDim hb0 hb1 hb, he]
  refine ⟨hP, ?_⟩
  rw [hP]
  have hle := passageCluster_dimH_le hb0 hb1 hb
  have hiff := cluster_dimH_eq_iff hα1 hα
  constructor
  · intro hlt
    by_contra hno
    push Not at hno
    exact hlt.ne (hiff.2 fun p hp hL => (hno p hp) hL)
  · rintro ⟨p, hp, hL⟩
    exact lt_of_le_of_ne hle fun heq => hiff.1 heq p hp hL

end Problems.Juggler.BeattySlope

import Problems.Juggler.BeattySlopeContent
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Continuity of the first-passage geometry in the slope

At an irrational boundary every comparison between `β*k` and an integer is
strict, so each actual first-passage count and each crossing index is locally
constant in the boundary. The jump weights therefore converge termwise, and
their exact total mass `β/(1-β)` converges too. A Scheffé argument upgrades
this to convergence in `ℓ¹`, with no uniform constants. Consequently the
profile converges at every non-atom phase, the limiting laws converge weakly,
and the exact Minkowski content is continuous at every irrational slope.
-/

namespace Problems.Juggler.BeattySlope

open Filter Topology Set MeasureTheory
open scoped BoundedContinuousFunction

/-- At an irrational boundary, the comparison of `β*k` with an integer is
locally constant in the boundary for every positive `k`. -/
theorem cmp_eventually {β₀ : ℝ} (hβ : Irrational β₀) {k : ℕ} (hk : 0 < k) (m : ℕ) :
    ∀ᶠ β : ℝ in 𝓝 β₀, (β*(k : ℝ) ≤ (m : ℝ) ↔ β₀*(k : ℝ) ≤ (m : ℝ)) := by
  have hne : β₀*k ≠ m := by
    intro h
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    exact hβ.ne_rat ((m : ℚ)/k) (by
      rw [show β₀ = (m : ℝ)/k by field_simp; linarith]; push_cast; ring)
  have ht : Tendsto (fun β : ℝ => β*k) (𝓝 β₀) (𝓝 (β₀*k)) :=
    (continuous_id.mul continuous_const).tendsto β₀
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · filter_upwards [ht (Iio_mem_nhds hlt)] with β hb
    exact ⟨fun _ => hlt.le, fun _ => (mem_Iio.1 hb).le⟩
  · filter_upwards [ht (Ioi_mem_nhds hgt)] with β hb
    exact ⟨fun h => absurd h (not_le.2 (mem_Ioi.1 hb)), fun h => absurd h (not_le.2 hgt)⟩

/-- All comparisons needed at length at most `n` are simultaneously frozen. -/
theorem cmp_eventually_all {β₀ : ℝ} (hβ : Irrational β₀) (n : ℕ) :
    ∀ᶠ β : ℝ in 𝓝 β₀, ∀ k ∈ Finset.range (n+1), ∀ m ∈ Finset.range (n+1),
      0 < k → (β*(k : ℝ) ≤ (m : ℝ) ↔ β₀*(k : ℝ) ≤ (m : ℝ)) := by
  rw [Filter.eventually_all_finset]
  intro k _
  rw [Filter.eventually_all_finset]
  intro m _
  by_cases hk : 0 < k
  · filter_upwards [cmp_eventually hβ hk m] with β h _
    exact h
  · exact Eventually.of_forall fun _ h => absurd h hk

/-- The first-passage predicate on words of a fixed length is locally
constant at an irrational boundary. -/
theorem firstPassage_eventually {β₀ : ℝ} (hβ : Irrational β₀) (n : ℕ) :
    ∀ᶠ β in 𝓝 β₀, ∀ w ∈ allWords n, (FirstPassage β w ↔ FirstPassage β₀ w) := by
  filter_upwards [cmp_eventually_all hβ n] with β h w hw
  have hlen : w.length = n := mem_allWords.mp hw
  have hcmp (k : ℕ) (hk : 0 < k) (hkn : k ≤ n) (m : ℕ) (hm : m ≤ n) :
      (β*(k : ℝ) ≤ (m : ℝ) ↔ β₀*(k : ℝ) ≤ (m : ℝ)) :=
    h k (Finset.mem_range.2 (Nat.lt_succ_of_le hkn)) m
      (Finset.mem_range.2 (Nat.lt_succ_of_le hm)) hk
  unfold FirstPassage Below
  by_cases hn : n = 0
  · have : w = [] := List.length_eq_zero_iff.1 (hlen.trans hn)
    simp [this]
  have hodd : oddCount w ≤ n := hlen ▸ oddCount_le_length w
  have hb : ((oddCount w : ℝ) < β*w.length ↔ (oddCount w : ℝ) < β₀*w.length) := by
    rw [hlen, ← not_le, ← not_le, hcmp n (Nat.pos_of_ne_zero hn) le_rfl _ hodd]
  have hp : (∀ k : ℕ, 0 < k → k < w.length → β*k ≤ (oddCount (w.take k) : ℝ)) ↔
      (∀ k : ℕ, 0 < k → k < w.length → β₀*k ≤ (oddCount (w.take k) : ℝ)) := by
    refine forall_congr' fun k => imp_congr_right fun hk => imp_congr_right fun hkl => ?_
    have hkn : k ≤ n := by omega
    have hm : oddCount (w.take k) ≤ n :=
      (oddCount_le_length _).trans ((List.length_take_le _ _).trans (by omega))
    exact hcmp k hk hkn _ hm
  rw [hb, hp]

/-- Each actual first-passage count is locally constant at an irrational boundary. -/
theorem passageCount_eventually {β₀ : ℝ} (hβ : Irrational β₀) (n : ℕ) :
    ∀ᶠ β in 𝓝 β₀, passageCount β n = passageCount β₀ n := by
  filter_upwards [firstPassage_eventually hβ n] with β h
  unfold passageCount passageWords
  congr 1
  ext w
  simp only [Finset.mem_filter]
  exact ⟨fun hw => ⟨hw.1, (h w hw.1).1 hw.2⟩, fun hw => ⟨hw.1, (h w hw.1).2 hw.2⟩⟩

/-- Each crossing index is locally constant at an irrational positive boundary. -/
theorem passageIndex_eventually {β₀ : ℝ} (hβ0 : 0 < β₀) (hβ : Irrational β₀) (r : ℕ) :
    ∀ᶠ β in 𝓝 β₀, passageIndex β r = passageIndex β₀ r := by
  by_cases hr : r = 0
  · subst hr
    exact Eventually.of_forall fun β => by simp [passageIndex]
  set m := passageIndex β₀ r with hm
  have hpos : (0 : ℝ) < (r : ℝ)/β₀ := div_pos (by exact_mod_cast Nat.pos_of_ne_zero hr) hβ0
  have hne : (r : ℝ)/β₀ ≠ m := by
    intro h
    have hm0 : (m : ℝ) ≠ 0 := by rw [← h]; exact hpos.ne'
    exact hβ.ne_rat ((r : ℚ)/m) (by
      have : β₀ = (r : ℝ)/m := by field_simp at h ⊢; linarith
      rw [this]; push_cast; ring)
  have hlo : (m : ℝ) < (r : ℝ)/β₀ :=
    lt_of_le_of_ne (Nat.floor_le hpos.le) (Ne.symm hne)
  have hhi : (r : ℝ)/β₀ < m+1 := Nat.lt_floor_add_one _
  have ht : Tendsto (fun β : ℝ => (r : ℝ)/β) (𝓝 β₀) (𝓝 ((r : ℝ)/β₀)) :=
    tendsto_const_nhds.div tendsto_id hβ0.ne'
  filter_upwards [ht (Ioo_mem_nhds hlo hhi)] with β hb
  unfold passageIndex
  rw [Nat.floor_eq_iff ((Nat.cast_nonneg m).trans hb.1.le)]
  exact ⟨hb.1.le, hb.2⟩

/-- Each actual jump weight is continuous in the boundary at an irrational
point of `(0,1)`. -/
theorem passageJumpWeight_tendsto {β₀ : ℝ} (hβ0 : 0 < β₀) (hβ1 : β₀ < 1)
    (hβ : Irrational β₀) (r : ℕ) :
    Tendsto (fun β => passageJumpWeight β r) (𝓝 β₀) (𝓝 (passageJumpWeight β₀ r)) := by
  set m := passageIndex β₀ r
  have hev : ∀ᶠ β in 𝓝 β₀, passageJumpWeight β r =
      (passageCount β₀ (m+1) : ℝ)*criticalWordMass β m r := by
    filter_upwards [passageIndex_eventually hβ0 hβ r, passageCount_eventually hβ (m+1)]
      with β hi hc
    unfold passageJumpWeight crossingDepth
    change (passageCount β (passageIndex β r+1) : ℝ)*criticalWordMass β (passageIndex β r) r = _
    rw [hi, hc]
  have hlim : Tendsto (fun β => (passageCount β₀ (m+1) : ℝ)*criticalWordMass β m r)
      (𝓝 β₀) (𝓝 ((passageCount β₀ (m+1) : ℝ)*criticalWordMass β₀ m r)) := by
    apply Tendsto.const_mul
    unfold criticalWordMass
    have h1 : (1 : ℝ)-β₀ ≠ 0 := by linarith
    exact ((tendsto_const_nhds.sub tendsto_id).pow m).mul
      ((tendsto_id.div (tendsto_const_nhds.sub tendsto_id) h1).pow r)
  have hval : passageJumpWeight β₀ r =
      (passageCount β₀ (m+1) : ℝ)*criticalWordMass β₀ m r := by
    unfold passageJumpWeight crossingDepth
    rfl
  rw [hval]
  exact hlim.congr' (hev.mono fun β h => h.symm)

/-- Scheffé's lemma for series: nonnegative termwise convergence together
with convergence of the exact sums gives convergence in `ℓ¹`. -/
theorem scheffe_tsum {ι : Type*} {L : Filter ι} {f : ι → ℕ → ℝ} {g : ℕ → ℝ}
    {S : ι → ℝ} {s : ℝ} (hf0 : ∀ᶠ i in L, ∀ n, 0 ≤ f i n)
    (hfs : ∀ᶠ i in L, HasSum (f i) (S i)) (hS : Tendsto S L (𝓝 s)) (hg : HasSum g s)
    (hg0 : ∀ n, 0 ≤ g n) (hpt : ∀ n, Tendsto (fun i => f i n) L (𝓝 (g n))) :
    Tendsto (fun i => ∑' n, |f i n - g n|) L (𝓝 0) := by
  have hpos : Tendsto (fun i => ∑' n, max (g n - f i n) 0) L (𝓝 0) := by
    have h := tendsto_tsum_of_dominated_convergence (f := fun i n => max (g n - f i n) 0)
      (g := fun _ => (0 : ℝ)) hg.summable
      (fun n => by
        have := ((tendsto_const_nhds (x := g n)).sub (hpt n)).max
          (tendsto_const_nhds (x := (0 : ℝ)))
        simpa using this)
      (by
        filter_upwards [hf0] with i hi n
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        exact max_le (by linarith [hi n]) (hg0 n))
    simpa using h
  have hmax_sum (i : ι) (hi : ∀ n, 0 ≤ f i n) :
      Summable (fun n => max (g n - f i n) 0) :=
    hg.summable.of_nonneg_of_le (fun _ => le_max_right _ _)
      (fun n => max_le (by linarith [hi n]) (hg0 n))
  have hev : ∀ᶠ i in L, ∑' n, |f i n - g n| =
      (S i - s) + 2*∑' n, max (g n - f i n) 0 := by
    filter_upwards [hf0, hfs] with i hi hsum
    have hm := hmax_sum i hi
    have hsplit : (fun n => |f i n - g n|) =
        fun n => (f i n - g n) + 2*max (g n - f i n) 0 := by
      funext n
      rcases le_total (g n) (f i n) with h | h
      · rw [abs_of_nonneg (by linarith), max_eq_right (by linarith)]; ring
      · rw [abs_of_nonpos (by linarith), max_eq_left (by linarith)]; ring
    rw [hsplit, ((hsum.sub hg).add (hm.hasSum.mul_left 2)).tsum_eq]
  have hlim : Tendsto (fun i => (S i - s) + 2*∑' n, max (g n - f i n) 0) L (𝓝 0) := by
    have := ((hS.sub_const s).add (hpos.const_mul 2))
    simpa using this
  exact hlim.congr' (hev.mono fun i h => h.symm)

/-- The filter of irrational boundaries approaching `β₀`. -/
abbrev irrNhds (β₀ : ℝ) : Filter ℝ := 𝓝[{β | Irrational β}] β₀

private theorem ev_unit {β₀ : ℝ} (hβ0 : 0 < β₀) (hβ1 : β₀ < 1) :
    ∀ᶠ β in irrNhds β₀, 0 < β ∧ β < 1 ∧ Irrational β := by
  have h1 : ∀ᶠ β in 𝓝 β₀, 0 < β ∧ β < 1 :=
    (eventually_gt_nhds hβ0).and (eventually_lt_nhds hβ1)
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds h1, self_mem_nhdsWithin]
    with β hb hi
  exact ⟨hb.1, hb.2, hi⟩

/-- The actual jump weights converge in `ℓ¹` as irrational boundaries
approach an irrational boundary, with no uniform constants. -/
theorem passageJumpWeight_l1 {β₀ : ℝ} (hβ0 : 0 < β₀) (hβ1 : β₀ < 1) (hβ : Irrational β₀) :
    Tendsto (fun β => ∑' r, |passageJumpWeight β (r+1) - passageJumpWeight β₀ (r+1)|)
      (irrNhds β₀) (𝓝 0) := by
  have hu := ev_unit hβ0 hβ1
  refine scheffe_tsum (S := fun β => β/(1-β)) (s := β₀/(1-β₀)) ?_ ?_ ?_
    (passage_jump_weights_hasSum hβ0 hβ1 hβ) (fun r => passageJumpWeight_nonneg hβ0 hβ1 _)
    (fun r => (passageJumpWeight_tendsto hβ0 hβ1 hβ (r+1)).mono_left nhdsWithin_le_nhds)
  · filter_upwards [hu] with β h r
    exact passageJumpWeight_nonneg h.1 h.2.1 _
  · filter_upwards [hu] with β h
    exact passage_jump_weights_hasSum h.1 h.2.1 h.2.2
  · have h1 : (1 : ℝ)-β₀ ≠ 0 := by linarith
    exact (tendsto_id.div (tendsto_const_nhds.sub tendsto_id) h1).mono_left nhdsWithin_le_nhds

/-- Each Beatty phase is continuous in the boundary at an irrational point. -/
theorem passagePhase_tendsto {β₀ : ℝ} (hβ0 : 0 < β₀) (hβ : Irrational β₀) (r : ℕ) :
    Tendsto (fun β => passagePhase β r) (𝓝 β₀) (𝓝 (passagePhase β₀ r)) := by
  have hev : ∀ᶠ β in 𝓝 β₀, passagePhase β r = (r : ℝ)/β - passageIndex β₀ r := by
    filter_upwards [passageIndex_eventually hβ0 hβ r] with β h
    unfold passagePhase
    rw [h]
  have hlim : Tendsto (fun β : ℝ => (r : ℝ)/β - passageIndex β₀ r) (𝓝 β₀)
      (𝓝 ((r : ℝ)/β₀ - passageIndex β₀ r)) :=
    (tendsto_const_nhds.div tendsto_id hβ0.ne').sub tendsto_const_nhds
  exact hlim.congr' (hev.mono fun β h => h.symm)

/-- At every phase that is not an atom of the limiting boundary, the actual
profile converges as irrational boundaries approach it. -/
theorem passageProfile_tendsto {β₀ : ℝ} (hβ0 : 0 < β₀) (hβ1 : β₀ < 1) (hβ : Irrational β₀)
    {t : ℝ} (ht : ∀ r : ℕ, passagePhase β₀ (r+1) ≠ t) :
    Tendsto (fun β => passageProfile β t) (irrNhds β₀) (𝓝 (passageProfile β₀ t)) := by
  have hu := ev_unit hβ0 hβ1
  set w₀ := fun r : ℕ => passageJumpWeight β₀ (r+1)
  have hw₀ : Summable w₀ := (passage_jump_weights_hasSum hβ0 hβ1 hβ).summable
  have hw₀0 (r : ℕ) : 0 ≤ w₀ r := passageJumpWeight_nonneg hβ0 hβ1 _
  -- The frozen-weight sums converge by dominated convergence.
  have hb : Tendsto (fun β => ∑' r, if passagePhase β (r+1) < t then w₀ r else 0)
      (irrNhds β₀) (𝓝 (∑' r, if passagePhase β₀ (r+1) < t then w₀ r else 0)) := by
    apply tendsto_tsum_of_dominated_convergence hw₀
    · intro r
      have hp := (passagePhase_tendsto hβ0 hβ (r+1)).mono_left
        (nhdsWithin_le_nhds (s := {β | Irrational β}))
      rcases lt_or_gt_of_ne (ht r) with hlt | hgt
      · have hev : ∀ᶠ β in irrNhds β₀, passagePhase β (r+1) < t := hp (Iio_mem_nhds hlt)
        rw [if_pos hlt]
        exact tendsto_const_nhds.congr' (hev.mono fun β h => by simp [h])
      · have hev : ∀ᶠ β in irrNhds β₀, t < passagePhase β (r+1) := hp (Ioi_mem_nhds hgt)
        rw [if_neg (not_lt.2 hgt.le)]
        exact tendsto_const_nhds.congr' (hev.mono fun β h => by simp [not_lt.2 h.le])
    · exact Eventually.of_forall fun β r => by
        split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg (hw₀0 r), hw₀0 r]
  -- The difference from the actual weights is controlled in `ℓ¹`.
  have hd : Tendsto (fun β => passageProfile β t -
      (1 + ∑' r, if passagePhase β (r+1) < t then w₀ r else 0)) (irrNhds β₀) (𝓝 0) := by
    apply squeeze_zero_norm' _ (passageJumpWeight_l1 hβ0 hβ1 hβ)
    filter_upwards [hu] with β h
    have hw : Summable (fun r => passageJumpWeight β (r+1)) :=
      (passage_jump_weights_hasSum h.1 h.2.1 h.2.2).summable
    have hs1 : Summable (fun r => if passagePhase β (r+1) < t then
        passageJumpWeight β (r+1) else 0) :=
      hw.of_norm_bounded (fun r => by
        split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg (passageJumpWeight_nonneg h.1 h.2.1 _),
          passageJumpWeight_nonneg h.1 h.2.1 _])
    have hs2 : Summable (fun r => if passagePhase β (r+1) < t then w₀ r else 0) :=
      hw₀.of_norm_bounded (fun r => by
        split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg (hw₀0 r), hw₀0 r])
    have hsd := hs1.sub hs2
    unfold passageProfile BeattyPhase.jumpProfile
    rw [add_sub_add_left_eq_sub, ← hs1.tsum_sub hs2]
    refine (norm_tsum_le_tsum_norm hsd.norm).trans ?_
    have hl1 : Summable (fun r => |passageJumpWeight β (r+1) - w₀ r|) :=
      (hw.sub hw₀).abs
    refine hsd.norm.tsum_le_tsum (fun r => ?_) hl1
    split_ifs <;> simp [Real.norm_eq_abs, w₀]
  have h := hd.add ((tendsto_const_nhds (x := (1 : ℝ))).add hb)
  simp only [sub_add_cancel, zero_add] at h
  have he : passageProfile β₀ t = 1 + ∑' r, if passagePhase β₀ (r+1) < t then w₀ r else 0 := rfl
  rw [he]
  exact h

private theorem ae_non_atom {β₀ : ℝ} :
    ∀ᵐ t : ℝ, ∀ r : ℕ, passagePhase β₀ (r+1) ≠ t := by
  have hc : (range (fun r : ℕ => passagePhase β₀ (r+1))).Countable := countable_range _
  have h := hc.ae_notMem volume
  filter_upwards [h] with t ht r hr
  exact ht ⟨r, hr⟩

/-- The limiting laws converge weakly as irrational boundaries approach an
irrational boundary: every bounded continuous phase average converges. -/
theorem passageLaw_slope_tendsto {β₀ : ℝ} (hβ0 : 0 < β₀) (hβ1 : β₀ < 1) (hβ : Irrational β₀)
    (g : ℝ →ᵇ ℝ) :
    Tendsto (fun β => ∫ t in Ioc (0 : ℝ) 1, g (passageProfile β t)) (irrNhds β₀)
      (𝓝 (∫ t in Ioc (0 : ℝ) 1, g (passageProfile β₀ t))) := by
  have hu := ev_unit hβ0 hβ1
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => ‖g‖) ?_ ?_ ?_ ?_
  · filter_upwards [hu] with β h
    exact (g.continuous.measurable.comp
      (passageProfile_monotone h.1 h.2.1 h.2.2).measurable).aestronglyMeasurable
  · exact Eventually.of_forall fun β => Eventually.of_forall fun t => g.norm_coe_le_norm _
  · exact integrableOn_const (hs := measure_Ioc_lt_top.ne)
  · filter_upwards [ae_restrict_of_ae (ae_non_atom (β₀ := β₀))] with t ht
    exact (g.continuous.tendsto _).comp (passageProfile_tendsto hβ0 hβ1 hβ ht)

/-- The exact Minkowski content of the actual cluster sets is continuous at
every irrational slope, along irrational slopes. -/
theorem passageContent_tendsto {β₀ : ℝ} (hβ0 : 0 < β₀) (hβ1 : β₀ < 1) (hβ : Irrational β₀) :
    Tendsto passageMinkowskiContent (irrNhds β₀) (𝓝 (passageMinkowskiContent β₀)) := by
  have hu := ev_unit hβ0 hβ1
  have hκ : Tendsto passageAmplitude (𝓝 β₀) (𝓝 (passageAmplitude β₀)) := by
    unfold passageAmplitude tiltedAmplitude
    have hq : 0 < 2*Real.pi*β₀*(1-β₀) := by
      have := Real.pi_pos
      have : 0 < 1-β₀ := by linarith
      positivity
    exact (tendsto_id.mul (Real.continuous_sqrt.tendsto β₀)).mul
      (((Real.continuous_sqrt.tendsto _).comp
        (((tendsto_const_nhds.mul tendsto_id).mul
          (tendsto_const_nhds.sub tendsto_id)))).inv₀ (Real.sqrt_pos.2 hq).ne')
  -- A uniform bound on a neighbourhood.
  set B := (passageAmplitude β₀ + 1)*(2/(1-β₀))
  have hbd : ∀ᶠ β in irrNhds β₀, ∀ t, 0 ≤ passageAmplitude β*passageProfile β t ∧
      passageAmplitude β*passageProfile β t ≤ B := by
    have hk1 : ∀ᶠ β in 𝓝 β₀, passageAmplitude β < passageAmplitude β₀ + 1 :=
      hκ (Iio_mem_nhds (by linarith))
    have hq : ∀ᶠ β in 𝓝 β₀, β < (1+β₀)/2 := Iio_mem_nhds (by linarith)
    filter_upwards [hu, eventually_nhdsWithin_of_eventually_nhds hk1,
      eventually_nhdsWithin_of_eventually_nhds hq] with β h hk hq t
    have hF := passageProfile_bounds h.1 h.2.1 h.2.2 t
    have hκ0 : 0 ≤ passageAmplitude β := (passageAmplitude_pos h.1 h.2.1).le
    have hinv : 1/(1-β) ≤ 2/(1-β₀) := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      linarith
    refine ⟨mul_nonneg hκ0 (by linarith [hF.1]), ?_⟩
    calc passageAmplitude β*passageProfile β t ≤ passageAmplitude β*(2/(1-β₀)) :=
          mul_le_mul_of_nonneg_left (hF.2.trans hinv) hκ0
      _ ≤ _ := mul_le_mul_of_nonneg_right hk.le (div_nonneg (by norm_num) (by linarith))
  have hmom : Tendsto passageGapMoment (irrNhds β₀) (𝓝 (passageGapMoment β₀)) := by
    unfold passageGapMoment
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => B^(2/3 : ℝ)) ?_ ?_ ?_ ?_
    · filter_upwards [hu] with β h
      exact ((measurable_const.mul (passageProfile_monotone h.1 h.2.1 h.2.2).measurable).pow_const
        _).aestronglyMeasurable
    · filter_upwards [hbd] with β h
      refine Eventually.of_forall fun t _ => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (h t).1 _)]
      exact Real.rpow_le_rpow (h t).1 (h t).2 (by norm_num)
    · exact intervalIntegrable_const
    · filter_upwards [ae_non_atom (β₀ := β₀)] with t ht _
      exact ((Real.continuousAt_rpow_const _ _ (Or.inr (by norm_num))).tendsto).comp
        ((hκ.mono_left nhdsWithin_le_nhds).mul (passageProfile_tendsto hβ0 hβ1 hβ ht))
  unfold passageMinkowskiContent
  exact hmom.const_mul _

/-- Irrational slopes near `α₀` give irrational boundaries near `1/α₀`. -/
theorem inv_tendsto_irrNhds {α₀ : ℝ} (hα0 : α₀ ≠ 0) :
    Tendsto (fun α : ℝ => 1/α) (irrNhds α₀) (irrNhds (1/α₀)) := by
  apply tendsto_nhdsWithin_iff.2
  refine ⟨((tendsto_const_nhds.div tendsto_id hα0).mono_left nhdsWithin_le_nhds), ?_⟩
  filter_upwards [self_mem_nhdsWithin] with α hα
  simpa using (show Irrational α from hα).inv

/-- In slope coordinates, the exact Minkowski content of the actual cluster
sets is continuous along irrational slopes at every irrational slope above one. -/
theorem passageContent_slope_tendsto {α₀ : ℝ} (h1 : 1 < α₀) (hα : Irrational α₀) :
    Tendsto (fun α => passageMinkowskiContent (1/α)) (irrNhds α₀)
      (𝓝 (passageMinkowskiContent (1/α₀))) := by
  have h0 : 0 < α₀ := by linarith
  exact (passageContent_tendsto (one_div_pos.mpr h0) ((div_lt_one h0).mpr h1)
    (by simpa using hα.inv)).comp (inv_tendsto_irrNhds h0.ne')

/-- In slope coordinates, the limiting laws converge weakly along irrational
slopes: every bounded continuous phase average of the profile converges. -/
theorem passageLaw_slope_cont {α₀ : ℝ} (h1 : 1 < α₀) (hα : Irrational α₀) (g : ℝ →ᵇ ℝ) :
    Tendsto (fun α => ∫ t in Ioc (0 : ℝ) 1, g (passageProfile (1/α) t)) (irrNhds α₀)
      (𝓝 (∫ t in Ioc (0 : ℝ) 1, g (passageProfile (1/α₀) t))) := by
  have h0 : 0 < α₀ := by linarith
  exact (passageLaw_slope_tendsto (one_div_pos.mpr h0) ((div_lt_one h0).mpr h1)
    (by simpa using hα.inv) g).comp (inv_tendsto_irrNhds h0.ne')

end Problems.Juggler.BeattySlope

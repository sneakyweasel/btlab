import Problems.Juggler.BeattySlopeRationalMass
import Problems.Juggler.BeattySlopeContinuity
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# One-sided limits of the first-passage laws at every boundary

Survival uses weak comparisons `β*k ≤ m`. For boundaries slightly below a
fixed `β₀`, each such comparison agrees with the one at `β₀`, even when
`β₀*k = m`, and `r/β` decreases to `r/β₀`, so every floor is frozen. Hence all
first-passage counts and crossing indices are eventually constant as `β ↑ β₀`,
and each jump weight is left-continuous. With the exact total masses valid at
every boundary, Scheffé's lemma gives `ℓ¹` convergence, the profiles converge
off the `β₀`-phases, and bounded continuous phase averages converge.

At a rational boundary `β₀ = b/a` every phase is a multiple of `1/b`, so the
limiting profile is a step function with at most `b` values and its law is the
uniform law on the values at `(j+1)/b`.
-/

namespace Problems.Juggler.BeattySlope

open Finset Filter Topology Set MeasureTheory
open scoped BoundedContinuousFunction

/-- For boundaries slightly below `β₀`, the weak comparison of `β*k` with an
integer agrees with the comparison at `β₀`, for every positive `k`. -/
theorem cmp_eventually_left (β₀ : ℝ) {k : ℕ} (hk : 0 < k) (m : ℕ) :
    ∀ᶠ β : ℝ in 𝓝[<] β₀, (β*(k : ℝ) ≤ (m : ℝ) ↔ β₀*(k : ℝ) ≤ (m : ℝ)) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  by_cases h : β₀*(k : ℝ) ≤ (m : ℝ)
  · filter_upwards [self_mem_nhdsWithin] with β hb
    have hb' : β < β₀ := hb
    exact ⟨fun _ => h, fun _ => by nlinarith⟩
  · have hgt : (m : ℝ) < β₀*k := lt_of_not_ge h
    have ht : Tendsto (fun β : ℝ => β*k) (𝓝 β₀) (𝓝 (β₀*k)) :=
      (continuous_id.mul continuous_const).tendsto β₀
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds (ht (Ioi_mem_nhds hgt))] with β hb
    exact ⟨fun h' => absurd h' (not_le.2 (Set.mem_Ioi.1 hb)), fun h' => absurd h' h⟩

private theorem cmp_all_left (β₀ : ℝ) (n : ℕ) :
    ∀ᶠ β : ℝ in 𝓝[<] β₀, ∀ k ∈ Finset.range (n+1), ∀ m ∈ Finset.range (n+1),
      0 < k → (β*(k : ℝ) ≤ (m : ℝ) ↔ β₀*(k : ℝ) ≤ (m : ℝ)) := by
  rw [Filter.eventually_all_finset]
  intro k _
  rw [Filter.eventually_all_finset]
  intro m _
  by_cases hk : 0 < k
  · filter_upwards [cmp_eventually_left β₀ hk m] with β h _
    exact h
  · exact Eventually.of_forall fun _ h => absurd h hk

/-- The first-passage predicate on words of a fixed length is eventually
the one at `β₀` as `β ↑ β₀`, for every real `β₀`. -/
theorem firstPassage_eventually_left (β₀ : ℝ) (n : ℕ) :
    ∀ᶠ β in 𝓝[<] β₀, ∀ w ∈ allWords n, (FirstPassage β w ↔ FirstPassage β₀ w) := by
  filter_upwards [cmp_all_left β₀ n] with β h w hw
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

/-- Each first-passage count is eventually constant as `β ↑ β₀`. -/
theorem passageCount_eventually_left (β₀ : ℝ) (n : ℕ) :
    ∀ᶠ β in 𝓝[<] β₀, passageCount β n = passageCount β₀ n := by
  filter_upwards [firstPassage_eventually_left β₀ n] with β h
  unfold passageCount passageWords
  congr 1
  ext w
  simp only [Finset.mem_filter]
  exact ⟨fun hw => ⟨hw.1, (h w hw.1).1 hw.2⟩, fun hw => ⟨hw.1, (h w hw.1).2 hw.2⟩⟩

/-- Each crossing index `⌊r/β⌋₊` is eventually constant as `β ↑ β₀ > 0`,
since `r/β` decreases to `r/β₀` and the floor is right-continuous. -/
theorem passageIndex_eventually_left {β₀ : ℝ} (hβ0 : 0 < β₀) (r : ℕ) :
    ∀ᶠ β in 𝓝[<] β₀, passageIndex β r = passageIndex β₀ r := by
  set m := passageIndex β₀ r
  have hlo : (m : ℝ) ≤ (r : ℝ)/β₀ := Nat.floor_le (div_nonneg (Nat.cast_nonneg r) hβ0.le)
  have hhi : (r : ℝ)/β₀ < m+1 := Nat.lt_floor_add_one _
  have ht : Tendsto (fun β : ℝ => (r : ℝ)/β) (𝓝 β₀) (𝓝 ((r : ℝ)/β₀)) :=
    tendsto_const_nhds.div tendsto_id hβ0.ne'
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds (ht (Iio_mem_nhds hhi)),
    self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds hβ0)] with β hb hlt hpos
  have hlt' : β < β₀ := hlt
  have hge : (r : ℝ)/β₀ ≤ (r : ℝ)/β :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg r) hpos hlt'.le
  unfold passageIndex
  rw [Nat.floor_eq_iff (div_nonneg (Nat.cast_nonneg r) hpos.le)]
  exact ⟨hlo.trans hge, hb⟩

private theorem ev_unit_left {β₀ : ℝ} (hβ0 : 0 < β₀) (hβ1 : β₀ < 1) :
    ∀ᶠ β in 𝓝[<] β₀, 0 < β ∧ β < 1 := by
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds hβ0),
    self_mem_nhdsWithin] with β h0 h1
  exact ⟨h0, (show β < β₀ from h1).trans hβ1⟩

/-- Each jump weight is left-continuous in the boundary at every point of
`(0,1)`, rational points included. -/
theorem passageJumpWeight_tendsto_left {β₀ : ℝ} (hβ0 : 0 < β₀) (hβ1 : β₀ < 1) (r : ℕ) :
    Tendsto (fun β => passageJumpWeight β r) (𝓝[<] β₀) (𝓝 (passageJumpWeight β₀ r)) := by
  set m := passageIndex β₀ r
  have hev : ∀ᶠ β in 𝓝[<] β₀, passageJumpWeight β r =
      (passageCount β₀ (m+1) : ℝ)*criticalWordMass β m r := by
    filter_upwards [passageIndex_eventually_left hβ0 r,
      passageCount_eventually_left β₀ (m+1)] with β hi hc
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
  exact (hlim.mono_left nhdsWithin_le_nhds).congr' (hev.mono fun β h => h.symm)

/-- As `β ↑ β₀` for any `β₀` in `(0,1)`, the positive-index jump weights
converge in `ℓ¹` to the weights at `β₀`. -/
theorem passageJumpWeight_l1_left {β₀ : ℝ} (hβ0 : 0 < β₀) (hβ1 : β₀ < 1) :
    Tendsto (fun β => ∑' r, |passageJumpWeight β (r+1) - passageJumpWeight β₀ (r+1)|)
      (𝓝[<] β₀) (𝓝 0) := by
  have hu := ev_unit_left hβ0 hβ1
  refine scheffe_tsum (S := fun β => β/(1-β)) (s := β₀/(1-β₀)) ?_ ?_ ?_
    (passage_jump_hasSum_all hβ0 hβ1) (fun r => passageJumpWeight_nonneg hβ0 hβ1 _)
    (fun r => passageJumpWeight_tendsto_left hβ0 hβ1 (r+1))
  · filter_upwards [hu] with β h r
    exact passageJumpWeight_nonneg h.1 h.2 _
  · filter_upwards [hu] with β h
    exact passage_jump_hasSum_all h.1 h.2
  · have h1 : (1 : ℝ)-β₀ ≠ 0 := by linarith
    exact (tendsto_id.div (tendsto_const_nhds.sub tendsto_id) h1).mono_left nhdsWithin_le_nhds

/-- Each Beatty phase is left-continuous in the boundary at every `β₀ > 0`. -/
theorem passagePhase_tendsto_left {β₀ : ℝ} (hβ0 : 0 < β₀) (r : ℕ) :
    Tendsto (fun β => passagePhase β r) (𝓝[<] β₀) (𝓝 (passagePhase β₀ r)) := by
  have hev : ∀ᶠ β in 𝓝[<] β₀, passagePhase β r = (r : ℝ)/β - passageIndex β₀ r := by
    filter_upwards [passageIndex_eventually_left hβ0 r] with β h
    unfold passagePhase
    rw [h]
  have hlim : Tendsto (fun β : ℝ => (r : ℝ)/β - passageIndex β₀ r) (𝓝 β₀)
      (𝓝 ((r : ℝ)/β₀ - passageIndex β₀ r)) :=
    (tendsto_const_nhds.div tendsto_id hβ0.ne').sub tendsto_const_nhds
  exact (hlim.mono_left nhdsWithin_le_nhds).congr' (hev.mono fun β h => h.symm)

/-- The profile is nondecreasing at every boundary in `(0,1)`. -/
theorem passageProfile_monotone_all {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Monotone (passageProfile β) :=
  BeattyPhase.jumpProfile_monotone (passage_jump_hasSum_all hβ0 hβ1).summable
    (fun r => passageJumpWeight_nonneg hβ0 hβ1 (r+1))

/-- At every phase that is not a `β₀`-phase, the profile converges as
`β ↑ β₀`, for every `β₀` in `(0,1)`, rational boundaries included. -/
theorem passageProfile_tendsto_left {β₀ : ℝ} (hβ0 : 0 < β₀) (hβ1 : β₀ < 1)
    {t : ℝ} (ht : ∀ r : ℕ, passagePhase β₀ (r+1) ≠ t) :
    Tendsto (fun β => passageProfile β t) (𝓝[<] β₀) (𝓝 (passageProfile β₀ t)) := by
  have hu := ev_unit_left hβ0 hβ1
  set w₀ := fun r : ℕ => passageJumpWeight β₀ (r+1)
  have hw₀ : Summable w₀ := (passage_jump_hasSum_all hβ0 hβ1).summable
  have hw₀0 (r : ℕ) : 0 ≤ w₀ r := passageJumpWeight_nonneg hβ0 hβ1 _
  have hb : Tendsto (fun β => ∑' r, if passagePhase β (r+1) < t then w₀ r else 0)
      (𝓝[<] β₀) (𝓝 (∑' r, if passagePhase β₀ (r+1) < t then w₀ r else 0)) := by
    apply tendsto_tsum_of_dominated_convergence hw₀
    · intro r
      have hp := passagePhase_tendsto_left hβ0 (r+1)
      rcases lt_or_gt_of_ne (ht r) with hlt | hgt
      · have hev : ∀ᶠ β in 𝓝[<] β₀, passagePhase β (r+1) < t := hp (Iio_mem_nhds hlt)
        rw [if_pos hlt]
        exact tendsto_const_nhds.congr' (hev.mono fun β h => by simp [h])
      · have hev : ∀ᶠ β in 𝓝[<] β₀, t < passagePhase β (r+1) := hp (Ioi_mem_nhds hgt)
        rw [if_neg (not_lt.2 hgt.le)]
        exact tendsto_const_nhds.congr' (hev.mono fun β h => by simp [not_lt.2 h.le])
    · exact Eventually.of_forall fun β r => by
        split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg (hw₀0 r), hw₀0 r]
  have hd : Tendsto (fun β => passageProfile β t -
      (1 + ∑' r, if passagePhase β (r+1) < t then w₀ r else 0)) (𝓝[<] β₀) (𝓝 0) := by
    apply squeeze_zero_norm' _ (passageJumpWeight_l1_left hβ0 hβ1)
    filter_upwards [hu] with β h
    have hw : Summable (fun r => passageJumpWeight β (r+1)) :=
      (passage_jump_hasSum_all h.1 h.2).summable
    have hs1 : Summable (fun r => if passagePhase β (r+1) < t then
        passageJumpWeight β (r+1) else 0) :=
      hw.of_norm_bounded (fun r => by
        split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg (passageJumpWeight_nonneg h.1 h.2 _),
          passageJumpWeight_nonneg h.1 h.2 _])
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

private theorem ae_non_atom' (β₀ : ℝ) :
    ∀ᵐ t : ℝ, ∀ r : ℕ, passagePhase β₀ (r+1) ≠ t := by
  have hc : (range (fun r : ℕ => passagePhase β₀ (r+1))).Countable := countable_range _
  have h := hc.ae_notMem volume
  filter_upwards [h] with t ht r hr
  exact ht ⟨r, hr⟩

/-- As `β ↑ β₀` for any `β₀` in `(0,1)`, every bounded continuous phase
average of the profile converges to the one at `β₀`. -/
theorem passageLaw_tendsto_left {β₀ : ℝ} (hβ0 : 0 < β₀) (hβ1 : β₀ < 1) (g : ℝ →ᵇ ℝ) :
    Tendsto (fun β => ∫ t in Ioc (0 : ℝ) 1, g (passageProfile β t)) (𝓝[<] β₀)
      (𝓝 (∫ t in Ioc (0 : ℝ) 1, g (passageProfile β₀ t))) := by
  have hu := ev_unit_left hβ0 hβ1
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => ‖g‖) ?_ ?_ ?_ ?_
  · filter_upwards [hu] with β h
    exact (g.continuous.measurable.comp
      (passageProfile_monotone_all h.1 h.2).measurable).aestronglyMeasurable
  · exact Eventually.of_forall fun β => Eventually.of_forall fun t => g.norm_coe_le_norm _
  · exact integrableOn_const (hs := measure_Ioc_lt_top.ne)
  · filter_upwards [ae_restrict_of_ae (ae_non_atom' β₀)] with t ht
    exact (g.continuous.tendsto _).comp (passageProfile_tendsto_left hβ0 hβ1 ht)

/-- At a rational boundary `b/a`, every Beatty phase is `((r*a) mod b)/b`. -/
theorem passagePhase_rational {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (r : ℕ) :
    passagePhase ((b : ℝ)/a) r = (((r*a) % b : ℕ) : ℝ)/b := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hq : (r : ℝ)/((b : ℝ)/a) = ((r*a : ℕ) : ℝ)/b := by
    push_cast
    field_simp
  have hidx : passageIndex ((b : ℝ)/a) r = r*a/b := by
    unfold passageIndex
    rw [hq]
    exact Nat.floor_div_eq_div (K := ℝ) (r*a) b
  have hdm : ((r*a : ℕ) : ℝ) = b*((r*a/b : ℕ) : ℝ) + (((r*a) % b : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod (r*a) b).symm
  unfold passagePhase
  rw [hidx, hq, hdm]
  field_simp
  ring

/-- At a rational boundary `b/a`, the profile is constant on each interval
`(j/b, (j+1)/b]`. -/
theorem passageProfile_rational_step {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (j : ℕ)
    {t : ℝ} (ht : t ∈ Ioc ((j : ℝ)/b) ((j+1 : ℝ)/b)) :
    passageProfile ((b : ℝ)/a) t = passageProfile ((b : ℝ)/a) ((j+1 : ℝ)/b) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  unfold passageProfile BeattyPhase.jumpProfile
  congr 1
  apply tsum_congr
  intro r
  dsimp only
  simp only [passagePhase_rational ha hb]
  set q : ℕ := ((r+1)*a) % b
  have hiff : (q : ℝ)/b < t ↔ (q : ℝ)/b < (j+1 : ℝ)/b := by
    rw [div_lt_div_iff_of_pos_right hbR]
    constructor
    · intro h
      by_contra hc
      have hc' : (j : ℝ)+1 ≤ q := le_of_not_gt hc
      have := ht.2
      have : (j+1 : ℝ)/b ≤ (q : ℝ)/b := div_le_div_of_nonneg_right hc' hbR.le
      linarith
    · intro h
      have hq : q ≤ j := by
        have : (q : ℝ) < (j : ℝ)+1 := h
        exact Nat.lt_succ_iff.mp (by exact_mod_cast this)
      have : (q : ℝ)/b ≤ (j : ℝ)/b :=
        div_le_div_of_nonneg_right (by exact_mod_cast hq) hbR.le
      linarith [ht.1]
  simp only [hiff]

/-- At a rational boundary `b/a`, the phase law of the profile is the uniform
law on its `b` values at the points `(j+1)/b`. -/
theorem passageLaw_rational_eq {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (g : ℝ →ᵇ ℝ) :
    ∫ t in Ioc (0 : ℝ) 1, g (passageProfile ((b : ℝ)/a) t) =
      (1/(b : ℝ))*∑ j ∈ range b, g (passageProfile ((b : ℝ)/a) ((j+1 : ℝ)/b)) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  set f := fun t => g (passageProfile ((b : ℝ)/a) t)
  set p : ℕ → ℝ := fun j => (j : ℝ)/b
  have hp (j : ℕ) : p (j+1) = ((j : ℝ)+1)/b := by simp [p]
  have hle (j : ℕ) : p j ≤ p (j+1) := by
    rw [hp]; exact div_le_div_of_nonneg_right (by linarith) hbR.le
  have heq (j : ℕ) : EqOn f (fun _ => g (passageProfile ((b : ℝ)/a) ((j+1 : ℝ)/b)))
      (Ioc (p j) (p (j+1))) := by
    intro t ht
    rw [hp] at ht
    exact congrArg g (passageProfile_rational_step ha hb j ht)
  have hpiece (j : ℕ) : ∫ t in p j..p (j+1), f t =
      (1/(b : ℝ))*g (passageProfile ((b : ℝ)/a) ((j+1 : ℝ)/b)) := by
    rw [intervalIntegral.integral_of_le (hle j), setIntegral_congr_fun measurableSet_Ioc (heq j),
      ← intervalIntegral.integral_of_le (hle j), intervalIntegral.integral_const, hp, smul_eq_mul]
    congr 1
    simp only [p]
    field_simp
    ring
  have hint : ∀ k < b, IntervalIntegrable f volume (p k) (p (k+1)) := by
    intro k _
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (hle k)]
    exact (integrableOn_const (hs := measure_Ioc_lt_top.ne)).congr_fun (heq k).symm
      measurableSet_Ioc
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  have h0 : p 0 = 0 := by simp [p]
  have h1 : p b = 1 := by simp only [p]; field_simp
  rw [h0, h1] at hsum
  rw [← intervalIntegral.integral_of_le zero_le_one, ← hsum, mul_sum]
  exact sum_congr rfl fun j _ => hpiece j

/-- Atomic limit at a rational boundary: as `β ↑ b/a` (slope `α ↓ a/b`), the
bounded continuous phase averages of the profile converge to the average over
the `b` values `F_{b/a}((j+1)/b)`, i.e. the laws converge to the uniform law
on these `b` values. Coprimality is not needed. -/
theorem passageLaw_rational_left {a b : ℕ} (hb : 0 < b) (hba : b < a) (g : ℝ →ᵇ ℝ) :
    Tendsto (fun β => ∫ t in Ioc (0 : ℝ) 1, g (passageProfile β t)) (𝓝[<] ((b : ℝ)/a))
      (𝓝 ((1/(b : ℝ))*∑ j ∈ range b, g (passageProfile ((b : ℝ)/a) ((j+1 : ℝ)/b)))) := by
  have ha : 0 < a := hb.trans hba
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hβ0 : 0 < (b : ℝ)/a := div_pos (by exact_mod_cast hb) haR
  have hβ1 : (b : ℝ)/a < 1 := (div_lt_one haR).2 (by exact_mod_cast hba)
  rw [← passageLaw_rational_eq ha hb g]
  exact passageLaw_tendsto_left hβ0 hβ1 g

/-- Slopes decreasing to `α₀ > 0` give boundaries increasing to `1/α₀`. -/
theorem inv_tendsto_left {α₀ : ℝ} (hα0 : 0 < α₀) :
    Tendsto (fun α : ℝ => 1/α) (𝓝[>] α₀) (𝓝[<] (1/α₀)) := by
  apply tendsto_nhdsWithin_iff.2
  refine ⟨(tendsto_const_nhds.div tendsto_id hα0.ne').mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with α hα
  exact one_div_lt_one_div_of_lt hα0 hα

/-- Slope form of the atomic limit: as the slope `α` decreases to `a/b`, the
bounded continuous phase averages of the profile at boundary `1/α` converge to
the uniform average over the `b` values `F_{b/a}((j+1)/b)`. -/
theorem passageLaw_rational_slope {a b : ℕ} (hb : 0 < b) (hba : b < a) (g : ℝ →ᵇ ℝ) :
    Tendsto (fun α => ∫ t in Ioc (0 : ℝ) 1, g (passageProfile (1/α) t)) (𝓝[>] ((a : ℝ)/b))
      (𝓝 ((1/(b : ℝ))*∑ j ∈ range b, g (passageProfile ((b : ℝ)/a) ((j+1 : ℝ)/b)))) := by
  have hα0 : 0 < (a : ℝ)/b := div_pos (by exact_mod_cast hb.trans hba) (by exact_mod_cast hb)
  have hi := inv_tendsto_left hα0
  rw [one_div_div] at hi
  exact (passageLaw_rational_left hb hba g).comp hi

/-- The profile increases strictly across any interval `[x, y)` that contains
a Beatty phase, at every boundary in `(0,1)`. -/
theorem passageProfile_lt_of_phase {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {x y : ℝ}
    (hxy : x < y) {r : ℕ} (hr : x ≤ passagePhase β (r+1)) (hr' : passagePhase β (r+1) < y) :
    passageProfile β x < passageProfile β y := by
  have hw := (passage_jump_hasSum_all hβ0 hβ1).summable
  have hn (s : ℕ) := passageJumpWeight_nonneg hβ0 hβ1 (s+1)
  unfold passageProfile BeattyPhase.jumpProfile
  apply add_lt_add_right
  dsimp only
  apply Summable.tsum_lt_tsum_of_nonneg (i := r)
  · intro s
    split_ifs <;> simp [hn s]
  · intro s
    by_cases hs : passagePhase β (s+1) < x
    · rw [if_pos hs, if_pos (hs.trans hxy)]
    · rw [if_neg hs]
      split_ifs <;> simp [hn s]
  · rw [if_neg (not_lt.2 hr), if_pos hr']
    exact passageJumpWeight_pos hβ0 hβ1 (r+1)
  · exact hw.of_norm_bounded (fun s => by
      split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg (hn s), hn s])

/-- For coprime `1 ≤ b < a`, the `b` values `F_{b/a}((j+1)/b)` are strictly
increasing in `j < b`, so the atomic limit law has exactly `b` atoms. -/
theorem passageProfile_rational_lt {a b : ℕ} (hb : 0 < b) (hba : b < a)
    (hab : Nat.Coprime a b) {j k : ℕ} (hjk : j < k) (hk : k < b) :
    passageProfile ((b : ℝ)/a) ((j+1 : ℝ)/b) < passageProfile ((b : ℝ)/a) ((k+1 : ℝ)/b) := by
  have ha : 0 < a := hb.trans hba
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hβ0 : 0 < (b : ℝ)/a := div_pos hbR haR
  have hβ1 : (b : ℝ)/a < 1 := (div_lt_one haR).2 (by exact_mod_cast hba)
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_of_coprime (j+1) hab hb.ne'
  rw [Nat.mod_eq_of_lt (by omega : j+1 < b)] at hm
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
  have hph : passagePhase ((b : ℝ)/a) (m-1+1) = ((j : ℝ)+1)/b := by
    rw [passagePhase_rational ha hb, Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0), mul_comm, hm]
    push_cast
    ring
  refine passageProfile_lt_of_phase hβ0 hβ1 ?_ (r := m-1) hph.ge ?_
  · exact div_lt_div_of_pos_right (by exact_mod_cast Nat.succ_lt_succ hjk) hbR
  · rw [hph]
    exact div_lt_div_of_pos_right (by exact_mod_cast Nat.succ_lt_succ hjk) hbR

end Problems.Juggler.BeattySlope

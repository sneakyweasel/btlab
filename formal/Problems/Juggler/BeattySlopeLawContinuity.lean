import Problems.Juggler.BeattySlopeGlobalLaw

/-!
# Continuity and jumps of the first-passage law in the slope

The Scheffé argument of `BeattySlopeContinuity` needs termwise convergence of
the jump weights and phases together with convergence of the exact total
masses. Since the masses `β/(1-β)` are now exact at every boundary, the
argument runs along any filter of boundaries in `(0,1)`.

* At an irrational boundary counts and crossing indices are locally constant
  on both sides, so `passageProfileLaw` is continuous there.
* As `β ↓ β₀` for any `β₀`, prefix comparisons become strict and crossings
  weak. Counts and indices are eventually constant, so the weights and phases
  have explicit right limits. The limit weights have the full mass
  `β₀/(1-β₀)`: the tail of the weights at `β` is bounded by the critical
  survival mass at `β`, which for fixed depth is at most a continuous
  function of `β` equal to the survival mass at `β₀`, and that tends to zero.
* At `β₀ = b/a` the right-limit phases are multiples of `1/b` in `[1/b, 1]`,
  so the right-limit law is uniform on `b` step values, one of which is `1`,
  whereas every atom of `passageProfileLaw (b/a)` exceeds `1`.

In slope coordinates `α = 1/β > 1` the law is right-continuous everywhere and
continuous exactly at the irrational slopes.
-/

namespace Problems.Juggler.BeattySlope

open Finset Filter Topology Set MeasureTheory BeattyPhase
open scoped BoundedContinuousFunction

/-! ### Convergence along an arbitrary filter of boundaries -/

/-- Profile convergence along any filter of boundaries in `(0,1)`: termwise
convergence of weights and phases, with total mass converging to the mass of
the limit weights, gives convergence at every phase avoiding the limit phases. -/
theorem passageProfile_tendsto_of {L : Filter ℝ} {φ w : ℕ → ℝ} {s : ℝ}
    (hu : ∀ᶠ β in L, 0 < β ∧ β < 1) (hw : HasSum w s) (hw0 : ∀ r, 0 ≤ w r)
    (hs : Tendsto (fun β => β/(1-β)) L (𝓝 s))
    (hwt : ∀ r, Tendsto (fun β => passageJumpWeight β (r+1)) L (𝓝 (w r)))
    (hφ : ∀ r, Tendsto (fun β => passagePhase β (r+1)) L (𝓝 (φ r)))
    {t : ℝ} (ht : ∀ r, φ r ≠ t) :
    Tendsto (fun β => passageProfile β t) L (𝓝 (BeattyPhase.jumpProfile φ w t)) := by
  have hl1 : Tendsto (fun β => ∑' r, |passageJumpWeight β (r+1) - w r|) L (𝓝 0) := by
    refine scheffe_tsum ?_ ?_ hs hw hw0 hwt
    · filter_upwards [hu] with β h r
      exact passageJumpWeight_nonneg h.1 h.2 _
    · filter_upwards [hu] with β h
      exact passage_jump_hasSum_all h.1 h.2
  have hb : Tendsto (fun β => ∑' r, if passagePhase β (r+1) < t then w r else 0)
      L (𝓝 (∑' r, if φ r < t then w r else 0)) := by
    apply tendsto_tsum_of_dominated_convergence hw.summable
    · intro r
      rcases lt_or_gt_of_ne (ht r) with hlt | hgt
      · have hev : ∀ᶠ β in L, passagePhase β (r+1) < t := hφ r (Iio_mem_nhds hlt)
        rw [if_pos hlt]
        exact tendsto_const_nhds.congr' (hev.mono fun β h => by simp [h])
      · have hev : ∀ᶠ β in L, t < passagePhase β (r+1) := hφ r (Ioi_mem_nhds hgt)
        rw [if_neg (not_lt.2 hgt.le)]
        exact tendsto_const_nhds.congr' (hev.mono fun β h => by simp [not_lt.2 h.le])
    · exact Eventually.of_forall fun β r => by
        split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg (hw0 r), hw0 r]
  have hd : Tendsto (fun β => passageProfile β t -
      (1 + ∑' r, if passagePhase β (r+1) < t then w r else 0)) L (𝓝 0) := by
    apply squeeze_zero_norm' _ hl1
    filter_upwards [hu] with β h
    have hw' : Summable (fun r => passageJumpWeight β (r+1)) :=
      (passage_jump_hasSum_all h.1 h.2).summable
    have hs1 : Summable (fun r => if passagePhase β (r+1) < t then
        passageJumpWeight β (r+1) else 0) :=
      hw'.of_norm_bounded (fun r => by
        split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg (passageJumpWeight_nonneg h.1 h.2 _),
          passageJumpWeight_nonneg h.1 h.2 _])
    have hs2 : Summable (fun r => if passagePhase β (r+1) < t then w r else 0) :=
      hw.summable.of_norm_bounded (fun r => by
        split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg (hw0 r), hw0 r])
    have hsd := hs1.sub hs2
    unfold passageProfile BeattyPhase.jumpProfile
    rw [add_sub_add_left_eq_sub, ← hs1.tsum_sub hs2]
    refine (norm_tsum_le_tsum_norm hsd.norm).trans ?_
    have hl : Summable (fun r => |passageJumpWeight β (r+1) - w r|) :=
      (hw'.sub hw.summable).abs
    refine hsd.norm.tsum_le_tsum (fun r => ?_) hl
    split_ifs <;> simp [Real.norm_eq_abs]
  have h := hd.add ((tendsto_const_nhds (x := (1 : ℝ))).add hb)
  simp only [sub_add_cancel, zero_add] at h
  exact h

private theorem ae_off_phases (φ : ℕ → ℝ) : ∀ᵐ t : ℝ, ∀ r : ℕ, φ r ≠ t := by
  have hc : (range φ).Countable := countable_range _
  filter_upwards [hc.ae_notMem volume] with t ht r hr
  exact ht ⟨r, hr⟩

/-- Phase averages converge along any countably generated filter of
boundaries in `(0,1)` under the hypotheses of `passageProfile_tendsto_of`. -/
theorem passageAvg_tendsto_of {L : Filter ℝ} [L.IsCountablyGenerated] {φ w : ℕ → ℝ} {s : ℝ}
    (hu : ∀ᶠ β in L, 0 < β ∧ β < 1) (hw : HasSum w s) (hw0 : ∀ r, 0 ≤ w r)
    (hs : Tendsto (fun β => β/(1-β)) L (𝓝 s))
    (hwt : ∀ r, Tendsto (fun β => passageJumpWeight β (r+1)) L (𝓝 (w r)))
    (hφ : ∀ r, Tendsto (fun β => passagePhase β (r+1)) L (𝓝 (φ r))) (g : ℝ →ᵇ ℝ) :
    Tendsto (fun β => ∫ t in Ioc (0 : ℝ) 1, g (passageProfile β t)) L
      (𝓝 (∫ t in Ioc (0 : ℝ) 1, g (BeattyPhase.jumpProfile φ w t))) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => ‖g‖) ?_ ?_ ?_ ?_
  · filter_upwards [hu] with β h
    exact (g.continuous.measurable.comp
      (passageProfile_monotone_all h.1 h.2).measurable).aestronglyMeasurable
  · exact Eventually.of_forall fun β => Eventually.of_forall fun t => g.norm_coe_le_norm _
  · exact integrableOn_const (hs := measure_Ioc_lt_top.ne)
  · filter_upwards [ae_restrict_of_ae (ae_off_phases φ)] with t ht
    exact (g.continuous.tendsto _).comp
      (passageProfile_tendsto_of hu hw hw0 hs hwt hφ ht)

/-- Weak convergence of the profile laws follows from convergence of every
bounded continuous phase average. -/
theorem passageLaw_tendsto_of_avg {L : Filter ℝ} {μ : ProbabilityMeasure ℝ}
    (hu : ∀ᶠ β in L, 0 < β ∧ β < 1)
    (h : ∀ g : ℝ →ᵇ ℝ, Tendsto (fun β => ∫ t in Ioc (0 : ℝ) 1, g (passageProfile β t)) L
      (𝓝 (∫ y, g y ∂(μ : Measure ℝ)))) :
    Tendsto passageProfileLaw L (𝓝 μ) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro g
  apply (h g).congr'
  filter_upwards [hu] with β hβ
  exact (integral_passageProfileLaw hβ.1 hβ.2 g).symm

/-! ### Continuity at irrational boundaries -/

/-- At an irrational boundary in `(0,1)` the law `passageProfileLaw` is
continuous along all nearby boundaries, rational ones included. -/
theorem passageProfileLaw_continuousAt {β₀ : ℝ} (hβ0 : 0 < β₀) (hβ1 : β₀ < 1)
    (hβ : Irrational β₀) :
    Tendsto passageProfileLaw (𝓝 β₀) (𝓝 (passageProfileLaw β₀)) := by
  have hu : ∀ᶠ β in 𝓝 β₀, 0 < β ∧ β < 1 :=
    (eventually_gt_nhds hβ0).and (eventually_lt_nhds hβ1)
  have hs : Tendsto (fun β : ℝ => β/(1-β)) (𝓝 β₀) (𝓝 (β₀/(1-β₀))) :=
    tendsto_id.div (tendsto_const_nhds.sub tendsto_id) (by linarith)
  apply passageLaw_tendsto_of_avg hu
  intro g
  rw [integral_passageProfileLaw hβ0 hβ1]
  exact passageAvg_tendsto_of hu (passage_jump_hasSum_all hβ0 hβ1)
    (fun r => passageJumpWeight_nonneg hβ0 hβ1 _) hs
    (fun r => passageJumpWeight_tendsto hβ0 hβ1 hβ (r+1))
    (fun r => passagePhase_tendsto hβ0 hβ (r+1)) g

/-- Left continuity at every boundary: as `β ↑ β₀` for any `β₀` in `(0,1)`,
the profile laws converge weakly to `passageProfileLaw β₀`. -/
theorem passageProfileLaw_tendsto_left {β₀ : ℝ} (hβ0 : 0 < β₀) (hβ1 : β₀ < 1) :
    Tendsto passageProfileLaw (𝓝[<] β₀) (𝓝 (passageProfileLaw β₀)) := by
  have hu : ∀ᶠ β in 𝓝[<] β₀, 0 < β ∧ β < 1 := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds hβ0),
      self_mem_nhdsWithin] with β h0 h1
    exact ⟨h0, (show β < β₀ from h1).trans hβ1⟩
  apply passageLaw_tendsto_of_avg hu
  intro g
  rw [integral_passageProfileLaw hβ0 hβ1]
  exact passageLaw_tendsto_left hβ0 hβ1 g

/-! ### Right limits: strict survival and weak crossing -/

/-- First passage in the limit of boundaries decreasing to `β`: earlier
prefixes stay strictly above the boundary and the end is weakly below it. -/
def FirstPassageUp (β : ℝ) (w : List Branch) : Prop :=
  w ≠ [] ∧ (oddCount w : ℝ) ≤ β * w.length ∧
    ∀ k : ℕ, 0 < k → k < w.length → β * k < (oddCount (w.take k) : ℝ)

/-- Number of words of length `n` with a strict-survival, weak-crossing first
passage at `β`. -/
noncomputable def passageCountUp (β : ℝ) (n : ℕ) : ℕ := by
  classical
  exact ((allWords n).filter (FirstPassageUp β)).card

/-- The right-limit crossing index `⌈r/β⌉₊ - 1`. -/
noncomputable def passageIndexUp (β : ℝ) (r : ℕ) : ℕ := ⌈(r : ℝ)/β⌉₊ - 1

/-- The right-limit Beatty phase `r/β - (⌈r/β⌉₊ - 1)`, which lies in `(0,1]`. -/
noncomputable def passagePhaseUp (β : ℝ) (r : ℕ) : ℝ := (r : ℝ)/β - passageIndexUp β r

/-- The right-limit jump weight built from the strict-survival counts. -/
noncomputable def passageWeightUp (β : ℝ) (r : ℕ) : ℝ :=
  (passageCountUp β (passageIndexUp β r + 1) : ℝ)*criticalWordMass β (passageIndexUp β r) r

/-- The right-limit profile, with the right-limit phases and weights. -/
noncomputable def passageProfileUp (β : ℝ) : ℝ → ℝ :=
  BeattyPhase.jumpProfile (fun r => passagePhaseUp β (r+1)) (fun r => passageWeightUp β (r+1))

/-- For boundaries slightly above `β₀`, the weak comparison `β*k ≤ m` agrees
with the strict comparison `β₀*k < m`, for every positive `k`. -/
theorem cmp_eventually_right (β₀ : ℝ) {k : ℕ} (hk : 0 < k) (m : ℕ) :
    ∀ᶠ β : ℝ in 𝓝[>] β₀, (β*(k : ℝ) ≤ (m : ℝ) ↔ β₀*(k : ℝ) < (m : ℝ)) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  by_cases h : β₀*(k : ℝ) < (m : ℝ)
  · have ht : Tendsto (fun β : ℝ => β*k) (𝓝 β₀) (𝓝 (β₀*k)) :=
      (continuous_id.mul continuous_const).tendsto β₀
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds (ht (Iio_mem_nhds h))] with β hb
    exact ⟨fun _ => h, fun _ => (Set.mem_Iio.1 hb).le⟩
  · filter_upwards [self_mem_nhdsWithin] with β hb
    have hb' : β₀ < β := hb
    have : (m : ℝ) < β*k := by nlinarith
    exact ⟨fun h' => absurd h' (not_le.2 this), fun h' => absurd h' h⟩

private theorem cmp_all_right (β₀ : ℝ) (n : ℕ) :
    ∀ᶠ β : ℝ in 𝓝[>] β₀, ∀ k ∈ Finset.range (n+1), ∀ m ∈ Finset.range (n+1),
      0 < k → (β*(k : ℝ) ≤ (m : ℝ) ↔ β₀*(k : ℝ) < (m : ℝ)) := by
  rw [Filter.eventually_all_finset]
  intro k _
  rw [Filter.eventually_all_finset]
  intro m _
  by_cases hk : 0 < k
  · filter_upwards [cmp_eventually_right β₀ hk m] with β h _
    exact h
  · exact Eventually.of_forall fun _ h => absurd h hk

/-- As `β ↓ β₀`, the first-passage predicate on words of a fixed length is
eventually the strict-survival, weak-crossing predicate at `β₀`. -/
theorem firstPassage_eventually_right (β₀ : ℝ) (n : ℕ) :
    ∀ᶠ β in 𝓝[>] β₀, ∀ w ∈ allWords n, (FirstPassage β w ↔ FirstPassageUp β₀ w) := by
  filter_upwards [cmp_all_right β₀ n] with β h w hw
  have hlen : w.length = n := mem_allWords.mp hw
  have hcmp (k : ℕ) (hk : 0 < k) (hkn : k ≤ n) (m : ℕ) (hm : m ≤ n) :
      (β*(k : ℝ) ≤ (m : ℝ) ↔ β₀*(k : ℝ) < (m : ℝ)) :=
    h k (Finset.mem_range.2 (Nat.lt_succ_of_le hkn)) m
      (Finset.mem_range.2 (Nat.lt_succ_of_le hm)) hk
  unfold FirstPassage FirstPassageUp Below
  by_cases hn : n = 0
  · have : w = [] := List.length_eq_zero_iff.1 (hlen.trans hn)
    simp [this]
  have hodd : oddCount w ≤ n := hlen ▸ oddCount_le_length w
  have hb : ((oddCount w : ℝ) < β*w.length ↔ (oddCount w : ℝ) ≤ β₀*w.length) := by
    rw [hlen, ← not_le, hcmp n (Nat.pos_of_ne_zero hn) le_rfl _ hodd, not_lt]
  have hp : (∀ k : ℕ, 0 < k → k < w.length → β*k ≤ (oddCount (w.take k) : ℝ)) ↔
      (∀ k : ℕ, 0 < k → k < w.length → β₀*k < (oddCount (w.take k) : ℝ)) := by
    refine forall_congr' fun k => imp_congr_right fun hk => imp_congr_right fun hkl => ?_
    have hkn : k ≤ n := by omega
    have hm : oddCount (w.take k) ≤ n :=
      (oddCount_le_length _).trans ((List.length_take_le _ _).trans (by omega))
    exact hcmp k hk hkn _ hm
  rw [hb, hp]

/-- Each first-passage count is eventually the strict-survival count as `β ↓ β₀`. -/
theorem passageCount_eventually_right (β₀ : ℝ) (n : ℕ) :
    ∀ᶠ β in 𝓝[>] β₀, passageCount β n = passageCountUp β₀ n := by
  filter_upwards [firstPassage_eventually_right β₀ n] with β h
  unfold passageCount passageWords passageCountUp
  congr 1
  ext w
  simp only [Finset.mem_filter]
  exact ⟨fun hw => ⟨hw.1, (h w hw.1).1 hw.2⟩, fun hw => ⟨hw.1, (h w hw.1).2 hw.2⟩⟩

/-- Each crossing index `⌊r/β⌋₊` is eventually `⌈r/β₀⌉₊ - 1` as `β ↓ β₀ > 0`,
since `r/β` increases strictly to `r/β₀`. -/
theorem passageIndex_eventually_right {β₀ : ℝ} (hβ0 : 0 < β₀) (r : ℕ) :
    ∀ᶠ β in 𝓝[>] β₀, passageIndex β r = passageIndexUp β₀ r := by
  by_cases hr : r = 0
  · subst hr
    exact Eventually.of_forall fun β => by simp [passageIndex, passageIndexUp]
  set c := ⌈(r : ℝ)/β₀⌉₊ with hc
  have hpos : (0 : ℝ) < (r : ℝ)/β₀ := div_pos (by exact_mod_cast Nat.pos_of_ne_zero hr) hβ0
  have hc1 : 0 < c := Nat.lt_ceil.2 (by simpa using hpos)
  have hcast : ((c-1 : ℕ) : ℝ) = (c : ℝ) - 1 := Nat.cast_pred hc1
  have hlo : ((c-1 : ℕ) : ℝ) < (r : ℝ)/β₀ := Nat.lt_ceil.1 (by omega)
  have hhi : (r : ℝ)/β₀ ≤ c := Nat.le_ceil _
  have ht : Tendsto (fun β : ℝ => (r : ℝ)/β) (𝓝 β₀) (𝓝 ((r : ℝ)/β₀)) :=
    tendsto_const_nhds.div tendsto_id hβ0.ne'
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds (ht (Ioi_mem_nhds hlo)),
    self_mem_nhdsWithin] with β hb hgt
  have hgt' : β₀ < β := hgt
  have hβ : 0 < β := hβ0.trans hgt'
  have hlt : (r : ℝ)/β < (r : ℝ)/β₀ :=
    div_lt_div_of_pos_left (by exact_mod_cast Nat.pos_of_ne_zero hr) hβ0 hgt'
  unfold passageIndex passageIndexUp
  rw [← hc, Nat.floor_eq_iff (div_nonneg (Nat.cast_nonneg r) hβ.le)]
  refine ⟨(Set.mem_Ioi.1 hb).le, ?_⟩
  rw [hcast]
  linarith

private theorem ev_unit_right {β₀ : ℝ} (hβ0 : 0 < β₀) (hβ1 : β₀ < 1) :
    ∀ᶠ β in 𝓝[>] β₀, 0 < β ∧ β < 1 := by
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hβ1),
    self_mem_nhdsWithin] with β h1 h0
  exact ⟨hβ0.trans h0, h1⟩

/-- Each jump weight converges as `β ↓ β₀` in `(0,1)` to the right-limit weight. -/
theorem passageWeight_tendsto_right {β₀ : ℝ} (hβ0 : 0 < β₀) (hβ1 : β₀ < 1) (r : ℕ) :
    Tendsto (fun β => passageJumpWeight β r) (𝓝[>] β₀) (𝓝 (passageWeightUp β₀ r)) := by
  set m := passageIndexUp β₀ r
  have hev : ∀ᶠ β in 𝓝[>] β₀, passageJumpWeight β r =
      (passageCountUp β₀ (m+1) : ℝ)*criticalWordMass β m r := by
    filter_upwards [passageIndex_eventually_right hβ0 r,
      passageCount_eventually_right β₀ (m+1)] with β hi hc
    unfold passageJumpWeight crossingDepth
    change (passageCount β (passageIndex β r+1) : ℝ)*criticalWordMass β (passageIndex β r) r = _
    rw [hi, hc]
  have hlim : Tendsto (fun β => (passageCountUp β₀ (m+1) : ℝ)*criticalWordMass β m r)
      (𝓝 β₀) (𝓝 ((passageCountUp β₀ (m+1) : ℝ)*criticalWordMass β₀ m r)) := by
    apply Tendsto.const_mul
    unfold criticalWordMass
    have h1 : (1 : ℝ)-β₀ ≠ 0 := by linarith
    exact ((tendsto_const_nhds.sub tendsto_id).pow m).mul
      ((tendsto_id.div (tendsto_const_nhds.sub tendsto_id) h1).pow r)
  exact (hlim.mono_left nhdsWithin_le_nhds).congr' (hev.mono fun β h => h.symm)

/-- Each Beatty phase converges as `β ↓ β₀ > 0` to the right-limit phase. -/
theorem passagePhase_tendsto_right {β₀ : ℝ} (hβ0 : 0 < β₀) (r : ℕ) :
    Tendsto (fun β => passagePhase β r) (𝓝[>] β₀) (𝓝 (passagePhaseUp β₀ r)) := by
  have hev : ∀ᶠ β in 𝓝[>] β₀, passagePhase β r = (r : ℝ)/β - passageIndexUp β₀ r := by
    filter_upwards [passageIndex_eventually_right hβ0 r] with β h
    unfold passagePhase
    rw [h]
  have hlim : Tendsto (fun β : ℝ => (r : ℝ)/β - passageIndexUp β₀ r) (𝓝 β₀)
      (𝓝 ((r : ℝ)/β₀ - passageIndexUp β₀ r)) :=
    (tendsto_const_nhds.div tendsto_id hβ0.ne').sub tendsto_const_nhds
  exact (hlim.mono_left nhdsWithin_le_nhds).congr' (hev.mono fun β h => h.symm)

/-! ### The right-limit weights keep the full mass -/

/-- The weights from index `R` on carry at most the critical survival mass at
depth `R`: `1 - (1-β) ∑_{r<R} w_r ≤ survivorCriticalMass β R`. -/
theorem passage_tail_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (R : ℕ) :
    1 - (1-β)*∑ r ∈ range R, passageJumpWeight β r ≤ survivorCriticalMass β R := by
  have hq : 0 < 1-β := by linarith
  have hW := passageJumpWeight_hasSum_all hβ0 hβ1
  have hP := passageCritMass_hasSum_all hβ0 hβ1
  have hP0 := passageCriticalMass_nonneg hβ0 hβ1
  set f : ℕ → ℝ := fun n => if R < n then passageCriticalMass β n else 0
  have hf0 (n : ℕ) : 0 ≤ f n := by dsimp only [f]; split_ifs <;> simp [hP0 n]
  have hfs : Summable f := hP.summable.of_nonneg_of_le hf0 (fun n => by
    dsimp only [f]; split_ifs <;> simp [hP0 n])
  -- Tail of the weights as a reindexed tail of the critical masses.
  have hinj : Function.Injective (fun i : ℕ => crossingDepth β (i+R)) :=
    (crossingDepth_strictMono hβ0 hβ1.le).injective.comp (add_left_injective R)
  have hcomp : (1-β)*∑' i, passageJumpWeight β (i+R) = ∑' i, f (crossingDepth β (i+R)) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro i
    have hge : R < crossingDepth β (i+R) := by
      have := passageIndex_ge hβ0 hβ1.le (i+R)
      change R < passageIndex β (i+R) + 1
      omega
    simp only [f, if_pos hge, passageCriticalMass_crossingDepth hβ0 hβ1]
  have hle : ∑' i, f (crossingDepth β (i+R)) ≤ ∑' n, f n :=
    tsum_comp_le_tsum_of_inj hfs hf0 hinj
  -- The tail of the critical masses is the survival mass.
  have hfsum : ∑' n, f n = survivorCriticalMass β R := by
    have h1 := hfs.sum_add_tsum_nat_add (R+1)
    have h2 := hP.summable.sum_add_tsum_nat_add (R+1)
    have hz : ∑ i ∈ range (R+1), f i = 0 :=
      sum_eq_zero fun i hi => by
        have : ¬ R < i := by have := mem_range.1 hi; omega
        simp [f, this]
    have ht : ∑' i, f (i+(R+1)) = ∑' i, passageCriticalMass β (i+(R+1)) :=
      tsum_congr fun i => by simp only [f]; rw [if_pos (by omega)]
    have hpart := criticalMass_partial_sum hβ1 R
    rw [hP.tsum_eq] at h2
    linarith
  have hsplit := hW.summable.sum_add_tsum_nat_add R
  rw [hW.tsum_eq] at hsplit
  have htot : (1-β)*(1/(1-β)) = 1 := by field_simp
  have : (1-β)*∑ r ∈ range R, passageJumpWeight β r + (1-β)*∑' i, passageJumpWeight β (i+R)
      = 1 := by rw [← mul_add, hsplit, htot]
  linarith

/-- Survival is antitone in the boundary: survivors at `β` survive at `β₀ ≤ β`. -/
theorem survivorWords_anti {β₀ β : ℝ} (h : β₀ ≤ β) (n : ℕ) :
    survivorWords β n ⊆ survivorWords β₀ n := by
  classical
  intro w hw
  unfold survivorWords at hw ⊢
  rw [Finset.mem_filter] at hw ⊢
  refine ⟨hw.1, fun k hk => le_trans ?_ (hw.2 k hk)⟩
  exact mul_le_mul_of_nonneg_right h (Nat.cast_nonneg k)

private theorem survival_bound {β₀ β : ℝ} (h : β₀ ≤ β) (hβ0 : 0 < β) (hβ1 : β < 1) (n : ℕ) :
    survivorCriticalMass β n ≤
      ∑ w ∈ survivorWords β₀ n, criticalWordMass β n (oddCount w) :=
  sum_le_sum_of_subset_of_nonneg (survivorWords_anti h n)
    fun _ _ _ => (criticalWordMass_pos hβ0 hβ1 _ _).le

/-- The right-limit weights, including index zero, sum to `1/(1-β₀)`. -/
theorem passageWeightUp_hasSum_all {β₀ : ℝ} (hβ0 : 0 < β₀) (hβ1 : β₀ < 1) :
    HasSum (passageWeightUp β₀) (1/(1-β₀)) := by
  have hu := ev_unit_right hβ0 hβ1
  have hq : (1 : ℝ)-β₀ ≠ 0 := by linarith
  have hq0 : 0 < 1-β₀ := by linarith
  have hW0 (r : ℕ) : 0 ≤ passageWeightUp β₀ r :=
    mul_nonneg (Nat.cast_nonneg _) (criticalWordMass_pos hβ0 hβ1 _ _).le
  have hpart (R : ℕ) : Tendsto (fun β => ∑ r ∈ range R, passageJumpWeight β r) (𝓝[>] β₀)
      (𝓝 (∑ r ∈ range R, passageWeightUp β₀ r)) :=
    tendsto_finsetSum _ fun r _ => passageWeight_tendsto_right hβ0 hβ1 r
  have hinv : Tendsto (fun β : ℝ => 1/(1-β)) (𝓝[>] β₀) (𝓝 (1/(1-β₀))) :=
    (tendsto_const_nhds.div (tendsto_const_nhds.sub tendsto_id) hq).mono_left
      nhdsWithin_le_nhds
  have hup (R : ℕ) : ∑ r ∈ range R, passageWeightUp β₀ r ≤ 1/(1-β₀) := by
    refine le_of_tendsto_of_tendsto (hpart R) hinv ?_
    filter_upwards [hu] with β h
    exact sum_le_hasSum _ (fun r _ => passageJumpWeight_nonneg h.1 h.2 r)
      (passageJumpWeight_hasSum_all h.1 h.2)
  have hlow (R : ℕ) :
      (1 - survivorCriticalMass β₀ R)/(1-β₀) ≤ ∑ r ∈ range R, passageWeightUp β₀ r := by
    set G : ℝ → ℝ := fun β => ∑ w ∈ survivorWords β₀ R, criticalWordMass β R (oddCount w)
    have hG : Tendsto G (𝓝 β₀) (𝓝 (survivorCriticalMass β₀ R)) := by
      apply tendsto_finsetSum
      intro _ _
      unfold criticalWordMass
      exact ((tendsto_const_nhds.sub tendsto_id).pow R).mul
        ((tendsto_id.div (tendsto_const_nhds.sub tendsto_id) hq).pow _)
    have hlim : Tendsto (fun β => (1 - G β)/(1-β)) (𝓝[>] β₀)
        (𝓝 ((1 - survivorCriticalMass β₀ R)/(1-β₀))) :=
      ((tendsto_const_nhds.sub hG).div (tendsto_const_nhds.sub tendsto_id) hq).mono_left
        nhdsWithin_le_nhds
    refine le_of_tendsto_of_tendsto hlim (hpart R) ?_
    filter_upwards [hu, self_mem_nhdsWithin] with β h hgt
    have h1 := passage_tail_le h.1 h.2 R
    have h2 := survival_bound (le_of_lt (show β₀ < β from hgt)) h.1 h.2 R
    rw [div_le_iff₀ (by linarith [h.2])]
    nlinarith
  apply (hasSum_iff_tendsto_nat_of_nonneg hW0 _).2
  have hl : Tendsto (fun R => (1 - survivorCriticalMass β₀ R)/(1-β₀)) atTop
      (𝓝 ((1 - 0)/(1-β₀))) :=
    (tendsto_const_nhds.sub (critSurvival_tendsto_zero hβ0 hβ1)).div_const _
  rw [sub_zero] at hl
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds hlow hup

/-- The right-limit weight at index zero is one. -/
theorem passageWeightUp_zero {β₀ : ℝ} (hβ0 : 0 < β₀) (hβ1 : β₀ < 1) :
    passageWeightUp β₀ 0 = 1 := by
  refine tendsto_nhds_unique (passageWeight_tendsto_right hβ0 hβ1 0) ?_
  apply tendsto_const_nhds.congr'
  filter_upwards [ev_unit_right hβ0 hβ1] with β h
  exact (passageJumpWeight_zero h.1 h.2).symm

/-- Full mass of the right limit: the positive-index right-limit weights sum
to exactly `β₀/(1-β₀)`, so no mass escapes as `β ↓ β₀`. -/
theorem passageWeightUp_hasSum {β₀ : ℝ} (hβ0 : 0 < β₀) (hβ1 : β₀ < 1) :
    HasSum (fun r => passageWeightUp β₀ (r+1)) (β₀/(1-β₀)) := by
  have hh : HasSum (fun r => passageWeightUp β₀ (r+1)) (1/(1-β₀)-1) := by
    apply (hasSum_nat_add_iff 1).2
    simpa [passageWeightUp_zero hβ0 hβ1] using passageWeightUp_hasSum_all hβ0 hβ1
  convert hh using 1
  field_simp [ne_of_gt (sub_pos.mpr hβ1)]
  ring

/-- The right-limit profile is nondecreasing. -/
theorem passageProfileUp_monotone {β₀ : ℝ} (hβ0 : 0 < β₀) (hβ1 : β₀ < 1) :
    Monotone (passageProfileUp β₀) :=
  BeattyPhase.jumpProfile_monotone (passageWeightUp_hasSum hβ0 hβ1).summable
    (fun _ => mul_nonneg (Nat.cast_nonneg _) (criticalWordMass_pos hβ0 hβ1 _ _).le)

/-- The right-limit law: the image of uniform phase measure under the
right-limit profile, for boundaries in `(0,1)`. -/
noncomputable def passageLawUp (β : ℝ) : ProbabilityMeasure ℝ :=
  if h : 0 < β ∧ β < 1 then
    unitPhaseLaw.map (passageProfileUp_monotone h.1 h.2).measurable.aemeasurable
  else unitPhaseLaw

/-- Integrals against the right-limit law are phase averages of the
right-limit profile. -/
theorem integral_passageLawUp {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (g : ℝ →ᵇ ℝ) :
    ∫ y, g y ∂(passageLawUp β : Measure ℝ) =
      ∫ t in Ioc (0 : ℝ) 1, g (passageProfileUp β t) := by
  rw [passageLawUp, dif_pos ⟨hβ0, hβ1⟩]
  exact integral_map_of_stronglyMeasurable (passageProfileUp_monotone hβ0 hβ1).measurable
    g.continuous.stronglyMeasurable

/-- Right limit at every boundary: as `β ↓ β₀` in `(0,1)`, the profile laws
converge weakly to the right-limit law `passageLawUp β₀`. -/
theorem passageProfileLaw_tendsto_right {β₀ : ℝ} (hβ0 : 0 < β₀) (hβ1 : β₀ < 1) :
    Tendsto passageProfileLaw (𝓝[>] β₀) (𝓝 (passageLawUp β₀)) := by
  have hu := ev_unit_right hβ0 hβ1
  have hs : Tendsto (fun β : ℝ => β/(1-β)) (𝓝[>] β₀) (𝓝 (β₀/(1-β₀))) :=
    (tendsto_id.div (tendsto_const_nhds.sub tendsto_id) (by linarith)).mono_left
      nhdsWithin_le_nhds
  apply passageLaw_tendsto_of_avg hu
  intro g
  rw [integral_passageLawUp hβ0 hβ1]
  exact passageAvg_tendsto_of hu (passageWeightUp_hasSum hβ0 hβ1)
    (fun _ => mul_nonneg (Nat.cast_nonneg _) (criticalWordMass_pos hβ0 hβ1 _ _).le) hs
    (fun r => passageWeight_tendsto_right hβ0 hβ1 (r+1))
    (fun r => passagePhase_tendsto_right hβ0 (r+1)) g

/-! ### The jump at a rational boundary -/

/-- At `b/a`, every positive-index right-limit phase is `q/b` with
`1 ≤ q ≤ b`: residue-zero phases sit at `1` rather than `0`. -/
theorem passagePhaseUp_rational {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (r : ℕ) :
    ∃ q : ℕ, 1 ≤ q ∧ q ≤ b ∧ passagePhaseUp ((b : ℝ)/a) (r+1) = (q : ℝ)/b := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  set N : ℕ := (r+1)*a
  have hx : ((r+1 : ℕ) : ℝ)/((b : ℝ)/a) = (N : ℝ)/b := by
    simp only [N]
    push_cast
    field_simp
  have hN : 0 < N := Nat.mul_pos (Nat.succ_pos r) ha
  have hpos : (0 : ℝ) < (N : ℝ)/b := div_pos (by exact_mod_cast hN) hbR
  set c := ⌈(N : ℝ)/b⌉₊ with hc
  have hc1 : 0 < c := Nat.lt_ceil.2 (by simpa using hpos)
  obtain ⟨d, hd⟩ : ∃ d, c = d+1 := ⟨c-1, by omega⟩
  have hlo : (d : ℝ) < (N : ℝ)/b := Nat.lt_ceil.1 (by omega)
  have hhi : (N : ℝ)/b ≤ c := Nat.le_ceil _
  have hlo' : b*d < N := by
    have : (b : ℝ)*d < N := by rw [lt_div_iff₀ hbR] at hlo; linarith
    exact_mod_cast this
  have hhi' : N ≤ b*d + b := by
    have : (N : ℝ) ≤ b*d + b := by
      rw [div_le_iff₀ hbR, hd] at hhi; push_cast at hhi; linarith
    exact_mod_cast this
  refine ⟨N - b*d, by omega, by omega, ?_⟩
  have hidx : passageIndexUp ((b : ℝ)/a) (r+1) = d := by
    unfold passageIndexUp
    push_cast at hx ⊢
    rw [hx, ← hc, hd, Nat.add_sub_cancel]
  unfold passagePhaseUp
  rw [hidx, Nat.cast_sub hlo'.le]
  push_cast at hx ⊢
  rw [hx]
  field_simp

/-- A jump profile whose phases are multiples of `1/b` is constant on each
interval `(j/b, (j+1)/b]`. -/
theorem jumpProfile_step {φ w : ℕ → ℝ} {b : ℕ} (hb : 0 < b)
    (hφ : ∀ r, ∃ q : ℕ, φ r = (q : ℝ)/b) (j : ℕ) {t : ℝ}
    (ht : t ∈ Ioc ((j : ℝ)/b) ((j+1 : ℝ)/b)) :
    BeattyPhase.jumpProfile φ w t = BeattyPhase.jumpProfile φ w ((j+1 : ℝ)/b) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  unfold BeattyPhase.jumpProfile
  congr 1
  apply tsum_congr
  intro r
  obtain ⟨q, hq⟩ := hφ r
  have hiff : φ r < t ↔ φ r < (j+1 : ℝ)/b := by
    rw [hq, div_lt_div_iff_of_pos_right hbR]
    constructor
    · intro h
      by_contra hc
      have hc' : (j : ℝ)+1 ≤ q := le_of_not_gt hc
      have : (j+1 : ℝ)/b ≤ (q : ℝ)/b := div_le_div_of_nonneg_right hc' hbR.le
      linarith [ht.2]
    · intro h
      have hq' : q ≤ j := by
        have : (q : ℝ) < (j : ℝ)+1 := h
        exact Nat.lt_succ_iff.mp (by exact_mod_cast this)
      have : (q : ℝ)/b ≤ (j : ℝ)/b :=
        div_le_div_of_nonneg_right (by exact_mod_cast hq') hbR.le
      linarith [ht.1]
  simp only [hiff]

/-- Phase averages of a function constant on each `(j/b, (j+1)/b]` are the
uniform averages of its values at the points `(j+1)/b`. -/
theorem integral_step_eq {F : ℝ → ℝ} {b : ℕ} (hb : 0 < b)
    (hF : ∀ (j : ℕ) (t : ℝ), t ∈ Ioc ((j : ℝ)/b) ((j+1 : ℝ)/b) → F t = F ((j+1 : ℝ)/b))
    (g : ℝ → ℝ) :
    ∫ t in Ioc (0 : ℝ) 1, g (F t) = (1/(b : ℝ))*∑ j ∈ range b, g (F ((j+1 : ℝ)/b)) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  set f := fun t => g (F t)
  set p : ℕ → ℝ := fun j => (j : ℝ)/b
  have hp (j : ℕ) : p (j+1) = ((j : ℝ)+1)/b := by simp [p]
  have hle (j : ℕ) : p j ≤ p (j+1) := by
    rw [hp]; exact div_le_div_of_nonneg_right (by linarith) hbR.le
  have heq (j : ℕ) : EqOn f (fun _ => g (F ((j+1 : ℝ)/b))) (Ioc (p j) (p (j+1))) := by
    intro t ht
    rw [hp] at ht
    exact congrArg g (hF j t ht)
  have hpiece (j : ℕ) : ∫ t in p j..p (j+1), f t = (1/(b : ℝ))*g (F ((j+1 : ℝ)/b)) := by
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

private theorem phaseUp_mult {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (r : ℕ) :
    ∃ q : ℕ, passagePhaseUp ((b : ℝ)/a) (r+1) = (q : ℝ)/b := by
  obtain ⟨q, -, -, hq⟩ := passagePhaseUp_rational ha hb r
  exact ⟨q, hq⟩

/-- At `b/a`, the right-limit profile equals `1` on the whole first interval
`(0, 1/b]`: no right-limit phase lies below `1/b`. -/
theorem passageProfileUp_rational_one {a b : ℕ} (ha : 0 < a) (hb : 0 < b) {t : ℝ}
    (ht : t ≤ 1/(b : ℝ)) : passageProfileUp ((b : ℝ)/a) t = 1 := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  unfold passageProfileUp BeattyPhase.jumpProfile
  have hz : ∀ r, ¬ passagePhaseUp ((b : ℝ)/a) (r+1) < t := by
    intro r
    obtain ⟨q, hq1, -, hq⟩ := passagePhaseUp_rational ha hb r
    rw [hq, not_lt]
    refine ht.trans ?_
    exact div_le_div_of_nonneg_right (by exact_mod_cast hq1) hbR.le
  simp [hz]

/-- The right-limit law at `b/a` is the uniform law on the `b` step values
`F⁺((j+1)/b)`, `j < b`, of the right-limit profile. -/
theorem integral_passageLawUp_rational {a b : ℕ} (hb : 0 < b) (hba : b < a) (g : ℝ →ᵇ ℝ) :
    ∫ y, g y ∂(passageLawUp ((b : ℝ)/a) : Measure ℝ) =
      (1/(b : ℝ))*∑ j ∈ range b, g (passageProfileUp ((b : ℝ)/a) ((j+1 : ℝ)/b)) := by
  have ha : 0 < a := hb.trans hba
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hβ0 : 0 < (b : ℝ)/a := div_pos (by exact_mod_cast hb) haR
  have hβ1 : (b : ℝ)/a < 1 := (div_lt_one haR).2 (by exact_mod_cast hba)
  rw [integral_passageLawUp hβ0 hβ1]
  exact integral_step_eq hb (fun j t ht => jumpProfile_step hb (phaseUp_mult ha hb) j ht) g

/-- The first of the `b` step values of the right-limit law at `b/a` is `1`. -/
theorem passageProfileUp_rational_first {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    passageProfileUp ((b : ℝ)/a) (1/(b : ℝ)) = 1 :=
  passageProfileUp_rational_one ha hb le_rfl

private theorem profileLaw_apply {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {s : Set ℝ}
    (hs : MeasurableSet s) :
    (passageProfileLaw β : Measure ℝ) s = volume (passageProfile β ⁻¹' s ∩ Ioc 0 1) := by
  rw [passageProfileLaw, dif_pos ⟨hβ0, hβ1⟩, ProbabilityMeasure.toMeasure_map,
    Measure.map_apply (passageProfile_monotone_all hβ0 hβ1).measurable hs]
  exact Measure.restrict_apply ((passageProfile_monotone_all hβ0 hβ1).measurable hs)

private theorem lawUp_apply {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {s : Set ℝ}
    (hs : MeasurableSet s) :
    (passageLawUp β : Measure ℝ) s = volume (passageProfileUp β ⁻¹' s ∩ Ioc 0 1) := by
  rw [passageLawUp, dif_pos ⟨hβ0, hβ1⟩, ProbabilityMeasure.toMeasure_map,
    Measure.map_apply (passageProfileUp_monotone hβ0 hβ1).measurable hs]
  exact Measure.restrict_apply ((passageProfileUp_monotone hβ0 hβ1).measurable hs)

/-- The right-limit law at `b/a` gives mass at least `1/b` to the value `1`. -/
theorem passageLawUp_one {a b : ℕ} (hb : 0 < b) (hba : b < a) :
    ENNReal.ofReal (1/(b : ℝ)) ≤ (passageLawUp ((b : ℝ)/a) : Measure ℝ) {1} := by
  have ha : 0 < a := hb.trans hba
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hβ0 : 0 < (b : ℝ)/a := div_pos (by linarith) haR
  have hβ1 : (b : ℝ)/a < 1 := (div_lt_one haR).2 (by exact_mod_cast hba)
  rw [lawUp_apply hβ0 hβ1 (measurableSet_singleton 1)]
  have hsub : Ioc (0 : ℝ) (1/b) ⊆ passageProfileUp ((b : ℝ)/a) ⁻¹' {1} ∩ Ioc 0 1 := by
    intro t ht
    refine ⟨passageProfileUp_rational_one ha hb ht.2, ht.1, ht.2.trans ?_⟩
    rw [div_le_one (by linarith)]
    exact hbR
  calc ENNReal.ofReal (1/(b : ℝ)) = volume (Ioc (0 : ℝ) (1/b)) := by
        rw [Real.volume_Ioc, sub_zero]
    _ ≤ _ := measure_mono hsub

/-- Every atom of `passageProfileLaw (b/a)` exceeds `1`, so it gives the value
`1` no mass. -/
theorem passageProfileLaw_one {a b : ℕ} (hb : 0 < b) (hba : b < a) :
    (passageProfileLaw ((b : ℝ)/a) : Measure ℝ) {1} = 0 := by
  have ha : 0 < a := hb.trans hba
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hβ0 : 0 < (b : ℝ)/a := div_pos (by exact_mod_cast hb) haR
  have hβ1 : (b : ℝ)/a < 1 := (div_lt_one haR).2 (by exact_mod_cast hba)
  rw [profileLaw_apply hβ0 hβ1 (measurableSet_singleton 1)]
  have hph : passagePhase ((b : ℝ)/a) (b-1+1) = 0 := by
    rw [passagePhase_rational ha hb, Nat.sub_add_cancel hb, Nat.mul_mod_right]
    simp
  have hF0 : 1 ≤ passageProfile ((b : ℝ)/a) 0 :=
    (BeattyPhase.jumpProfile_bounds (passage_jump_hasSum_all hβ0 hβ1).summable
      (fun r => passageJumpWeight_nonneg hβ0 hβ1 (r+1)) 0).1
  have hempty : passageProfile ((b : ℝ)/a) ⁻¹' {1} ∩ Ioc 0 1 = ∅ := by
    ext t
    constructor
    · rintro ⟨h1, ht0, -⟩
      have h1' : passageProfile ((b : ℝ)/a) t = 1 := h1
      have := passageProfile_lt_of_phase hβ0 hβ1 ht0 (r := b-1) hph.ge (by rw [hph]; exact ht0)
      linarith
    · intro h
      exact h.elim
  rw [hempty, measure_empty]

/-- The jump: the right-limit law at `b/a` differs from `passageProfileLaw (b/a)`. -/
theorem passageLawUp_ne_rational {a b : ℕ} (hb : 0 < b) (hba : b < a) :
    passageLawUp ((b : ℝ)/a) ≠ passageProfileLaw ((b : ℝ)/a) := by
  intro h
  have h1 := passageLawUp_one hb hba
  rw [h, passageProfileLaw_one hb hba, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h1
  have : (0 : ℝ) < 1/(b : ℝ) := one_div_pos.2 (by exact_mod_cast hb)
  linarith

/-- At a rational boundary `b/a` in `(0,1)` the law is not continuous: the
right limit (boundaries decreasing to `b/a`) is a different law. -/
theorem passageProfileLaw_discont {a b : ℕ} (hb : 0 < b) (hba : b < a) :
    ¬ Tendsto passageProfileLaw (𝓝 ((b : ℝ)/a)) (𝓝 (passageProfileLaw ((b : ℝ)/a))) := by
  intro h
  have ha : 0 < a := hb.trans hba
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hβ0 : 0 < (b : ℝ)/a := div_pos (by exact_mod_cast hb) haR
  have hβ1 : (b : ℝ)/a < 1 := (div_lt_one haR).2 (by exact_mod_cast hba)
  exact passageLawUp_ne_rational hb hba (tendsto_nhds_unique
    (passageProfileLaw_tendsto_right hβ0 hβ1) (h.mono_left nhdsWithin_le_nhds))

private theorem rational_unit {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ : ¬ Irrational β) :
    ∃ a b : ℕ, 0 < b ∧ b < a ∧ β = (b : ℝ)/a := by
  obtain ⟨q, rfl⟩ : ∃ q : ℚ, (q : ℝ) = β := by
    unfold Irrational at hβ
    simpa using hβ
  have hq0 : (0 : ℚ) < q := by exact_mod_cast hβ0
  have hnum : 0 < q.num := Rat.num_pos.2 hq0
  set b := q.num.natAbs
  set a := q.den
  have hb : 0 < b := Int.natAbs_pos.2 hnum.ne'
  have hbZ : (b : ℤ) = q.num := Int.natAbs_of_nonneg hnum.le
  have hq : (q : ℝ) = (b : ℝ)/a := by
    rw [Rat.cast_def]
    congr 1
    exact_mod_cast hbZ.symm
  refine ⟨a, b, hb, ?_, hq⟩
  have haR : (0 : ℝ) < a := by exact_mod_cast Nat.pos_of_ne_zero q.den_nz
  have h1 : (b : ℝ)/a < 1 := hq ▸ hβ1
  exact_mod_cast (div_lt_one haR).1 h1

/-- Boundary coordinate: for `β₀` in `(0,1)`, `passageProfileLaw` is continuous
at `β₀` (weak topology) if and only if `β₀` is irrational. -/
theorem passageProfileLaw_contAt_iff {β₀ : ℝ} (hβ0 : 0 < β₀) (hβ1 : β₀ < 1) :
    ContinuousAt passageProfileLaw β₀ ↔ Irrational β₀ := by
  refine ⟨fun h => ?_, passageProfileLaw_continuousAt hβ0 hβ1⟩
  by_contra hβ
  obtain ⟨a, b, hb, hba, rfl⟩ := rational_unit hβ0 hβ1 hβ
  exact passageProfileLaw_discont hb hba h

/-! ### Slope coordinates -/

/-- Slopes increasing to `α₀ > 0` give boundaries decreasing to `1/α₀`. -/
theorem inv_tendsto_right {α₀ : ℝ} (hα0 : 0 < α₀) :
    Tendsto (fun α : ℝ => 1/α) (𝓝[<] α₀) (𝓝[>] (1/α₀)) := by
  apply tendsto_nhdsWithin_iff.2
  refine ⟨(tendsto_const_nhds.div tendsto_id hα0.ne').mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds hα0)] with α hα hpos
  exact one_div_lt_one_div_of_lt hpos hα

/-- Right continuity in the slope at every real `α₀ > 1`, rational or not:
as `α ↓ α₀` the laws `passageProfileLaw (1/α)` converge weakly to
`passageProfileLaw (1/α₀)`. -/
theorem passageLaw_slope_right {α₀ : ℝ} (h1 : 1 < α₀) :
    Tendsto (fun α => passageProfileLaw (1/α)) (𝓝[>] α₀) (𝓝 (passageProfileLaw (1/α₀))) := by
  have h0 : 0 < α₀ := by linarith
  exact (passageProfileLaw_tendsto_left (one_div_pos.2 h0) ((div_lt_one h0).2 h1)).comp
    (inv_tendsto_left h0)

/-- Right continuity in the slope, as `ContinuousWithinAt` on `[α₀, ∞)`. -/
theorem passageLaw_slope_rightCont {α₀ : ℝ} (h1 : 1 < α₀) :
    ContinuousWithinAt (fun α => passageProfileLaw (1/α)) (Ici α₀) α₀ :=
  continuousWithinAt_Ioi_iff_Ici.1 (passageLaw_slope_right h1)

/-- Left limit in the slope at every real `α₀ > 1`: as `α ↑ α₀` the laws
`passageProfileLaw (1/α)` converge weakly to the right-limit law at `1/α₀`. -/
theorem passageLaw_slope_left {α₀ : ℝ} (h1 : 1 < α₀) :
    Tendsto (fun α => passageProfileLaw (1/α)) (𝓝[<] α₀) (𝓝 (passageLawUp (1/α₀))) := by
  have h0 : 0 < α₀ := by linarith
  exact (passageProfileLaw_tendsto_right (one_div_pos.2 h0) ((div_lt_one h0).2 h1)).comp
    (inv_tendsto_right h0)

/-- The slope jump at `a/b > 1`: as `α ↑ a/b` the laws converge to a law
different from the value `passageProfileLaw (b/a)` at `α = a/b`. -/
theorem passageLaw_slope_jump {a b : ℕ} (hb : 0 < b) (hba : b < a) :
    Tendsto (fun α => passageProfileLaw (1/α)) (𝓝[<] ((a : ℝ)/b))
        (𝓝 (passageLawUp ((b : ℝ)/a))) ∧
      passageLawUp ((b : ℝ)/a) ≠ passageProfileLaw (1/((a : ℝ)/b)) := by
  have h1 : 1 < (a : ℝ)/b := (one_lt_div (by exact_mod_cast hb)).2 (by exact_mod_cast hba)
  have h := passageLaw_slope_left h1
  rw [one_div_div] at h ⊢
  exact ⟨h, passageLawUp_ne_rational hb hba⟩

/-- Headline: for every real slope `α₀ > 1`, the map `α ↦ passageProfileLaw (1/α)`
into probability measures with the weak topology is continuous at `α₀` if and
only if `α₀` is irrational. It is right-continuous at every `α₀ > 1`
(`passageLaw_slope_rightCont`). -/
theorem passageLaw_slope_contAt_iff {α₀ : ℝ} (h1 : 1 < α₀) :
    ContinuousAt (fun α => passageProfileLaw (1/α)) α₀ ↔ Irrational α₀ := by
  have h0 : 0 < α₀ := by linarith
  have hb0 : 0 < 1/α₀ := one_div_pos.2 h0
  have hb1 : 1/α₀ < 1 := (div_lt_one h0).2 h1
  have hinv : Tendsto (fun α : ℝ => 1/α) (𝓝 α₀) (𝓝 (1/α₀)) :=
    tendsto_const_nhds.div tendsto_id h0.ne'
  constructor
  · intro h
    by_contra hα
    have hβ : ¬ Irrational (1/α₀) := fun hi => hα (by simpa using hi.inv)
    obtain ⟨a, b, hb, hba, hab⟩ := rational_unit hb0 hb1 hβ
    have hl : passageLawUp (1/α₀) = passageProfileLaw (1/α₀) :=
      tendsto_nhds_unique (passageLaw_slope_left h1)
      ((show Tendsto _ (𝓝 α₀) _ from h).mono_left nhdsWithin_le_nhds)
    rw [hab] at hl
    exact passageLawUp_ne_rational hb hba hl
  · intro hα
    exact (passageProfileLaw_continuousAt hb0 hb1 (by simpa using hα.inv)).comp hinv

/-- Slope form of continuity at irrational slopes: for irrational `α₀ > 1`,
`α ↦ passageProfileLaw (1/α)` is continuous at `α₀`, along all nearby slopes. -/
theorem passageLaw_slope_contAt {α₀ : ℝ} (h1 : 1 < α₀) (hα : Irrational α₀) :
    ContinuousAt (fun α => passageProfileLaw (1/α)) α₀ :=
  (passageLaw_slope_contAt_iff h1).2 hα

end Problems.Juggler.BeattySlope

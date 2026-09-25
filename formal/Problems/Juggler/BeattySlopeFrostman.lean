import Problems.Juggler.BeattySlopeIsolated
import Problems.Juggler.BeattyJumpCover

/-!
# Frostman bounds on phases give positive Hausdorff measure

For the cut-out set `K` of a jump profile `F`, the atom mass strictly inside a
phase interval `(u, v)` is `F(v) - F⁺(u)`. If an atomless finite measure on
the phases satisfies `ν[u, v] ≤ C (F(v) - F⁺(u))^s`, its image under `F` is
`s`-Frostman: a set of diameter `δ` pulls back into a phase interval whose atom
mass is at most `2δ`. The mass distribution principle then gives
`H^s(K) > 0`. The measure may be given by a continuous distribution function
`h`, through its Stieltjes measure.
-/

namespace Problems.Juggler.BeattySlope

open Filter Topology Set MeasureTheory BeattyPhase
open scoped NNReal ENNReal

/-- **Mass distribution on phases.** An atomless finite phase measure of
positive mass on `(0,1)` whose intervals carry at most `C` times the `s`-th
power of their atom mass forces `H^s(K) > 0`. -/
theorem jumpRange_hausdorff_ne_zero {φ w : ℕ → ℝ} (hw : Summable w) (hn : ∀ n, 0 ≤ w n)
    (hi : Function.Injective φ) (hp : ∀ n, φ n ∈ Ioo (0 : ℝ) 1) {s C : ℝ} (hs : 0 < s)
    (hC : 0 < C) (ν : Measure ℝ) [IsFiniteMeasure ν] (hpos : ν (Ioo 0 1) ≠ 0)
    (hatom : ∀ x, ν {x} = 0)
    (hfrost : ∀ u v : ℝ, 0 ≤ u → u < v → v ≤ 1 →
      ν (Icc u v) ≤ ENNReal.ofReal (C * (jumpProfile φ w v - jumpProfileRight φ w u) ^ s)) :
    Measure.hausdorffMeasure s (jumpRange φ w) ≠ 0 := by
  classical
  set F := jumpProfile φ w
  set Fr := jumpProfileRight φ w
  have hFm : Measurable F := (jumpProfile_monotone hw hn).measurable
  have hmono : Monotone F := jumpProfile_monotone hw hn
  set μs := (ν.restrict (Ioo 0 1)).map F
  have hKm : MeasurableSet (jumpRange φ w) := (isCompact_jumpRange hw hn hi hp).isClosed.measurableSet
  have hK : μs (jumpRange φ w) = ν (Ioo 0 1) := by
    have hpre : F ⁻¹' jumpRange φ w = univ := by
      ext t
      simp only [mem_preimage, mem_univ, iff_true]
      rw [← closure_range_jumpProfile hw hn hi hp]
      exact subset_closure (mem_range_self t)
    rw [Measure.map_apply hFm hKm, hpre, Measure.restrict_apply MeasurableSet.univ, univ_inter]
  set c : ℝ≥0∞ := ENNReal.ofReal (C * 2 ^ s)
  have hc0 : c ≠ 0 := by
    simp only [c, ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hcT : c ≠ ⊤ := ENNReal.ofReal_ne_top
  -- the Frostman bound for the image measure
  have hball : ∀ t : Set ℝ, Metric.ediam t ≤ 1 → c⁻¹ * μs t ≤ Metric.ediam t ^ s := by
    intro t ht
    rcases t.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · simp
    have hdT : Metric.ediam t ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top ht
    have hbdd : Bornology.IsBounded t := Metric.isBounded_iff_ediam_ne_top.2 hdT
    set δ := (Metric.ediam t).toReal
    have hδ0 : 0 ≤ δ := ENNReal.toReal_nonneg
    have hsub : t ⊆ Icc (x - δ) (x + δ) := by
      intro y hy
      have hd : dist y x ≤ Metric.diam t := Metric.dist_le_diam_of_mem hbdd hy hx
      have hdd : Metric.diam t = δ := rfl
      rw [Real.dist_eq, abs_le] at hd
      constructor <;> linarith [hd.1, hd.2]
    set S := F ⁻¹' Icc (x - δ) (x + δ) ∩ Ioo 0 1 with hSdef
    have hμS : μs t ≤ ν S := by
      refine (measure_mono hsub).trans (le_of_eq ?_)
      rw [Measure.map_apply hFm measurableSet_Icc, Measure.restrict_apply (hFm measurableSet_Icc)]
    have hνS : ν S ≤ ENNReal.ofReal (C * (2 * δ) ^ s) := by
      rcases S.eq_empty_or_nonempty with hSe | hSne
      · rw [hSe, measure_empty]; exact bot_le
      have hSbdd : BddBelow S := ⟨0, fun y hy => hy.2.1.le⟩
      have hSbdd' : BddAbove S := ⟨1, fun y hy => hy.2.2.le⟩
      set u := sInf S
      set v := sSup S
      have hSuv : S ⊆ Icc u v := fun y hy => ⟨csInf_le hSbdd hy, le_csSup hSbdd' hy⟩
      have hu0 : 0 ≤ u := le_csInf hSne fun y hy => hy.2.1.le
      have hv1 : v ≤ 1 := csSup_le hSne fun y hy => hy.2.2.le
      have huv0 : u ≤ v := by
        obtain ⟨y, hy⟩ := hSne
        exact (csInf_le hSbdd hy).trans (le_csSup hSbdd' hy)
      rcases huv0.lt_or_eq with huv | huv
      · refine (measure_mono hSuv).trans ((hfrost u v hu0 huv hv1).trans ?_)
        apply ENNReal.ofReal_le_ofReal
        -- the atom mass is at most `2δ`
        have hFv : F v ≤ x + δ := by
          by_cases hvS : v ∈ S
          · exact hvS.1.2
          · have hlub : IsLUB S v := isLUB_csSup hSne hSbdd'
            have hfreq : ∃ᶠ y in 𝓝[<] v, F y ≤ x + δ := by
              rw [Filter.frequently_iff]
              intro U hU
              obtain ⟨l, hl, hlU⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hU
              obtain ⟨y, hyS, hly, hyv⟩ := hlub.exists_between hl
              have hyv' : y < v := lt_of_le_of_ne hyv fun h => hvS (h ▸ hyS)
              exact ⟨y, hlU ⟨hly, hyv'⟩, hyS.1.2⟩
            exact le_of_tendsto_of_frequently (jumpProfile_tendsto_left hw hn v) hfreq
        have hFu : x - δ ≤ Fr u := by
          by_cases huS : u ∈ S
          · exact huS.1.1.trans (jumpProfile_le_right hw hn u)
          · have hglb : IsGLB S u := isGLB_csInf hSne hSbdd
            have hfreq : ∃ᶠ y in 𝓝[>] u, x - δ ≤ F y := by
              rw [Filter.frequently_iff]
              intro U hU
              obtain ⟨l, hl, hlU⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hU
              obtain ⟨y, hyS, hyu, hyl⟩ := hglb.exists_between hl
              have huy : u < y := lt_of_le_of_ne hyu fun h => huS (h ▸ hyS)
              exact ⟨y, hlU ⟨huy, hyl⟩, hyS.1.1⟩
            exact ge_of_tendsto_of_frequently (jumpProfile_tendsto_right hw hn u) hfreq
        have hinc0 : 0 ≤ F v - Fr u := sub_nonneg.2 (jumpProfileRight_le_of_lt hw hn huv)
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hinc0 (by linarith) hs.le) hC.le
      · have : S ⊆ {u} := fun y hy => by
          have h1 := hSuv hy
          rw [← huv] at h1
          exact le_antisymm h1.2 h1.1 |>.symm ▸ rfl
        rw [measure_mono_null this (hatom u)]; exact bot_le
    have hed : Metric.ediam t = ENNReal.ofReal δ := (ENNReal.ofReal_toReal hdT).symm
    calc c⁻¹ * μs t ≤ c⁻¹ * ENNReal.ofReal (C * (2 * δ) ^ s) := by gcongr; exact hμS.trans hνS
      _ = c⁻¹ * (c * ENNReal.ofReal (δ ^ s)) := by
          rw [← ENNReal.ofReal_mul (by positivity), Real.mul_rpow (by norm_num) hδ0, mul_assoc]
      _ = ENNReal.ofReal (δ ^ s) := by rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hcT, one_mul]
      _ = Metric.ediam t ^ s := by rw [hed, ENNReal.ofReal_rpow_of_nonneg hδ0 hs.le]
  have hle : c⁻¹ • μs ≤ Measure.hausdorffMeasure s :=
    Measure.le_hausdorffMeasure s _ 1 one_pos fun t ht => by
      rw [Measure.smul_apply, smul_eq_mul]; exact hball t ht
  intro h0
  have := hle (jumpRange φ w)
  rw [Measure.smul_apply, smul_eq_mul, hK, h0, nonpos_iff_eq_zero, mul_eq_zero] at this
  rcases this with h | h
  · exact (ENNReal.inv_ne_zero.2 hcT) h
  · exact hpos h

/-- **Frostman through a distribution function.** A continuous nondecreasing
`h` with `h 0 < h 1` whose increments over phase intervals are at most `C`
times the `s`-th power of the atom mass forces `H^s(K) > 0`. -/
theorem frostman_cdf_hausdorff {φ w : ℕ → ℝ} (hw : Summable w) (hn : ∀ n, 0 ≤ w n)
    (hi : Function.Injective φ) (hp : ∀ n, φ n ∈ Ioo (0 : ℝ) 1) {s C : ℝ} (hs : 0 < s)
    (hC : 0 < C) (h : ℝ → ℝ) (hmono : Monotone h) (hcont : Continuous h) (hne : h 0 < h 1)
    (hfrost : ∀ u v : ℝ, 0 ≤ u → u < v → v ≤ 1 →
      h v - h u ≤ C * (jumpProfile φ w v - jumpProfileRight φ w u) ^ s) :
    Measure.hausdorffMeasure s (jumpRange φ w) ≠ 0 := by
  let f : StieltjesFunction ℝ := ⟨h, hmono, fun x => hcont.continuousWithinAt⟩
  have hleft (a : ℝ) : Function.leftLim h a = h a :=
    leftLim_eq_of_tendsto (hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  set ν := f.measure.restrict (Icc 0 1)
  have hIcc (a b : ℝ) : f.measure (Icc a b) = ENNReal.ofReal (h b - h a) := by
    rw [StieltjesFunction.measure_Icc]; congr 2; exact hleft a
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 (by rw [hIcc]; exact ENNReal.ofReal_ne_top)
  refine jumpRange_hausdorff_ne_zero hw hn hi hp hs hC ν ?_ ?_ ?_
  · rw [Measure.restrict_apply measurableSet_Ioo, Set.inter_eq_left.2 Ioo_subset_Icc_self,
      StieltjesFunction.measure_Ioo]
    have : Function.leftLim f 1 = h 1 := hleft 1
    rw [this]
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact sub_pos.2 hne
  · intro x
    have h0 : f.measure {x} = 0 := by
      rw [StieltjesFunction.measure_singleton]
      have : Function.leftLim f x = h x := hleft x
      rw [this, sub_self, ENNReal.ofReal_zero]
    exact le_antisymm ((Measure.restrict_le_self {x}).trans (le_of_eq h0)) bot_le
  · intro u v hu huv hv
    refine (Measure.restrict_le_self (Icc u v)).trans ?_
    rw [hIcc]
    exact ENNReal.ofReal_le_ofReal (hfrost u v hu huv hv)

/-- **Bases at the grid.** For a reduced approximation `p/q` with error
`θ = qα - p`, `|θ| < 1/q`, every grid point `i/q` with `0 < i < q` carries the
orbit point `{tα} = i/q + tθ/q` of an index `0 < t < q`. -/
theorem base_at_grid {α : ℝ} {q : ℕ} (hq : 1 < q) {p : ℤ} (hcop : IsCoprime p (q : ℤ))
    (hθ : |(q : ℝ) * α - p| < 1 / q) {i : ℕ} (hi1 : 1 ≤ i) (hiq : i < q) :
    ∃ t : ℕ, 1 ≤ t ∧ t < q ∧
      Int.fract ((t : ℝ) * α) = (i : ℝ) / q + (t : ℝ) * ((q : ℝ) * α - p) / q := by
  obtain ⟨a, b, hab⟩ := hcop
  have hq0 : (0 : ℤ) < q := by exact_mod_cast (show 0 < q by omega)
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  set r : ℤ := ((i : ℤ) * a) % q with hr
  have hr0 : 0 ≤ r := Int.emod_nonneg _ hq0.ne'
  have hrq : r < q := Int.emod_lt_of_pos _ hq0
  set t : ℕ := r.toNat with ht
  have htr : (t : ℤ) = r := Int.toNat_of_nonneg hr0
  -- `t p ≡ i` modulo `q`
  have hmod : (q : ℤ) ∣ (t : ℤ) * p - i := by
    have h1 : (q : ℤ) ∣ (i : ℤ) * a - r := by
      exact ⟨(i : ℤ) * a / q, by rw [hr, Int.emod_def]; ring⟩
    have h2 : (t : ℤ) * p - i = -((i : ℤ) * a - r) * p + (i : ℤ) * (a * p - 1) := by
      rw [htr]; ring
    rw [h2]
    refine dvd_add (dvd_mul_of_dvd_left (dvd_neg.2 h1) _) (dvd_mul_of_dvd_right ?_ _)
    exact ⟨-b, by linarith⟩
  obtain ⟨m, hm⟩ := hmod
  have ht1 : 1 ≤ t := by
    by_contra h0
    have ht0 : t = 0 := by omega
    rw [ht0] at hm
    simp only [Nat.cast_zero, zero_mul, zero_sub] at hm
    have : (q : ℤ) ∣ (i : ℤ) := ⟨-m, by linarith⟩
    have hle := Int.le_of_dvd (by exact_mod_cast (show 0 < i by omega)) this
    have : (q : ℤ) ≤ i := hle
    omega
  have htq : t < q := by
    have : (t : ℤ) < q := by rw [htr]; exact hrq
    exact_mod_cast this
  refine ⟨t, ht1, htq, ?_⟩
  set θ := (q : ℝ) * α - p
  have hmR : (t : ℝ) * p = i + q * m := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hm
    push_cast at this
    linarith
  have heq : (t : ℝ) * α = (m : ℝ) + ((i : ℝ) / q + (t : ℝ) * θ / q) := by
    have hα : α = (p + θ) / q := by simp only [θ]; field_simp; ring
    rw [hα]
    field_simp
    linarith
  rw [heq, Int.fract_intCast_add, Int.fract_eq_self]
  have htR : (t : ℝ) < q := by exact_mod_cast htq
  have hiR : (1 : ℝ) ≤ i := by exact_mod_cast hi1
  have hiq' : (i : ℝ) + 1 ≤ q := by exact_mod_cast hiq
  have hsmall : |(t : ℝ) * θ / q| < 1 / q := by
    rw [abs_div, abs_mul, abs_of_nonneg (Nat.cast_nonneg t), abs_of_pos hqR,
      div_lt_div_iff_of_pos_right hqR]
    calc (t : ℝ) * |θ| ≤ q * |θ| := mul_le_mul_of_nonneg_right htR.le (abs_nonneg θ)
      _ < q * (1 / q) := mul_lt_mul_of_pos_left hθ hqR
      _ = 1 := by field_simp
  rw [abs_lt] at hsmall
  have h1 : 1 / (q : ℝ) ≤ (i : ℝ) / q := div_le_div_of_nonneg_right hiR hqR.le
  have h2 : (i : ℝ) / q ≤ 1 - 1 / q := by
    rw [le_sub_iff_add_le, ← add_div, div_le_one hqR]; exact hiq'
  constructor <;> linarith [hsmall.1, hsmall.2]

end Problems.Juggler.BeattySlope

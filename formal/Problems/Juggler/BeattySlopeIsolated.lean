import Problems.Juggler.BeattySlopeStarDim
import Problems.Juggler.BeattySlopeLawPacking

/-!
# Slopes with isolated good levels

For `ν > 1` and a set `G` of good indices, the partial quotients are
`a_k = ⌈Q_k^(ν-1)⌉ + 1` at good `k ≥ 1` and `a_k = 1` otherwise. With infinitely
many good indices the slope has Diophantine class exactly `ν`: the good levels
give `Q_(k+1) ≥ Q_k^ν` infinitely often, and every level satisfies
`Q_(k+1) ≤ 4 Q_k^ν`. Its limit law therefore has dimension `2/(2+ν)`, and its
cluster set has Hausdorff dimension at most `s*(ν)`. With the good indices
sparse (the tower `2^(2^j)`), the written argument of the working notes gives
the matching lower bound `s*(ν)`, which is not formalized here.
-/

namespace Problems.Juggler.BeattySlope

open Filter Topology Set MeasureTheory

/-- Continuant denominators with big partial quotients exactly at good indices. -/
noncomputable def isoDen (ν : ℝ) (G : ℕ → Prop) [DecidablePred G] : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | k + 2 => ((if G (k + 1) then ⌈(isoDen ν G (k + 1) : ℝ) ^ (ν - 1)⌉₊ + 1 else 1) *
      isoDen ν G (k + 1) + isoDen ν G k)

/-- Partial quotients: `a_0 = 1`, `a_k = ⌈Q_k^(ν-1)⌉ + 1` at good `k ≥ 1`, else `1`. -/
noncomputable def isoQuot (ν : ℝ) (G : ℕ → Prop) [DecidablePred G] (k : ℕ) : ℕ :=
  if k = 0 then 1 else if G k then ⌈(isoDen ν G k : ℝ) ^ (ν - 1)⌉₊ + 1 else 1

variable {ν : ℝ} {G : ℕ → Prop} [DecidablePred G]

/-- The partial quotients after the first are at least one. -/
theorem isoQuot_succ_ge (ν : ℝ) (G : ℕ → Prop) [DecidablePred G] (k : ℕ) :
    1 ≤ isoQuot ν G (k + 1) := by
  unfold isoQuot; split_ifs <;> simp

/-- The continuant denominators of `isoQuot ν G` are `isoDen ν G`. -/
theorem cfDen_isoQuot (ν : ℝ) (G : ℕ → Prop) [DecidablePred G] :
    ∀ k, cfDen (isoQuot ν G) k = isoDen ν G k
  | 0 => rfl
  | 1 => rfl
  | k + 2 => by
    rw [cfDen_add_two, cfDen_isoQuot ν G (k + 1), cfDen_isoQuot ν G k]
    simp [isoQuot, isoDen]

/-- The slope with isolated good levels. -/
noncomputable def isoSlope (ν : ℝ) (G : ℕ → Prop) [DecidablePred G] : ℝ := cfLim (isoQuot ν G)

/-- The isolated slope exceeds one. -/
theorem one_lt_isoSlope (ν : ℝ) (G : ℕ → Prop) [DecidablePred G] : 1 < isoSlope ν G := by
  have h := cfLim_gt (isoQuot_succ_ge ν G)
  simpa [isoQuot, isoSlope] using h

/-- The isolated slope is irrational. -/
theorem isoSlope_irrational (ν : ℝ) (G : ℕ → Prop) [DecidablePred G] :
    Irrational (isoSlope ν G) :=
  cfLim_irrational (isoQuot_succ_ge ν G)

/-- Growth: always `Q_(n+2) ≤ 4 Q_(n+1)^ν`, and `Q_(n+2) ≥ Q_(n+1)^ν` at good `n+1`. -/
theorem isoDen_growth (hν : 1 ≤ ν) (n : ℕ) :
    (isoDen ν G (n + 2) : ℝ) ≤ 4 * (isoDen ν G (n + 1) : ℝ) ^ ν ∧
      (G (n + 1) → (isoDen ν G (n + 1) : ℝ) ^ ν ≤ isoDen ν G (n + 2)) := by
  have hx : (1 : ℝ) ≤ isoDen ν G (n + 1) := by
    have := cfDen_succ_pos (isoQuot_succ_ge ν G) n
    rw [cfDen_isoQuot] at this
    exact_mod_cast this
  have hle : (isoDen ν G n : ℝ) ≤ isoDen ν G (n + 1) := by
    have := cfDen_le_succ (isoQuot_succ_ge ν G) n
    rw [cfDen_isoQuot, cfDen_isoQuot] at this
    exact_mod_cast this
  set x : ℝ := (isoDen ν G (n + 1) : ℝ)
  set t : ℝ := x ^ (ν - 1)
  have ht1 : 1 ≤ t := Real.one_le_rpow hx (by linarith)
  have hxν : x ^ ν = t * x := by
    rw [show t = x ^ (ν - 1) from rfl, ← Real.rpow_add_one (by linarith), sub_add_cancel]
  have hn0 : (0 : ℝ) ≤ isoDen ν G n := Nat.cast_nonneg _
  by_cases hg : G (n + 1)
  · have hQ : (isoDen ν G (n + 2) : ℝ) = (⌈t⌉₊ + 1) * x + isoDen ν G n := by
      simp [isoDen, hg, x, t]
    have hc1 : t ≤ ⌈t⌉₊ := Nat.le_ceil t
    have hc2 : (⌈t⌉₊ : ℝ) < t + 1 := Nat.ceil_lt_add_one (by linarith)
    rw [hQ, hxν]
    exact ⟨by nlinarith, fun _ => by nlinarith⟩
  · have hQ : (isoDen ν G (n + 2) : ℝ) = x + isoDen ν G n := by
      simp [isoDen, hg, x]
    refine ⟨?_, fun h => absurd h hg⟩
    rw [hQ, hxν]
    nlinarith

/-- **Class of the isolated slope.** With infinitely many good indices the
slope has Diophantine class exactly `ν`. -/
theorem isoSlope_diophClass (hν : 1 < ν) (hG : ∀ N, ∃ k, N ≤ k ∧ G (k + 1)) :
    DiophClass (isoSlope ν G) ν := by
  have hgood := cf_goodConvergents (isoQuot_succ_ge ν G)
  have hq : Tendsto (fun n => cfDen (isoQuot ν G) (n + 1)) atTop atTop :=
    (cfDen_tendsto (isoQuot_succ_ge ν G)).comp (tendsto_add_atTop_nat 1)
  constructor
  · intro μ hμ
    have tq : Tendsto (fun n => ((cfDen (isoQuot ν G) (n + 1) : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hq
    have hbig : Tendsto (fun n => ((cfDen (isoQuot ν G) (n + 1) : ℕ) : ℝ) ^ (ν - μ)) atTop atTop :=
      (tendsto_rpow_atTop (by linarith)).comp tq
    refine Set.infinite_of_forall_exists_gt fun N => ?_
    obtain ⟨M, hM⟩ := eventually_atTop.1 ((hbig.eventually_gt_atTop 1).and (hq.eventually_gt_atTop N))
    obtain ⟨k, hk, hgk⟩ := hG M
    obtain ⟨h1, h2⟩ := hM k hk
    set q := cfDen (isoQuot ν G) (k + 1)
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hgood.pos k
    refine ⟨q, ⟨hgood.pos k, (cfNum (isoQuot ν G) (k + 1) : ℤ), ?_⟩, h2⟩
    have hgr := (isoDen_growth (G := G) hν.le k).2 hgk
    rw [← cfDen_isoQuot, ← cfDen_isoQuot] at hgr
    have hden : (0 : ℝ) < (q : ℝ) ^ ν := by positivity
    calc |(q : ℝ) * isoSlope ν G - (cfNum (isoQuot ν G) (k + 1) : ℤ)|
        ≤ 1 / (cfDen (isoQuot ν G) (k + 1 + 1) : ℝ) := hgood.approx k
      _ ≤ 1 / (q : ℝ) ^ ν := one_div_le_one_div_of_le hden hgr
      _ < (q : ℝ) ^ (-μ) := by
          rw [div_lt_iff₀ hden]
          have : (q : ℝ) ^ (-μ) * (q : ℝ) ^ ν = (q : ℝ) ^ (ν - μ) := by
            rw [← Real.rpow_add hq0]; ring_nf
          rw [this]; exact h1
  · intro μ hμ
    have hup : ∀ n, (cfDen (isoQuot ν G) (n + 1 + 1) : ℝ) ≤
        4 * (cfDen (isoQuot ν G) (n + 1) : ℝ) ^ ν := by
      intro n; rw [cfDen_isoQuot, cfDen_isoQuot]; exact (isoDen_growth hν.le n).1
    obtain ⟨c', hc', hdio⟩ := regular_dio_lower (by linarith) hgood hq (by norm_num) hup
    have hsmall : Tendsto (fun m : ℕ => (m : ℝ) ^ (-(μ - ν))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hsmall).2 c' hc')
    refine (Set.finite_Iio N).subset fun m hm => ?_
    obtain ⟨hm0, r, hr⟩ := hm
    by_contra hmN
    have hmN' : N ≤ m := not_lt.1 hmN
    have hm0R : (0 : ℝ) < m := by exact_mod_cast hm0
    have h1 : c' ≤ (m : ℝ) ^ ν * |(m : ℝ) * isoSlope ν G - r| := hdio m hm0 r
    have h2 : (m : ℝ) ^ ν * |(m : ℝ) * isoSlope ν G - r| < (m : ℝ) ^ ν * (m : ℝ) ^ (-μ) :=
      mul_lt_mul_of_pos_left hr (by positivity)
    rw [← Real.rpow_add hm0R, show ν + -μ = -(μ - ν) by ring] at h2
    have := hN m hmN'
    linarith

/-- **Isolated slopes: the law and the upper bound.** With infinitely many
good indices the limit law has lower Hausdorff dimension `2/(2+ν)`, and the
cluster set has Hausdorff dimension at most `s*(ν)`. -/
theorem isoSlope_dims (hν : 1 < ν) (hG : ∀ N, ∃ k, N ≤ k ∧ G (k + 1)) :
    lawDimH (passageLaw (β := 1 / isoSlope ν G)
      (one_div_pos.2 (by linarith [one_lt_isoSlope ν G]))
      ((div_lt_one (by linarith [one_lt_isoSlope ν G])).2 (one_lt_isoSlope ν G))
      (by simpa using (isoSlope_irrational ν G).inv) : Measure ℝ) =
      ENNReal.ofReal (2 / (2 + ν)) ∧
    dimH (passageClusterSet (1 / isoSlope ν G)) ≤ ENNReal.ofReal (starDim ν) := by
  have hcls := isoSlope_diophClass hν hG
  refine ⟨passageLaw_lawDimH_eq (one_lt_isoSlope ν G) (isoSlope_irrational ν G) hν.le hcls, ?_⟩
  -- the upper bound with every exponent `ν' < ν`, and continuity of `s*`
  apply le_of_forall_gt_imp_ge_of_dense
  intro c hc
  by_cases hct : c = ⊤
  · rw [hct]; exact le_top
  have hs : starDim ν < c.toReal := by
    rw [← ENNReal.ofReal_lt_ofReal_iff_of_nonneg (starDim_pos (by linarith)).le,
      ENNReal.ofReal_toReal hct]
    exact hc
  have hcont : ContinuousAt starDim ν := by
    unfold starDim
    apply ContinuousAt.div _ (continuousAt_const.mul continuousAt_id)
      (mul_ne_zero (by norm_num) (by simp only [id]; linarith))
    exact continuousAt_const.mul ((Real.continuous_sqrt.continuousAt).comp
      (continuousAt_const.add (continuousAt_const.mul continuousAt_id)) |>.sub continuousAt_const)
  obtain ⟨δ, hδ, hδs⟩ := Metric.continuousAt_iff.1 hcont _ (sub_pos.2 hs)
  set ν' := max ((1 + ν) / 2) (ν - δ / 2)
  have hν'1 : 1 < ν' := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hν'ν : ν' < ν := max_lt (by linarith) (by linarith)
  have hs' : starDim ν' < c.toReal := by
    have h := hδs (x := ν') (by
      rw [Real.dist_eq, abs_lt]
      constructor
      · have := le_max_right ((1 + ν) / 2) (ν - δ / 2); linarith
      · linarith)
    rw [Real.dist_eq, abs_lt] at h
    linarith [h.2]
  have happ : ∀ Q : ℕ, ∃ q : ℕ, Q < q ∧ ∃ p : ℤ,
      |(q : ℝ) * isoSlope ν G - p| ≤ (q : ℝ) ^ (-ν') := by
    intro Q
    obtain ⟨q, ⟨hq0, p, hp⟩, hqQ⟩ := (hcls.1 ν' hν'ν).exists_gt Q
    exact ⟨q, hqQ, p, hp.le⟩
  refine (dio_star_dimH_le (one_lt_isoSlope ν G) (isoSlope_irrational ν G) hν'1 happ).trans ?_
  calc ENNReal.ofReal (starDim ν') ≤ ENNReal.ofReal c.toReal := ENNReal.ofReal_le_ofReal hs'.le
    _ = c := ENNReal.ofReal_toReal hct

end Problems.Juggler.BeattySlope

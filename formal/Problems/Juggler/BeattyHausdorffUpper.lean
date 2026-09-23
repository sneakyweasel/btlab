import Problems.Juggler.BeattyCertificateCantor
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.MetricSpace.CoveringNumbers

/-!
# Hausdorff upper bounds from real-line tube volumes

Finite separated nets turn cube-root tube bounds into finite two-thirds
Hausdorff measure. The certificate specialization has no phase-spacing premise.
-/

namespace Problems.Juggler.BeattyPhase

open Filter Topology Set MeasureTheory Metric
open scoped NNReal ENNReal

private theorem compact_tube_cover {K : Set ℝ} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset ℝ, (↑s : Set ℝ) ⊆ K ∧
      K ⊆ ⋃ x ∈ s, closedBall x (2*ε) ∧
      (s.card : ℝ)*(2*ε) ≤ volume.real (thickening ε K) := by
  classical
  let e : ℝ≥0 := ⟨ε,hε.le⟩
  obtain ⟨N,hNK,hNf,hNc⟩ := exists_finite_isCover_of_isCompact (ε := e)
    (by intro hz; have hz' := congrArg (fun a : ℝ≥0 => (a : ℝ)) hz; exact hε.ne' hz') hK
  have hp : packingNumber (2*e) K ≠ ⊤ :=
    ((packingNumber_two_mul_le_externalCoveringNumber e K).trans
      hNc.externalCoveringNumber_le_encard).trans_lt hNf.encard_lt_top |>.ne
  let D := maximalSeparatedSet (2*e) K
  have hDf : D.Finite := Set.encard_ne_top_iff.1 (by
    dsimp only [D]
    rw [encard_maximalSeparatedSet hp]
    exact hp)
  let s := hDf.toFinset
  have hs : (↑s : Set ℝ) = D := hDf.coe_toFinset
  have hsmem {x : ℝ} : x ∈ s ↔ x ∈ D := by
    change x ∈ (↑s : Set ℝ) ↔ x ∈ D
    rw [hs]
  have hDK : D ⊆ K := maximalSeparatedSet_subset
  have hcover : K ⊆ ⋃ x ∈ s, closedBall x (2*ε) := by
    change K ⊆ ⋃ x ∈ (↑s : Set ℝ), closedBall x (2*ε)
    rw [hs]
    have hc := (isCover_maximalSeparatedSet hp).subset_iUnion_closedBall
    change K ⊆ ⋃ x ∈ D, closedBall x (2*ε) at hc
    exact hc
  have hdis : (↑s : Set ℝ).PairwiseDisjoint (fun x => ball x ε) := by
    intro x hx y hy hxy
    have hd := isSeparated_maximalSeparatedSet (ε := 2*e) (A := K)
      (hsmem.1 hx) (hsmem.1 hy) hxy
    have hd' : 2*ε < dist x y := by
      have hh : ENNReal.ofReal (2*ε) < ENNReal.ofReal (dist x y) := by
        dsimp only at hd
        rw [edist_dist, ← ENNReal.ofReal_coe_nnreal] at hd
        change ENNReal.ofReal (2*ε) < ENNReal.ofReal (dist x y) at hd
        exact hd
      exact (ENNReal.ofReal_lt_ofReal_iff'.1 hh).1
    exact ball_disjoint_ball (by linarith)
  have hsub : (⋃ x ∈ s, ball x ε) ⊆ thickening ε K := by
    intro z hz
    obtain ⟨x,hx,hzx⟩ := mem_iUnion₂.1 hz
    exact mem_thickening_iff.2 ⟨x,hDK (hsmem.1 hx),hzx⟩
  have hvol := measureReal_mono (μ := volume) hsub
    hK.isBounded.thickening.measure_lt_top.ne
  rw [measureReal_biUnion_finset hdis (fun _ _ => measurableSet_ball)] at hvol
  simp only [Real.volume_real_ball hε.le, Finset.sum_const, nsmul_eq_mul] at hvol
  exact ⟨s, hs ▸ hDK, hcover, hvol⟩

/-- A compact real set with a cube-root upper tube bound has finite
two-thirds Hausdorff measure, in Mathlib's diameter normalization. -/
theorem hausdorffMeasure_two_thirds_ne_top_of_tube_bound {K : Set ℝ}
    (hK : IsCompact K) {C : ℝ}
    (hv : ∀ ε : ℝ, 0 < ε → ε ≤ 1/2 →
      volume.real (thickening ε K) ≤ C*ε^(1/3 : ℝ)) :
    Measure.hausdorffMeasure (2/3 : ℝ) K ≠ ⊤ := by
  classical
  let e : ℕ → ℝ := fun n => 1/((n : ℝ)+2)
  have he (n : ℕ) : 0 < e n := by dsimp [e]; positivity
  have he' (n : ℕ) : e n ≤ 1/2 := by
    dsimp [e]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) n])
  choose s hsK hscover hsvol using fun n => compact_tube_cover hK (he n)
  let t (n : ℕ) (x : ↥(s n)) : Set ℝ := closedBall x (2*e n)
  have hd (n : ℕ) (x : ↥(s n)) : ediam (t n x) ≤ ENNReal.ofReal (4*e n) := by
    apply ediam_le_of_forall_dist_le
    intro a ha b hb
    have h := dist_triangle a (x : ℝ) b
    rw [dist_comm (x : ℝ) b] at h
    exact h.trans (by linarith [(mem_closedBall.1 ha),(mem_closedBall.1 hb)])
  have hzero : Tendsto (fun n => ENNReal.ofReal (4*e n)) atTop (𝓝 0) := by
    have hh : Tendsto e atTop (𝓝 0) := by
      exact tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
    have hh' : Tendsto (fun n => 4*e n) atTop (𝓝 0) := by simpa using hh.const_mul 4
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp hh'
  have hcover (n : ℕ) : K ⊆ ⋃ x : ↥(s n), t n x := by
    intro y hy
    obtain ⟨x,hx,hyx⟩ := mem_iUnion₂.1 (hscover n hy)
    exact mem_iUnion.2 ⟨⟨x,hx⟩,hyx⟩
  have hbound (n : ℕ) :
      (∑ x : ↥(s n), ediam (t n x)^(2/3 : ℝ)) ≤ ENNReal.ofReal (2*C) := by
    have hcard := (hsvol n).trans (hv _ (he n) (he' n))
    have hp := Real.rpow_pos_of_pos (he n) (1/3 : ℝ)
    have hprod : e n^(1/3 : ℝ)*e n^(2/3 : ℝ) = e n := by
      rw [← Real.rpow_add (he n)]
      norm_num
    have hreal : (s n).card*(4*e n)^(2/3 : ℝ) ≤ 2*C := by
      have hpow : (4 : ℝ)^(2/3 : ℝ) ≤ 4 := by
        simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4)
          (by norm_num : (2/3 : ℝ) ≤ 1)
      have hfac : 2*((s n).card : ℝ)*e n^(2/3 : ℝ) ≤ C := by
        have heq : (2*((s n).card : ℝ)*e n^(2/3 : ℝ))*e n^(1/3 : ℝ) =
            (s n).card*(2*e n) := by
          calc
            _ = (2*((s n).card : ℝ))*(e n^(1/3 : ℝ)*e n^(2/3 : ℝ)) := by ring
            _ = _ := by rw [hprod]; ring
        nlinarith [hcard,heq]
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (he n).le]
      have h := mul_le_mul_of_nonneg_left hpow
        (mul_nonneg (by positivity : (0 : ℝ) ≤ (s n).card)
          (Real.rpow_nonneg (he n).le (2/3 : ℝ)))
      nlinarith
    calc
      _ ≤ ∑ _x : ↥(s n), (ENNReal.ofReal (4*e n))^(2/3 : ℝ) := by
        exact Finset.sum_le_sum fun x _ => ENNReal.rpow_le_rpow (hd n x) (by norm_num)
      _ = ENNReal.ofReal ((s n).card*(4*e n)^(2/3 : ℝ)) := by
        rw [ENNReal.ofReal_rpow_of_pos (by positivity : 0 < 4*e n)]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
        rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (s n).card), ENNReal.ofReal_natCast]
      _ ≤ _ := ENNReal.ofReal_le_ofReal hreal
  have hh := Measure.hausdorffMeasure_le_liminf_sum (2/3 : ℝ) K _ hzero t
    (Eventually.of_forall hd) (Eventually.of_forall hcover)
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (hh.trans (liminf_le_of_frequently_le' (Eventually.of_forall hbound).frequently))

/-- The actual certificate cluster set has finite two-thirds Hausdorff
measure, unconditionally. Positivity is a separate arithmetic question. -/
theorem certificateClusterSet_hausdorffMeasure_ne_top :
    Measure.hausdorffMeasure (2/3 : ℝ) certificateClusterSet ≠ ⊤ := by
  obtain ⟨c,C,_,_,h⟩ := certificateClusterSet_tube_bounds
  exact hausdorffMeasure_two_thirds_ne_top_of_tube_bound isCompact_certificateClusterSet
    (fun ε hε hsmall => (h ε hε hsmall).2)

/-- The Hausdorff dimension of the original certificate cluster set is
at most two-thirds. No lower bound on phase spacing is assumed. -/
theorem certificateClusterSet_dimH_upper : dimH certificateClusterSet ≤ (2/3 : ℝ≥0∞) := by
  simpa using dimH_le_of_hausdorffMeasure_ne_top
    (d := (2/3 : ℝ≥0)) certificateClusterSet_hausdorffMeasure_ne_top

end Problems.Juggler.BeattyPhase

import Problems.Juggler.BeattySlopeGapCounting
import Problems.Juggler.BeattyLocalCounting

/-!
# Spatial gap counting for every irrational slope

The corresponding gap and tube assertions for every irrational boundary in `(0,1)`.
All inputs concern the actual first-passage counts, without an arithmetic rate premise.
-/

namespace Problems.Juggler.BeattySlope

open Filter Topology Set MeasureTheory BeattyPhase
open scoped NNReal ENNReal BoundedContinuousFunction
open BTCalculus.FourierBoxCounting

variable {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ : Irrational β)

include hβ0 hβ1 hβ

/-- The passage weights retained strictly above a spatial threshold.
Their positions are the left endpoints of the actual complementary gaps. -/
noncomputable def passageTailWeight (β : ℝ) (y : ℝ) (n : ℕ) : ℝ :=
  if y < (passageProfile β) ((passagePhase β) (n+1)) then (passageJumpWeight β) (n+1) else 0

/-- The phase density whose integral counts gaps retained above a threshold. -/
noncomputable def passageTailDensity (β : ℝ) (y t : ℝ) : ℝ :=
  if y < (passageProfile β) t then ((passageAmplitude β)*(passageProfile β) t)^(2/3 : ℝ) else 0

/-- Retaining an upper segment preserves monotonicity of the nonnegative phase density. -/
theorem passageTailDensity_monotone (y : ℝ) : Monotone ((passageTailDensity β) y) := by
  intro a b hab
  have hF := (passageProfile_monotone hβ0 hβ1 hβ) hab
  unfold passageTailDensity
  split_ifs with ha hb hb
  · exact Real.rpow_le_rpow
      (mul_nonneg (passageAmplitude_pos hβ0 hβ1).le (by linarith [((passageProfile_bounds hβ0 hβ1 hβ) a).1]))
      (mul_le_mul_of_nonneg_left hF (passageAmplitude_pos hβ0 hβ1).le) (by norm_num)
  · exact False.elim (hb (ha.trans_le hF))
  · exact Real.rpow_nonneg (mul_nonneg (passageAmplitude_pos hβ0 hβ1).le
      (by linarith [((passageProfile_bounds hβ0 hβ1 hβ) b).1])) _
  · rfl

/-- The retained density is nonnegative, including where the cutoff makes it zero. -/
theorem passageTailDensity_nonneg (y t : ℝ) : 0 ≤ (passageTailDensity β) y t := by
  unfold passageTailDensity
  split_ifs
  · exact Real.rpow_nonneg (mul_nonneg (passageAmplitude_pos hβ0 hβ1).le
      (by linarith [((passageProfile_bounds hβ0 hβ1 hβ) t).1])) _
  · rfl

/-- Retaining any upper spatial segment preserves summability of the gap lengths. -/
theorem passageTailWeight_summable (y : ℝ) : Summable ((passageTailWeight β) y) := by
  apply (passage_jump_weights_hasSum hβ0 hβ1 hβ).summable.of_norm_bounded
  intro n
  unfold passageTailWeight
  split_ifs <;> simp [Real.norm_of_nonneg ((passageJumpWeight_nonneg hβ0 hβ1) _), (passageJumpWeight_nonneg hβ0 hβ1)]

omit hβ in
/-- Every retained gap length is nonnegative. -/
theorem passageTailWeight_nonneg (y : ℝ) (n : ℕ) : 0 ≤ (passageTailWeight β) y n := by
  unfold passageTailWeight
  split_ifs <;> simp [(passageJumpWeight_nonneg hβ0 hβ1)]

/-- Exact spatially localized gap-counting asymptotic for every real threshold. -/
theorem passage_tail_gapCount_asymptotic (y : ℝ) :
    Tendsto (fun x : ℝ => x^(2/3 : ℝ)*(gapCount ((passageTailWeight β) y) x : ℝ))
      (𝓝[>] 0) (𝓝 (∫ t in (0 : ℝ)..1, (passageTailDensity β) y t)) := by
  obtain ⟨a,b,ha,hb,hh⟩ := (passageWeight_three_halves hβ0 hβ1 hβ)
  let u (n : ℕ) := ((n : ℝ)+1)*((passageTailWeight β) y n)^(2/3 : ℝ)
  have hun (n : ℕ) : 0 ≤ u n := mul_nonneg (by positivity)
    (Real.rpow_nonneg ((passageTailWeight_nonneg hβ0 hβ1) y n) _)
  have hu (n : ℕ) : u n ≤ b^(2/3 : ℝ) := by
    dsimp [u]
    have h : (passageTailWeight β) y n ≤ (passageJumpWeight β) (n+1) := by
      unfold passageTailWeight
      split_ifs <;> simp [(passageJumpWeight_nonneg hβ0 hβ1)]
    have hh' := (le_div_iff₀ (Real.rpow_pos_of_pos (by positivity : 0 < (n : ℝ)+1) _)).1 (hh n).2
    have he : ((n : ℝ)+1)*((passageTailWeight β) y n)^(2/3 : ℝ) =
        (((n : ℝ)+1)^(3/2 : ℝ)*(passageTailWeight β) y n)^(2/3 : ℝ) := by
      rw [Real.mul_rpow (by positivity) ((passageTailWeight_nonneg hβ0 hβ1) y n),
        ← Real.rpow_mul (by positivity)]
      norm_num
    rw [he]
    apply Real.rpow_le_rpow (mul_nonneg (by positivity) ((passageTailWeight_nonneg hβ0 hβ1) y n)) _ (by norm_num)
    exact (mul_le_mul_of_nonneg_left h (by positivity)).trans (by simpa [mul_comm] using hh')
  have he : Tendsto (fun n => u n-(passageTailDensity β) y ((passagePhase β) (n+1)))
      atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.2
    intro ε hε
    filter_upwards [Metric.tendsto_nhds.1 (passageWeight_two_thirds_limit hβ0 hβ1 hβ) ε hε]
      with n hn
    dsimp only [u, passageTailWeight, passageTailDensity]
    split_ifs
    · exact hn
    · simpa using hε
  have h := diagonalCount_nonneg_tendsto_of_sub_tendsto_zero
    (fun n => (passagePhase_mem_Ico hβ0) (n+1))
    (fun _ _ ha hab hb => (passagePhase_shift_frequency hβ0 hβ) ha hab hb)
    ((passageTailDensity_monotone hβ0 hβ1 hβ) y) ((passageTailDensity_nonneg hβ0 hβ1 hβ) y 0) hun hu he
  have ht := h.comp (tendsto_rpow_neg_nhdsGT_zero (by norm_num : (-2/3 : ℝ) < 0))
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  dsimp only [Function.comp_def, u]
  rw [gapCount_eq_diagonalCount ((passageTailWeight_nonneg hβ0 hβ1) y) hx,
    show (-2/3 : ℝ) = -(2/3) by ring, Real.rpow_neg hx.le, div_inv_eq_mul, mul_comm]

end Problems.Juggler.BeattySlope

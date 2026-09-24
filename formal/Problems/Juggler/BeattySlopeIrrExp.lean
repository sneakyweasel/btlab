import Problems.Juggler.BeattySlopeArithmetic
import Problems.Juggler.BeattySlopeDiophantineDim

/-!
# Hausdorff dimension two-thirds and the irrationality exponent

For every irrational slope `α > 1`, the complete cluster set of the actual
first-passage ratios has Hausdorff dimension exactly two-thirds if and only if
`α` is not Liouville with any exponent above two, that is, if and only if the
irrationality exponent of `α` equals two. Bounds at every exponent above one
give dimension two-thirds; a Liouville approximation of exponent `p > 2`
gives approximations of order `q^(-p/2)` and hence dimension at most
`2/(2+√(p/2)) < 2/3`.
-/

namespace Problems.Juggler.BeattySlope

open Filter Topology Set MeasureTheory BeattyPhase
open scoped ENNReal

/-- A Liouville approximation of exponent `p > 2` supplies approximations
`|q α - m| ≤ q^(-p/2)` at arbitrarily large denominators. -/
theorem approx_of_liouvilleWith {α p : ℝ} (hp : 2 < p) (hL : LiouvilleWith p α) :
    ∀ Q : ℕ, ∃ q : ℕ, Q < q ∧ ∃ m : ℤ, |(q : ℝ)*α-(m : ℝ)| ≤ (q : ℝ)^(-(p/2)) := by
  obtain ⟨C, hC⟩ := hL
  have hexp : 0 < p-1-p/2 := by linarith
  have hev : ∀ᶠ n : ℕ in atTop, C ≤ (n : ℝ)^(p-1-p/2) :=
    ((tendsto_rpow_atTop hexp).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop C
  have hfr := hC.and_eventually (hev.and (eventually_gt_atTop 0))
  intro Q
  obtain ⟨n, hnQ, ⟨m, -, hm⟩, hCn, hn0⟩ := frequently_atTop.1 hfr (Q+1)
  refine ⟨n, by omega, m, ?_⟩
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
  have heq : (n : ℝ)*α-(m : ℝ) = n*(α-(m : ℝ)/n) := by field_simp
  rw [heq, abs_mul, abs_of_pos hnr]
  have h1 : (n : ℝ)*|α-(m : ℝ)/n| ≤ n*(C/(n : ℝ)^p) :=
    mul_le_mul_of_nonneg_left hm.le hnr.le
  refine h1.trans ?_
  have hsplit : (n : ℝ)^(-(p/2)) = (n : ℝ)^(p-1-p/2)*((n : ℝ)*(n : ℝ)^(-p)) := by
    rw [← Real.rpow_one_add' hnr.le (by linarith), ← Real.rpow_add hnr]
    · ring_nf
  rw [hsplit, Real.rpow_neg hnr.le, div_eq_mul_inv]
  have hpos : 0 ≤ (n : ℝ)*((n : ℝ)^p)⁻¹ := by positivity
  calc (n : ℝ)*(C*((n : ℝ)^p)⁻¹) = C*((n : ℝ)*((n : ℝ)^p)⁻¹) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hCn hpos

/-- For every irrational slope above one, the actual cluster set has Hausdorff
dimension exactly two-thirds if and only if the slope is not Liouville with
any exponent above two (irrationality exponent two). -/
theorem cluster_dimH_eq_iff {α : ℝ} (hα1 : 1 < α) (hα : Irrational α) :
    dimH (passageClusterSet (1/α)) = (2/3 : ℝ≥0∞) ↔ ∀ p > (2 : ℝ), ¬ LiouvilleWith p α := by
  have hα0 : 0 < α := by linarith
  constructor
  · intro hdim p hp hL
    have hν : 1 < p/2 := by linarith
    have hle := dio_exponent_dimH_le hα1 hα hν (approx_of_liouvilleWith hp hL)
    rw [hdim] at hle
    have hs : 1 < Real.sqrt (p/2) := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_lt_sqrt (by norm_num) hν
    have hlt : 2/(2+Real.sqrt (p/2)) < 2/3 :=
      div_lt_div_of_pos_left (by norm_num) (by norm_num) (by linarith)
    have h23 : ((2/3 : ℝ≥0∞)) = ENNReal.ofReal (2/3) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
    rw [h23] at hle
    exact absurd ((ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hle) (not_le.2 hlt)
  · intro hL
    apply passageCluster_dimH_eq (one_div_pos.mpr hα0) ((div_lt_one hα0).mpr hα1)
      (by simpa using hα.inv)
    intro τ hτ
    obtain ⟨c, hc, h⟩ := dio_of_not_liouvilleWith hα (hL (τ+1) (by linarith))
    exact ⟨c, hc, by simpa [one_div_one_div] using h⟩

/-- At the laboratory's slope `log₂ 3 = 1/β` (with `β = log 2 / log 3`), the
actual cluster set has Hausdorff dimension two-thirds if and only if `log₂ 3`
has irrationality exponent two, an open problem in number theory. -/
theorem log_cluster_dimH_iff :
    dimH (passageClusterSet PaperBThreshold.beta) = (2/3 : ℝ≥0∞) ↔
      ∀ p > (2 : ℝ), ¬ LiouvilleWith p (1/PaperBThreshold.beta) := by
  have hb0 : 0 < PaperBThreshold.beta := by linarith [PaperBThreshold.beta_gt_five_eighths]
  have hα1 : 1 < 1/PaperBThreshold.beta := by
    rw [lt_div_iff₀ hb0, one_mul]; exact PaperBThreshold.beta_lt_one
  have h := cluster_dimH_eq_iff hα1 (by simpa using logarithmic_irrational.inv)
  simpa only [one_div_one_div] using h

end Problems.Juggler.BeattySlope

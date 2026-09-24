import Problems.Juggler.BeattyCertificateIdentification
import Problems.Juggler.BeattySlopeProfileSpecialization

/-!
# The normalized certificate phase asymptotic

The original count theorem is the exact logarithmic specialization of the
irrational-slope family theorem. The finite crossing identities remain public
for downstream binomial and geometric arguments.
-/

namespace Problems.Juggler.BeattyPhase

open Filter Topology PaperBThreshold

private theorem beta_pos : 0 < beta := by linarith [beta_gt_five_eighths]

/-- Every crossing length is at least its prescribed odd count. -/
theorem le_certificateIndex (r : ℕ) : r ≤ certificateIndex r := by
  apply Nat.le_floor
  exact (le_div_iff₀ beta_pos).2 (mul_le_of_le_one_right (Nat.cast_nonneg r) beta_lt_one.le)

/-- At a positive certificate crossing the strict binomial cutoff is its odd count. -/
theorem endpointCutoff_certificateIndex {r : ℕ} (hr : 0 < r) : endpointCutoff (certificateIndex r) = r := by
  have hp := certificatePhase_pos hr
  have hw := (certWindow_iff_endpoint _ _).1 (certificateIndex_window r)
  have hl : (certificateIndex r : ℝ)*beta < r := by
    unfold certificatePhase at hp
    exact (lt_div_iff₀ beta_pos).1 (by linarith : (certificateIndex r : ℝ) < (r : ℝ)/beta)
  have hu : (r : ℝ) < (certificateIndex r : ℝ)*beta+1 := by
    push_cast at hw
    nlinarith [beta_lt_one]
  have he : ⌊(certificateIndex r : ℝ)*beta⌋₊ = r-1 := by
    apply (Nat.floor_eq_iff (mul_nonneg (Nat.cast_nonneg _) beta_pos.le)).2
    rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]
    constructor <;> linarith
  unfold endpointCutoff
  rw [he]
  omega

/-- The two survivor phases adjoining a positive certificate crossing. -/
theorem certificateIndex_crossing_phases {r : ℕ} (hr : 0 < r) :
    Int.fract ((certificateIndex r : ℝ)*beta) = 1-beta*certificatePhase r ∧
    Int.fract ((certificateIndex r : ℝ)*beta+beta) = beta*(1-certificatePhase r) := by
  have ha : 1 < 1/beta := (one_lt_div beta_pos).2 beta_lt_one
  have h := fract_crossing_pair (alpha := 1/beta) (m := certificateIndex r) (r := r) ha
    (certificatePhase_pos hr) (certificatePhase_mem_Ico r).2
    (show certificatePhase r = (1/beta)*(r : ℝ)-certificateIndex r by
      unfold certificatePhase; ring)
  have hne := ne_of_gt beta_pos
  convert h using 1 <;> field_simp

/-- The all-depth binomial normalization equals the original odd-count normalization. -/
theorem certificate_normalization_identity {r : ℕ} (hr : 0 < r) :
    (certificateIndex r : ℝ)*(minimalCertCount (certificateIndex r+1) : ℝ)/
      ((certificateIndex r).choose (endpointCutoff (certificateIndex r)) : ℝ) =
    (r : ℝ)*(minimalCertCount (certificateIndex r+1) : ℝ)/
      ((certificateIndex r-1).choose (r-1) : ℝ) := by
  have hmr := le_certificateIndex r
  have hm : 0 < certificateIndex r := lt_of_lt_of_le hr hmr
  have he := Nat.add_one_mul_choose_eq (certificateIndex r-1) (r-1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ certificateIndex r), Nat.sub_add_cancel (by omega : 1 ≤ r)] at he
  have heR : (certificateIndex r : ℝ)*((certificateIndex r-1).choose (r-1) : ℝ) =
      ((certificateIndex r).choose r : ℝ)*(r : ℝ) := by exact_mod_cast he
  have hc : ((certificateIndex r).choose r : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hmr).ne'
  have hc' : ((certificateIndex r-1).choose (r-1) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.sub_le_sub_right hmr 1)).ne'
  rw [endpointCutoff_certificateIndex hr]
  field_simp
  linear_combination (minimalCertCount (certificateIndex r+1) : ℝ)*heR

/-- The original normalized certificate counts converge to the explicit
left-continuous jump profile along their exact Beatty phases. This is the
logarithmic specialization of the family theorem; the error is additive
`o(1)`, without a quantitative rate. -/
theorem certificate_phase_asymptotic :
    Tendsto (fun r : ℕ =>
      (r : ℝ)*(minimalCertCount (certificateIndex r+1) : ℝ)/
        ((certificateIndex r-1).choose (r-1) : ℝ) - certificateProfile (certificatePhase r))
      atTop (𝓝 0) := by
  simpa only [BeattySlope.passageIndex_logarithmic, BeattySlope.passageCount_logarithmic,
    BeattySlope.passageProfile_logarithmic, BeattySlope.passagePhase_logarithmic] using
    BeattySlope.passage_phase_asymptotic_odd_count beta_pos beta_lt_one
      BeattySlope.logarithmic_irrational

end Problems.Juggler.BeattyPhase

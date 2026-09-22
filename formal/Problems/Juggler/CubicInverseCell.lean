import Problems.Juggler.OddCubicPhase

/-!
# Exact algebra for the cubic inverse-cell estimate

The analytic transform and derivative tests are written proofs. This module
checks the rational phase decomposition, the normalized derivative quotients,
their sign factors, and the numerical exponent budget used in that proof.
-/

namespace Problems.Juggler.CubicInverseCell

open OddCubicPhase

noncomputable def dualIndex (h j t : ℝ) : ℝ :=
  3 * h * t ^ 3 / 2 + 2 * j / (3 * t ^ 2)

noncomputable def remainder (h j t : ℝ) : ℝ :=
  j * t ^ 4 / 2 + 4 * j ^ 2 / (27 * h * t) +
    16 * j ^ 3 / (729 * h ^ 2 * t ^ 6)

theorem phase_decomposition {h t : ℝ} (hh : h ≠ 0) (ht : t ≠ 0) (j : ℝ) :
    dualIndex h j t / 2 - h * t ^ 9 / 4 + j * t ^ 4 / 6 =
      dualPhase h (dualIndex h j t) + remainder h j t := by
  unfold dualIndex dualPhase remainder
  field_simp
  ring

theorem halfCubic_periodic {q : ℕ} (hq : q ≠ 0) (r : ℕ) :
    wave (halfCubic q (r + 2 * q)) = wave (halfCubic q r) := by
  have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have he : halfCubic (q : ℝ) (r + 2 * q) =
      halfCubic q r + ((q : ℤ) - 12 * (r : ℤ) ^ 2 -
        24 * r * q - 16 * q ^ 2 : ℤ) := by
    unfold halfCubic
    push_cast
    field_simp
    ring
  rw [he, wave_add_int]

theorem dual_periodic {h : ℕ} (hh : h ≠ 0) (r : ℕ) :
    wave (dualPhase h (r + 54 * h ^ 2)) = wave (dualPhase h r) := by
  have hq : 27 * h ^ 2 ≠ 0 := by positivity
  have hp := halfCubic_periodic hq r
  norm_num [dualPhase, halfCubic, ← mul_assoc] at hp ⊢
  exact hp

noncomputable def second (h t u : ℝ) : ℝ :=
  3 * h / (2 * t ^ 3) * (1 - u)

noncomputable def third (h t u : ℝ) : ℝ :=
  -(3 * h / (2 * t ^ 9)) * (1 - 8 * u / 3)

noncomputable def fourth (h t u : ℝ) : ℝ :=
  9 * h / (2 * t ^ 15) * (1 - 112 * u / 27)

noncomputable def thirdRemainder (h u : ℝ) : ℝ :=
  -4 * u * (1 - 9 * u + 3 * u ^ 2) / (27 * h ^ 2 * (1 - u) ^ 3)

noncomputable def fourthRemainder (h t u : ℝ) : ℝ :=
  40 * u * (1 - 16 * u) / (243 * h ^ 3 * t ^ 3 * (1 - u) ^ 5)

theorem normalized_source_forms {h t : ℝ} (hh : h ≠ 0) (ht : t ≠ 0) (j : ℝ) :
    let u := 8 * j / (27 * h * t ^ 5)
    second h t u = 3 * h / (2 * t ^ 3) - 4 * j / (9 * t ^ 8) ∧
    third h t u = -(3 * h / (2 * t ^ 9)) + 32 * j / (27 * t ^ 14) ∧
    fourth h t u = 9 * h / (2 * t ^ 15) - 448 * j / (81 * t ^ 20) := by
  dsimp [second, third, fourth]
  constructor
  · field_simp
    ring
  constructor <;> field_simp <;> ring

theorem third_quotient {h t u : ℝ}
    (hh : h ≠ 0) (ht : t ≠ 0) (hu : 1 - u ≠ 0) :
    third h t u / second h t u ^ 3 + 4 / (9 * h ^ 2) =
      thirdRemainder h u := by
  unfold second third thirdRemainder
  field_simp
  ring

theorem fourth_quotient {h t u : ℝ}
    (hh : h ≠ 0) (ht : t ≠ 0) (hu : 1 - u ≠ 0) :
    (fourth h t u * second h t u - 3 * third h t u ^ 2) /
        second h t u ^ 5 = fourthRemainder h t u := by
  unfold second third fourth fourthRemainder
  field_simp
  ring

theorem small_parameter_factors {u : ℝ} (hu : |u| ≤ 1 / 100) :
    0 < 1 - u ∧ 0 < 1 - 9 * u + 3 * u ^ 2 ∧ 0 < 1 - 16 * u := by
  have hb := (abs_le.mp hu)
  constructor
  · linarith
  constructor
  · nlinarith [sq_nonneg u]
  · linarith

theorem third_opposite_sign {h u : ℝ}
    (hh : 0 < h) (hu : |u| ≤ 1 / 100) (hu0 : u ≠ 0) :
    u * thirdRemainder h u < 0 := by
  obtain ⟨hp, hn, _⟩ := small_parameter_factors hu
  have he : u * thirdRemainder h u =
      -(4 * u ^ 2 * (1 - 9 * u + 3 * u ^ 2) /
        (27 * h ^ 2 * (1 - u) ^ 3)) := by
    unfold thirdRemainder
    ring
  rw [he]
  exact neg_neg_of_pos (by positivity)

theorem fourth_same_sign {h t u : ℝ}
    (hh : 0 < h) (ht : 0 < t) (hu : |u| ≤ 1 / 100) (hu0 : u ≠ 0) :
    0 < u * fourthRemainder h t u := by
  obtain ⟨hp, _, hn⟩ := small_parameter_factors hu
  have he : u * fourthRemainder h t u =
      40 * u ^ 2 * (1 - 16 * u) /
        (243 * h ^ 3 * t ^ 3 * (1 - u) ^ 5) := by
    unfold fourthRemainder
    ring
  rw [he]
  positivity

def theta : ℚ := 1 / 6 + 1 / 1354
def splitLoss : ℚ := 1 / 2708
def frequencyGain : ℚ := 1 / 50000
def mixedGain : ℚ := 1 / 25000

theorem exponent_budget :
    (11 / 18 : ℚ) + (1 / 3 - splitLoss) / 6 + frequencyGain < 2 / 3 - mixedGain ∧
    (23 / 36 : ℚ) + frequencyGain / 2 < 2 / 3 - mixedGain ∧
    (3 / 4 : ℚ) - 5 * theta / 6 + (1 / 3 + frequencyGain) * theta +
        (1 / 2 + 3 * theta) * frequencyGain < 2 / 3 - mixedGain ∧
    (1 / 4 : ℚ) + 5 * (1 - theta) / 6 +
        (1 / 3 - splitLoss) * (theta - 1) < 2 / 3 - mixedGain := by
  norm_num [theta, splitLoss, frequencyGain, mixedGain]

theorem endpoint_budget :
    mixedGain - frequencyGain = frequencyGain ∧
    (1 / 2 : ℚ) + frequencyGain / 2 < 2 / 3 - frequencyGain ∧
    (5 / 12 : ℚ) + frequencyGain / 2 < 2 / 3 - frequencyGain ∧
    (1 / 100000 : ℚ) < frequencyGain ∧ -1 + 3 / 1354 < (0 : ℚ) ∧
    -(1 / 2 : ℚ) + 4 * frequencyGain < 0 ∧ theta < 1 := by
  norm_num [frequencyGain, mixedGain, theta]

end Problems.Juggler.CubicInverseCell

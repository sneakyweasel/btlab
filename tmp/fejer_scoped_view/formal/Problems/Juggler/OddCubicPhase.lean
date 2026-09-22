import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Exact cubic phase behind odd-source discrepancy

These identities verify the stationary-point algebra and the zero complete
mean of odd harmonics. The analytic transform, incomplete cubic estimates,
and the discrepancy bound are written proofs in the companion dossier.
-/

namespace Problems.Juggler.OddCubicPhase

open Finset

noncomputable def wave (x : ℝ) : ℂ :=
  Complex.exp ((x : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))

theorem wave_add (x y : ℝ) : wave (x + y) = wave x * wave y := by
  simp [wave, add_mul, Complex.exp_add]

theorem wave_int (k : ℤ) : wave k = 1 := by
  simp [wave, Complex.exp_int_mul_two_pi_mul_I]

theorem wave_half : wave (1 / 2) = -1 := by
  unfold wave
  have he : (((1 / 2 : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) =
      (Real.pi : ℂ) * Complex.I := by
    push_cast
    ring
  rw [he, Complex.exp_pi_mul_I]

theorem wave_add_int (x : ℝ) (k : ℤ) : wave (x + k) = wave x := by
  rw [wave_add, wave_int, mul_one]

theorem wave_half_int (x : ℝ) (k : ℤ) :
    wave (x + (1 / 2 + k)) = -wave x := by
  rw [wave_add, wave_add, wave_half, wave_int]
  ring

noncomputable def dualPhase (h r : ℝ) : ℝ :=
  r / 2 - 2 * r ^ 3 / (27 * h ^ 2)

noncomputable def stationaryPoint (h r : ℝ) : ℝ :=
  ((2 * r / (3 * h)) ^ 2 - 1) / 2

theorem stationary_sqrt {h r : ℝ} (hh : 0 < h) (hr : 0 < r) :
    Real.sqrt (2 * stationaryPoint h r + 1) = 2 * r / (3 * h) := by
  have he : 2 * stationaryPoint h r + 1 = (2 * r / (3 * h)) ^ 2 := by
    unfold stationaryPoint
    ring
  rw [he, Real.sqrt_sq (by positivity)]

theorem stationary_derivative {h r : ℝ} (hh : 0 < h) (hr : 0 < r) :
    (3 * h / 2) * Real.sqrt (2 * stationaryPoint h r + 1) = r := by
  rw [stationary_sqrt hh hr]
  field_simp

theorem stationary_phase {h r : ℝ} (hh : 0 < h) (hr : 0 < r) :
    h / 2 * (2 * stationaryPoint h r + 1) *
        Real.sqrt (2 * stationaryPoint h r + 1) -
        r * stationaryPoint h r = dualPhase h r := by
  rw [stationary_sqrt hh hr]
  unfold stationaryPoint dualPhase
  field_simp
  ring

theorem stationary_curvature {h r : ℝ} (hh : 0 < h) (hr : 0 < r) :
    (3 * h / 2) / Real.sqrt (2 * stationaryPoint h r + 1) =
      9 * h ^ 2 / (4 * r) := by
  rw [stationary_sqrt hh hr]
  field_simp
  ring

noncomputable def halfCubic (q r : ℝ) : ℝ := r / 2 - 2 * r ^ 3 / q

theorem halfCubic_shift {q : ℝ} (hq : q ≠ 0) (r : ℝ) :
    halfCubic q (r + q) =
      halfCubic q r + (q / 2 - 6 * r ^ 2 - 6 * r * q - 2 * q ^ 2) := by
  unfold halfCubic
  field_simp
  ring

theorem halfCubic_antiperiodic {q : ℕ} (hq : Odd q) (r : ℕ) :
    wave (halfCubic q (r + q)) = -wave (halfCubic q r) := by
  obtain ⟨k, hk⟩ := hq
  have hq0 : (q : ℝ) ≠ 0 := by
    have : q ≠ 0 := by omega
    exact_mod_cast this
  rw [halfCubic_shift hq0]
  have hc : (q : ℝ) / 2 - 6 * (r : ℝ) ^ 2 - 6 * r * q - 2 * q ^ 2 =
      1 / 2 + ((k : ℤ) - 6 * (r : ℤ) ^ 2 - 6 * r * q - 2 * q ^ 2 : ℤ) := by
    push_cast
    rw [hk]
    push_cast
    ring
  rw [hc, wave_half_int]

theorem antiperiodic_sum_zero (f : ℕ → ℂ) (q : ℕ)
    (hf : ∀ r, f (r + q) = -f r) :
    ∑ r ∈ range (2 * q), f r = 0 := by
  rw [two_mul, sum_range_add]
  simp_rw [Nat.add_comm q, hf, sum_neg_distrib]
  exact add_neg_cancel _

theorem odd_complete_mean_zero {q : ℕ} (hq : Odd q) :
    ∑ r ∈ range (2 * q), wave (halfCubic q r) = 0 := by
  apply antiperiodic_sum_zero
  intro r
  simpa only [Nat.cast_add] using halfCubic_antiperiodic hq r

theorem dual_odd_antiperiodic {h : ℕ} (hh : Odd h) (r : ℕ) :
    wave (dualPhase h (r + 27 * h ^ 2)) = -wave (dualPhase h r) := by
  have hq : Odd (27 * h ^ 2) := (by decide : Odd (27 : ℕ)).mul (hh.pow)
  simpa [dualPhase, halfCubic] using halfCubic_antiperiodic hq r

theorem dual_odd_complete_mean_zero {h : ℕ} (hh : Odd h) :
    ∑ r ∈ range (54 * h ^ 2), wave (dualPhase h r) = 0 := by
  have hq : Odd (27 * h ^ 2) := (by decide : Odd (27 : ℕ)).mul (hh.pow)
  simpa [dualPhase, halfCubic, ← mul_assoc] using odd_complete_mean_zero hq

end Problems.Juggler.OddCubicPhase

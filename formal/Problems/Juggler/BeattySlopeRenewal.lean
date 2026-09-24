import Problems.Juggler.BeattySlopeCounting
import Problems.Juggler.BeattyRenewalSeries

/-!
# Weighted boundary counts and the renewal limit

The finite word identity is normalized by an arbitrary exponential base and
identified with the existing formal renewal exponential. Consequently its
analytic transfer theorems apply to the actual weighted counts. A terminal
binomial estimate is still an explicit hypothesis of every analytic conclusion
here. The final elementary tilt gives terminal ratio one half for every
boundary in `(0, 1)`, including boundaries below the fair-walk drift.
-/

namespace Problems.Juggler.BeattySlope

open Finset Filter Topology

/-- Actual weighted survivors divided by the exponential normalization `v^n`. -/
noncomputable def normalizedSurvivor (β z v : ℝ) (n : ℕ) : ℝ :=
  survivorWeight β z n / v^n

/-- Actual terminal binomial weights with the same exponential normalization. -/
noncomputable def normalizedEndpoint (β z v : ℝ) (n : ℕ) : ℝ :=
  endpointWeight β z n / v^n

/-- The empty normalized survivor has weight one, even when the base is zero. -/
theorem normalizedSurvivor_zero (β z v : ℝ) : normalizedSurvivor β z v 0 = 1 := by
  simp [normalizedSurvivor, survivorWeight_zero]

/-- Nonnegative letter weights and normalization give nonnegative endpoints. -/
theorem normalizedEndpoint_nonneg (β : ℝ) {z v : ℝ} (hz : 0 ≤ z) (hv : 0 ≤ v)
    (n : ℕ) : 0 ≤ normalizedEndpoint β z v n :=
  div_nonneg (endpointWeight_nonneg β hz n) (pow_nonneg hv n)

/-- Exponential normalization preserves the exact weighted renewal recurrence.
This is an algebraic identity for every real letter weight and base. -/
theorem normalizedSurvivor_recurrence (β : ℝ) (hβ : Irrational β) (z v : ℝ)
    (n : ℕ) :
    (n : ℝ)*normalizedSurvivor β z v n =
      ∑ j ∈ range n, normalizedEndpoint β z v (n-j)*normalizedSurvivor β z v j := by
  unfold normalizedSurvivor normalizedEndpoint
  calc
    _ = ((n : ℝ)*survivorWeight β z n)/v^n := by ring
    _ = (∑ j ∈ range n, endpointWeight β z (n-j)*survivorWeight β z j)/v^n := by
      rw [survivorWeight_recurrence β hβ]
    _ = ∑ j ∈ range n, (endpointWeight β z (n-j)*survivorWeight β z j)/v^n := by
      rw [sum_div]
    _ = _ := by
      apply sum_congr rfl
      intro j hj
      rw [div_mul_div_comm, ← pow_add, Nat.sub_add_cancel (mem_range.mp hj).le]

/-- The actual normalized survivor sequence is the formal renewal exponential
of its terminal binomial sequence. No analytic premise is needed. -/
theorem normalizedSurvivor_eq_renewalCoeff (β : ℝ) (hβ : Irrational β) (z v : ℝ) :
    normalizedSurvivor β z v = BeattyPhase.renewalCoeff (normalizedEndpoint β z v) :=
  BeattyPhase.eq_renewalCoeff_of_recurrence (normalizedSurvivor_zero β z v)
    (normalizedSurvivor_recurrence β hβ z v)

/-- A terminal square-root bound transfers to a three-halves bound on the
actual weighted survivors. The terminal estimate remains an explicit premise. -/
theorem normalizedSurvivor_three_halves_bound (β : ℝ) (hβ : Irrational β)
    {z v K : ℝ} (hz : 0 ≤ z) (hv : 0 ≤ v) (hK : 0 ≤ K)
    (hA : ∀ n : ℕ, 0 < n → normalizedEndpoint β z v n ≤ K/Real.sqrt n) :
    ∃ U : ℝ, 0 ≤ U ∧ ∀ n : ℕ, 0 < n →
      normalizedSurvivor β z v n ≤ U/((n : ℝ)*Real.sqrt n) := by
  rw [normalizedSurvivor_eq_renewalCoeff β hβ]
  exact BeattyPhase.exists_renewalCoeff_three_halves_bound
    (normalizedEndpoint_nonneg β hz hv) hK hA

/-- A bounded terminal phase asymptotic implies the renewal-series phase
asymptotic for the actual weighted survivor counts. All slope, weight and
normalization parameters are explicit; the terminal asymptotic is assumed. -/
theorem normalizedSurvivor_phase_limit (β : ℝ) (hβ : Irrational β)
    {z v P : ℝ} {Phi : ℝ → ℝ} (hz : 0 ≤ z) (hv : 0 ≤ v)
    (hPhi : ∀ x, |Phi x| ≤ P)
    (hA : Tendsto (fun n : ℕ =>
      Real.sqrt (n : ℝ)*normalizedEndpoint β z v n - Phi (n*β)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (n : ℝ)*Real.sqrt n*normalizedSurvivor β z v n -
      ∑' j, normalizedSurvivor β z v j*Phi (((n : ℝ)-j)*β)) atTop (𝓝 0) := by
  rw [normalizedSurvivor_eq_renewalCoeff β hβ]
  exact BeattyPhase.renewalCoeff_phase_limit (normalizedEndpoint_nonneg β hz hv) hPhi hA

/-- Odd-letter tilt that fixes the boundary terminal ratio to one half. -/
noncomputable def tiltedOddWeight (β : ℝ) : ℝ := β/(2*(1-β))

/-- Bernoulli success probability obtained from the chosen odd-letter tilt. -/
noncomputable def tiltedBernoulliBias (β : ℝ) : ℝ := β/(2-β)

/-- Every boundary strictly between zero and one admits a positive letter
tilt; this includes the entire reciprocal-slope family `α > 1`. -/
theorem tiltedOddWeight_pos {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    0 < tiltedOddWeight β := by
  unfold tiltedOddWeight
  positivity

/-- Normalizing the two letter weights gives precisely the chosen bias. -/
theorem tiltedBernoulliBias_eq {β : ℝ} (hβ1 : β < 1) :
    tiltedBernoulliBias β = tiltedOddWeight β/(1+tiltedOddWeight β) := by
  unfold tiltedBernoulliBias tiltedOddWeight
  have hq : 1-β ≠ 0 := ne_of_gt (by linarith)
  have hd : 2-β ≠ 0 := ne_of_gt (by linarith)
  have he : 1+β/(2*(1-β)) = (2-β)/(2*(1-β)) := by
    field_simp
    ring
  rw [he]
  field_simp

/-- The tilted random walk has drift strictly below the boundary for every
`0 < β < 1`, which puts the survivor problem in the large-deviation regime. -/
theorem tiltedBernoulliBias_bounds {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    0 < tiltedBernoulliBias β ∧ tiltedBernoulliBias β < β := by
  have hd : 0 < 2-β := by linarith
  constructor
  · exact div_pos hβ0 hd
  · exact (div_lt_iff₀ hd).2 (by nlinarith)

/-- The terminal binomial ratio supplied by the tilt is exactly one half,
uniformly in the boundary parameter. This does not assert a Stirling estimate. -/
theorem tiltedOddWeight_terminal_ratio {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    tiltedOddWeight β*(1-β)/β = 1/2 := by
  unfold tiltedOddWeight
  have hq : 1-β ≠ 0 := ne_of_gt (by linarith)
  field_simp

end Problems.Juggler.BeattySlope

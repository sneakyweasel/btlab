import BTCalculus.WeylDifferencing
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Qualitative van der Corput cancellation

The finite overlap inequality implies cancellation of averages when each
positive fixed-shift correlation average tends to zero. All limits here are
for one fixed sequence; there is no uniformity in a varying phase family.
-/

noncomputable section

namespace BTCalculus.WeylDifferencing

open Finset Filter
open scoped Topology ComplexConjugate

/-- The finite inequality divided by the square of the summation length. -/
theorem normalized_van_der_corput {z : ℕ → ℂ} {N H : ℕ}
    (hH : 1 ≤ H) (hHN : H ≤ N) (hz : ∀ n, n < N → ‖z n‖ ≤ 1) :
    (‖∑ n ∈ range N, z n‖ / (N : ℝ)) ^ 2 ≤
      2 / (H : ℝ) + (4 / (H : ℝ)) *
        ∑ d ∈ Ico 1 H, ‖correlation z N d‖ / (N : ℝ) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < H) hHN)
  have hHp : (0 : ℝ) < H := by exact_mod_cast hH
  have hv := div_le_div_of_nonneg_right (van_der_corput hH hHN hz)
    (sq_nonneg (N : ℝ))
  rw [div_pow]
  apply hv.trans_eq
  simp_rw [div_eq_mul_inv]
  rw [← sum_mul]
  field_simp [ne_of_gt hNp, ne_of_gt hHp]

/-- Qualitative differencing with the exact overlap correlations. -/
theorem tendsto_average_norm_zero_of_correlations {z : ℕ → ℂ}
    (hz : ∀ n, ‖z n‖ ≤ 1)
    (hcorr : ∀ d : ℕ, 0 < d →
      Tendsto (fun N => ‖correlation z N d‖ / (N : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun N => ‖∑ n ∈ range N, z n‖ / (N : ℝ)) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun N => ha.trans_le (by positivity))
  · intro ε hε
    have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
    have hsmall := (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).eventually
      (gt_mem_nhds hεsq)
    obtain ⟨H, hH, hbound⟩ := ((eventually_ge_atTop 1).and hsmall).exists
    have hsum : Tendsto (fun N => ∑ d ∈ Ico 1 H,
        ‖correlation z N d‖ / (N : ℝ)) atTop (𝓝 0) := by
      simpa using tendsto_finsetSum (Ico 1 H)
        (fun d hd => hcorr d (by have := (mem_Ico.mp hd).1; omega))
    have hlim : Tendsto (fun N => 2 / (H : ℝ) + (4 / (H : ℝ)) *
        ∑ d ∈ Ico 1 H, ‖correlation z N d‖ / (N : ℝ))
        atTop (𝓝 (2 / (H : ℝ))) := by
      simpa using (hsum.const_mul (4 / (H : ℝ))).const_add (2 / (H : ℝ))
    filter_upwards [eventually_ge_atTop H, hlim.eventually (gt_mem_nhds hbound)]
      with N hHN hlt
    have hv := normalized_van_der_corput hH hHN (fun n _ => hz n)
    have hnonneg : 0 ≤ ‖∑ n ∈ range N, z n‖ / (N : ℝ) := by positivity
    nlinarith

/-- Normalized complex partial sums; the length-zero value is zero. -/
def average (z : ℕ → ℂ) (N : ℕ) : ℂ := (∑ n ∈ range N, z n) / (N : ℂ)

theorem norm_average (z : ℕ → ℂ) (N : ℕ) :
    ‖average z N‖ = ‖∑ n ∈ range N, z n‖ / (N : ℝ) := by
  simp [average]

theorem average_div_const (z : ℕ → ℂ) (c : ℂ) (N : ℕ) :
    average (fun n => z n / c) N = average z N / c := by
  simp only [average, div_eq_mul_inv, ← sum_mul]
  ring

/-- The full shifted sum and its overlap differ by at most the shift. -/
theorem correlation_boundary_bound {z : ℕ → ℂ} (hz : ∀ n, ‖z n‖ ≤ 1) (N d : ℕ) :
    ‖(∑ n ∈ range N, z (n + d) * conj (z n)) - correlation z N d‖ ≤ d := by
  have he : (∑ n ∈ range N, z (n + d) * conj (z n)) - correlation z N d =
      ∑ n ∈ Ico (N - d) N, z (n + d) * conj (z n) := by
    unfold correlation
    rw [← sum_range_add_sum_Ico (fun n => z (n + d) * conj (z n)) (Nat.sub_le N d)]
    ring
  rw [he]
  calc ‖∑ n ∈ Ico (N - d) N, z (n + d) * conj (z n)‖
      ≤ ∑ n ∈ Ico (N - d) N, ‖z (n + d) * conj (z n)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Ico (N - d) N, (1 : ℝ) := by
      apply sum_le_sum
      intro n _
      rw [norm_mul, Complex.norm_conj]
      exact (mul_le_mul (hz (n + d)) (hz n) (norm_nonneg _) (by norm_num)).trans_eq
        (one_mul 1)
    _ = ((N - (N - d) : ℕ) : ℝ) := by simp
    _ ≤ (d : ℝ) := by exact_mod_cast (by omega : N - (N - d) ≤ d)

/-- Removing the last `d` terms does not change a fixed-shift correlation limit. -/
theorem tendsto_overlap_zero_of_shifted {z : ℕ → ℂ} (hz : ∀ n, ‖z n‖ ≤ 1)
    (d : ℕ) (hcorr : Tendsto (average (fun n => z (n + d) * conj (z n)))
      atTop (𝓝 0)) :
    Tendsto (fun N => ‖correlation z N d‖ / (N : ℝ)) atTop (𝓝 0) := by
  have hboundary : Tendsto (fun N =>
      ((∑ n ∈ range N, z (n + d) * conj (z n)) - correlation z N d) / (N : ℂ))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun N : ℕ => (d : ℝ) / (N : ℝ))
    · intro N
      rw [norm_div, Complex.norm_natCast]
      exact div_le_div_of_nonneg_right (correlation_boundary_bound hz N d) (by positivity)
    · exact tendsto_const_div_atTop_nhds_zero_nat (d : ℝ)
  have hlim : Tendsto (fun N => correlation z N d / (N : ℂ)) atTop (𝓝 0) := by
    convert hcorr.sub hboundary using 1
    · funext N
      dsimp [average]
      ring
    · simp
  simpa [norm_div, Complex.norm_natCast] using hlim.norm

/-- Qualitative van der Corput with the usual full shifted correlation averages. -/
theorem tendsto_average_zero_of_shifted_correlations {z : ℕ → ℂ}
    (hz : ∀ n, ‖z n‖ ≤ 1)
    (hcorr : ∀ d : ℕ, 0 < d →
      Tendsto (average (fun n => z (n + d) * conj (z n))) atTop (𝓝 0)) :
    Tendsto (average z) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.2
  simp_rw [norm_average]
  exact tendsto_average_norm_zero_of_correlations hz
    (fun d hd => tendsto_overlap_zero_of_shifted hz d (hcorr d hd))

/-- The usual bounded-sequence form, with any fixed positive norm bound. -/
theorem tendsto_average_zero_of_bounded_correlations {z : ℕ → ℂ} {C : ℝ}
    (hC : 0 < C) (hz : ∀ n, ‖z n‖ ≤ C)
    (hcorr : ∀ d : ℕ, 0 < d →
      Tendsto (average (fun n => z (n + d) * conj (z n))) atTop (𝓝 0)) :
    Tendsto (average z) atTop (𝓝 0) := by
  let w : ℕ → ℂ := fun n => z n / (C : ℂ)
  have hw : ∀ n, ‖w n‖ ≤ 1 := by
    intro n
    dsimp [w]
    simpa [norm_div, abs_of_pos hC] using (div_le_one hC).mpr (hz n)
  have he (d n : ℕ) : w (n + d) * conj (w n) =
      (z (n + d) * conj (z n)) / (C : ℂ) ^ 2 := by
    change (z (n + d) / (C : ℂ)) * conj (z n / (C : ℂ)) = _
    rw [map_div₀, Complex.conj_ofReal]
    ring
  have hcw : ∀ d : ℕ, 0 < d →
      Tendsto (average (fun n => w (n + d) * conj (w n))) atTop (𝓝 0) := by
    intro d hd
    change Tendsto (fun N => average (fun n => w (n + d) * conj (w n)) N) _ _
    simp_rw [he, average_div_const]
    simpa using (hcorr d hd).div_const ((C : ℂ) ^ 2)
  have hlim := (tendsto_average_zero_of_shifted_correlations hw hcw).mul_const (C : ℂ)
  have hCn : (C : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hC)
  simpa only [w, average_div_const, div_mul_cancel₀ _ hCn, zero_mul] using hlim

/-- Cancellation of every positive fixed difference phase suffices for the phase. -/
theorem tendsto_phase_average_zero_of_differences (f : ℕ → ℝ)
    (hdiff : ∀ d : ℕ, 0 < d →
      Tendsto (average (fun n => phase (f (n + d) - f n))) atTop (𝓝 0)) :
    Tendsto (average (fun n => phase (f n))) atTop (𝓝 0) := by
  apply tendsto_average_zero_of_shifted_correlations (fun n => (phase_norm (f n)).le)
  intro d hd
  simpa only [phase_mul_conj] using hdiff d hd

end BTCalculus.WeylDifferencing

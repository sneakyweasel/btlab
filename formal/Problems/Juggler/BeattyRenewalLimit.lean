import Problems.Juggler.BeattyPhaseTransfer
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Sqrt

/-!
# A moving-phase limit for the positive-partial-sum renewal recurrence

The profile can have dense jumps. The proof uses the phases at their exact
values, dominated convergence for the first half of the convolution, and a
Cesaro estimate for the second half. The classical counting recurrence and
the terminal binomial asymptotic are explicit inputs.
-/

namespace Problems.Juggler.BeattyPhase

open Filter Topology Finset

private theorem zero_mul_bounded {f g : ℕ → ℝ} {C : ℝ}
    (hf : Tendsto f atTop (𝓝 0)) (hg : ∀ n, |g n| ≤ C) :
    Tendsto (fun n => f n * g n) atTop (𝓝 0) := by
  refine squeeze_zero_norm (a := fun n => |f n| * C) (fun n => ?_) ?_
  · rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hg n) (abs_nonneg _)
  · simpa using hf.abs.mul_const C

private theorem sqrt_ratio_le_two {n k : ℕ} (hk : 0 < k) (hn : n ≤ 2*k) :
    Real.sqrt (n : ℝ) / Real.sqrt (k : ℝ) ≤ 2 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hnR : (n : ℝ) ≤ 2 * k := by exact_mod_cast hn
  have hs := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have ht := Real.sq_sqrt hkR.le
  have hnon := Real.sqrt_nonneg (n : ℝ)
  have hpos := Real.sqrt_pos.2 hkR
  apply (div_le_iff₀ hpos).2
  nlinarith

private theorem sqrt_ratio_tendsto_one (j : ℕ) :
    Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) / Real.sqrt (n-j : ℕ))
      atTop (𝓝 1) := by
  have hrat : Tendsto (fun n : ℕ => (n : ℝ) / (n-j : ℕ)) atTop (𝓝 1) := by
    apply (tendsto_natCast_div_add_atTop (-(j : ℝ))).congr'
    filter_upwards [eventually_ge_atTop j] with n hn
    simp [Nat.cast_sub hn, sub_eq_add_neg]
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hrat
  simpa [Function.comp_def, Real.sqrt_div (Nat.cast_nonneg _)] using hs

/-- The first-half kernel in the coefficient recurrence. Its cutoff ensures
the square-root ratio stays uniformly bounded. -/
noncomputable def renewalNear (A : ℕ → ℝ) (n j : ℕ) : ℝ :=
  if j < n ∧ 2*j ≤ n then Real.sqrt (n : ℝ) * A (n-j) else 0

/-- The second-half contribution, before any estimate is made. -/
noncomputable def renewalFar (u A : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ range n, if n < 2*j then
    u j * (Real.sqrt (n : ℝ) * A (n-j)) else 0

/-- The near kernel is bounded uniformly in both indices by the terminal
square-root bound. -/
theorem renewalNear_abs_le {A : ℕ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hA : ∀ k, 0 < k → |A k| ≤ K / Real.sqrt (k : ℝ)) (n j : ℕ) :
    |renewalNear A n j| ≤ 2*K := by
  unfold renewalNear
  split_ifs with h
  · have hk : 0 < n-j := by omega
    have hr := sqrt_ratio_le_two hk (show n ≤ 2*(n-j) by omega)
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc
      _ ≤ Real.sqrt (n : ℝ) * (K / Real.sqrt (n-j : ℕ)) :=
        mul_le_mul_of_nonneg_left (hA _ hk) (Real.sqrt_nonneg _)
      _ = (Real.sqrt (n : ℝ) / Real.sqrt (n-j : ℕ)) * K := by ring
      _ ≤ 2*K := mul_le_mul_of_nonneg_right hr hK
  · simp only [abs_zero]
    positivity

/-- At each fixed lag the near kernel approaches the terminal phase kernel.
The bounded profile can be discontinuous everywhere on a dense subset. -/
theorem renewalNear_sub_phase_tendsto {A : ℕ → ℝ} {Phi : ℝ → ℝ}
    {beta P : ℝ} (hPhi : ∀ x, |Phi x| ≤ P)
    (hA : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) * A n - Phi (n*beta))
      atTop (𝓝 0)) (j : ℕ) :
    Tendsto (fun n : ℕ => renewalNear A n j - Phi (((n : ℝ)-j)*beta))
      atTop (𝓝 0) := by
  have hr := sqrt_ratio_tendsto_one j
  have he := hA.comp (tendsto_sub_atTop_nat j)
  have hf := zero_mul_bounded (by simpa using hr.sub_const 1)
    (fun n : ℕ => hPhi (((n : ℝ)-j)*beta))
  have hlim := (hr.mul he).add hf
  simp only [mul_zero, zero_add] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (2*j+1)] with n hn
  have hj : j < n ∧ 2*j ≤ n := by omega
  have hjn : j ≤ n := by omega
  have hkR : (0 : ℝ) < (n-j : ℕ) := by exact_mod_cast (show 0 < n-j by omega)
  have hsq : Real.sqrt (n-j : ℕ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hkR)
  simp only [renewalNear, if_pos hj, Function.comp_apply]
  rw [Nat.cast_sub hjn]
  have hsq' : Real.sqrt ((n : ℝ)-j) ≠ 0 := by simpa [Nat.cast_sub hjn] using hsq
  field_simp
  ring

private theorem far_coefficient_le {u : ℕ → ℝ} {U : ℝ}
    (hU : 0 ≤ U) (hu : ∀ j, 0 < j → |u j| ≤ U / ((j : ℝ)*Real.sqrt j))
    {n j : ℕ} (hn : 0 < n) (hj : n < 2*j) :
    |u j| * Real.sqrt (n : ℝ) ≤ 4*U/n := by
  have hj0 : 0 < j := by omega
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnle : (n : ℝ) ≤ 2*j := by exact_mod_cast (show n ≤ 2*j by omega)
  have hs := sqrt_ratio_le_two hj0 (show n ≤ 2*j by omega)
  have hsj : 0 < Real.sqrt (j : ℝ) := Real.sqrt_pos.2 hjR
  calc
    _ ≤ (U / ((j : ℝ)*Real.sqrt j)) * Real.sqrt n :=
      mul_le_mul_of_nonneg_right (hu _ hj0) (Real.sqrt_nonneg _)
    _ = (U/j) * (Real.sqrt (n : ℝ)/Real.sqrt j) := by ring
    _ ≤ (U/j)*2 := mul_le_mul_of_nonneg_left hs (div_nonneg hU hjR.le)
    _ ≤ 4*U/n := by
      apply (le_div_iff₀ hnR).2
      have h : (U/j)*n ≤ 2*U := by
        calc (U/j)*n ≤ (U/j)*(2*j) :=
              mul_le_mul_of_nonneg_left hnle (div_nonneg hU hjR.le)
          _ = 2*U := by field_simp
      nlinarith

/-- The far half is bounded by a constant times a Cesaro mean of the
terminal sequence. This is a concrete estimate, not a small-remainder premise. -/
theorem renewalFar_abs_le {u A : ℕ → ℝ} {U : ℝ}
    (hU : 0 ≤ U) (hu : ∀ j, 0 < j → |u j| ≤ U / ((j : ℝ)*Real.sqrt j))
    {n : ℕ} (hn : 0 < n) :
    |renewalFar u A n| ≤ 4*U*((n : ℝ)⁻¹ * ∑ k ∈ range n, |A (k+1)|) := by
  have hnon : 0 ≤ 4*U/(n : ℝ) := by positivity
  unfold renewalFar
  calc
    _ ≤ ∑ j ∈ range n, |if n < 2*j then
        u j * (Real.sqrt (n : ℝ)*A (n-j)) else 0| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ range n, (4*U/(n : ℝ))*|A (n-j)| := by
      apply sum_le_sum
      intro j _
      split_ifs with hj
      · rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (far_coefficient_le hU hu hn hj) (abs_nonneg _)
      · simp only [abs_zero]
        positivity
    _ = (4*U/(n : ℝ)) * ∑ j ∈ range n, |A (n-j)| := (mul_sum _ _ _).symm
    _ = (4*U/(n : ℝ)) * ∑ k ∈ range n, |A (k+1)| := by
      congr 1
      convert sum_range_reflect (fun k => |A (k+1)|) n using 1
      apply sum_congr rfl
      intro j hj
      have hjn := mem_range.1 hj
      congr 2
      omega
    _ = _ := by ring

/-- Decay of the terminal sequence and the three-halves coefficient bound
force the far half to vanish. -/
theorem renewalFar_tendsto_zero {u A : ℕ → ℝ} {U : ℝ}
    (hU : 0 ≤ U) (hu : ∀ j, 0 < j → |u j| ≤ U / ((j : ℝ)*Real.sqrt j))
    (hA : Tendsto A atTop (𝓝 0)) :
    Tendsto (renewalFar u A) atTop (𝓝 0) := by
  have hc := ((hA.comp (tendsto_add_atTop_nat 1)).abs).cesaro
  have hl := hc.const_mul (4*U)
  simp only [abs_zero, mul_zero] at hl
  apply squeeze_zero_norm' _ hl
  filter_upwards [eventually_ge_atTop 1] with n hn
  simpa [Real.norm_eq_abs] using renewalFar_abs_le hU hu (show 0 < n by omega)

/-- Exact near/far splitting of the normalized renewal recurrence. -/
theorem renewal_split {u A : ℕ → ℝ}
    (hrec : ∀ n : ℕ, (n : ℝ)*u n = ∑ j ∈ range n, A (n-j)*u j) (n : ℕ) :
    (n : ℝ)*Real.sqrt n*u n =
      (∑' j, u j * renewalNear A n j) + renewalFar u A n := by
  have hnear : (∑' j, u j * renewalNear A n j) =
      ∑ j ∈ range n, u j * renewalNear A n j := by
    apply tsum_eq_sum
    intro j hj
    have hjn : ¬ j < n := by simpa using hj
    simp [renewalNear, hjn]
  rw [hnear, renewalFar, ← sum_add_distrib]
  calc
    _ = Real.sqrt (n : ℝ) * ((n : ℝ)*u n) := by ring
    _ = Real.sqrt (n : ℝ) * ∑ j ∈ range n, A (n-j)*u j := by rw [hrec]
    _ = ∑ j ∈ range n, Real.sqrt (n : ℝ)*(A (n-j)*u j) := mul_sum _ _ _
    _ = _ := by
      apply sum_congr rfl
      intro j hj
      have hjn := mem_range.1 hj
      by_cases h : 2*j ≤ n
      · simp [renewalNear, hjn, h, not_lt_of_ge h]
        ring
      · have hn2 : n < 2*j := by omega
        simp [renewalNear, hjn, h, hn2]
        ring

/-- A square-root bound on the terminal counts already implies their
normalized sequence tends to zero. -/
theorem terminal_tendsto_zero {A : ℕ → ℝ} {K : ℝ}
    (hA : ∀ n, 0 < n → |A n| ≤ K / Real.sqrt (n : ℝ)) :
    Tendsto A atTop (𝓝 0) := by
  have hs : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun n : ℕ => K / Real.sqrt (n : ℝ)) atTop (𝓝 0) :=
    by simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp hs).const_mul K
  apply squeeze_zero_norm' _ hl
  filter_upwards [eventually_ge_atTop 1] with n hn
  simpa [Real.norm_eq_abs] using hA n (by omega)

/-- The concrete renewal phase limit. All domination, fixed-lag passage to
the limit, and far-tail estimates are proved here. The remaining inputs are
the exact renewal recurrence, a summable three-halves coefficient bound,
and the terminal square-root phase asymptotic. No regularity of `Phi` is
required beyond boundedness. -/
theorem renewal_phase_limit {u A : ℕ → ℝ} {Phi : ℝ → ℝ}
    {beta U K P : ℝ} (hu : Summable u) (hun : ∀ n, 0 ≤ u n)
    (hU : 0 ≤ U) (hK : 0 ≤ K)
    (hub : ∀ n, 0 < n → |u n| ≤ U / ((n : ℝ)*Real.sqrt n))
    (hAb : ∀ n, 0 < n → |A n| ≤ K / Real.sqrt (n : ℝ))
    (hPhi : ∀ x, |Phi x| ≤ P)
    (hA : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)*A n - Phi (n*beta))
      atTop (𝓝 0))
    (hrec : ∀ n : ℕ, (n : ℝ)*u n = ∑ j ∈ range n, A (n-j)*u j) :
    Tendsto (fun n : ℕ => (n : ℝ)*Real.sqrt n*u n -
      ∑' j, u j * Phi (((n : ℝ)-j)*beta)) atTop (𝓝 0) := by
  exact tendsto_weighted_moving_profile hu hun
    (renewalNear_abs_le hK hAb) (fun n j => hPhi _)
    (renewalNear_sub_phase_tendsto hPhi hA)
    (renewalFar_tendsto_zero hU hub (terminal_tendsto_zero hAb)) (renewal_split hrec)

end Problems.Juggler.BeattyPhase

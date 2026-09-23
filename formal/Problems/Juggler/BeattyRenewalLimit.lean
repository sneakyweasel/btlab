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
    {n : ℕ} (hU : 0 ≤ U)
    (hu : ∀ j, j < n → 0 < j → |u j| ≤ U / ((j : ℝ)*Real.sqrt j))
    (hn : 0 < n) :
    |renewalFar u A n| ≤ 4*U*((n : ℝ)⁻¹ * ∑ k ∈ range n, |A (k+1)|) := by
  have hnon : 0 ≤ 4*U/(n : ℝ) := by positivity
  unfold renewalFar
  calc
    _ ≤ ∑ j ∈ range n, |if n < 2*j then
        u j * (Real.sqrt (n : ℝ)*A (n-j)) else 0| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ range n, (4*U/(n : ℝ))*|A (n-j)| := by
      apply sum_le_sum
      intro j hjn
      split_ifs with hj
      · rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), ← mul_assoc]
        have hlocal : ∀ i, 0 < i →
            |(if i < n then u i else 0)| ≤ U / ((i : ℝ)*Real.sqrt i) := by
          intro i hi
          split_ifs with hin
          · exact hu i hin hi
          · simp only [abs_zero]
            positivity
        have hbound := far_coefficient_le hU hlocal hn hj
        simp only [if_pos (mem_range.1 hjn)] at hbound
        exact mul_le_mul_of_nonneg_right hbound (abs_nonneg _)
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
  simpa [Real.norm_eq_abs] using
    renewalFar_abs_le hU (fun j _ hj => hu j hj) (show 0 < n by omega)

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

private theorem renewalNear_tsum_abs_le {u A : ℕ → ℝ} {K : ℝ}
    (hu : Summable u) (hun : ∀ n, 0 ≤ u n) (hK : 0 ≤ K)
    (hAb : ∀ n, 0 < n → |A n| ≤ K / Real.sqrt (n : ℝ)) (n : ℕ) :
    |∑' j, u j * renewalNear A n j| ≤ 2*K*(∑' j, u j) := by
  have heq : (∑' j, u j * renewalNear A n j) =
      ∑ j ∈ range n, u j * renewalNear A n j := by
    apply tsum_eq_sum
    intro j hj
    have hjn : ¬ j < n := by simpa using hj
    simp [renewalNear, hjn]
  rw [heq]
  calc
    _ ≤ ∑ j ∈ range n, |u j * renewalNear A n j| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ range n, 2*K*u j := by
      apply sum_le_sum
      intro j _
      rw [abs_mul, abs_of_nonneg (hun j)]
      simpa [mul_comm] using
        mul_le_mul_of_nonneg_left (renewalNear_abs_le hK hAb n j) (hun j)
    _ = 2*K*∑ j ∈ range n, u j := (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (hu.sum_le_tsum (range n) (fun j _ => hun j)) (by positivity)

/-- The renewal recurrence and summability imply the three-halves bound.
The proof uses strong induction after a finite cutoff where the far-half
Cesaro factor is small. No coefficient decay is assumed. -/
theorem exists_renewal_three_halves_bound {u A : ℕ → ℝ} {K : ℝ}
    (hu : Summable u) (hun : ∀ n, 0 ≤ u n) (hK : 0 ≤ K)
    (hAb : ∀ n, 0 < n → |A n| ≤ K / Real.sqrt (n : ℝ))
    (hrec : ∀ n : ℕ, (n : ℝ)*u n = ∑ j ∈ range n, A (n-j)*u j) :
    ∃ U : ℝ, 0 ≤ U ∧ ∀ n : ℕ, 0 < n → |u n| ≤ U / ((n : ℝ)*Real.sqrt n) := by
  have hc := (((terminal_tendsto_zero hAb).comp (tendsto_add_atTop_nat 1)).abs).cesaro
  have he : ∀ᶠ n : ℕ in atTop,
      (n : ℝ)⁻¹ * ∑ k ∈ range n, |A (k+1)| < (1/8 : ℝ) :=
    hc.eventually_lt_const (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.1 he
  let L : ℝ := ∑' j, u j
  let U : ℝ := 4*K*L + ∑ j ∈ range N, (j : ℝ)*Real.sqrt j*|u j|
  have hL : 0 ≤ L := tsum_nonneg hun
  have hsum : 0 ≤ ∑ j ∈ range N, (j : ℝ)*Real.sqrt j*|u j| :=
    sum_nonneg (fun j _ => by positivity)
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hUK : 4*K*L ≤ U := by dsimp [U]; linarith
  have hbound (n : ℕ) : (n : ℝ)*Real.sqrt n*|u n| ≤ U := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hnN : n < N
      · have ht : (n : ℝ)*Real.sqrt n*|u n| ≤
            ∑ j ∈ range N, (j : ℝ)*Real.sqrt j*|u j| :=
          single_le_sum (f := fun j : ℕ => (j : ℝ)*Real.sqrt j*|u j|)
            (fun j _ => by positivity) (mem_range.2 hnN)
        dsimp [U]
        nlinarith [mul_nonneg hK hL]
      · by_cases hn0 : n = 0
        · simpa [hn0] using hU
        have hn : 0 < n := by omega
        have hprev : ∀ j, j < n → 0 < j →
            |u j| ≤ U / ((j : ℝ)*Real.sqrt j) := by
          intro j hj hj0
          apply (le_div_iff₀ (show 0 < (j : ℝ)*Real.sqrt j by positivity)).2
          simpa [mul_comm, mul_left_comm, mul_assoc] using ih j hj
        have hnear := renewalNear_tsum_abs_le hu hun hK hAb n
        have hfar := renewalFar_abs_le (A := A) hU hprev hn
        have hsmall := hN n (by omega)
        have hfar' : |renewalFar u A n| ≤ U/2 := by
          calc
            _ ≤ 4*U*((n : ℝ)⁻¹ * ∑ k ∈ range n, |A (k+1)|) := hfar
            _ ≤ 4*U*(1/8) := mul_le_mul_of_nonneg_left hsmall.le (by positivity)
            _ = U/2 := by ring
        calc
          _ = |(n : ℝ)*Real.sqrt n*u n| := by
            simp only [abs_mul, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n),
              abs_of_nonneg (Real.sqrt_nonneg _)]
          _ = |(∑' j, u j * renewalNear A n j) + renewalFar u A n| :=
            congrArg abs (renewal_split hrec n)
          _ ≤ |∑' j, u j * renewalNear A n j| + |renewalFar u A n| := abs_add_le _ _
          _ ≤ 2*K*L + U/2 := add_le_add hnear hfar'
          _ ≤ U := by linarith
  refine ⟨U, hU, fun n hn => ?_⟩
  apply (le_div_iff₀ (show 0 < (n : ℝ)*Real.sqrt n by positivity)).2
  simpa [mul_comm, mul_left_comm, mul_assoc] using hbound n

/-- The concrete renewal phase limit. All domination, fixed-lag passage to
the limit, and far-tail estimates are proved here. The remaining inputs are
the exact renewal recurrence, a summable three-halves coefficient bound,
and the terminal square-root phase asymptotic. No regularity of `Phi` is
required beyond boundedness. -/
theorem renewal_phase_limit_of_bound {u A : ℕ → ℝ} {Phi : ℝ → ℝ}
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

/-- A summable nonnegative solution of the renewal recurrence inherits the
moving terminal profile through convolution. The three-halves decay and
the small-tail estimate are conclusions of the proof, not hypotheses.
This proves convergence to zero, without a quantitative error rate. -/
theorem renewal_phase_limit {u A : ℕ → ℝ} {Phi : ℝ → ℝ}
    {beta K P : ℝ} (hu : Summable u) (hun : ∀ n, 0 ≤ u n) (hK : 0 ≤ K)
    (hAb : ∀ n, 0 < n → |A n| ≤ K / Real.sqrt (n : ℝ))
    (hPhi : ∀ x, |Phi x| ≤ P)
    (hA : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)*A n - Phi (n*beta))
      atTop (𝓝 0))
    (hrec : ∀ n : ℕ, (n : ℝ)*u n = ∑ j ∈ range n, A (n-j)*u j) :
    Tendsto (fun n : ℕ => (n : ℝ)*Real.sqrt n*u n -
      ∑' j, u j * Phi (((n : ℝ)-j)*beta)) atTop (𝓝 0) := by
  obtain ⟨U, hU, hub⟩ := exists_renewal_three_halves_bound hu hun hK hAb hrec
  exact renewal_phase_limit_of_bound hu hun hU hK hub hAb hPhi hA hrec

end Problems.Juggler.BeattyPhase

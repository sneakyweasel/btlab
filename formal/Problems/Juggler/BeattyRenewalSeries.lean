import Problems.Juggler.BeattyRenewalLimit
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Exponential renewal coefficients

The formal exponential of `sum A_n X^n/n` supplies the exact renewal
recurrence and, for nonnegative summable logarithmic coefficients, a
summable nonnegative coefficient sequence. Combined with the renewal limit,
this isolates the classical counting identity and terminal binomial estimate.
-/

namespace Problems.Juggler.BeattyPhase

open Filter Topology Finset Finset.Nat PowerSeries

/-- The logarithmic coefficient sequence; its zeroth entry is zero by
the convention for division by zero. -/
noncomputable def renewalLogCoeff (A : ℕ → ℝ) (n : ℕ) : ℝ := A n / n

/-- The formal exponential whose coefficients are the survivor sequence
in the positive-partial-sum counting identity. -/
noncomputable def renewalExponential (A : ℕ → ℝ) : PowerSeries ℝ :=
  (PowerSeries.exp ℝ).subst (PowerSeries.mk (renewalLogCoeff A))

/-- Coefficients of the formal renewal exponential. Equality with actual
survivor counts is a separate combinatorial theorem. -/
noncomputable def renewalCoeff (A : ℕ → ℝ) (n : ℕ) : ℝ :=
  PowerSeries.coeff n (renewalExponential A)

private theorem renewal_hasSubst (A : ℕ → ℝ) :
    HasSubst (PowerSeries.mk (renewalLogCoeff A)) :=
  HasSubst.of_constantCoeff_zero' (by simp [renewalLogCoeff])

/-- The exponential coefficient is an absolutely finite sum in each fixed
degree, expressed as an infinite sum to support the mass calculation. -/
theorem renewalCoeff_eq_tsum (A : ℕ → ℝ) (n : ℕ) :
    renewalCoeff A n = ∑' k : ℕ,
      coeff n ((PowerSeries.mk (renewalLogCoeff A))^k) / (Nat.factorial k : ℝ) := by
  unfold renewalCoeff renewalExponential
  rw [coeff_subst' (renewal_hasSubst A),
    ← tsum_eq_finsum (L := SummationFilter.unconditional ℕ)
      (coeff_subst_finite' (renewal_hasSubst A) (PowerSeries.exp ℝ) n)]
  apply tsum_congr
  intro k
  simp [coeff_exp, smul_eq_mul, div_eq_mul_inv, mul_comm]

private theorem coeff_pow_nonneg {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n) (k n : ℕ) :
    0 ≤ coeff n ((PowerSeries.mk b)^k) := by
  induction k generalizing n with
  | zero => simp [coeff_one]; split_ifs <;> norm_num
  | succ k ih =>
    rw [pow_succ', coeff_mul]
    apply sum_nonneg
    intro p _
    exact mul_nonneg (by simpa using hb p.1) (ih p.2)

private theorem hasSum_coeff_pow {b : ℕ → ℝ} (hb : Summable b) (k : ℕ) :
    HasSum (fun n => coeff n ((PowerSeries.mk b)^k)) ((∑' n, b n)^k) := by
  induction k with
  | zero => simpa [coeff_one] using (hasSum_ite_eq (0 : ℕ) (1 : ℝ))
  | succ k ih =>
    have hs := hasSum_sum_range_mul_of_summable_norm hb.norm ih.summable.norm
    have he (n : ℕ) : coeff n ((PowerSeries.mk b)^(k+1)) =
        ∑ j ∈ range (n+1), b j * coeff (n-j) ((PowerSeries.mk b)^k) := by
      rw [pow_succ', coeff_mul, sum_antidiagonal_eq_sum_range_succ_mk]
      simp only [coeff_mk]
    simp_rw [he]
    simpa [ih.tsum_eq, pow_succ', mul_comm] using hs

/-- Nonnegative terminal coefficients give nonnegative exponential
coefficients. -/
theorem renewalCoeff_nonneg {A : ℕ → ℝ} (hA : ∀ n, 0 ≤ A n) (n : ℕ) :
    0 ≤ renewalCoeff A n := by
  rw [renewalCoeff_eq_tsum]
  apply tsum_nonneg
  intro k
  apply div_nonneg
  · exact coeff_pow_nonneg (fun j => div_nonneg (hA j) (Nat.cast_nonneg j)) k n
  · positivity

/-- A summable nonnegative logarithmic sequence yields summable exponential
coefficients. The proof exchanges the two sums using nonnegativity and the
ordinary exponential majorant, without assuming coefficient decay. -/
theorem summable_renewalCoeff {A : ℕ → ℝ} (hA : ∀ n, 0 ≤ A n)
    (hb : Summable (renewalLogCoeff A)) : Summable (renewalCoeff A) := by
  let b := renewalLogCoeff A
  let f : ℕ × ℕ → ℝ := fun p => coeff p.2 ((PowerSeries.mk b)^p.1) /
    (Nat.factorial p.1 : ℝ)
  have hbn (n : ℕ) : 0 ≤ b n := div_nonneg (hA n) (Nat.cast_nonneg n)
  have hfn : 0 ≤ f := fun p => div_nonneg (coeff_pow_nonneg hbn _ _) (by positivity)
  have hrows (k : ℕ) : HasSum (fun n => f (k,n))
      ((∑' n, b n)^k / (Nat.factorial k : ℝ)) := (hasSum_coeff_pow hb k).div_const _
  have hf : Summable f := (summable_prod_of_nonneg hfn).2
    ⟨fun k => (hrows k).summable, by
      simpa only [(hrows _).tsum_eq] using Real.summable_pow_div_factorial (∑' n, b n)⟩
  have hs := hf.prod_symm.prod
  simpa only [f, b, Prod.swap_prod_mk, ← renewalCoeff_eq_tsum] using hs

/-- Differentiating the formal exponential gives the exact coefficient
renewal recurrence, including its empty zeroth equation. -/
theorem renewalCoeff_recurrence (A : ℕ → ℝ) (n : ℕ) :
    (n : ℝ)*renewalCoeff A n = ∑ j ∈ range n, A (n-j)*renewalCoeff A j := by
  cases n with
  | zero => simp
  | succ n =>
    have hd : derivative ℝ (renewalExponential A) =
        renewalExponential A * derivative ℝ (PowerSeries.mk (renewalLogCoeff A)) := by
      unfold renewalExponential
      rw [derivative_subst (renewal_hasSubst A), derivative_exp]
    have hc := congrArg (coeff n) hd
    rw [coeff_derivative, coeff_mul, sum_antidiagonal_eq_sum_range_succ_mk] at hc
    change _ * (n+1 : ℝ) = _ at hc
    rw [mul_comm] at hc
    convert hc using 1
    · simp [renewalCoeff]
    · apply sum_congr rfl
      intro j hj
      have hjn : j ≤ n := by have := mem_range.1 hj; omega
      have hidx : n+1-j = n-j+1 := by omega
      have hpos : (0 : ℝ) < (n-j+1 : ℕ) := by positivity
      simp only [coeff_derivative, coeff_mk, renewalLogCoeff, hidx, renewalCoeff]
      rw [Nat.cast_add, Nat.cast_one]
      field_simp

private theorem summable_three_halves :
    Summable (fun n : ℕ => 1 / ((n : ℝ)*Real.sqrt n)) := by
  have hp := (Real.summable_one_div_nat_rpow (p := 3/2)).2 (by norm_num)
  apply hp.congr
  intro n
  by_cases hn : n = 0
  · simp [hn]
  have hnR : (0 : ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero hn)
  rw [show (3/2 : ℝ) = 1 + 1/2 by norm_num, Real.rpow_add hnR,
    Real.rpow_one, ← Real.sqrt_eq_rpow]

/-- The terminal square-root bound makes the logarithmic coefficients
summable, by comparison with the three-halves series. -/
theorem summable_renewalLogCoeff_of_bound {A : ℕ → ℝ} {K : ℝ}
    (hA : ∀ n, 0 < n → |A n| ≤ K / Real.sqrt (n : ℝ)) :
    Summable (renewalLogCoeff A) := by
  apply (summable_three_halves.mul_left K).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, renewalLogCoeff, abs_div,
    abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  by_cases hn : n = 0
  · simp [hn]
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  calc
    _ ≤ (K / Real.sqrt (n : ℝ)) / n :=
      div_le_div_of_nonneg_right (hA n hn0) (Nat.cast_nonneg n)
    _ = _ := by ring

/-- Convergence to any bounded terminal phase profile implies a global
square-root bound, including the finite initial segment. -/
theorem exists_terminal_sqrt_bound_of_phase_limit {A : ℕ → ℝ} {Phi : ℝ → ℝ}
    {beta P : ℝ} (hPhi : ∀ x, |Phi x| ≤ P)
    (hA : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)*A n - Phi (n*beta))
      atTop (𝓝 0)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 0 < n → |A n| ≤ K / Real.sqrt (n : ℝ) := by
  obtain ⟨C, hC⟩ := hA.abs.bddAbove_range
  have hC' (n : ℕ) : |Real.sqrt (n : ℝ)*A n - Phi (n*beta)| ≤ C :=
    hC (Set.mem_range_self n)
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC' 0)
  have hP : 0 ≤ P := (abs_nonneg _).trans (hPhi 0)
  refine ⟨C+P, by positivity, fun n hn => ?_⟩
  apply (le_div_iff₀ (show 0 < Real.sqrt (n : ℝ) by positivity)).2
  have h := abs_add_le (Real.sqrt (n : ℝ)*A n - Phi (n*beta)) (Phi (n*beta))
  rw [sub_add_cancel, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] at h
  nlinarith [hC' n, hPhi (n*beta)]

/-- The full analytic implication for formal exponential coefficients.
Only nonnegativity and convergence to a bounded terminal profile are
assumed. Summability, recurrence, coefficient decay and the moving-profile
passage to the limit are all derived inside Lean. This asserts `o(1)`,
not a quantitative convergence rate. -/
theorem renewalCoeff_phase_limit {A : ℕ → ℝ} {Phi : ℝ → ℝ} {beta P : ℝ}
    (hAn : ∀ n, 0 ≤ A n) (hPhi : ∀ x, |Phi x| ≤ P)
    (hA : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)*A n - Phi (n*beta))
      atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (n : ℝ)*Real.sqrt n*renewalCoeff A n -
      ∑' j, renewalCoeff A j * Phi (((n : ℝ)-j)*beta)) atTop (𝓝 0) := by
  obtain ⟨K, hK, hAb⟩ := exists_terminal_sqrt_bound_of_phase_limit hPhi hA
  exact renewal_phase_limit
    (summable_renewalCoeff hAn (summable_renewalLogCoeff_of_bound hAb))
    (renewalCoeff_nonneg hAn) hK hAb hPhi hA (renewalCoeff_recurrence A)

/-- The empty coefficient of the formal renewal exponential is one. -/
theorem renewalCoeff_zero (A : ℕ → ℝ) : renewalCoeff A 0 = 1 := by
  rw [renewalCoeff_eq_tsum]
  have hterm (k : ℕ) : coeff 0 ((PowerSeries.mk (renewalLogCoeff A))^k) /
      (Nat.factorial k : ℝ) = if k = 0 then 1 else 0 := by
    by_cases hk : k = 0
    · simp [hk]
    · simp [coeff_zero_eq_constantCoeff_apply, map_pow, constantCoeff_mk,
        renewalLogCoeff, hk]
  simp_rw [hterm]
  simp

/-- The coefficient recurrence and the empty coefficient uniquely determine
the formal exponential coefficients. This uses no positivity or asymptotics. -/
theorem eq_renewalCoeff_of_recurrence {u A : ℕ → ℝ} (hu0 : u 0 = 1)
    (hrec : ∀ n : ℕ, (n : ℝ)*u n = ∑ j ∈ range n, A (n-j)*u j) :
    u = renewalCoeff A := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · simp [hn, hu0, renewalCoeff_zero]
    · have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      apply mul_left_cancel₀ hnR
      rw [hrec, renewalCoeff_recurrence]
      apply sum_congr rfl
      intro j hj
      rw [ih j (mem_range.1 hj)]

/-- With the empty coefficient fixed, equality to the formal exponential is
equivalent to its finite renewal recurrence at every degree. -/
theorem eq_renewalCoeff_iff_recurrence {u A : ℕ → ℝ} (hu0 : u 0 = 1) :
    u = renewalCoeff A ↔
      ∀ n : ℕ, (n : ℝ)*u n = ∑ j ∈ range n, A (n-j)*u j := by
  constructor
  · rintro rfl
    exact renewalCoeff_recurrence A
  · exact eq_renewalCoeff_of_recurrence hu0

/-- The first nonconstant exponential term supplies a coefficient lower
bound. Nonnegativity is sufficient; summability is not required. -/
theorem renewalLogCoeff_le_renewalCoeff {A : ℕ → ℝ}
    (hA : ∀ n, 0 ≤ A n) (n : ℕ) :
    A n / (n : ℝ) ≤ renewalCoeff A n := by
  by_cases hn : n = 0
  · simp [hn, renewalCoeff_zero]
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  have h : A n * renewalCoeff A 0 ≤
      ∑ j ∈ range n, A (n-j)*renewalCoeff A j := by
    simpa using single_le_sum
      (f := fun j => A (n-j)*renewalCoeff A j)
      (fun j _ => mul_nonneg (hA _) (renewalCoeff_nonneg hA _)) (mem_range.2 hn0)
  rw [renewalCoeff_zero, mul_one, ← renewalCoeff_recurrence] at h
  exact (div_le_iff₀ (show (0 : ℝ) < n by exact_mod_cast hn0)).2 (by
    simpa [mul_comm] using h)

/-- A mere terminal square-root upper bound gives three-halves decay of
the exponential coefficients. No phase profile or local limit is needed. -/
theorem exists_renewalCoeff_three_halves_bound {A : ℕ → ℝ} {K : ℝ}
    (hA : ∀ n, 0 ≤ A n) (hK : 0 ≤ K)
    (hAb : ∀ n, 0 < n → A n ≤ K / Real.sqrt (n : ℝ)) :
    ∃ U : ℝ, 0 ≤ U ∧ ∀ n : ℕ, 0 < n →
      renewalCoeff A n ≤ U / ((n : ℝ)*Real.sqrt n) := by
  have hAbs (n : ℕ) (hn : 0 < n) : |A n| ≤ K / Real.sqrt (n : ℝ) := by
    simpa [abs_of_nonneg (hA n)] using hAb n hn
  obtain ⟨U, hU, hu⟩ := exists_renewal_three_halves_bound
    (summable_renewalCoeff hA (summable_renewalLogCoeff_of_bound hAbs))
    (renewalCoeff_nonneg hA) hK hAbs (renewalCoeff_recurrence A)
  exact ⟨U, hU, fun n hn => by simpa [abs_of_nonneg (renewalCoeff_nonneg hA n)] using hu n hn⟩

/-- Two-sided square-root terminal bounds imply two-sided three-halves
coefficient bounds, without proving any phase limit. Positivity of `a`
turns these inequalities into a sharp-order estimate. -/
theorem renewalCoeff_three_halves_bounds {A : ℕ → ℝ} {a K : ℝ}
    (hA : ∀ n, 0 ≤ A n) (hK : 0 ≤ K)
    (hAb : ∀ n, 0 < n → A n ≤ K / Real.sqrt (n : ℝ))
    (hAl : ∀ n : ℕ, 0 < n → a / Real.sqrt (n : ℝ) ≤ A n) :
    ∃ U : ℝ, 0 ≤ U ∧ ∀ n : ℕ, 0 < n →
      a / ((n : ℝ)*Real.sqrt n) ≤ renewalCoeff A n ∧
      renewalCoeff A n ≤ U / ((n : ℝ)*Real.sqrt n) := by
  obtain ⟨U, hU, hu⟩ := exists_renewalCoeff_three_halves_bound hA hK hAb
  refine ⟨U, hU, fun n hn => ⟨?_, hu n hn⟩⟩
  calc
    _ = (a / Real.sqrt (n : ℝ)) / n := by ring
    _ ≤ A n / n := div_le_div_of_nonneg_right (hAl n hn) (Nat.cast_nonneg n)
    _ ≤ _ := renewalLogCoeff_le_renewalCoeff hA n

end Problems.Juggler.BeattyPhase

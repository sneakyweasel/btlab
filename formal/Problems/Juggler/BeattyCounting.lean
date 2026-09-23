import Problems.Juggler.BeattySurvivorProfile
import Problems.Juggler.PaperBCertificateRecursion
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# The exact survivor counting identity

The proof retains the odd-letter variable. Survivor polynomials have positive
endpoint support, whereas first-descent polynomials have negative support.
The last-letter identity factors the unrestricted word series. Taking its
formal logarithmic derivative separates the two endpoint half-planes.
-/

namespace Problems.Juggler.BeattyPhase

open Finset PowerSeries
open PaperBThreshold PaperBCertificates

private abbrev Poly := Polynomial ℝ
private abbrev Series := PowerSeries Poly

private def polySupported (a b : ℝ) (n : ℕ) (p : Poly) : Prop :=
  ∀ k : ℕ, a * n + b * k < 0 → p.coeff k = 0

private def supported (a b : ℝ) (f : Series) : Prop :=
  ∀ n, polySupported a b n (coeff n f)

private theorem polySupported_zero (a b : ℝ) (n : ℕ) :
    polySupported a b n 0 := by intro k _; simp

private theorem polySupported_one (a b : ℝ) : polySupported a b 0 1 := by
  intro k hk
  by_cases h : k = 0
  · subst k; norm_num at hk
  · simp [Polynomial.coeff_one, h]

private theorem polySupported_add {a b : ℝ} {n : ℕ} {p q : Poly}
    (hp : polySupported a b n p) (hq : polySupported a b n q) :
    polySupported a b n (p + q) := by
  intro k hk
  simp [hp k hk, hq k hk]

private theorem polySupported_neg {a b : ℝ} {n : ℕ} {p : Poly}
    (hp : polySupported a b n p) : polySupported a b n (-p) := by
  intro k hk
  simp [hp k hk]

private theorem polySupported_sum {ι : Type*} {a b : ℝ} {n : ℕ}
    (s : Finset ι) (p : ι → Poly) (h : ∀ i ∈ s, polySupported a b n (p i)) :
    polySupported a b n (∑ i ∈ s, p i) := by
  intro k hk
  rw [Polynomial.finsetSum_coeff]
  exact sum_eq_zero fun i hi => h i hi k hk

private theorem polySupported_mul {a b : ℝ} {n m : ℕ} {p q : Poly}
    (hp : polySupported a b n p) (hq : polySupported a b m q) :
    polySupported a b (n+m) (p*q) := by
  intro k hk
  rw [Polynomial.coeff_mul]
  apply sum_eq_zero
  intro ij hij
  have he := Finset.mem_antidiagonal.1 hij
  by_cases hi : a*n+b*ij.1 < 0
  · simp [hp _ hi]
  · have hj : a*m+b*ij.2 < 0 := by
      rw [← he, Nat.cast_add, Nat.cast_add] at hk
      push Not at hi
      nlinarith
    simp [hq _ hj]

private theorem supported_mul {a b : ℝ} {f g : Series}
    (hf : supported a b f) (hg : supported a b g) : supported a b (f*g) := by
  intro n
  rw [coeff_mul]
  apply polySupported_sum
  intro ij hij
  have he := Finset.mem_antidiagonal.1 hij
  simpa [he] using polySupported_mul (hf ij.1) (hg ij.2)

private theorem supported_inv {a b : ℝ} {f : Series} (hf : supported a b f) :
    supported a b (invOfUnit f 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [coeff_invOfUnit]
    split_ifs with hn
    · subst n
      simpa using polySupported_one a b
    · simp only [inv_one, Units.val_one, neg_one_mul]
      apply polySupported_neg
      apply polySupported_sum
      intro ij hij
      split_ifs with hj
      · simpa [Finset.mem_antidiagonal.1 hij] using
          polySupported_mul (hf ij.1) (ih ij.2 hj)
      · exact polySupported_zero _ _ _

private noncomputable def euler (f : Series) : Series := X * derivative Poly f

private theorem coeff_euler (f : Series) (n : ℕ) :
    coeff n (euler f) = (n : Poly) * coeff n f := by
  cases n with
  | zero => simp [euler]
  | succ n => simp [euler, coeff_derivative, mul_comm]

private theorem supported_euler {a b : ℝ} {f : Series} (hf : supported a b f) :
    supported a b (euler f) := by
  intro n k hk
  rw [coeff_euler]
  simpa using congrArg (fun x : ℝ => (n : ℝ) * x) (hf n k hk)

private theorem euler_mul (f g : Series) :
    euler (f*g) = euler f*g + f*euler g := by
  simp only [euler, Derivation.leibniz]
  ring

private noncomputable def survivorPoly (n : ℕ) : Poly :=
  ∑ w ∈ neverNegWords n, Polynomial.X ^ oddCount w

private noncomputable def descentPoly (n : ℕ) : Poly :=
  ∑ w ∈ minimalCertWords n, Polynomial.X ^ oddCount w

private noncomputable def survivorSeries : Series := mk survivorPoly

private noncomputable def descentSeries : Series := 1 - mk descentPoly

private theorem survivorPoly_zero : survivorPoly 0 = 1 := by
  have he : prefixNoncontracting [] := by
    intro k hk
    simp [exponentGap]
  have hw : neverNegWords 0 = {[]} := by
    ext w
    simp only [neverNegWords, allWords, mem_filter, mem_singleton]
    exact ⟨And.left, fun h => ⟨h, h ▸ he⟩⟩
  simp only [survivorPoly, hw, sum_singleton, oddCount, pow_zero]

private theorem descentPoly_zero : descentPoly 0 = 0 := by
  have hw : minimalCertWords 0 = ∅ := by
    ext w
    simp only [minimalCertWords, allWords, mem_filter, mem_singleton, Finset.notMem_empty,
      iff_false, not_and]
    intro h
    subst w
    exact fun h => h.1 rfl
  simp [descentPoly, hw]

private theorem survivorPoly_eval (n : ℕ) :
    (survivorPoly n).eval 1 = (neverNegCount n : ℝ) := by
  simp [survivorPoly, Polynomial.eval_finsetSum, neverNegCount]

private theorem survivorPoly_step (n : ℕ) :
    survivorPoly (n+1) + descentPoly (n+1) =
      (1 + Polynomial.X) * survivorPoly n := by
  classical
  rw [survivorPoly, descentPoly, ← sum_union (survivors_disjoint_certs n),
    ← extensions_eq_survivors_union_certs,
    sum_biUnion (fun x _ y _ hne => extend_fiber_disjoint hne)]
  simp only [survivorPoly, mul_sum]
  apply sum_congr rfl
  intro w _
  have hne : w ++ [Branch.even] ≠ w ++ [Branch.odd] := fun h =>
    Branch.noConfusion (append_singleton_inj h).2
  rw [sum_pair hne]
  simp only [oddCount_append, oddCount, add_zero, pow_succ]
  ring

private theorem gap_iff (n k : ℕ) :
    (3 : ℕ)^k < 2^n ↔ (k : ℝ) < n*beta := by
  have hcast : ((3 : ℕ)^k < 2^n) ↔ ((3 : ℝ)^k < 2^n) := by
    exact_mod_cast Iff.rfl
  rw [hcast, ← Real.log_lt_log_iff (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, PaperBThreshold.beta, ← mul_div_assoc,
    lt_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 3))]

private theorem supported_survivor : supported (-beta) 1 survivorSeries := by
  intro n k hk
  simp only [survivorSeries, coeff_mk, survivorPoly, Polynomial.finsetSum_coeff]
  apply sum_eq_zero
  intro w hw
  have hle := neverNeg_endpoint hw
  have hn : ¬ (oddCount w : ℝ) < n*beta := fun h =>
    (not_lt_of_ge hle) ((gap_iff n _).2 h)
  have hne : k ≠ oddCount w := by
    intro h; subst k; apply hn; linarith
  simp [Polynomial.coeff_X_pow, hne]

private theorem supported_descent : supported beta (-1) descentSeries := by
  intro n k hk
  cases n with
  | zero => simpa [descentSeries, descentPoly_zero] using polySupported_one beta (-1) k hk
  | succ n =>
    simp only [descentSeries, map_sub, coeff_one, Nat.succ_ne_zero, if_false,
      coeff_mk, zero_sub, Polynomial.coeff_neg, neg_eq_zero,
      descentPoly, Polynomial.finsetSum_coeff]
    apply sum_eq_zero
    intro w hw
    have hlen := mem_allWords.1 (mem_filter.1 hw).1
    have hg := (mem_filter.1 hw).2.2.1
    have hlt : (oddCount w : ℝ) < (n+1 : ℕ)*beta := by
      apply (gap_iff (n+1) _).1
      simpa [exponentGap, hlen] using hg
    have hne : k ≠ oddCount w := by
      intro h; subst k; nlinarith
    simp [Polynomial.coeff_X_pow, hne]

private noncomputable def stepSeries : Series := X * C (1 + Polynomial.X)

private noncomputable def unrestrictedSeries : Series :=
  mk fun n => (1 + Polynomial.X)^n

private theorem descent_factor : descentSeries = (1-stepSeries)*survivorSeries := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [descentSeries, stepSeries, survivorSeries, descentPoly_zero, survivorPoly_zero]
  | succ n =>
    simp only [descentSeries, map_sub, coeff_one, Nat.succ_ne_zero, if_false,
      coeff_mk, zero_sub, sub_mul, one_mul, stepSeries, mul_assoc,
      coeff_succ_X_mul, coeff_C_mul, survivorSeries]
    have h := survivorPoly_step n
    linear_combination -h

private theorem unrestricted_inverse : (1-stepSeries)*unrestrictedSeries = 1 := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [stepSeries, unrestrictedSeries]
  | succ n =>
    simp only [sub_mul, one_mul, map_sub, stepSeries, mul_assoc, coeff_succ_X_mul,
      coeff_C_mul, unrestrictedSeries, coeff_mk, pow_succ', sub_self, coeff_one,
      Nat.succ_ne_zero, if_false]

private theorem euler_step : euler stepSeries = stepSeries := by
  simp [euler, stepSeries, Derivation.leibniz]

private theorem euler_sub (f g : Series) : euler (f-g) = euler f-euler g := by
  simp only [euler, map_sub, mul_sub]

private theorem euler_one : euler 1 = 0 := by simp [euler]

private noncomputable def logDerivative (f : Series) : Series :=
  euler f * invOfUnit f 1

private theorem logDerivative_difference :
    logDerivative survivorSeries - logDerivative descentSeries =
      stepSeries * unrestrictedSeries := by
  have hf0 : constantCoeff survivorSeries = (1 : Poly) := by
    simp [survivorSeries, survivorPoly_zero]
  have hh0 : constantCoeff descentSeries = (1 : Poly) := by
    simp [descentSeries, descentPoly_zero]
  have hfi := mul_invOfUnit survivorSeries 1 hf0
  have hhi := mul_invOfUnit descentSeries 1 hh0
  have hfh : survivorSeries * invOfUnit descentSeries 1 = unrestrictedSeries := by
    calc
      _ = unrestrictedSeries * ((1-stepSeries)*survivorSeries) *
          invOfUnit descentSeries 1 := by
        rw [← mul_assoc unrestrictedSeries, mul_comm unrestrictedSeries,
          unrestricted_inverse]
        simp
      _ = unrestrictedSeries := by rw [← descent_factor, mul_assoc, hhi, mul_one]
  have hwh : (1-stepSeries) * invOfUnit descentSeries 1 = invOfUnit survivorSeries 1 := by
    calc
      _ = invOfUnit survivorSeries 1 * ((1-stepSeries)*survivorSeries) *
          invOfUnit descentSeries 1 := by
        calc
          _ = (survivorSeries * invOfUnit survivorSeries 1) *
              ((1-stepSeries) * invOfUnit descentSeries 1) := by rw [hfi, one_mul]
          _ = _ := by ring
      _ = invOfUnit survivorSeries 1 := by rw [← descent_factor, mul_assoc, hhi, mul_one]
  have he : euler descentSeries = -stepSeries*survivorSeries +
      (1-stepSeries)*euler survivorSeries := by
    rw [descent_factor, euler_mul, euler_sub, euler_one, euler_step, zero_sub]
  unfold logDerivative
  rw [he, add_mul]
  calc
    _ = euler survivorSeries * invOfUnit survivorSeries 1 +
        stepSeries * (survivorSeries * invOfUnit descentSeries 1) -
        euler survivorSeries * ((1-stepSeries)*invOfUnit descentSeries 1) := by ring
    _ = _ := by rw [hfh, hwh]; ring

private theorem logDerivative_zero (f : Series) : coeff 0 (logDerivative f) = 0 := by
  simp [logDerivative, euler]

private theorem supported_logDerivative {a b : ℝ} {f : Series}
    (hf : supported a b f) : supported a b (logDerivative f) :=
  supported_mul (supported_euler hf) (supported_inv hf)

private theorem slope_ne_integer {n : ℕ} (hn : 0 < n) (k : ℕ) :
    (n : ℝ)*beta ≠ k := by
  intro he
  have hl : Real.log ((2 : ℝ)^n) = Real.log ((3 : ℝ)^k) := by
    rw [Real.log_pow, Real.log_pow]
    have h3 : Real.log 3 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
    dsimp [PaperBThreshold.beta] at he
    field_simp at he
    simpa [mul_comm] using he
  have heq : (2 : ℕ)^n = 3^k := by
    exact_mod_cast (Real.log_injOn_pos (show (0 : ℝ) < 2^n by positivity)
      (show (0 : ℝ) < 3^k by positivity) hl)
  exact two_pow_ne_three_pow hn heq

private theorem logDerivative_survivor_coeff (n k : ℕ) :
    (coeff n (logDerivative survivorSeries)).coeff k =
      if (n : ℝ)*beta < k then (n.choose k : ℝ) else 0 := by
  cases n with
  | zero => cases k <;> simp [logDerivative_zero]
  | succ n =>
    have hdiff := congrArg (fun f : Series => (coeff (n+1) f).coeff k)
      logDerivative_difference
    simp only [map_sub, Polynomial.coeff_sub, stepSeries, mul_assoc,
      coeff_succ_X_mul, coeff_C_mul, unrestrictedSeries, coeff_mk,
      ← pow_succ', Polynomial.coeff_one_add_X_pow] at hdiff
    by_cases h : (n+1 : ℕ)*beta < (k : ℝ)
    · rw [if_pos h]
      have hz := supported_logDerivative supported_descent (n+1) k (by linarith :
        beta*(n+1 : ℕ) + (-1)*(k : ℝ) < 0)
      linarith
    · rw [if_neg h]
      have hne := slope_ne_integer (by omega : 0 < n+1) k
      apply supported_logDerivative supported_survivor (n+1) k
      have hh : (k : ℝ) < (n+1 : ℕ)*beta := lt_of_le_of_ne (le_of_not_gt h) hne.symm
      linarith

private theorem logDerivative_survivor_eval (n : ℕ) :
    (coeff n (logDerivative survivorSeries)).eval 1 = (endpointCount n : ℝ) := by
  have hd : (coeff n (logDerivative survivorSeries)).natDegree ≤ n := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.2
    intro k hk
    rw [logDerivative_survivor_coeff, Nat.choose_eq_zero_of_lt hk]
    split_ifs <;> simp
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hd)]
  simp only [one_pow, mul_one, logDerivative_survivor_coeff, endpointCount,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]

/-- The exact integer positive-partial-sum recurrence for the existing
survivor counts. The proof uses the last-letter partition with an odd-count
variable; it has no asymptotic or generating-identity assumption. -/
theorem survivor_count_recurrence (n : ℕ) :
    n * neverNegCount n = ∑ j ∈ range n, endpointCount (n-j)*neverNegCount j := by
  have hf0 : constantCoeff survivorSeries = (1 : Poly) := by
    simp [survivorSeries, survivorPoly_zero]
  have he : euler survivorSeries = survivorSeries * logDerivative survivorSeries := by
    unfold logDerivative
    calc
      _ = euler survivorSeries * (survivorSeries * invOfUnit survivorSeries 1) := by
        rw [mul_invOfUnit survivorSeries 1 hf0, mul_one]
      _ = _ := by ring
  have hc := congrArg (fun f : Series => (coeff n f).eval 1) he
  rw [coeff_euler, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hc
  have hf (j : ℕ) : (coeff j survivorSeries).eval 1 = (neverNegCount j : ℝ) :=
    by simpa [survivorSeries] using survivorPoly_eval j
  simp only [Polynomial.eval_mul, Polynomial.eval_natCast, Polynomial.eval_finsetSum,
    hf, logDerivative_survivor_eval] at hc
  rw [sum_range_succ] at hc
  have hz : endpointCount 0 = 0 := by simp [endpointCount]
  simp only [Nat.sub_self, hz, Nat.cast_zero, mul_zero, add_zero] at hc
  have hr : (n * neverNegCount n : ℝ) =
      ((∑ j ∈ range n, endpointCount (n-j)*neverNegCount j : ℕ) : ℝ) := by
    simpa only [Nat.cast_sum, Nat.cast_mul, mul_comm] using hc
  exact_mod_cast hr

/-- The formal exponential identity is now proved for the actual survivor
counts, by the unconditional integer recurrence. -/
theorem survivor_exponential_identity : SurvivorExponentialIdentity :=
  survivorExponentialIdentity_iff_count_recurrence.2 survivor_count_recurrence

end Problems.Juggler.BeattyPhase

import Problems.Juggler.BeattySlopeWords
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Exact survivor counting at an arbitrary irrational slope

Keeping the odd-letter variable separates positive and negative endpoint
support. The formal logarithmic derivative then gives the classical
positive-partial-sum recurrence directly for the integer word counts.
Only irrationality is needed here; the large-deviation restriction belongs
to the later asymptotic analysis.
-/

namespace Problems.Juggler.BeattySlope

open Finset PowerSeries

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

private noncomputable def survivorPoly (β : ℝ) (n : ℕ) : Poly :=
  ∑ w ∈ (survivorWords β) n, Polynomial.X ^ oddCount w

private noncomputable def descentPoly (β : ℝ) (n : ℕ) : Poly :=
  ∑ w ∈ (passageWords β) n, Polynomial.X ^ oddCount w

private noncomputable def survivorSeries (β : ℝ) : Series := mk (survivorPoly β)

private noncomputable def descentSeries (β : ℝ) : Series := 1 - mk (descentPoly β)

private theorem survivorPoly_zero (β : ℝ) : survivorPoly β 0 = 1 := by
  classical
  have hw : (survivorWords β) 0 = {[]} := by
    ext w
    simp only [survivorWords, allWords, mem_filter, mem_singleton]
    exact ⟨And.left, fun h => ⟨h, h ▸ survives_nil β⟩⟩
  simp [survivorPoly, hw, oddCount]

private theorem descentPoly_zero (β : ℝ) : descentPoly β 0 = 0 := by
  classical
  have hw : (passageWords β) 0 = ∅ := by
    simp [passageWords, allWords, FirstPassage]
  simp [descentPoly, hw]

private theorem survivorPoly_eval (β z : ℝ) (n : ℕ) :
    (survivorPoly β n).eval z = survivorWeight β z n := by
  simp [survivorPoly, Polynomial.eval_finsetSum, survivorWeight]

private theorem descentPoly_eval (β z : ℝ) (n : ℕ) :
    (descentPoly β n).eval z = passageWeight β z n := by
  simp [descentPoly, Polynomial.eval_finsetSum, passageWeight]

private theorem survivorPoly_step (β : ℝ) (n : ℕ) :
    survivorPoly β (n+1) + descentPoly β (n+1) =
      (1 + Polynomial.X) * survivorPoly β n := by
  classical
  rw [survivorPoly, descentPoly, ← sum_union ((survivors_disjoint_passages β) n),
    ← (extensions_eq_survivors_union_passages β),
    sum_biUnion (fun x _ y _ hne => extend_fiber_disjoint hne)]
  simp only [survivorPoly, mul_sum]
  apply sum_congr rfl
  intro w _
  have hne : w ++ [Branch.even] ≠ w ++ [Branch.odd] := fun h =>
    Branch.noConfusion (append_singleton_inj h).2
  rw [sum_pair hne]
  simp only [oddCount_append, oddCount, add_zero, pow_succ]
  ring

/-- The weighted survivor/first-passage partition is valid at every real
boundary and every real letter weight, including the unweighted case `z = 1`. -/
theorem survivorWeight_add_passageWeight (β z : ℝ) (n : ℕ) :
    survivorWeight β z (n+1) + passageWeight β z (n+1) =
      (1+z)*survivorWeight β z n := by
  simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one,
    Polynomial.eval_X, survivorPoly_eval, descentPoly_eval] using
    congrArg (Polynomial.eval z) (survivorPoly_step β n)

private theorem supported_survivor (β : ℝ) : supported (-β) 1 (survivorSeries β) := by
  classical
  intro n k hk
  simp only [survivorSeries, coeff_mk, survivorPoly, Polynomial.finsetSum_coeff]
  apply sum_eq_zero
  intro w hw
  have hlen := mem_allWords.1 (mem_filter.1 hw).1
  have hp := (mem_filter.1 hw).2
  have hle : β*n ≤ (oddCount w : ℝ) := by
    have h := hp w.length le_rfl
    rw [List.take_length, hlen] at h
    exact h
  have hne : k ≠ oddCount w := by
    intro h
    subst k
    linarith
  simp [Polynomial.coeff_X_pow, hne]

private theorem supported_descent (β : ℝ) : supported β (-1) (descentSeries β) := by
  classical
  intro n k hk
  cases n with
  | zero => simpa [descentSeries, (descentPoly_zero β)] using polySupported_one β (-1) k hk
  | succ n =>
    simp only [descentSeries, map_sub, coeff_one, Nat.succ_ne_zero, if_false,
      coeff_mk, zero_sub, Polynomial.coeff_neg, neg_eq_zero,
      descentPoly, Polynomial.finsetSum_coeff]
    apply sum_eq_zero
    intro w hw
    have hlen := mem_allWords.1 (mem_filter.1 hw).1
    have hg := (mem_filter.1 hw).2.2.1
    have hlt : (oddCount w : ℝ) < β*(n+1 : ℕ) := by
      simpa [Below, hlen] using hg
    have hne : k ≠ oddCount w := by
      intro h
      subst k
      nlinarith
    simp [Polynomial.coeff_X_pow, hne]

private noncomputable def stepSeries : Series := X * C (1 + Polynomial.X)

private noncomputable def unrestrictedSeries : Series :=
  mk fun n => (1 + Polynomial.X)^n

private theorem descent_factor (β : ℝ) : (descentSeries β) = (1-stepSeries)*(survivorSeries β) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [descentSeries, stepSeries, survivorSeries, (descentPoly_zero β), (survivorPoly_zero β)]
  | succ n =>
    simp only [descentSeries, map_sub, coeff_one, Nat.succ_ne_zero, if_false,
      coeff_mk, zero_sub, sub_mul, one_mul, stepSeries, mul_assoc,
      coeff_succ_X_mul, coeff_C_mul, survivorSeries]
    have h := (survivorPoly_step β) n
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

private theorem logDerivative_difference (β : ℝ) :
    logDerivative (survivorSeries β) - logDerivative (descentSeries β) =
      stepSeries * unrestrictedSeries := by
  have hf0 : constantCoeff (survivorSeries β) = (1 : Poly) := by
    simp [survivorSeries, (survivorPoly_zero β)]
  have hh0 : constantCoeff (descentSeries β) = (1 : Poly) := by
    simp [descentSeries, (descentPoly_zero β)]
  have hfi := mul_invOfUnit (survivorSeries β) 1 hf0
  have hhi := mul_invOfUnit (descentSeries β) 1 hh0
  have hfh : (survivorSeries β) * invOfUnit (descentSeries β) 1 = unrestrictedSeries := by
    calc
      _ = unrestrictedSeries * ((1-stepSeries)*(survivorSeries β)) *
          invOfUnit (descentSeries β) 1 := by
        rw [← mul_assoc unrestrictedSeries, mul_comm unrestrictedSeries,
          unrestricted_inverse]
        simp
      _ = unrestrictedSeries := by rw [← (descent_factor β), mul_assoc, hhi, mul_one]
  have hwh : (1-stepSeries) * invOfUnit (descentSeries β) 1 = invOfUnit (survivorSeries β) 1 := by
    calc
      _ = invOfUnit (survivorSeries β) 1 * ((1-stepSeries)*(survivorSeries β)) *
          invOfUnit (descentSeries β) 1 := by
        calc
          _ = ((survivorSeries β) * invOfUnit (survivorSeries β) 1) *
              ((1-stepSeries) * invOfUnit (descentSeries β) 1) := by rw [hfi, one_mul]
          _ = _ := by ring
      _ = invOfUnit (survivorSeries β) 1 := by rw [← (descent_factor β), mul_assoc, hhi, mul_one]
  have he : euler (descentSeries β) = -stepSeries*(survivorSeries β) +
      (1-stepSeries)*euler (survivorSeries β) := by
    rw [(descent_factor β), euler_mul, euler_sub, euler_one, euler_step, zero_sub]
  unfold logDerivative
  rw [he, add_mul]
  calc
    _ = euler (survivorSeries β) * invOfUnit (survivorSeries β) 1 +
        stepSeries * ((survivorSeries β) * invOfUnit (descentSeries β) 1) -
        euler (survivorSeries β) * ((1-stepSeries)*invOfUnit (descentSeries β) 1) := by ring
    _ = _ := by rw [hfh, hwh]; ring

private theorem logDerivative_zero (f : Series) : coeff 0 (logDerivative f) = 0 := by
  simp [logDerivative, euler]

private theorem supported_logDerivative {a b : ℝ} {f : Series}
    (hf : supported a b f) : supported a b (logDerivative f) :=
  supported_mul (supported_euler hf) (supported_inv hf)

private theorem logDerivative_survivor_coeff (β : ℝ) (hβ : Irrational β) (n k : ℕ) :
    (coeff n (logDerivative (survivorSeries β))).coeff k =
      if (n : ℝ)*β < k then (n.choose k : ℝ) else 0 := by
  cases n with
  | zero => cases k <;> simp [logDerivative_zero]
  | succ n =>
    have hdiff := congrArg (fun f : Series => (coeff (n+1) f).coeff k)
      (logDerivative_difference β)
    simp only [map_sub, Polynomial.coeff_sub, stepSeries, mul_assoc,
      coeff_succ_X_mul, coeff_C_mul, unrestrictedSeries, coeff_mk,
      ← pow_succ', Polynomial.coeff_one_add_X_pow] at hdiff
    by_cases h : (n+1 : ℕ)*β < (k : ℝ)
    · rw [if_pos h]
      have hz := supported_logDerivative (supported_descent β) (n+1) k (by linarith :
        β*(n+1 : ℕ) + (-1)*(k : ℝ) < 0)
      linarith
    · rw [if_neg h]
      have hne := mul_ne_nat hβ (by omega : 0 < n+1) k
      apply supported_logDerivative (supported_survivor β) (n+1) k
      have hh : (k : ℝ) < (n+1 : ℕ)*β := lt_of_le_of_ne (le_of_not_gt h) hne.symm
      linarith

private theorem logDerivative_survivor_eval (β : ℝ) (hβ : Irrational β) (z : ℝ) (n : ℕ) :
    (coeff n (logDerivative (survivorSeries β))).eval z = endpointWeight β z n := by
  have hd : (coeff n (logDerivative (survivorSeries β))).natDegree ≤ n := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.2
    intro k hk
    rw [(logDerivative_survivor_coeff β hβ), Nat.choose_eq_zero_of_lt hk]
    split_ifs <;> simp
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hd)]
  simp only [logDerivative_survivor_coeff β hβ, endpointWeight, ite_mul, zero_mul]

/-- The exact weighted positive-partial-sum recurrence for the actual
prefix-constrained word sums. Irrationality is the only boundary hypothesis;
the real odd-letter weight need not be positive for this algebraic identity. -/
theorem survivorWeight_recurrence (β : ℝ) (hβ : Irrational β) (z : ℝ) (n : ℕ) :
    (n : ℝ)*survivorWeight β z n =
      ∑ j ∈ range n, endpointWeight β z (n-j)*survivorWeight β z j := by
  have hf0 : constantCoeff (survivorSeries β) = (1 : Poly) := by
    simp [survivorSeries, (survivorPoly_zero β)]
  have he : euler (survivorSeries β) = (survivorSeries β) * logDerivative (survivorSeries β) := by
    unfold logDerivative
    calc
      _ = euler (survivorSeries β) * ((survivorSeries β) * invOfUnit (survivorSeries β) 1) := by
        rw [mul_invOfUnit (survivorSeries β) 1 hf0, mul_one]
      _ = _ := by ring
  have hc := congrArg (fun f : Series => (coeff n f).eval z) he
  rw [coeff_euler, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hc
  have hf (j : ℕ) : (coeff j (survivorSeries β)).eval z = survivorWeight β z j :=
    by simpa [survivorSeries] using survivorPoly_eval β z j
  simp only [Polynomial.eval_mul, Polynomial.eval_natCast, Polynomial.eval_finsetSum,
    hf, logDerivative_survivor_eval β hβ z] at hc
  rw [sum_range_succ] at hc
  simpa only [Nat.sub_self, endpointWeight_zero, mul_zero, zero_mul, add_zero, mul_comm] using hc

/-- The exact integer positive-partial-sum recurrence at every irrational
real boundary, recovered from the weighted word identity at weight one. -/
theorem survivorCount_recurrence (β : ℝ) (hβ : Irrational β) (n : ℕ) :
    n * survivorCount β n = ∑ j ∈ range n, endpointCount β (n-j)*survivorCount β j := by
  have h := survivorWeight_recurrence β hβ 1 n
  simp only [survivorWeight_one, endpointWeight_one] at h
  exact_mod_cast h

end Problems.Juggler.BeattySlope

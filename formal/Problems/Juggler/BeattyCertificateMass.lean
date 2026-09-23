import Problems.Juggler.BeattyEndpointAsymptotic

/-!
# Total first-passage mass at the critical Bernoulli tilt

The last-letter partition preserves probability and the centered first
moment. Certificate overshoots lie between `-beta` and zero. Thus surviving
first moments are bounded. Splitting surviving words by their endpoint
height and using the proved decay of `survivorNormalized` forces their
critical probability to zero and gives total certificate mass one.
-/

namespace Problems.Juggler.BeattyPhase

open Finset Filter Topology PaperBThreshold PaperBCertificates

private theorem beta_pos : 0 < beta := by linarith [beta_gt_five_eighths]
private theorem q_pos : 0 < 1-beta := sub_pos.2 beta_lt_one

/-- Critical Bernoulli weight of a length-`n` word with `k` odd letters. -/
noncomputable def criticalWordMass (n k : ℕ) : ℝ := (1-beta)^n*(beta/(1-beta))^k

private noncomputable def height (n k : ℕ) : ℝ := k-(n : ℝ)*beta

/-- Probability of surviving to depth `n` for Bernoulli parameter `beta`.
The finite word sum, rather than a probability-space construction, fixes the convention. -/
noncomputable def survivorCriticalMass (n : ℕ) : ℝ :=
  ∑ w ∈ neverNegWords n, criticalWordMass n (oddCount w)

/-- Probability of first descent exactly at depth `n` under the critical
Bernoulli tilt. Depth zero contributes zero. -/
noncomputable def certificateCriticalMass (n : ℕ) : ℝ :=
  ∑ w ∈ minimalCertWords n, criticalWordMass n (oddCount w)

private noncomputable def survivorMoment (n : ℕ) : ℝ :=
  ∑ w ∈ neverNegWords n, criticalWordMass n (oddCount w)*height n (oddCount w)

private noncomputable def certificateMoment (n : ℕ) : ℝ :=
  ∑ w ∈ minimalCertWords n, criticalWordMass n (oddCount w)*height n (oddCount w)

/-- Every finite critical word weight is strictly positive. -/
theorem criticalWordMass_pos (n k : ℕ) : 0 < criticalWordMass n k :=
  mul_pos (pow_pos q_pos _) (pow_pos (div_pos beta_pos q_pos) _)

private theorem extension_sum (f : ℕ → ℝ) (n : ℕ) :
    (∑ w ∈ neverNegWords (n+1), f (oddCount w)) +
      (∑ w ∈ minimalCertWords (n+1), f (oddCount w)) =
    ∑ w ∈ neverNegWords n, (f (oddCount w)+f (oddCount w+1)) := by
  classical
  rw [← sum_union (survivors_disjoint_certs n), ← extensions_eq_survivors_union_certs,
    sum_biUnion (fun x _ y _ hne => extend_fiber_disjoint hne)]
  apply sum_congr rfl
  intro w _
  have hne : w ++ [Branch.even] ≠ w ++ [Branch.odd] := fun h =>
    Branch.noConfusion (append_singleton_inj h).2
  rw [sum_pair hne]
  simp [oddCount_append, oddCount]

private theorem criticalWordMass_step (n k : ℕ) :
    criticalWordMass (n+1) k+criticalWordMass (n+1) (k+1) = criticalWordMass n k := by
  unfold criticalWordMass
  rw [pow_succ, pow_succ]
  field_simp [ne_of_gt q_pos]
  ring

private theorem wordMoment_step (n k : ℕ) :
    criticalWordMass (n+1) k*height (n+1) k +
      criticalWordMass (n+1) (k+1)*height (n+1) (k+1) = criticalWordMass n k*height n k := by
  unfold criticalWordMass height
  rw [pow_succ, pow_succ]
  push_cast
  field_simp [ne_of_gt q_pos]
  ring

private theorem probability_step (n : ℕ) :
    survivorCriticalMass (n+1)+certificateCriticalMass (n+1) = survivorCriticalMass n := by
  simpa only [survivorCriticalMass, certificateCriticalMass, criticalWordMass_step] using
    extension_sum (criticalWordMass (n+1)) n

private theorem moment_step (n : ℕ) :
    survivorMoment (n+1)+certificateMoment (n+1) = survivorMoment n := by
  simpa only [survivorMoment, certificateMoment, wordMoment_step] using
    extension_sum (fun k => criticalWordMass (n+1) k*height (n+1) k) n

private theorem gap_iff (n k : ℕ) :
    (3 : ℕ)^k < 2^n ↔ (k : ℝ) < n*beta := by
  have hcast : ((3 : ℕ)^k < 2^n) ↔ ((3 : ℝ)^k < 2^n) := by exact_mod_cast Iff.rfl
  rw [hcast, ← Real.log_lt_log_iff (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, PaperBThreshold.beta, ← mul_div_assoc,
    lt_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 3))]

private theorem survivor_height_nonneg {n : ℕ} {w : List Branch} (hw : w ∈ neverNegWords n) :
    0 ≤ height n (oddCount w) := by
  have hp := neverNeg_endpoint hw
  have h : ¬ (oddCount w : ℝ) < n*beta := fun h => (not_lt_of_ge hp) ((gap_iff _ _).2 h)
  unfold height
  linarith

private theorem certificate_height_bounds {n : ℕ} {w : List Branch}
    (hw : w ∈ minimalCertWords n) : -beta ≤ height n (oddCount w) ∧ height n (oddCount w) < 0 := by
  obtain ⟨hwlen, hwcert⟩ := mem_filter.1 hw
  have hlen := mem_allWords.1 hwlen
  have hn : 0 < n := by
    have hp := List.length_pos_iff.2 hwcert.1
    omega
  have hwin := minimalCert_window hwcert
  rw [hlen] at hwin
  have hlo := (gap_iff (n-1) (oddCount w)).not.1 (not_lt_of_ge hwin.1)
  have hhi := (gap_iff n (oddCount w)).1 hwin.2
  rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] at hlo
  unfold height
  constructor <;> linarith

private theorem survivorMass_nonneg (n : ℕ) : 0 ≤ survivorCriticalMass n :=
  sum_nonneg fun w _ => (criticalWordMass_pos n (oddCount w)).le

/-- First-descent probabilities are nonnegative. -/
theorem certificateCriticalMass_nonneg (n : ℕ) : 0 ≤ certificateCriticalMass n :=
  sum_nonneg fun w _ => (criticalWordMass_pos n (oddCount w)).le

private theorem moment_compensated_nonneg (n : ℕ) :
    0 ≤ certificateMoment n+beta*certificateCriticalMass n := by
  unfold certificateMoment certificateCriticalMass
  rw [mul_sum, ← sum_add_distrib]
  apply sum_nonneg
  intro w hw
  have h := mul_nonneg (criticalWordMass_pos n (oddCount w)).le
    (show 0 ≤ height n (oddCount w)+beta by linarith [(certificate_height_bounds hw).1])
  nlinarith

private theorem initial_values : survivorCriticalMass 0 = 1 ∧ survivorMoment 0 = 0 ∧
    certificateCriticalMass 0 = 0 := by
  have he : prefixNoncontracting [] := by intro k hk; simp [exponentGap]
  have hs : neverNegWords 0 = {[]} := by
    ext w
    simp only [neverNegWords, allWords, mem_filter, mem_singleton]
    exact ⟨And.left, fun h => ⟨h, h ▸ he⟩⟩
  have hc : minimalCertWords 0 = ∅ := by
    ext w
    simp only [minimalCertWords, allWords, mem_filter, mem_singleton, Finset.notMem_empty,
      iff_false, not_and]
    intro h
    subst w
    exact fun h => h.1 rfl
  simp [survivorCriticalMass, survivorMoment, certificateCriticalMass, hs, hc, criticalWordMass, height, oddCount]

private theorem survivorMoment_bound (n : ℕ) : survivorMoment n ≤ beta := by
  have hcomp : survivorMoment n+beta*survivorCriticalMass n ≤ beta := by
    induction n with
    | zero => rw [initial_values.1, initial_values.2.1]; simp
    | succ n ih =>
      have hp := probability_step n
      have hm := moment_step n
      have hc := moment_compensated_nonneg (n+1)
      rw [← hp, ← hm] at ih
      nlinarith
  have hp := mul_nonneg beta_pos.le (survivorMass_nonneg n)
  linarith

private theorem tilt_log_pos : 0 < Real.log (beta/(1-beta)) := by
  apply Real.log_pos
  exact (one_lt_div q_pos).2 (by linarith [beta_gt_five_eighths])

/-- The entropy normalization isolates the centered endpoint height exactly. -/
theorem criticalWordMass_eq_exp (n k : ℕ) :
    criticalWordMass n k = Real.exp (((k : ℝ)-(n : ℝ)*beta)*Real.log (beta/(1-beta)))/survivorBase^n := by
  have he : Real.log (criticalWordMass n k) =
      height n k*Real.log (beta/(1-beta))-(n : ℝ)*Real.log survivorBase := by
    unfold criticalWordMass height
    rw [Real.log_mul (ne_of_gt (pow_pos q_pos n))
        (ne_of_gt (pow_pos (div_pos beta_pos q_pos) k)),
      Real.log_pow, Real.log_pow, Real.log_div (ne_of_gt beta_pos) (ne_of_gt q_pos),
      log_survivorBase]
    ring
  calc
    criticalWordMass n k = Real.exp (Real.log (criticalWordMass n k)) := (Real.exp_log (criticalWordMass_pos n k)).symm
    _ = _ := by
      rw [he, Real.exp_sub, Real.exp_nat_mul, Real.exp_log survivorBase_pos]
      rfl

private theorem survivorMass_height_split {H : ℝ} (hH : 0 < H) (n : ℕ) :
    survivorCriticalMass n ≤ survivorNormalized n*Real.exp (H*Real.log (beta/(1-beta)))+beta/H := by
  have hterm (w : List Branch) (hw : w ∈ neverNegWords n) :
      criticalWordMass n (oddCount w) ≤ Real.exp (H*Real.log (beta/(1-beta)))/survivorBase^n +
        criticalWordMass n (oddCount w)*height n (oddCount w)/H := by
    have hheight := survivor_height_nonneg hw
    by_cases hh : height n (oddCount w) ≤ H
    · have he : criticalWordMass n (oddCount w) ≤ Real.exp (H*Real.log (beta/(1-beta)))/survivorBase^n := by
        rw [criticalWordMass_eq_exp]
        exact div_le_div_of_nonneg_right (Real.exp_le_exp.2
          (mul_le_mul_of_nonneg_right hh tilt_log_pos.le)) (pow_pos survivorBase_pos n).le
      have hp := div_nonneg (mul_nonneg (criticalWordMass_pos n (oddCount w)).le hheight) hH.le
      linarith
    · have hm : criticalWordMass n (oddCount w) ≤ criticalWordMass n (oddCount w)*height n (oddCount w)/H := by
        apply (le_div_iff₀ hH).2
        exact mul_le_mul_of_nonneg_left (le_of_not_ge hh) (criticalWordMass_pos n (oddCount w)).le
      have hp : 0 ≤ Real.exp (H*Real.log (beta/(1-beta)))/survivorBase^n := by
        exact div_nonneg (Real.exp_pos _).le (pow_pos survivorBase_pos n).le
      linarith
  have hsum := sum_le_sum hterm
  rw [sum_add_distrib, sum_const, nsmul_eq_mul, ← sum_div] at hsum
  have he : (neverNegWords n).card * (Real.exp (H*Real.log (beta/(1-beta)))/survivorBase^n) =
      survivorNormalized n*Real.exp (H*Real.log (beta/(1-beta))) := by
    unfold survivorNormalized neverNegCount
    ring
  rw [he] at hsum
  exact hsum.trans (add_le_add_right (div_le_div_of_nonneg_right (survivorMoment_bound n) hH.le) _)

/-- Critical survival probability tends to zero. This follows from finite
first-moment bookkeeping and the proved survivor coefficient decay. -/
theorem survivorCriticalMass_tendsto_zero : Tendsto survivorCriticalMass atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  let H := 2*beta/ε
  have hH : 0 < H := by dsimp [H]; exact div_pos (mul_pos (by norm_num) beta_pos) hε
  have hhalf : beta/H = ε/2 := by dsimp [H]; field_simp [ne_of_gt beta_pos]
  have hlim := summable_survivorNormalized_unconditional.tendsto_atTop_zero.mul_const
    (Real.exp (H*Real.log (beta/(1-beta))))
  simp only [zero_mul] at hlim
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hlim (ε/2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hnear := hN n hn
  rw [Real.dist_eq, sub_zero] at hnear
  have hupper := survivorMass_height_split hH n
  rw [hhalf] at hupper
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (survivorMass_nonneg n)]
  linarith [le_abs_self (survivorNormalized n*Real.exp (H*Real.log (beta/(1-beta))))]

private theorem partial_mass (n : ℕ) :
    (∑ j ∈ range (n+1), certificateCriticalMass j)+survivorCriticalMass n = 1 := by
  induction n with
  | zero => simp [initial_values.1, initial_values.2.2]
  | succ n ih =>
    rw [sum_range_succ]
    linarith [probability_step n]

/-- The actual first-descent words carry total critical Bernoulli probability
one. In particular, no escape mass is left at infinite depth. -/
theorem certificateCriticalMass_hasSum : HasSum certificateCriticalMass 1 := by
  apply (hasSum_iff_tendsto_nat_of_nonneg certificateCriticalMass_nonneg 1).2
  have h : Tendsto (fun n : ℕ => ∑ j ∈ range (n+1), certificateCriticalMass j) atTop (𝓝 1) := by
    have hl := (tendsto_const_nhds (x := (1 : ℝ))).sub survivorCriticalMass_tendsto_zero
    simp only [sub_zero] at hl
    apply hl.congr'
    exact Eventually.of_forall fun n => by linarith [partial_mass n]
  exact (tendsto_add_atTop_iff_nat 1).1 h

/-- The certificate window in real endpoint coordinates, with its exact
weak lower and strict upper inequalities. -/
theorem certWindow_iff_endpoint (n r : ℕ) : CertWindow (n+1) r ↔
    (n : ℝ)*beta ≤ r ∧ (r : ℝ) < (n+1 : ℕ)*beta := by
  simp only [CertWindow, Nat.add_sub_cancel_right]
  constructor
  · rintro ⟨hl, hu⟩
    exact ⟨not_lt.1 (fun h => (not_lt_of_ge hl) ((gap_iff n r).2 h)), (gap_iff _ _).1 hu⟩
  · rintro ⟨hl, hu⟩
    exact ⟨not_lt.1 (fun h => (not_lt_of_ge hl) ((gap_iff n r).1 h)), (gap_iff _ _).2 hu⟩

/-- Within a certificate window all first-descent words have the same odd
count, so the critical mass is the integer count times one word weight. -/
theorem certificateCriticalMass_of_window {n r : ℕ} (hw : CertWindow n r) :
    certificateCriticalMass n = (minimalCertCount n : ℝ)*criticalWordMass n r := by
  unfold certificateCriticalMass
  have he : ∀ w ∈ minimalCertWords n, oddCount w = r := by
    intro w hw'
    have hlen := mem_allWords.1 (mem_filter.1 hw').1
    have hwin := minimalCert_window (mem_filter.1 hw').2
    rw [hlen] at hwin
    exact certWindow_unique hwin hw
  simp only [sum_congr rfl (fun w hw' => congrArg (criticalWordMass n) (he w hw')),
    sum_const, nsmul_eq_mul, minimalCertCount]

/-- There is no first descent at depth zero. -/
theorem certificateCriticalMass_zero : certificateCriticalMass 0 = 0 := initial_values.2.2

end Problems.Juggler.BeattyPhase

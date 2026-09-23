import Problems.Juggler.BeattyCounting
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Coarse terminal binomial bounds

The strict endpoint tail starts at `floor (n * beta) + 1`. Its consecutive
terms have ratio at most `3/5`, so the whole tail lies between its first
term and `5/2` times that term. Coarse Stirling bounds supply the square-root
scale; no limiting phase or continuity of a profile is needed.
-/

namespace Problems.Juggler.BeattyPhase

open Finset Filter Topology
open PaperBThreshold

/-- First integer strictly above the endpoint threshold. -/
noncomputable def endpointCutoff (n : ℕ) : ℕ := ⌊(n : ℝ)*beta⌋₊ + 1

private theorem beta_pos : 0 < beta := by linarith [beta_gt_five_eighths]

/-- The strict cutoff exceeds the real threshold by at most one. -/
theorem endpointCutoff_bounds (n : ℕ) :
    (n : ℝ)*beta < endpointCutoff n ∧ (endpointCutoff n : ℝ) ≤ n*beta+1 := by
  constructor
  · simpa [endpointCutoff] using Nat.lt_floor_add_one ((n : ℝ)*beta)
  · have h := Nat.floor_le (mul_nonneg (Nat.cast_nonneg n) beta_pos.le)
    dsimp [endpointCutoff]
    push_cast
    linarith

/-- At positive depth the strict cutoff is a valid binomial index. -/
theorem endpointCutoff_le {n : ℕ} (hn : 0 < n) : endpointCutoff n ≤ n := by
  apply Nat.succ_le_of_lt
  apply (Nat.floor_lt (mul_nonneg (Nat.cast_nonneg n) beta_pos.le)).2
  exact mul_lt_of_lt_one_right (by exact_mod_cast hn) beta_lt_one

/-- The endpoint count is exactly the binomial tail starting at the strict cutoff. -/
theorem endpointCount_eq_tail (n : ℕ) :
    endpointCount n = ∑ k ∈ Ico (endpointCutoff n) (n+1), n.choose k := by
  have hh (k : ℕ) : (n : ℝ)*beta < k ↔ endpointCutoff n ≤ k := by
    rw [← Nat.floor_lt (mul_nonneg (Nat.cast_nonneg n) beta_pos.le)]
    exact Nat.lt_iff_add_one_le
  simp only [endpointCount, hh, ← sum_filter]
  congr 1
  ext k
  simp only [mem_filter, mem_range, mem_Ico]
  exact and_comm

private theorem choose_step_bound {n k : ℕ} (hk : endpointCutoff n ≤ k) :
    (n.choose (k+1) : ℝ) ≤ (3/5 : ℝ)*(n.choose k : ℝ) := by
  by_cases hkn : k ≤ n
  · have hkR : (n : ℝ)*beta < k :=
      (endpointCutoff_bounds n).1.trans_le (by exact_mod_cast hk)
    have hratio : (5 : ℝ)*(n-k : ℕ) ≤ 3*(k+1 : ℕ) := by
      rw [Nat.cast_sub hkn, Nat.cast_add, Nat.cast_one]
      have h := mul_le_mul_of_nonneg_left beta_gt_five_eighths.le (Nat.cast_nonneg n)
      nlinarith
    have he : (n.choose (k+1) : ℝ)*(k+1 : ℕ) =
        (n.choose k : ℝ)*(n-k : ℕ) := by
      exact_mod_cast Nat.choose_succ_right_eq n k
    have hm := mul_le_mul_of_nonneg_left hratio (Nat.cast_nonneg (n.choose k) : (0:ℝ) ≤ _)
    have hp : (0 : ℝ) < (k+1 : ℕ) := by positivity
    nlinarith
  · rw [Nat.choose_eq_zero_of_lt (by omega : n < k+1)]
    simp only [Nat.cast_zero]
    positivity

/-- A summable geometric majorant for binomial terms beyond the strict cutoff. -/
theorem endpoint_choose_shift_bound (n j : ℕ) :
    (n.choose (endpointCutoff n+j) : ℝ) ≤
      (n.choose (endpointCutoff n) : ℝ)*(3/5 : ℝ)^j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hs := choose_step_bound (n := n) (k := endpointCutoff n+j) (by omega)
    calc
      _ ≤ (3/5 : ℝ)*(n.choose (endpointCutoff n+j) : ℝ) := by simpa [Nat.add_assoc] using hs
      _ ≤ (3/5 : ℝ)*((n.choose (endpointCutoff n) : ℝ)*(3/5 : ℝ)^j) :=
        mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := by rw [pow_succ]; ring

/-- Uniform first-term comparison for the actual strict binomial tail.
This finite inequality is independent of Stirling and all phase asymptotics. -/
theorem endpointCount_first_term_bounds {n : ℕ} (hn : 0 < n) :
    (n.choose (endpointCutoff n) : ℝ) ≤ endpointCount n ∧
      (endpointCount n : ℝ) ≤ (5/2 : ℝ)*(n.choose (endpointCutoff n) : ℝ) := by
  rw [endpointCount_eq_tail, Nat.cast_sum]
  constructor
  · exact single_le_sum (fun _ _ => Nat.cast_nonneg _) (mem_Ico.2 ⟨le_rfl, by
      have h := endpointCutoff_le hn; omega⟩)
  · rw [sum_Ico_eq_sum_range]
    have hgeom (m : ℕ) : ∑ j ∈ range m, (3/5 : ℝ)^j ≤ 5/2 := by
      have h := geom_sum_mul (3/5 : ℝ) m
      have hp := pow_nonneg (by norm_num : (0 : ℝ) ≤ 3/5) m
      nlinarith
    calc
      _ ≤ ∑ j ∈ range (n+1-endpointCutoff n),
          (n.choose (endpointCutoff n) : ℝ)*(3/5 : ℝ)^j :=
        sum_le_sum fun j _ => endpoint_choose_shift_bound n j
      _ = (n.choose (endpointCutoff n) : ℝ)*
          (∑ j ∈ range (n+1-endpointCutoff n), (3/5 : ℝ)^j) := by rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hgeom _) (Nat.cast_nonneg _) |>.trans_eq (mul_comm _ _)

private noncomputable def factorialLogError (n : ℕ) : ℝ :=
  Real.log (n.factorial : ℝ) - (((n : ℝ)+1/2)*Real.log n-n)

private theorem factorialLogError_eq {n : ℕ} (hn : 0 < n) :
    factorialLogError n = Real.log (Stirling.stirlingSeq n) + Real.log 2/2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Stirling.stirlingSeq, Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_sqrt (by positivity),
    Real.log_mul (by norm_num) (ne_of_gt hnR), Real.log_pow,
    Real.log_div (ne_of_gt hnR) (ne_of_gt (Real.exp_pos 1)), Real.log_exp]
  unfold factorialLogError
  ring

private theorem factorialLogError_bounds {n : ℕ} (hn : 0 < n) :
    0 ≤ factorialLogError n ∧ factorialLogError n ≤ 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [factorialLogError_eq (by omega)]
  have hlo := Stirling.log_stirlingSeq_bounded_by_constant m
  have hup := Stirling.log_stirlingSeq'_antitone (show 0 ≤ m from Nat.zero_le _)
  simp only [Function.comp_apply, Stirling.stirlingSeq_one,
    Real.log_div (ne_of_gt (Real.exp_pos 1)) (show Real.sqrt (2 : ℝ) ≠ 0 by positivity), Real.log_exp,
    Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at hup
  constructor <;> linarith

/-- The entropy growth base is strictly positive. -/
theorem survivorBase_pos : 0 < survivorBase := by
  unfold survivorBase
  have h := PaperBSurvivorAsymptotic.rateBase_pos
  positivity

/-- The logarithm of the growth base is binary entropy at the threshold. -/
theorem log_survivorBase : Real.log survivorBase =
    -beta*Real.log beta-(1-beta)*Real.log (1-beta) := by
  have hb := beta_pos
  have hq : 0 < 1-beta := sub_pos.2 beta_lt_one
  have he : survivorBase = beta^(-beta)*(1-beta)^(beta-1) := by
    unfold survivorBase PaperBSurvivorAsymptotic.rateBase PaperBChernoff.theta
    ring
  rw [he, Real.log_mul (by positivity) (by positivity),
    Real.log_rpow beta_pos, Real.log_rpow hq]
  ring

private theorem entropy_correction {t k l : ℝ} (ht : 0 < t) (hk : 0 < k)
    (hl : 0 < l) (hsum : k+l=t) (hlo : t*beta ≤ k) (hup : k ≤ t*beta+1) :
    Real.log ((1-beta)/beta)-1/beta ≤
      t*Real.log t-k*Real.log k-l*Real.log l-t*Real.log survivorBase ∧
    t*Real.log t-k*Real.log k-l*Real.log l-t*Real.log survivorBase ≤ 0 := by
  have hq : 0 < 1-beta := sub_pos.2 beta_lt_one
  have hbp := beta_pos
  have htp : 0 < t*beta := mul_pos ht hbp
  have htq : 0 < t*(1-beta) := mul_pos ht hq
  let D := k*Real.log (k/(t*beta)) + l*Real.log (l/(t*(1-beta)))
  have hD0 : 0 ≤ D := by
    have ha := mul_le_mul_of_nonneg_left
      (Real.one_sub_inv_le_log_of_pos (div_pos hk htp)) hk.le
    have hb := mul_le_mul_of_nonneg_left
      (Real.one_sub_inv_le_log_of_pos (div_pos hl htq)) hl.le
    have ha' : k*(1-(k/(t*beta))⁻¹) = k-t*beta := by field_simp
    have hb' : l*(1-(l/(t*(1-beta)))⁻¹) = l-t*(1-beta) := by field_simp
    rw [ha'] at ha
    rw [hb'] at hb
    dsimp [D]
    nlinarith
  have hD1 : D ≤ 1/beta := by
    have ha := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hk htp)) hk.le
    have hb : l*Real.log (l/(t*(1-beta))) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hl.le (Real.log_nonpos (by positivity)
        ((div_le_one htq).2 (by nlinarith)))
    have he : k*(k/(t*beta)-1) = k*(k-t*beta)/(t*beta) := by field_simp
    rw [he] at ha
    have hc : k*(k-t*beta)/(t*beta) ≤ k/(t*beta) := by
      apply div_le_div_of_nonneg_right _ htp.le
      nlinarith
    have hd : k/(t*beta) ≤ 1/beta := by
      apply (div_le_iff₀ htp).2
      have he' : 1/beta*(t*beta) = t := by field_simp
      rw [he']
      linarith
    dsimp [D]
    linarith
  have hlog : Real.log ((1-beta)/beta) ≤ 0 :=
    Real.log_nonpos (by positivity) ((div_le_one hbp).2 (by linarith [beta_gt_five_eighths]))
  have hdl : Real.log ((1-beta)/beta) ≤ (k-t*beta)*Real.log ((1-beta)/beta) := by
    nlinarith
  have hdu : (k-t*beta)*Real.log ((1-beta)/beta) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) hlog
  have he : t*Real.log t-k*Real.log k-l*Real.log l-t*Real.log survivorBase =
      -D+(k-t*beta)*Real.log ((1-beta)/beta) := by
    dsimp [D]
    rw [log_survivorBase, Real.log_div (ne_of_gt hk) (ne_of_gt htp),
      Real.log_div (ne_of_gt hl) (ne_of_gt htq),
      Real.log_mul (ne_of_gt ht) (ne_of_gt hbp),
      Real.log_mul (ne_of_gt ht) (ne_of_gt hq),
      Real.log_div (ne_of_gt hq) (ne_of_gt hbp), ← hsum]
    ring
  rw [he]
  constructor <;> linarith

/-- The first strict binomial term with its exponential and square-root scales removed. -/
noncomputable def endpointFirstTermScaled (n : ℕ) : ℝ :=
  Real.sqrt n * (n.choose (endpointCutoff n) : ℝ) / survivorBase^n

/-- The scaled first term is positive at every positive depth. -/
theorem endpointFirstTermScaled_pos {n : ℕ} (hn : 0 < n) : 0 < endpointFirstTermScaled n := by
  have hv := survivorBase_pos
  have hc : (0 : ℝ) < n.choose (endpointCutoff n) := by
    exact_mod_cast Nat.choose_pos (endpointCutoff_le hn)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold endpointFirstTermScaled
  positivity

private theorem firstTermScaled_log_bounds {n : ℕ} (hn : 6 ≤ n) :
    Real.log ((1-beta)/beta)-1/beta-2 ≤ Real.log (endpointFirstTermScaled n) ∧
      Real.log (endpointFirstTermScaled n) ≤ 1+Real.log 6 := by
  let k := endpointCutoff n
  let l := n-k
  have hn0 : 0 < n := by omega
  have hkn : k ≤ n := endpointCutoff_le hn0
  have hs : k+l=n := Nat.add_sub_of_le hkn
  have hsR : (k : ℝ)+l=n := by exact_mod_cast hs
  have ht : (0 : ℝ) < n := by exact_mod_cast hn0
  have hnR : (6 : ℝ) ≤ n := by exact_mod_cast hn
  have hb := endpointCutoff_bounds n
  change (n : ℝ)*beta < (k : ℝ) ∧ (k : ℝ) ≤ n*beta+1 at hb
  have hkr : (n : ℝ)/6 ≤ k ∧ (k : ℝ) ≤ 5*n/6 := by
    constructor
    · have h := mul_le_mul_of_nonneg_left beta_gt_five_eighths.le ht.le
      nlinarith
    · have h := mul_le_mul_of_nonneg_left beta_le_two_thirds ht.le
      nlinarith
  have hlr : (n : ℝ)/6 ≤ l ∧ (l : ℝ) ≤ n := by constructor <;> nlinarith
  have hk : (0 : ℝ) < k := by linarith
  have hl : (0 : ℝ) < l := by linarith
  have hkN : 0 < k := by exact_mod_cast hk
  have hlN : 0 < l := by exact_mod_cast hl
  have hfN := factorialLogError_bounds hn0
  have hfK := factorialLogError_bounds hkN
  have hfL := factorialLogError_bounds hlN
  have he := entropy_correction ht hk hl hsR hb.1.le hb.2
  have hlogK : -Real.log 6 ≤ Real.log ((k : ℝ)/n) ∧ Real.log ((k : ℝ)/n) ≤ 0 := by
    constructor
    · have hx : (1/6 : ℝ) ≤ (k : ℝ)/n := (le_div_iff₀ ht).2 (by linarith [hkr.1])
      simpa using Real.log_le_log (by norm_num : (0 : ℝ) < 1/6) hx
    · exact Real.log_nonpos (by positivity) ((div_le_one ht).2 (by linarith [hkr.2]))
  have hlogL : -Real.log 6 ≤ Real.log ((l : ℝ)/n) ∧ Real.log ((l : ℝ)/n) ≤ 0 := by
    constructor
    · have hx : (1/6 : ℝ) ≤ (l : ℝ)/n := (le_div_iff₀ ht).2 (by linarith [hlr.1])
      simpa using Real.log_le_log (by norm_num : (0 : ℝ) < 1/6) hx
    · exact Real.log_nonpos (by positivity) ((div_le_one ht).2 hlr.2)
  have hc : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hkn
  have hf : (n.choose k : ℝ)*(k.factorial : ℝ)*(l.factorial : ℝ) = n.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkn
  have hfLog := congrArg Real.log hf
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (ne_of_gt hc) (by positivity)] at hfLog
  have heq : Real.log (endpointFirstTermScaled n) =
      factorialLogError n-factorialLogError k-factorialLogError l +
      ((n : ℝ)*Real.log n-k*Real.log k-l*Real.log l-n*Real.log survivorBase) -
      (Real.log ((k : ℝ)/n)+Real.log ((l : ℝ)/n))/2 := by
    change Real.log (Real.sqrt n*(n.choose k : ℝ)/survivorBase^n) = _
    rw [Real.log_div (by positivity) (ne_of_gt (pow_pos survivorBase_pos n)),
      Real.log_mul (by positivity) (ne_of_gt hc), Real.log_sqrt ht.le, Real.log_pow,
      Real.log_div (ne_of_gt hk) (ne_of_gt ht), Real.log_div (ne_of_gt hl) (ne_of_gt ht)]
    dsimp [factorialLogError]
    linarith
  rw [heq]
  constructor <;> linarith

private theorem finite_positive_bounds (f : ℕ → ℝ) (hf : ∀ n, 0 < n → 0 < f n)
    (N : ℕ) : ∃ a K : ℝ, 0 < a ∧ 0 ≤ K ∧ ∀ n, 0 < n → n ≤ N → a ≤ f n ∧ f n ≤ K := by
  induction N with
  | zero => exact ⟨1, 1, by norm_num, by norm_num, fun n hn hN => by omega⟩
  | succ N ih =>
    obtain ⟨a, K, ha, hK, h⟩ := ih
    refine ⟨min a (f (N+1)), max K (f (N+1)), lt_min ha (hf _ (by omega)),
      hK.trans (le_max_left _ _), fun n hn hN => ?_⟩
    by_cases he : n = N+1
    · subst n; exact ⟨min_le_right _ _, le_max_right _ _⟩
    · have hh := h n hn (by omega)
      exact ⟨(min_le_left _ _).trans hh.1, hh.2.trans (le_max_left _ _)⟩

private theorem firstTermScaled_bounds :
    ∃ a K : ℝ, 0 < a ∧ 0 ≤ K ∧ ∀ n : ℕ, 0 < n →
      a ≤ endpointFirstTermScaled n ∧ endpointFirstTermScaled n ≤ K := by
  obtain ⟨a, K, ha, hK, h⟩ := finite_positive_bounds endpointFirstTermScaled
    (fun _ hn => endpointFirstTermScaled_pos hn) 5
  let a' := Real.exp (Real.log ((1-beta)/beta)-1/beta-2)
  let K' := Real.exp (1+Real.log 6)
  refine ⟨min a a', max K K', lt_min ha (Real.exp_pos _),
    hK.trans (le_max_left _ _), fun n hn => ?_⟩
  by_cases hsmall : n ≤ 5
  · exact ⟨(min_le_left _ _).trans (h n hn hsmall).1,
      (h n hn hsmall).2.trans (le_max_left _ _)⟩
  · have hh := firstTermScaled_log_bounds (by omega : 6 ≤ n)
    have hlo : a' ≤ endpointFirstTermScaled n := by
      simpa [a', Real.exp_log (endpointFirstTermScaled_pos hn)] using Real.exp_le_exp.2 hh.1
    have hup : endpointFirstTermScaled n ≤ K' := by
      simpa [K', Real.exp_log (endpointFirstTermScaled_pos hn)] using Real.exp_le_exp.2 hh.2
    exact ⟨(min_le_right _ _).trans hlo, hup.trans (le_max_right _ _)⟩

/-- Unconditional coarse square-root bounds for the actual entropy-normalized
terminal binomial tail. Constants are existential, positive on the lower
side, and uniform over every positive integer depth. -/
theorem endpointNormalized_sqrt_bounds :
    ∃ a K : ℝ, 0 < a ∧ 0 ≤ K ∧ ∀ n : ℕ, 0 < n →
      a / Real.sqrt n ≤ endpointNormalized n ∧
      endpointNormalized n ≤ K / Real.sqrt n := by
  obtain ⟨a, K, ha, hK, h⟩ := firstTermScaled_bounds
  refine ⟨a, (5/2)*K, ha, by positivity, fun n hn => ?_⟩
  have hv := pow_pos survivorBase_pos n
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq := Real.sqrt_pos.2 hnR
  have hc := endpointCount_first_term_bounds hn
  have hl := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hc.1 hsq.le) hv.le
  have hu := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hc.2 hsq.le) hv.le
  have hlo : a ≤ endpointNormalized n * Real.sqrt n := by
    calc
      _ ≤ endpointFirstTermScaled n := (h n hn).1
      _ ≤ _ := by simpa [endpointFirstTermScaled, endpointNormalized, mul_div_assoc, mul_comm] using hl
  have hup : endpointNormalized n * Real.sqrt n ≤ (5/2)*K := by
    calc
      _ ≤ (5/2)*endpointFirstTermScaled n := by
        simpa only [endpointNormalized, endpointFirstTermScaled, div_eq_mul_inv,
          mul_assoc, mul_left_comm, mul_comm] using hu
      _ ≤ _ := mul_le_mul_of_nonneg_left (h n hn).2 (by norm_num)
  exact ⟨(div_le_iff₀ hsq).2 hlo, (le_div_iff₀ hsq).2 hup⟩

/-- Sharp three-halves order for the actual survivor counts after entropy
normalization. Both constants are positive and the bounds hold for every
positive depth. No counting identity, terminal estimate, or phase-limit
hypothesis remains. -/
theorem survivor_three_halves_bounds :
    ∃ a U : ℝ, 0 < a ∧ 0 < U ∧ ∀ n : ℕ, 0 < n →
      a / ((n : ℝ)*Real.sqrt n) ≤ survivorNormalized n ∧
      survivorNormalized n ≤ U / ((n : ℝ)*Real.sqrt n) := by
  obtain ⟨a, K, ha, hK, h⟩ := endpointNormalized_sqrt_bounds
  obtain ⟨U, _, hU⟩ := survivor_three_halves_bounds_of_terminal_bounds
    survivor_exponential_identity hK (fun n hn => (h n hn).2) (fun n hn => (h n hn).1)
  have hp : 0 < U := by
    have hh := hU 1 (by omega)
    norm_num at hh
    linarith
  exact ⟨a, U, ha, hp, hU⟩

/-- The actual entropy-normalized survivor counts are summable without
assuming the terminal phase asymptotic. This discharges the premise of the
previous uniform profile-truncation and profile-bound theorems. -/
theorem summable_survivorNormalized_unconditional : Summable survivorNormalized := by
  obtain ⟨_, K, _, _, h⟩ := endpointNormalized_sqrt_bounds
  have hnn (n : ℕ) : 0 ≤ endpointNormalized n :=
    div_nonneg (Nat.cast_nonneg _) (pow_nonneg survivorBase_pos.le _)
  have hAbs (n : ℕ) (hn : 0 < n) : |endpointNormalized n| ≤ K/Real.sqrt n := by
    rw [abs_of_nonneg (hnn n)]
    exact (h n hn).2
  exact (summable_renewalCoeff hnn (summable_renewalLogCoeff_of_bound hAbs)).congr
    (fun n => (survivor_exponential_identity n).symm)

private theorem density_eq_normalized_mul_model {n : ℕ} (hn : 0 < n) :
    PaperBSurvivorAsymptotic.survivorDensity n =
      ((n : ℝ)*Real.sqrt n*survivorNormalized n)*PaperBSurvivorAsymptotic.model n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpower : (n : ℝ)^(-(3 : ℝ)/2) = ((n : ℝ)*Real.sqrt n)⁻¹ := by
    rw [show -(3 : ℝ)/2 = -(1+1/2) by norm_num, Real.rpow_neg hnR.le,
      Real.rpow_add hnR, Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hr := PaperBSurvivorAsymptotic.rateBase_pos
  have hsq := Real.sqrt_pos.2 hnR
  simp only [PaperBSurvivorAsymptotic.survivorDensity, PaperBSurvivorAsymptotic.model,
    survivorNormalized, survivorBase, hpower, mul_pow]
  field_simp

/-- The actual survivor density is of sharp order `rateBase^n * n^(-3/2)`.
This proves the previously conditional Paper B sharp-order comparison with
no hypothesis on a phase profile or on the counting identity. It concerns
parity words, not termination of integer trajectories. -/
theorem survivorDensity_isTheta_model :
    PaperBSurvivorAsymptotic.survivorDensity =Θ[atTop] PaperBSurvivorAsymptotic.model := by
  obtain ⟨a, U, ha, hU, h⟩ := survivor_three_halves_bounds
  have hb (n : ℕ) (hn : 0 < n) :
      a*PaperBSurvivorAsymptotic.model n ≤ PaperBSurvivorAsymptotic.survivorDensity n ∧
      PaperBSurvivorAsymptotic.survivorDensity n ≤ U*PaperBSurvivorAsymptotic.model n := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hd : (0 : ℝ) < (n : ℝ)*Real.sqrt n := by positivity
    have hm := PaperBSurvivorAsymptotic.model_pos hn
    have hl := (div_le_iff₀ hd).1 (h n hn).1
    have hu := (le_div_iff₀ hd).1 (h n hn).2
    rw [density_eq_normalized_mul_model hn]
    constructor
    · exact mul_le_mul_of_nonneg_right (by simpa [mul_comm] using hl) hm.le
    · exact mul_le_mul_of_nonneg_right (by simpa [mul_comm] using hu) hm.le
  constructor
  · refine Asymptotics.isBigO_iff.2 ⟨U, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hm := PaperBSurvivorAsymptotic.model_pos hn
    have hs : 0 ≤ PaperBSurvivorAsymptotic.survivorDensity n := by
      unfold PaperBSurvivorAsymptotic.survivorDensity
      positivity
    simpa [Real.norm_eq_abs, abs_of_nonneg hs, abs_of_nonneg hm.le] using (hb n hn).2
  · refine Asymptotics.isBigO_iff.2 ⟨1/a, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hm := PaperBSurvivorAsymptotic.model_pos hn
    have hh := (hb n hn).1
    have hs : 0 ≤ PaperBSurvivorAsymptotic.survivorDensity n := (mul_pos ha hm).le.trans hh
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hm.le, abs_of_nonneg hs]
    calc
      _ = (a*PaperBSurvivorAsymptotic.model n)/a := by field_simp
      _ ≤ PaperBSurvivorAsymptotic.survivorDensity n/a :=
        div_le_div_of_nonneg_right hh ha.le
      _ = _ := by ring

end Problems.Juggler.BeattyPhase

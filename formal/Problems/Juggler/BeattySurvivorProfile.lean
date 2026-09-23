import Problems.Juggler.BeattyRenewalSeries
import Problems.Juggler.PaperBSurvivorAsymptotic

/-!
# The survivor profile with its two classical inputs exposed

This module uses the existing `neverNegCount` and logarithmic slope. It proves
the phase asymptotic from an explicit formal exponential identity and the
explicit terminal binomial asymptotic. Neither classical input is asserted
here. The series manipulation and moving-phase limit are kernel-checked.
-/

namespace Problems.Juggler.BeattyPhase

open Filter Topology Finset
open PaperBThreshold PaperBSurvivorAsymptotic

/-- Entropy normalization of the survivor counts, equal to twice the
existing exponential rate for survivor density. -/
noncomputable def survivorBase : ℝ := 2*rateBase

/-- The exact terminal positive-endpoint binomial count. At the irrational
slope the strict inequality is the positive-partial-sum convention. -/
noncomputable def endpointCount (n : ℕ) : ℕ :=
  ∑ k ∈ range (n+1), if (n : ℝ)*beta < k then n.choose k else 0

/-- Terminal binomial counts after removing their exponential rate. -/
noncomputable def endpointNormalized (n : ℕ) : ℝ :=
  (endpointCount n : ℝ) / survivorBase^n

/-- The existing exact survivor counts after removing their exponential rate. -/
noncomputable def survivorNormalized (n : ℕ) : ℝ :=
  (neverNegCount n : ℝ) / survivorBase^n

/-- The geometric ratio of successive terms in the limiting binomial tail. -/
noncomputable def terminalRatio : ℝ := (1-beta)/beta

/-- The central Stirling amplitude at the logarithmic slope. -/
noncomputable def terminalAmplitude : ℝ := (Real.sqrt (2*Real.pi*beta*(1-beta)))⁻¹

/-- The bounded periodic terminal phase kernel, with its value at integers
fixed by the right-hand convention for the fractional part. -/
noncomputable def terminalPhase (x : ℝ) : ℝ :=
  terminalAmplitude * terminalRatio^(1-Int.fract x) / (1-terminalRatio)

/-- The proposed survivor profile as the convolution of the exact survivor
coefficients with the terminal phase kernel. -/
noncomputable def survivorPhase (x : ℝ) : ℝ :=
  ∑' j : ℕ, survivorNormalized j * terminalPhase (x-(j : ℝ)*beta)

/-- The exact positive-partial-sum exponential counting identity required
for these concrete counts. This proposition is an exposed proof obligation. -/
def SurvivorExponentialIdentity : Prop :=
  ∀ n, survivorNormalized n = renewalCoeff endpointNormalized n

/-- The explicit binomial-tail asymptotic required for the phase limit.
This proposition is an exposed proof obligation, not an axiom. -/
def EndpointPhaseAsymptotic : Prop :=
  Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)*endpointNormalized n - terminalPhase (n*beta))
    atTop (𝓝 0)

private theorem survivorBase_pos : 0 < survivorBase := by
  have h := rateBase_pos
  unfold survivorBase
  positivity

private theorem endpointNormalized_nonneg (n : ℕ) : 0 ≤ endpointNormalized n := by
  unfold endpointNormalized
  exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg survivorBase_pos.le _)

private theorem survivorNormalized_nonneg (n : ℕ) : 0 ≤ survivorNormalized n := by
  unfold survivorNormalized
  exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg survivorBase_pos.le _)

private theorem terminalRatio_bounds : 0 < terminalRatio ∧ terminalRatio < 1 := by
  have hb : 0 < beta := by linarith [beta_gt_five_eighths]
  constructor
  · exact div_pos (sub_pos.2 beta_lt_one) hb
  · exact (div_lt_one hb).2 (by linarith [beta_gt_five_eighths])

private theorem terminalAmplitude_pos : 0 < terminalAmplitude := by
  have hb : 0 < beta := by linarith [beta_gt_five_eighths]
  have hq : 0 < 1-beta := sub_pos.2 beta_lt_one
  unfold terminalAmplitude
  positivity

/-- The terminal profile is bounded above and bounded away from zero
uniformly, including at its jump. -/
theorem terminalPhase_bounds (x : ℝ) :
    terminalAmplitude*terminalRatio/(1-terminalRatio) ≤ terminalPhase x ∧
      terminalPhase x ≤ terminalAmplitude/(1-terminalRatio) := by
  have hs := terminalRatio_bounds
  have hd : 0 < 1-terminalRatio := sub_pos.2 hs.2
  have hl : terminalRatio ≤ terminalRatio^(1-Int.fract x) := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hs.1 hs.2.le
      (show 1-Int.fract x ≤ 1 by linarith [Int.fract_nonneg x])
  have hu := Real.rpow_le_one hs.1.le hs.2.le
    (show 0 ≤ 1-Int.fract x by linarith [Int.fract_lt_one x])
  constructor
  · exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hl terminalAmplitude_pos.le) hd.le
  · simpa [terminalPhase] using div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hu terminalAmplitude_pos.le) hd.le

private theorem terminalPhase_nonneg (x : ℝ) : 0 ≤ terminalPhase x := by
  have hs := terminalRatio_bounds
  have ha := terminalAmplitude_pos
  have hd : 0 < 1-terminalRatio := sub_pos.2 hs.2
  exact (div_nonneg (mul_nonneg ha.le hs.1.le) hd.le).trans
    (terminalPhase_bounds x).1

private theorem terminalPhase_abs_le (x : ℝ) :
    |terminalPhase x| ≤ terminalAmplitude/(1-terminalRatio) := by
  rw [abs_of_nonneg (terminalPhase_nonneg x)]
  exact (terminalPhase_bounds x).2

/-- Under the two classical inputs the actual normalized survivor counts
are summable. This fact is derived, not supplied with the phase limit. -/
theorem summable_survivorNormalized (hcount : SurvivorExponentialIdentity)
    (hterminal : EndpointPhaseAsymptotic) : Summable survivorNormalized := by
  obtain ⟨K, _, hK⟩ := exists_terminal_sqrt_bound_of_phase_limit terminalPhase_abs_le hterminal
  exact (summable_renewalCoeff endpointNormalized_nonneg
    (summable_renewalLogCoeff_of_bound hK)).congr (fun n => (hcount n).symm)

/-- The concrete survivor phase limit, conditional only on the displayed
classical counting identity and terminal binomial asymptotic. Dense jumps
require no continuity premise. The conclusion has additive `o(1)` error. -/
theorem survivor_phase_limit (hcount : SurvivorExponentialIdentity)
    (hterminal : EndpointPhaseAsymptotic) :
    Tendsto (fun n : ℕ => (n : ℝ)*Real.sqrt n*survivorNormalized n -
      survivorPhase ((n : ℝ)*beta)) atTop (𝓝 0) := by
  have h := renewalCoeff_phase_limit endpointNormalized_nonneg terminalPhase_abs_le hterminal
  have hcount' : ∀ n, survivorNormalized n = renewalCoeff endpointNormalized n := hcount
  convert h using 1
  funext n
  simp only [survivorPhase, hcount']
  congr 1
  apply tsum_congr
  intro j
  rw [sub_mul]

/-- Periodicity in the exact phase coordinate. Taking fractional parts
does not take a limit through a discontinuity. -/
theorem survivorPhase_fract (x : ℝ) : survivorPhase (Int.fract x) = survivorPhase x := by
  unfold survivorPhase
  apply tsum_congr
  intro j
  congr 1
  have hfr : Int.fract (Int.fract x-(j : ℝ)*beta) = Int.fract (x-(j : ℝ)*beta) := by
    rw [show Int.fract x-(j : ℝ)*beta = (x-(j : ℝ)*beta)-(⌊x⌋ : ℤ) by
      rw [Int.fract]; ring, Int.fract_sub_intCast]
  simp only [terminalPhase, hfr]

private theorem summable_survivorPhase_terms (hu : Summable survivorNormalized) (x : ℝ) :
    Summable (fun j : ℕ => survivorNormalized j * terminalPhase (x-(j : ℝ)*beta)) :=
  (hu.mul_left (terminalAmplitude/(1-terminalRatio))).of_norm_bounded fun j => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (survivorNormalized_nonneg j)]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left
      (terminalPhase_abs_le (x-(j : ℝ)*beta)) (survivorNormalized_nonneg j)

/-- Summability yields explicit bounds for the proposed survivor profile.
The positive lower bound is supplied by the zeroth survivor coefficient. -/
theorem survivorPhase_bounds (hu : Summable survivorNormalized) (x : ℝ) :
    terminalAmplitude*terminalRatio/(1-terminalRatio) ≤ survivorPhase x ∧
      survivorPhase x ≤ terminalAmplitude/(1-terminalRatio)*(∑' j, survivorNormalized j) := by
  have hs := summable_survivorPhase_terms hu x
  constructor
  · have hz : survivorNormalized 0 = 1 := by
      have hc : neverNegCount 0 = 1 := by decide +kernel
      simp [survivorNormalized, hc]
    have h := hs.le_tsum 0 (fun j _ =>
      mul_nonneg (survivorNormalized_nonneg j) (terminalPhase_nonneg _))
    simp only [hz, Nat.cast_zero, zero_mul, sub_zero, one_mul] at h
    exact (terminalPhase_bounds x).1.trans h
  · calc
      _ ≤ ∑' j, (terminalAmplitude/(1-terminalRatio))*survivorNormalized j :=
        hs.tsum_le_tsum (fun j => by
          simpa [mul_comm] using mul_le_mul_of_nonneg_left
            (terminalPhase_bounds (x-(j : ℝ)*beta)).2 (survivorNormalized_nonneg j))
          (hu.mul_left _)
      _ = _ := tsum_mul_left

/-- The two explicit classical inputs imply the existing Paper B
`MeanderShape` predicate for the explicit convolution profile. No new
assumption about profile positivity or continuity is required. This is a
conditional theorem; neither classical input is discharged in this file. -/
theorem meanderShape_survivorPhase (hcount : SurvivorExponentialIdentity)
    (hterminal : EndpointPhaseAsymptotic) : MeanderShape survivorPhase := by
  have hu := summable_survivorNormalized hcount hterminal
  let c : ℝ := terminalAmplitude*terminalRatio/(1-terminalRatio)
  have hc : 0 < c := div_pos (mul_pos terminalAmplitude_pos terminalRatio_bounds.1)
    (sub_pos.2 terminalRatio_bounds.2)
  have hl (x : ℝ) : c ≤ survivorPhase x := (survivorPhase_bounds hu x).1
  have hp (x : ℝ) : 0 < survivorPhase x := hc.trans_le (hl x)
  let err : ℕ → ℝ := fun n => (n : ℝ)*Real.sqrt n*survivorNormalized n -
    survivorPhase ((n : ℝ)*beta)
  have herr : Tendsto err atTop (𝓝 0) := survivor_phase_limit hcount hterminal
  have hratio : Tendsto (fun n : ℕ => err n / survivorPhase ((n : ℝ)*beta))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun n => |err n| / c) (fun n => ?_)
      (by simpa using herr.abs.div_const c)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (hp _)]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hc (hl _)
  have hlim := hratio.add_const 1
  simp only [zero_add] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnz : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hsq : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hnR)
  have hr : rateBase ≠ 0 := ne_of_gt rateBase_pos
  have hpsi : survivorPhase ((n : ℝ)*beta) ≠ 0 := ne_of_gt (hp _)
  have hpower : (n : ℝ)^(-(3 : ℝ)/2) = ((n : ℝ)*Real.sqrt n)⁻¹ := by
    rw [show -(3 : ℝ)/2 = -(1+1/2) by norm_num, Real.rpow_neg hnR.le,
      Real.rpow_add hnR, Real.rpow_one, ← Real.sqrt_eq_rpow]
  change err n / survivorPhase ((n : ℝ)*beta) + 1 =
    survivorDensity n / (model n * survivorPhase (Int.fract ((n : ℝ)*beta)))
  rw [survivorPhase_fract]
  simp only [err, survivorNormalized, survivorBase, survivorDensity, model, hpower, mul_pow]
  field_simp
  ring

/-- The remaining exponential counting identity is equivalent to a purely
integer finite-sum recurrence at every degree. This is an equivalence, not
a proof of the recurrence for the actual counts. -/
theorem survivorExponentialIdentity_iff_count_recurrence :
    SurvivorExponentialIdentity ↔ ∀ n : ℕ,
      n * neverNegCount n = ∑ j ∈ range n, endpointCount (n-j)*neverNegCount j := by
  have hu0 : survivorNormalized 0 = 1 := by
    have hc : neverNegCount 0 = 1 := by decide +kernel
    simp [survivorNormalized, hc]
  have heq : SurvivorExponentialIdentity ↔
      survivorNormalized = renewalCoeff endpointNormalized :=
    ⟨fun h => funext h, fun h => congrFun h⟩
  rw [heq, eq_renewalCoeff_iff_recurrence hu0]
  apply forall_congr'
  intro n
  have hl : (n : ℝ)*survivorNormalized n =
      (n * neverNegCount n : ℕ) / (survivorBase^n : ℝ) := by
    simp only [survivorNormalized, Nat.cast_mul]
    ring
  have hr : (∑ j ∈ range n, endpointNormalized (n-j)*survivorNormalized j) =
      (∑ j ∈ range n, endpointCount (n-j)*neverNegCount j : ℕ) /
        (survivorBase^n : ℝ) := by
    simp only [Nat.cast_sum, Nat.cast_mul, sum_div]
    apply sum_congr rfl
    intro j hj
    have hjn : j ≤ n := (mem_range.1 hj).le
    simp only [endpointNormalized, survivorNormalized]
    rw [div_mul_div_comm, ← pow_add, Nat.sub_add_cancel hjn]
  rw [hl, hr, div_left_inj' (pow_ne_zero n (ne_of_gt survivorBase_pos))]
  exact Nat.cast_inj

/-- A partial survivor theorem needing only coarse two-sided terminal
bounds, rather than the terminal phase asymptotic. The counting identity
remains an explicit premise. A positive `a` gives sharp three-halves order. -/
theorem survivor_three_halves_bounds_of_terminal_bounds {a K : ℝ}
    (hcount : SurvivorExponentialIdentity) (hK : 0 ≤ K)
    (hupper : ∀ n : ℕ, 0 < n → endpointNormalized n ≤ K / Real.sqrt (n : ℝ))
    (hlower : ∀ n : ℕ, 0 < n → a / Real.sqrt (n : ℝ) ≤ endpointNormalized n) :
    ∃ U : ℝ, 0 ≤ U ∧ ∀ n : ℕ, 0 < n →
      a / ((n : ℝ)*Real.sqrt n) ≤ survivorNormalized n ∧
      survivorNormalized n ≤ U / ((n : ℝ)*Real.sqrt n) := by
  obtain ⟨U, hU, hu⟩ := renewalCoeff_three_halves_bounds
    endpointNormalized_nonneg hK hupper hlower
  exact ⟨U, hU, fun n hn => by rw [hcount n]; exact hu n hn⟩

/-- The finite profile approximation has a phase-independent remainder
bound given by the remaining coefficient mass. It remains valid at jumps. -/
theorem survivorPhase_truncation_bound (hu : Summable survivorNormalized)
    (N : ℕ) (x : ℝ) :
    |survivorPhase x - ∑ j ∈ range N,
      survivorNormalized j * terminalPhase (x-(j : ℝ)*beta)| ≤
      (terminalAmplitude/(1-terminalRatio)) * ∑' j, survivorNormalized (j+N) := by
  have hs := summable_survivorPhase_terms hu x
  have hsplit := hs.sum_add_tsum_nat_add N
  have heq : survivorPhase x - ∑ j ∈ range N,
      survivorNormalized j * terminalPhase (x-(j : ℝ)*beta) =
      ∑' j, survivorNormalized (j+N) * terminalPhase (x-((j+N : ℕ) : ℝ)*beta) := by
    unfold survivorPhase
    linarith [hsplit]
  rw [heq, abs_of_nonneg (tsum_nonneg (fun j =>
    mul_nonneg (survivorNormalized_nonneg _) (terminalPhase_nonneg _)))]
  have hut : Summable (fun j => survivorNormalized (j+N)) :=
    hu.comp_injective (add_left_injective N)
  have hst : Summable (fun j => survivorNormalized (j+N) *
      terminalPhase (x-((j+N : ℕ) : ℝ)*beta)) := hs.comp_injective (add_left_injective N)
  calc
    _ ≤ ∑' j, (terminalAmplitude/(1-terminalRatio))*survivorNormalized (j+N) :=
      hst.tsum_le_tsum (fun j => by
        simpa [mul_comm] using mul_le_mul_of_nonneg_left
          (terminalPhase_bounds (x-((j+N : ℕ) : ℝ)*beta)).2
          (survivorNormalized_nonneg _)) (hut.mul_left _)
    _ = _ := tsum_mul_left

/-- Finite truncations converge uniformly over every real phase, including
all discontinuity points. The theorem is qualitative; a numerical cutoff
requires a numerical bound on the remaining coefficient mass. -/
theorem survivorPhase_uniform_approximation (hu : Summable survivorNormalized)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ N0 : ℕ, ∀ N ≥ N0, ∀ x : ℝ,
      |survivorPhase x - ∑ j ∈ range N,
        survivorNormalized j * terminalPhase (x-(j : ℝ)*beta)| < epsilon := by
  have hlim := (tendsto_sum_nat_add survivorNormalized).const_mul
    (terminalAmplitude/(1-terminalRatio))
  simp only [mul_zero] at hlim
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 (hlim.eventually_lt_const hepsilon)
  exact ⟨N0, fun N hN x => (survivorPhase_truncation_bound hu N x).trans_lt (hN0 N hN)⟩

end Problems.Juggler.BeattyPhase

import Problems.Juggler.BeattySlopeBinomial
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# The tilted terminal phase at arbitrary boundaries

Stirling's formula is applied at the strict cutoff `floor(n*β)+1`. The
fractional-part correction is kept throughout, rather than replaced by a
continuous approximation at its jumps. The endpoint estimate is valid for
every real `0 < β < 1`; only the subsequent survivor transfer needs an
irrational boundary. All limits are for each fixed boundary, with no uniform
error estimate as the boundary approaches zero or one.
-/

namespace Problems.Juggler.BeattySlope

open Filter Topology Finset

/-- Exponential base for the chosen tilt, equal to `2^(-β)/(1-β)` in its
probabilistic range. The exponential definition simplifies the logarithmic proof. -/
noncomputable def tiltedBase (β : ℝ) : ℝ := Real.exp (-β*Real.log 2-Real.log (1-β))

/-- Central Stirling amplitude at the boundary. -/
noncomputable def tiltedAmplitude (β : ℝ) : ℝ := (Real.sqrt (2*Real.pi*β*(1-β)))⁻¹

/-- Square-root normalization of the first strict tilted binomial term. -/
noncomputable def tiltedFirstTermScaled (β : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt n*(n.choose (endpointCutoff β n) : ℝ)*
    tiltedOddWeight β^endpointCutoff β n / tiltedBase β^n

/-- Periodic endpoint phase, with its exact value at integer phases retained. -/
noncomputable def tiltedTerminalPhase (β t : ℝ) : ℝ :=
  2*tiltedAmplitude β*(1/2 : ℝ)^(1-Int.fract t)

/-- The tilted exponential base is positive for every real parameter. -/
theorem tiltedBase_pos (β : ℝ) : 0 < tiltedBase β := Real.exp_pos _

/-- The exponential definition agrees with the explicit base in real powers. -/
theorem tiltedBase_eq {β : ℝ} (hβ1 : β < 1) :
    tiltedBase β = (2 : ℝ)^(-β)/(1-β) := by
  rw [tiltedBase, Real.exp_sub, Real.exp_log (sub_pos.mpr hβ1),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [mul_comm (-β)]

/-- The strict endpoint phase has the simple fractional-part formula. -/
theorem tiltedTerminalPhase_eq (β t : ℝ) :
    tiltedTerminalPhase β t = tiltedAmplitude β*(2 : ℝ)^Int.fract t := by
  unfold tiltedTerminalPhase
  rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 1/2), Real.rpow_one,
    one_div (2 : ℝ), Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
  ring

/-- The amplitude is positive in the nondegenerate boundary interval. -/
theorem tiltedAmplitude_pos {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    0 < tiltedAmplitude β := by
  unfold tiltedAmplitude
  positivity

/-- The scaled first term is positive at every positive depth. -/
theorem tiltedFirstTermScaled_pos {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {n : ℕ} (hn : 0 < n) : 0 < tiltedFirstTermScaled β n := by
  have hc : (0 : ℝ) < n.choose (endpointCutoff β n) := by
    exact_mod_cast Nat.choose_pos (endpointCutoff_le hβ0.le hβ1 hn)
  have hz := tiltedOddWeight_pos hβ0 hβ1
  have hv := tiltedBase_pos β
  unfold tiltedFirstTermScaled
  positivity

private theorem cutoff_ratio_limit {β : ℝ} (hβ0 : 0 < β) :
    Tendsto (fun n : ℕ => (endpointCutoff β n : ℝ)/n) atTop (𝓝 β) := by
  have h := (tendsto_nat_floor_mul_div_atTop hβ0.le).comp tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n : ℕ => (1 : ℝ)/n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  simpa [endpointCutoff, Nat.cast_add, Nat.cast_one, add_div, mul_comm] using h.add hi

private theorem complement_ratio_limit {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun n : ℕ => ((n-endpointCutoff β n : ℕ) : ℝ)/n) atTop (𝓝 (1-β)) := by
  apply (tendsto_const_nhds.sub (cutoff_ratio_limit hβ0)).congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [Nat.cast_sub (endpointCutoff_le hβ0.le hβ1 (by omega)), sub_div, div_self hn0]

private theorem cutoff_atTop {β : ℝ} (hβ0 : 0 < β) :
    Tendsto (endpointCutoff β) atTop atTop := by
  change Tendsto (fun n : ℕ => ⌊(n : ℝ)*β⌋₊+1) atTop atTop
  simpa [endpointCutoff, Function.comp_def, mul_comm] using
    (tendsto_add_atTop_nat 1).comp (tendsto_nat_floor_mul_atTop β hβ0)

private theorem complement_atTop {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun n => n-endpointCutoff β n) atTop atTop := by
  have h := (complement_ratio_limit hβ0 hβ1).pos_mul_atTop (sub_pos.mpr hβ1)
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply tendsto_atTop.2
  intro b
  filter_upwards [h.eventually_ge_atTop (b : ℝ), eventually_ge_atTop 1] with n hb hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [div_mul_cancel₀ _ hn0] at hb
  exact_mod_cast hb

private noncomputable def factorialError (n : ℕ) : ℝ :=
  Real.log (n.factorial : ℝ)-(((n : ℝ)+1/2)*Real.log n-n)

private theorem factorialError_limit : Tendsto factorialError atTop
    (𝓝 (Real.log (Real.sqrt Real.pi)+Real.log 2/2)) := by
  have h := (Stirling.tendsto_stirlingSeq_sqrt_pi.log (by positivity)).add_const
    (Real.log 2/2)
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  rw [Stirling.stirlingSeq, Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_sqrt (by positivity),
    Real.log_mul (by norm_num) (ne_of_gt hnR), Real.log_pow,
    Real.log_div (ne_of_gt hnR) (ne_of_gt (Real.exp_pos 1)), Real.log_exp]
  unfold factorialError
  ring

private noncomputable def entropyRemainder (β : ℝ) (n : ℕ) : ℝ :=
  let k : ℝ := endpointCutoff β n
  let l : ℝ := n-endpointCutoff β n
  k*Real.log (k/(n*β))+l*Real.log (l/(n*(1-β)))

private theorem entropyRemainder_bounds {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {n : ℕ} (hn : 0 < n) (hlN : 0 < n-endpointCutoff β n) :
    0 ≤ entropyRemainder β n ∧ entropyRemainder β n ≤ 1/((n : ℝ)*β*(1-β)) := by
  let t : ℝ := n
  let k : ℝ := endpointCutoff β n
  let l := t-k
  have ht : 0 < t := by dsimp [t]; exact_mod_cast hn
  have hq : 0 < 1-β := sub_pos.mpr hβ1
  have hc := endpointCutoff_bounds hβ0.le n
  change t*β < k ∧ k ≤ t*β+1 at hc
  have hk : 0 < k := (mul_pos ht hβ0).trans hc.1
  have hl : 0 < l := by
    dsimp [l, t, k]
    apply sub_pos.mpr
    exact_mod_cast (Nat.sub_pos_iff_lt.mp hlN)
  have htb := mul_pos ht hβ0
  have htq := mul_pos ht hq
  change 0 ≤ k*Real.log (k/(t*β))+l*Real.log (l/(t*(1-β))) ∧ _
  constructor
  · have ha := mul_le_mul_of_nonneg_left
      (Real.one_sub_inv_le_log_of_pos (div_pos hk htb)) hk.le
    have hb := mul_le_mul_of_nonneg_left
      (Real.one_sub_inv_le_log_of_pos (div_pos hl htq)) hl.le
    have he : k*(1-(k/(t*β))⁻¹) = k-t*β := by field_simp
    have he' : l*(1-(l/(t*(1-β)))⁻¹) = l-t*(1-β) := by field_simp
    rw [he] at ha
    rw [he'] at hb
    dsimp [l] at *
    linarith
  · have ha := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hk htb)) hk.le
    have hb := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hl htq)) hl.le
    have he : k*(k/(t*β)-1)+l*(l/(t*(1-β))-1) = (k-t*β)^2/(t*β*(1-β)) := by
      dsimp [l]
      field_simp [ne_of_gt ht, ne_of_gt hβ0, ne_of_gt hq]
      ring
    have he' : (k-t*β)^2 ≤ 1 := by nlinarith [hc.1, hc.2]
    have hh := div_le_div_of_nonneg_right he' (mul_pos htb hq).le
    change k*Real.log (k/(t*β))+l*Real.log (l/(t*(1-β))) ≤ _
    linarith

private theorem entropyRemainder_limit {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Tendsto (entropyRemainder β) atTop (𝓝 0) := by
  have hq : 0 < 1-β := sub_pos.mpr hβ1
  have h : Tendsto (fun n : ℕ => 1/((n : ℝ)*β*(1-β))) atTop (𝓝 0) := by
    apply tendsto_const_nhds.div_atTop
    simpa [mul_comm, mul_left_comm] using
      (tendsto_natCast_atTop_atTop.const_mul_atTop hβ0).const_mul_atTop hq
  have hb : ∀ᶠ n : ℕ in atTop,
      0 ≤ entropyRemainder β n ∧ entropyRemainder β n ≤ 1/((n : ℝ)*β*(1-β)) := by
    filter_upwards [eventually_ge_atTop 1,
      (complement_atTop hβ0 hβ1).eventually_ge_atTop 1] with n hn hl
    exact entropyRemainder_bounds hβ0 hβ1 (by omega) (by omega)
  exact squeeze_zero' (hb.mono fun _ h => h.1) (hb.mono fun _ h => h.2) h

private theorem cutoff_offset {β : ℝ} (hβ0 : 0 < β) (n : ℕ) :
    (endpointCutoff β n : ℝ)-n*β = 1-Int.fract (n*β) := by
  simp only [endpointCutoff, Nat.cast_add, Nat.cast_one, Int.fract]
  rw [natCast_floor_eq_intCast_floor (mul_nonneg (Nat.cast_nonneg n) hβ0.le)]
  ring

private theorem log_tiltedOddWeight {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Real.log (tiltedOddWeight β) = Real.log β-Real.log 2-Real.log (1-β) := by
  rw [tiltedOddWeight, Real.log_div hβ0.ne' (by positivity),
    Real.log_mul (by norm_num) (ne_of_gt (sub_pos.mpr hβ1))]
  ring

private theorem firstTerm_log_identity {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {n : ℕ} (hn : 0 < n) (hlN : 0 < n-endpointCutoff β n) :
    Real.log (tiltedFirstTermScaled β n)-(1-Int.fract (n*β))*Real.log (1/2 : ℝ) =
    factorialError n-factorialError (endpointCutoff β n)-factorialError (n-endpointCutoff β n) -
      entropyRemainder β n - (Real.log ((endpointCutoff β n : ℝ)/n) +
        Real.log (((n-endpointCutoff β n : ℕ) : ℝ)/n))/2 := by
  let k := endpointCutoff β n
  let l := n-k
  have hkn : k ≤ n := endpointCutoff_le hβ0.le hβ1 hn
  have hs : k+l=n := Nat.add_sub_of_le hkn
  have hsR : (k : ℝ)+l=n := by exact_mod_cast hs
  have ht : (0 : ℝ) < n := by exact_mod_cast hn
  have hb := endpointCutoff_bounds hβ0.le n
  change (n : ℝ)*β < (k : ℝ) ∧ (k : ℝ) ≤ n*β+1 at hb
  have hk : (0 : ℝ) < k := (mul_pos ht hβ0).trans hb.1
  have hl : (0 : ℝ) < l := by exact_mod_cast hlN
  have hq : 0 < 1-β := sub_pos.mpr hβ1
  have hz := tiltedOddWeight_pos hβ0 hβ1
  have hv := tiltedBase_pos β
  have hc : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hkn
  have hf : (n.choose k : ℝ)*(k.factorial : ℝ)*(l.factorial : ℝ) = n.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkn
  have hfLog := congrArg Real.log hf
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (ne_of_gt hc) (by positivity)] at hfLog
  have hoff := cutoff_offset hβ0 n
  change (k : ℝ)-n*β = _ at hoff
  rw [← hoff]
  change Real.log (Real.sqrt n*(n.choose k : ℝ)*tiltedOddWeight β^k/tiltedBase β^n) - _ = _
  rw [Real.log_div (by positivity) (ne_of_gt (pow_pos hv n)),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (ne_of_gt hc), Real.log_sqrt ht.le,
    Real.log_pow, Real.log_pow, log_tiltedOddWeight hβ0 hβ1, tiltedBase, Real.log_exp]
  have hhalf : Real.log (1/2 : ℝ) = -Real.log 2 := by simp [one_div, Real.log_inv]
  rw [hhalf]
  change _ = factorialError n-factorialError k-factorialError l-entropyRemainder β n - _
  have hcast : ((n-k : ℕ) : ℝ) = n-k := Nat.cast_sub hkn
  unfold factorialError entropyRemainder
  change _ = _ - ((k : ℝ)*Real.log ((k : ℝ)/(n*β)) +
    ((n : ℝ)-k)*Real.log (((n : ℝ)-k)/(n*(1-β)))) - _
  rw [← hcast]
  change _ = _ - ((k : ℝ)*Real.log ((k : ℝ)/(n*β)) +
    (l : ℝ)*Real.log ((l : ℝ)/(n*(1-β)))) - _
  rw [Real.log_div (ne_of_gt hk) (ne_of_gt (mul_pos ht hβ0)),
    Real.log_div (ne_of_gt hl) (ne_of_gt (mul_pos ht hq)),
    Real.log_mul (ne_of_gt ht) (ne_of_gt hβ0),
    Real.log_mul (ne_of_gt ht) (ne_of_gt hq),
    Real.log_div (ne_of_gt hk) (ne_of_gt ht),
    Real.log_div (ne_of_gt hl) (ne_of_gt ht)]
  rw [← hsR]
  linear_combination hfLog

private theorem firstTerm_log_limit {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun n : ℕ => Real.log (tiltedFirstTermScaled β n) -
      (1-Int.fract (n*β))*Real.log (1/2 : ℝ)) atTop (𝓝 (Real.log (tiltedAmplitude β))) := by
  have hq : 0 < 1-β := sub_pos.mpr hβ1
  have h := (((factorialError_limit.sub (factorialError_limit.comp (cutoff_atTop hβ0))).sub
    (factorialError_limit.comp (complement_atTop hβ0 hβ1))).sub
      (entropyRemainder_limit hβ0 hβ1)).sub
      ((((cutoff_ratio_limit hβ0).log hβ0.ne').add
        ((complement_ratio_limit hβ0 hβ1).log hq.ne')).div_const 2)
  have he : Real.log (Real.sqrt Real.pi)+Real.log 2/2 -
      (Real.log (Real.sqrt Real.pi)+Real.log 2/2) -
      (Real.log (Real.sqrt Real.pi)+Real.log 2/2) - 0 -
      (Real.log β+Real.log (1-β))/2 = Real.log (tiltedAmplitude β) := by
    unfold tiltedAmplitude
    rw [Real.log_inv, Real.log_sqrt Real.pi_pos.le,
      Real.log_sqrt (by positivity : 0 ≤ 2*Real.pi*β*(1-β)),
      Real.log_mul (by positivity) hq.ne', Real.log_mul (by positivity) hβ0.ne',
      Real.log_mul (by norm_num) Real.pi_pos.ne']
    ring
  rw [he] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1,
    (complement_atTop hβ0 hβ1).eventually_ge_atTop 1] with n hn hl
  exact (firstTerm_log_identity hβ0 hβ1 (by omega) (by omega)).symm

private theorem zero_mul_bounded {f g : ℕ → ℝ} {C : ℝ}
    (hf : Tendsto f atTop (𝓝 0)) (hg : ∀ n, |g n| ≤ C) :
    Tendsto (fun n => f n*g n) atTop (𝓝 0) := by
  refine squeeze_zero_norm (a := fun n => |f n| * C) (fun n => ?_) ?_
  · rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hg n) (abs_nonneg _)
  · simpa using hf.abs.mul_const C

/-- For every fixed boundary in `(0,1)`, the first tilted binomial term has
the exact moving Stirling phase. No irrationality or asymptotic input is assumed. -/
theorem tilted_first_term_phase_limit {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun n : ℕ => tiltedFirstTermScaled β n -
      tiltedAmplitude β*(1/2 : ℝ)^(1-Int.fract (n*β))) atTop (𝓝 0) := by
  have ha := tiltedAmplitude_pos hβ0 hβ1
  have h := Real.continuous_exp.tendsto _ |>.comp (firstTerm_log_limit hβ0 hβ1)
  rw [Real.exp_log ha] at h
  have h' : Tendsto (fun n : ℕ => tiltedFirstTermScaled β n /
      (1/2 : ℝ)^(1-Int.fract (n*β))) atTop (𝓝 (tiltedAmplitude β)) := by
    apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp only [Function.comp_apply]
    rw [Real.exp_sub, Real.exp_log (tiltedFirstTermScaled_pos hβ0 hβ1 (by omega)),
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 1/2)]
    rw [mul_comm (Real.log (1/2 : ℝ))]
  have hb (n : ℕ) : |(1/2 : ℝ)^(1-Int.fract (n*β))| ≤ 1 := by
    rw [abs_of_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 1/2) _)]
    exact Real.rpow_le_one (by norm_num) (by norm_num)
      (by linarith [Int.fract_lt_one ((n : ℝ)*β)])
  have hz := zero_mul_bounded (by simpa using h'.sub_const (tiltedAmplitude β)) hb
  apply hz.congr'
  exact Eventually.of_forall fun n => by
    have hp := ne_of_gt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 1/2)
      (1-Int.fract ((n : ℝ)*β)))
    dsimp
    field_simp

private theorem adjacent_ratio_limit {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (j : ℕ) :
    Tendsto (fun n : ℕ => ((n-(endpointCutoff β n+j) : ℕ) : ℝ)/(endpointCutoff β n+j+1 : ℕ))
      atTop (𝓝 ((1-β)/β)) := by
  have hc (c : ℝ) : Tendsto (fun n : ℕ => c/n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h := (((tendsto_const_nhds (x := (1 : ℝ))).sub (cutoff_ratio_limit hβ0)).sub (hc j)).div
    ((cutoff_ratio_limit hβ0).add (hc (j+1))) (by simpa using hβ0.ne')
  simp only [sub_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1,
    (complement_atTop hβ0 hβ1).eventually_ge_atTop j] with n hn hj
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hk := endpointCutoff_le hβ0.le hβ1 (by omega : 0 < n)
  have hkn : endpointCutoff β n+j ≤ n := by omega
  dsimp
  simp only [Nat.cast_sub hkn, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

private theorem choose_ratio_limit {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (j : ℕ) :
    Tendsto (fun n : ℕ =>
      (n.choose (endpointCutoff β n+j) : ℝ)/(n.choose (endpointCutoff β n) : ℝ))
      atTop (𝓝 (((1-β)/β)^j)) := by
  induction j with
  | zero =>
    simp only [pow_zero]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hc : (n.choose (endpointCutoff β n) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (endpointCutoff_le hβ0.le hβ1 (by omega))).ne'
    simp [hc]
  | succ j ih =>
    rw [pow_succ]
    apply (ih.mul (adjacent_ratio_limit hβ0 hβ1 j)).congr'
    exact Eventually.of_forall fun n => by
      have he : (n.choose (endpointCutoff β n+j+1) : ℝ)*(endpointCutoff β n+j+1 : ℕ) =
          (n.choose (endpointCutoff β n+j) : ℝ)*(n-(endpointCutoff β n+j) : ℕ) := by
        exact_mod_cast Nat.choose_succ_right_eq n (endpointCutoff β n+j)
      have hp : ((endpointCutoff β n+j+1 : ℕ) : ℝ) ≠ 0 := by positivity
      dsimp
      rw [show endpointCutoff β n+(j+1) = endpointCutoff β n+j+1 by omega]
      rw [div_mul_div_comm, ← he]
      field_simp

private noncomputable def binomialRatio (β : ℝ) (n j : ℕ) : ℝ :=
  ((n.choose (endpointCutoff β n+j) : ℝ)/(n.choose (endpointCutoff β n) : ℝ))*
    tiltedOddWeight β^j

private theorem binomialRatio_limit {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (j : ℕ) :
    Tendsto (fun n => binomialRatio β n j) atTop (𝓝 ((1/2 : ℝ)^j)) := by
  have he : ((1-β)/β)*tiltedOddWeight β = 1/2 := by
    calc
      _ = tiltedOddWeight β*(1-β)/β := by ring
      _ = _ := tiltedOddWeight_terminal_ratio hβ0 hβ1
  have h := (choose_ratio_limit hβ0 hβ1 j).mul_const (tiltedOddWeight β^j)
  rw [← mul_pow, he] at h
  exact h

private theorem binomialRatio_eq {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {n : ℕ} (hn : 0 < n) (j : ℕ) :
    binomialRatio β n j =
      ((n.choose (endpointCutoff β n+j) : ℝ)*tiltedOddWeight β^(endpointCutoff β n+j))/
      ((n.choose (endpointCutoff β n) : ℝ)*tiltedOddWeight β^endpointCutoff β n) := by
  have hc : (n.choose (endpointCutoff β n) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (endpointCutoff_le hβ0.le hβ1 hn)).ne'
  have hz := (tiltedOddWeight_pos hβ0 hβ1).ne'
  unfold binomialRatio
  rw [pow_add]
  field_simp

private theorem binomialRatio_bound {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (n j : ℕ) : |binomialRatio β n j| ≤ (1/2 : ℝ)^j := by
  by_cases hn : n = 0
  · subst n
    simp [binomialRatio, endpointCutoff]
  · have hc : (0 : ℝ) < n.choose (endpointCutoff β n) := by
      exact_mod_cast Nat.choose_pos (endpointCutoff_le hβ0.le hβ1 (Nat.pos_of_ne_zero hn))
    have hz := tiltedOddWeight_pos hβ0 hβ1
    rw [binomialRatio_eq hβ0 hβ1 (Nat.pos_of_ne_zero hn), abs_of_nonneg (by positivity)]
    exact (div_le_iff₀ (by positivity)).2 (by
      simpa [mul_comm] using tilted_choose_shift_bound hβ0 hβ1 n j)

private theorem tail_ratio_eq_tsum {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {n : ℕ} (hn : 0 < n) :
    endpointWeight β (tiltedOddWeight β) n /
        ((n.choose (endpointCutoff β n) : ℝ)*tiltedOddWeight β^endpointCutoff β n) =
      ∑' j, binomialRatio β n j := by
  rw [endpointWeight_eq_tail hβ0.le, sum_Ico_eq_sum_range, sum_div]
  simp_rw [← binomialRatio_eq hβ0 hβ1 hn]
  symm
  apply tsum_eq_sum
  intro j hj
  have hj' : n+1-endpointCutoff β n ≤ j := by simpa only [mem_range, not_lt] using hj
  unfold binomialRatio
  rw [Nat.choose_eq_zero_of_lt (by omega : n < endpointCutoff β n+j)]
  simp

/-- The tilted endpoint tail divided by its first term tends to two at every
fixed real boundary in `(0,1)`. The half-geometric majorant justifies summation. -/
theorem tilted_binomial_tail_ratio_limit {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun n : ℕ => endpointWeight β (tiltedOddWeight β) n /
      ((n.choose (endpointCutoff β n) : ℝ)*tiltedOddWeight β^endpointCutoff β n))
      atTop (𝓝 2) := by
  have h := tendsto_tsum_of_dominated_convergence
    (summable_geometric_of_abs_lt_one (by norm_num : |(1/2 : ℝ)| < 1))
    (binomialRatio_limit hβ0 hβ1) (Eventually.of_forall fun n j => by
      simpa only [Real.norm_eq_abs] using binomialRatio_bound hβ0 hβ1 n j)
  rw [tsum_geometric_of_abs_lt_one (by norm_num : |(1/2 : ℝ)| < 1)] at h
  norm_num at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (tail_ratio_eq_tsum hβ0 hβ1 (by omega)).symm

/-- The actual tilted binomial endpoint sum has its explicit periodic phase
for every real `0 < β < 1`. Stirling and the tail limit are proved, not assumed. -/
theorem tilted_endpoint_phase_limit {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun n : ℕ => Real.sqrt n*
      normalizedEndpoint β (tiltedOddWeight β) (tiltedBase β) n -
      tiltedTerminalPhase β (n*β)) atTop (𝓝 0) := by
  let R (n : ℕ) : ℝ := endpointWeight β (tiltedOddWeight β) n /
    ((n.choose (endpointCutoff β n) : ℝ)*tiltedOddWeight β^endpointCutoff β n)
  let P (n : ℕ) : ℝ := tiltedAmplitude β*(1/2 : ℝ)^(1-Int.fract (n*β))
  have ha := tiltedAmplitude_pos hβ0 hβ1
  have hz := tiltedOddWeight_pos hβ0 hβ1
  have hv := tiltedBase_pos β
  have hR (n : ℕ) : |R n| ≤ 2 := by
    dsimp [R]
    rw [abs_of_nonneg (by apply div_nonneg (endpointWeight_nonneg β hz.le n); positivity)]
    by_cases hn : n = 0
    · subst n
      simp [endpointWeight_zero]
    · have hc : (0 : ℝ) < n.choose (endpointCutoff β n) := by
        exact_mod_cast Nat.choose_pos (endpointCutoff_le hβ0.le hβ1 (Nat.pos_of_ne_zero hn))
      exact (div_le_iff₀ (by positivity)).2
        (tilted_endpoint_first_term_bounds hβ0 hβ1 (Nat.pos_of_ne_zero hn)).2
  have hP (n : ℕ) : |P n| ≤ tiltedAmplitude β := by
    dsimp [P]
    rw [abs_mul, abs_of_pos ha,
      abs_of_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 1/2) _)]
    exact mul_le_of_le_one_right ha.le (Real.rpow_le_one (by norm_num) (by norm_num)
      (by linarith [Int.fract_lt_one ((n : ℝ)*β)]))
  have h1 := zero_mul_bounded (tilted_first_term_phase_limit hβ0 hβ1) hR
  have h2 := zero_mul_bounded
    (by simpa using (tilted_binomial_tail_ratio_limit hβ0 hβ1).sub_const 2) hP
  have h := h1.add h2
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hc : (n.choose (endpointCutoff β n) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (endpointCutoff_le hβ0.le hβ1 (by omega))).ne'
  dsimp [R, P, tiltedFirstTermScaled, normalizedEndpoint, tiltedTerminalPhase]
  field_simp
  ring

/-- The explicit terminal phase is bounded on the whole real line. -/
theorem tiltedTerminalPhase_bound {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (t : ℝ) :
    |tiltedTerminalPhase β t| ≤ 2*tiltedAmplitude β := by
  have ha := tiltedAmplitude_pos hβ0 hβ1
  unfold tiltedTerminalPhase
  rw [abs_mul, abs_of_pos (by positivity : 0 < 2*tiltedAmplitude β),
    abs_of_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 1/2) _)]
  exact mul_le_of_le_one_right (by positivity) (Real.rpow_le_one (by norm_num) (by norm_num)
    (by linarith [Int.fract_lt_one t]))

/-- Explicit convolution profile of the actual normalized tilted survivors. -/
noncomputable def tiltedSurvivorPhase (β t : ℝ) : ℝ :=
  ∑' j : ℕ, normalizedSurvivor β (tiltedOddWeight β) (tiltedBase β) j *
    tiltedTerminalPhase β (t-j*β)

private theorem tilted_survivor_nonneg {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (n : ℕ) :
    0 ≤ normalizedSurvivor β (tiltedOddWeight β) (tiltedBase β) n := by
  unfold normalizedSurvivor survivorWeight
  exact div_nonneg (sum_nonneg fun _ _ => pow_nonneg (tiltedOddWeight_pos hβ0 hβ1).le _)
    (pow_nonneg (tiltedBase_pos β).le _)

/-- The actual normalized tilted survivor weights form a summable sequence.
This follows from the proved terminal asymptotic and the exact renewal identity. -/
theorem summable_tilted_survivor {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ : Irrational β) :
    Summable (normalizedSurvivor β (tiltedOddWeight β) (tiltedBase β)) := by
  obtain ⟨K, -, hK⟩ := BeattyPhase.exists_terminal_sqrt_bound_of_phase_limit
    (tiltedTerminalPhase_bound hβ0 hβ1) (tilted_endpoint_phase_limit hβ0 hβ1)
  rw [normalizedSurvivor_eq_renewalCoeff β hβ]
  exact BeattyPhase.summable_renewalCoeff
    (normalizedEndpoint_nonneg β (tiltedOddWeight_pos hβ0 hβ1).le (tiltedBase_pos β).le)
    (BeattyPhase.summable_renewalLogCoeff_of_bound hK)

/-- The convolution series defining the phase is absolutely summable at every
real argument; the profile does not rely on a default value of an undefined sum. -/
theorem summable_tiltedSurvivorPhase_terms {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβ : Irrational β) (t : ℝ) :
    Summable (fun j : ℕ => normalizedSurvivor β (tiltedOddWeight β) (tiltedBase β) j *
      tiltedTerminalPhase β (t-j*β)) :=
  ((summable_tilted_survivor hβ0 hβ1 hβ).mul_left (2*tiltedAmplitude β)).of_norm_bounded
    fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (tilted_survivor_nonneg hβ0 hβ1 j)]
      simpa [mul_comm] using mul_le_mul_of_nonneg_left
        (tiltedTerminalPhase_bound hβ0 hβ1 (t-j*β)) (tilted_survivor_nonneg hβ0 hβ1 j)

private theorem terminal_phase_lower {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (t : ℝ) :
    tiltedAmplitude β ≤ tiltedTerminalPhase β t := by
  rw [tiltedTerminalPhase_eq]
  exact le_mul_of_one_le_right (tiltedAmplitude_pos hβ0 hβ1).le
    (Real.one_le_rpow (by norm_num) (Int.fract_nonneg t))

/-- The survivor phase has a strictly positive lower bound and a finite upper
bound independent of its phase argument. The lower bound comes from the empty word. -/
theorem tiltedSurvivorPhase_bounds {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβ : Irrational β) (t : ℝ) :
    tiltedAmplitude β ≤ tiltedSurvivorPhase β t ∧
      tiltedSurvivorPhase β t ≤ 2*tiltedAmplitude β*
        (∑' j, normalizedSurvivor β (tiltedOddWeight β) (tiltedBase β) j) := by
  have hs := summable_tiltedSurvivorPhase_terms hβ0 hβ1 hβ t
  have hu := summable_tilted_survivor hβ0 hβ1 hβ
  have ha := tiltedAmplitude_pos hβ0 hβ1
  constructor
  · have h := hs.le_tsum 0 (fun j _ =>
      mul_nonneg (tilted_survivor_nonneg hβ0 hβ1 j)
        (ha.le.trans (terminal_phase_lower hβ0 hβ1 _)))
    simp only [normalizedSurvivor_zero, Nat.cast_zero, zero_mul, sub_zero, one_mul] at h
    exact (terminal_phase_lower hβ0 hβ1 t).trans h
  · calc
      _ ≤ ∑' j, (2*tiltedAmplitude β)*
          normalizedSurvivor β (tiltedOddWeight β) (tiltedBase β) j :=
        hs.tsum_le_tsum (fun j => by
          simpa [mul_comm] using mul_le_mul_of_nonneg_left
            ((le_abs_self _).trans (tiltedTerminalPhase_bound hβ0 hβ1 (t-j*β)))
            (tilted_survivor_nonneg hβ0 hβ1 j)) (hu.mul_left _)
      _ = _ := tsum_mul_left

/-- The convolution phase has period one, with no continuity convention needed. -/
theorem tiltedSurvivorPhase_periodic (β : ℝ) : Function.Periodic (tiltedSurvivorPhase β) 1 := by
  intro t
  unfold tiltedSurvivorPhase
  apply tsum_congr
  intro j
  rw [show t+1-j*β = (t-j*β)+1 by ring]
  simp [tiltedTerminalPhase]

/-- At every irrational boundary in `(0,1)`, the actual weighted survivors
have the explicit convolution phase after three-halves normalization. There is
no assumed counting identity, Stirling estimate, or terminal asymptotic. -/
theorem tilted_survivor_phase_limit {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβ : Irrational β) :
    Tendsto (fun n : ℕ => (n : ℝ)*Real.sqrt n*
      normalizedSurvivor β (tiltedOddWeight β) (tiltedBase β) n -
      tiltedSurvivorPhase β (n*β)) atTop (𝓝 0) := by
  simpa only [tiltedSurvivorPhase, sub_mul] using
    normalizedSurvivor_phase_limit β hβ (tiltedOddWeight_pos hβ0 hβ1).le (tiltedBase_pos β).le
      (tiltedTerminalPhase_bound hβ0 hβ1) (tilted_endpoint_phase_limit hβ0 hβ1)

/-- The general survivor theorem in the original reciprocal-slope parameter.
Every irrational `α > 1` is included, without an upper bound on the slope. -/
theorem tilted_survivor_phase_limit_reciprocal {α : ℝ} (hα1 : 1 < α) (hα : Irrational α) :
    Tendsto (fun n : ℕ => (n : ℝ)*Real.sqrt n*
      normalizedSurvivor (1/α) (tiltedOddWeight (1/α)) (tiltedBase (1/α)) n -
      tiltedSurvivorPhase (1/α) (n/α)) atTop (𝓝 0) := by
  have hα0 : 0 < α := lt_trans zero_lt_one hα1
  have hβ0 : 0 < 1/α := one_div_pos.mpr hα0
  have hβ1 : 1/α < 1 := (div_lt_one hα0).mpr hα1
  have hβ : Irrational (1/α) := by simpa only [one_div] using hα.inv
  simpa only [div_eq_mul_inv, one_mul] using tilted_survivor_phase_limit hβ0 hβ1 hβ

end Problems.Juggler.BeattySlope

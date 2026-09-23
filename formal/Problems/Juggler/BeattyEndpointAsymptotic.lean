import Problems.Juggler.BeattyBinomialBounds

/-!
# The terminal phase asymptotic

Stirling's formula and a dominated geometric-tail limit retain the exact
fractional-part correction at the strict binomial cutoff. In particular,
no continuity assumption at the jumps of the phase kernel is used.
-/

namespace Problems.Juggler.BeattyPhase

open Filter Topology Finset
open PaperBThreshold

private theorem beta_pos : 0 < beta := by linarith [beta_gt_five_eighths]

private theorem q_pos : 0 < 1-beta := sub_pos.2 beta_lt_one

private theorem ratio_bounds : 0 < terminalRatio ∧ terminalRatio < 1 := by
  constructor
  · exact div_pos q_pos beta_pos
  · exact (div_lt_one beta_pos).2 (by linarith [beta_gt_five_eighths])

private theorem cutoff_ratio_limit :
    Tendsto (fun n : ℕ => (endpointCutoff n : ℝ)/n) atTop (𝓝 beta) := by
  have h := (tendsto_nat_floor_mul_div_atTop beta_pos.le).comp
    tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n : ℕ => (1 : ℝ)/n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  simpa [endpointCutoff, Nat.cast_add, Nat.cast_one, add_div, mul_comm] using h.add hi

private theorem complement_ratio_limit :
    Tendsto (fun n : ℕ => ((n-endpointCutoff n : ℕ) : ℝ)/n) atTop (𝓝 (1-beta)) := by
  apply (tendsto_const_nhds.sub cutoff_ratio_limit).congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [Nat.cast_sub (endpointCutoff_le (by omega)), sub_div, div_self hn0]

private theorem cutoff_atTop : Tendsto endpointCutoff atTop atTop := by
  change Tendsto (fun n : ℕ => ⌊(n : ℝ)*beta⌋₊+1) atTop atTop
  simpa [endpointCutoff, Function.comp_def, mul_comm] using
    (tendsto_add_atTop_nat 1).comp (tendsto_nat_floor_mul_atTop beta beta_pos)

private theorem complement_atTop : Tendsto (fun n => n-endpointCutoff n) atTop atTop := by
  apply tendsto_atTop_mono' (f₁ := fun n : ℕ => ⌊((1-beta)/2)*(n : ℝ)⌋₊)
  · filter_upwards [eventually_ge_atTop 6] with n hn
    have hc := endpointCutoff_bounds n
    have hb := mul_le_mul_of_nonneg_right beta_le_two_thirds (Nat.cast_nonneg n : (0:ℝ) ≤ n)
    have hnR : (6 : ℝ) ≤ n := by exact_mod_cast hn
    have hfloor := Nat.floor_le (mul_nonneg (by linarith [q_pos] : 0 ≤ (1-beta)/2)
      (Nat.cast_nonneg n))
    have hkn := endpointCutoff_le (by omega : 0 < n)
    have hcast : ((n-endpointCutoff n : ℕ) : ℝ) = n-endpointCutoff n := Nat.cast_sub hkn
    exact_mod_cast (show (⌊((1-beta)/2)*(n : ℝ)⌋₊ : ℝ) ≤ (n-endpointCutoff n : ℕ) by
      rw [hcast]; nlinarith)
  · exact tendsto_nat_floor_mul_atTop _ (by linarith [q_pos])

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

private noncomputable def entropyRemainder (n : ℕ) : ℝ :=
  let k : ℝ := endpointCutoff n
  let l : ℝ := n-endpointCutoff n
  k*Real.log (k/(n*beta))+l*Real.log (l/(n*(1-beta)))

private theorem entropyRemainder_bounds {n : ℕ} (hn : 6 ≤ n) :
    0 ≤ entropyRemainder n ∧ entropyRemainder n ≤ 1/((n : ℝ)*beta*(1-beta)) := by
  let t : ℝ := n
  let k : ℝ := endpointCutoff n
  let l := t-k
  have ht : 0 < t := by dsimp [t]; exact_mod_cast (by omega : 0 < n)
  have ht6 : 6 ≤ t := by dsimp [t]; exact_mod_cast hn
  have hc := endpointCutoff_bounds n
  change t*beta < k ∧ k ≤ t*beta+1 at hc
  have hb := mul_le_mul_of_nonneg_left beta_le_two_thirds ht.le
  have hk : 0 < k := (mul_pos ht beta_pos).trans hc.1
  have hl : 0 < l := by dsimp [l]; nlinarith
  have htb := mul_pos ht beta_pos
  have htq := mul_pos ht q_pos
  change 0 ≤ k*Real.log (k/(t*beta))+l*Real.log (l/(t*(1-beta))) ∧ _
  constructor
  · have ha := mul_le_mul_of_nonneg_left
      (Real.one_sub_inv_le_log_of_pos (div_pos hk htb)) hk.le
    have hb' := mul_le_mul_of_nonneg_left
      (Real.one_sub_inv_le_log_of_pos (div_pos hl htq)) hl.le
    have he : k*(1-(k/(t*beta))⁻¹) = k-t*beta := by field_simp
    have he' : l*(1-(l/(t*(1-beta)))⁻¹) = l-t*(1-beta) := by field_simp
    rw [he] at ha
    rw [he'] at hb'
    dsimp [l] at *
    linarith
  · have ha := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hk htb)) hk.le
    have hb' := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hl htq)) hl.le
    have he : k*(k/(t*beta)-1)+l*(l/(t*(1-beta))-1) =
        (k-t*beta)^2/(t*beta*(1-beta)) := by
      dsimp [l]
      field_simp [ne_of_gt ht, ne_of_gt beta_pos, ne_of_gt q_pos]
      ring
    have he' : (k-t*beta)^2 ≤ 1 := by nlinarith [hc.1, hc.2]
    have hh := div_le_div_of_nonneg_right he' (mul_pos htb q_pos).le
    change k*Real.log (k/(t*beta))+l*Real.log (l/(t*(1-beta))) ≤ _
    linarith

private theorem entropyRemainder_limit : Tendsto entropyRemainder atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => 1/((n : ℝ)*beta*(1-beta))) atTop (𝓝 0) := by
    apply tendsto_const_nhds.div_atTop
    simpa [mul_comm, mul_left_comm] using
      (tendsto_natCast_atTop_atTop.const_mul_atTop beta_pos).const_mul_atTop q_pos
  exact squeeze_zero' (eventually_atTop.2 ⟨6, fun n hn => (entropyRemainder_bounds hn).1⟩)
    (eventually_atTop.2 ⟨6, fun n hn => (entropyRemainder_bounds hn).2⟩) h

private theorem cutoff_offset (n : ℕ) :
    (endpointCutoff n : ℝ)-n*beta = 1-Int.fract (n*beta) := by
  simp only [endpointCutoff, Nat.cast_add, Nat.cast_one, Int.fract]
  rw [natCast_floor_eq_intCast_floor (mul_nonneg (Nat.cast_nonneg n) beta_pos.le)]
  ring

private theorem firstTerm_log_identity {n : ℕ} (hn : 6 ≤ n) :
    Real.log (endpointFirstTermScaled n) -
      (1-Int.fract (n*beta))*Real.log terminalRatio =
    factorialError n-factorialError (endpointCutoff n)-factorialError (n-endpointCutoff n) -
      entropyRemainder n - (Real.log ((endpointCutoff n : ℝ)/n) +
        Real.log (((n-endpointCutoff n : ℕ) : ℝ)/n))/2 := by
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
  have hk : (0 : ℝ) < k := (mul_pos ht beta_pos).trans hb.1
  have hl : (0 : ℝ) < l := by
    have hh := mul_le_mul_of_nonneg_left beta_le_two_thirds ht.le
    nlinarith
  have hc : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hkn
  have hf : (n.choose k : ℝ)*(k.factorial : ℝ)*(l.factorial : ℝ) = n.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkn
  have hfLog := congrArg Real.log hf
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (ne_of_gt hc) (by positivity)] at hfLog
  have hoff := cutoff_offset n
  change (k : ℝ)-n*beta = _ at hoff
  rw [← hoff]
  change Real.log (Real.sqrt n*(n.choose k : ℝ)/survivorBase^n) - _ = _
  rw [Real.log_div (by positivity) (ne_of_gt (pow_pos survivorBase_pos n)),
    Real.log_mul (by positivity) (ne_of_gt hc), Real.log_sqrt ht.le, Real.log_pow]
  change _ = factorialError n-factorialError k-factorialError l-entropyRemainder n - _
  have hcast : ((n-k : ℕ) : ℝ) = n-k := Nat.cast_sub hkn
  unfold factorialError entropyRemainder terminalRatio
  change _ = _ - ((k : ℝ)*Real.log ((k : ℝ)/(n*beta)) +
    ((n : ℝ)-k)*Real.log (((n : ℝ)-k)/(n*(1-beta)))) - _
  rw [← hcast]
  change _ = _ - ((k : ℝ)*Real.log ((k : ℝ)/(n*beta)) +
    (l : ℝ)*Real.log ((l : ℝ)/(n*(1-beta)))) - _
  rw [log_survivorBase, Real.log_div (ne_of_gt hk) (ne_of_gt (mul_pos ht beta_pos)),
    Real.log_div (ne_of_gt hl) (ne_of_gt (mul_pos ht q_pos)),
    Real.log_mul (ne_of_gt ht) (ne_of_gt beta_pos),
    Real.log_mul (ne_of_gt ht) (ne_of_gt q_pos),
    Real.log_div (ne_of_gt q_pos) (ne_of_gt beta_pos),
    Real.log_div (ne_of_gt hk) (ne_of_gt ht),
    Real.log_div (ne_of_gt hl) (ne_of_gt ht)]
  rw [← hsR]
  linear_combination hfLog

private theorem firstTerm_log_limit :
    Tendsto (fun n : ℕ => Real.log (endpointFirstTermScaled n) -
      (1-Int.fract (n*beta))*Real.log terminalRatio) atTop (𝓝 (Real.log terminalAmplitude)) := by
  have h := (((factorialError_limit.sub (factorialError_limit.comp cutoff_atTop)).sub
    (factorialError_limit.comp complement_atTop)).sub entropyRemainder_limit).sub
      (((cutoff_ratio_limit.log (ne_of_gt beta_pos)).add
        (complement_ratio_limit.log (ne_of_gt q_pos))).div_const 2)
  have he : Real.log (Real.sqrt Real.pi)+Real.log 2/2 -
      (Real.log (Real.sqrt Real.pi)+Real.log 2/2) -
      (Real.log (Real.sqrt Real.pi)+Real.log 2/2) - 0 -
      (Real.log beta+Real.log (1-beta))/2 = Real.log terminalAmplitude := by
    have hb := beta_pos
    have hq := q_pos
    unfold terminalAmplitude
    rw [Real.log_inv, Real.log_sqrt Real.pi_pos.le,
      Real.log_sqrt (by positivity : 0 ≤ 2*Real.pi*beta*(1-beta)),
      Real.log_mul (by positivity) (ne_of_gt q_pos),
      Real.log_mul (by positivity) (ne_of_gt beta_pos),
      Real.log_mul (by norm_num) (ne_of_gt Real.pi_pos)]
    ring
  rw [he] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 6] with n hn
  exact (firstTerm_log_identity hn).symm

private theorem zero_mul_bounded {f g : ℕ → ℝ} {C : ℝ}
    (hf : Tendsto f atTop (𝓝 0)) (hg : ∀ n, |g n| ≤ C) :
    Tendsto (fun n => f n*g n) atTop (𝓝 0) := by
  refine squeeze_zero_norm (a := fun n => |f n| * C) (fun n => ?_) ?_
  · rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hg n) (abs_nonneg _)
  · simpa using hf.abs.mul_const C

/-- Stirling's formula for the first strict binomial term, with the exact
moving fractional-part factor retained. The error is additive and tends to zero. -/
theorem endpoint_first_term_phase_limit :
    Tendsto (fun n : ℕ => endpointFirstTermScaled n -
      terminalAmplitude*terminalRatio^(1-Int.fract (n*beta))) atTop (𝓝 0) := by
  have ha : 0 < terminalAmplitude := by
    have hb := beta_pos
    have hq := q_pos
    unfold terminalAmplitude
    positivity
  have h := (Real.continuous_exp.tendsto _).comp firstTerm_log_limit
  rw [Real.exp_log ha] at h
  have h' : Tendsto (fun n : ℕ => endpointFirstTermScaled n /
      terminalRatio^(1-Int.fract (n*beta))) atTop (𝓝 terminalAmplitude) := by
    apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp only [Function.comp_apply]
    rw [Real.exp_sub, Real.exp_log (endpointFirstTermScaled_pos (by omega)),
      Real.rpow_def_of_pos ratio_bounds.1]
    rw [mul_comm (Real.log terminalRatio)]
  have hb (n : ℕ) : |terminalRatio^(1-Int.fract (n*beta))| ≤ 1 := by
    rw [abs_of_pos (Real.rpow_pos_of_pos ratio_bounds.1 _)]
    exact Real.rpow_le_one ratio_bounds.1.le ratio_bounds.2.le
      (by linarith [Int.fract_lt_one ((n : ℝ)*beta)])
  have hz := zero_mul_bounded (by simpa using h'.sub_const terminalAmplitude) hb
  apply hz.congr'
  exact Eventually.of_forall fun n => by
    have hp := ne_of_gt (Real.rpow_pos_of_pos ratio_bounds.1 (1-Int.fract ((n : ℝ)*beta)))
    dsimp
    field_simp

private noncomputable def binomialRatio (n j : ℕ) : ℝ :=
  (n.choose (endpointCutoff n+j) : ℝ)/(n.choose (endpointCutoff n) : ℝ)

private theorem adjacent_ratio_limit (j : ℕ) :
    Tendsto (fun n : ℕ => ((n-(endpointCutoff n+j) : ℕ) : ℝ)/(endpointCutoff n+j+1 : ℕ))
      atTop (𝓝 terminalRatio) := by
  have hc (c : ℝ) : Tendsto (fun n : ℕ => c/n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h := (((tendsto_const_nhds (x := (1 : ℝ))).sub cutoff_ratio_limit).sub (hc j)).div
    (cutoff_ratio_limit.add (hc (j+1))) (by simpa using ne_of_gt beta_pos)
  simp only [sub_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1, complement_atTop.eventually (eventually_ge_atTop j)] with n hn hj
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hk := endpointCutoff_le (by omega : 0 < n)
  have hkn : endpointCutoff n+j ≤ n := by omega
  dsimp
  simp only [Nat.cast_sub hkn, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

private theorem binomialRatio_limit (j : ℕ) :
    Tendsto (fun n => binomialRatio n j) atTop (𝓝 (terminalRatio^j)) := by
  induction j with
  | zero =>
    simp only [pow_zero]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hc : (n.choose (endpointCutoff n) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (endpointCutoff_le (by omega))).ne'
    simp [binomialRatio, hc]
  | succ j ih =>
    rw [pow_succ]
    apply (ih.mul (adjacent_ratio_limit j)).congr'
    exact Eventually.of_forall fun n => by
      have he : (n.choose (endpointCutoff n+j+1) : ℝ)*(endpointCutoff n+j+1 : ℕ) =
          (n.choose (endpointCutoff n+j) : ℝ)*(n-(endpointCutoff n+j) : ℕ) := by
        exact_mod_cast Nat.choose_succ_right_eq n (endpointCutoff n+j)
      have hp : ((endpointCutoff n+j+1 : ℕ) : ℝ) ≠ 0 := by positivity
      dsimp [binomialRatio]
      rw [show endpointCutoff n+(j+1) = endpointCutoff n+j+1 by omega]
      rw [div_mul_div_comm, ← he]
      field_simp

private theorem binomialRatio_bound (n j : ℕ) : |binomialRatio n j| ≤ (3/5 : ℝ)^j := by
  unfold binomialRatio
  rw [abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
  by_cases hn : n=0
  · subst n
    simp [endpointCutoff]
    positivity
  · have hc : (0 : ℝ) < n.choose (endpointCutoff n) := by
      exact_mod_cast Nat.choose_pos (endpointCutoff_le (Nat.pos_of_ne_zero hn))
    exact (div_le_iff₀ hc).2 (by simpa [mul_comm] using endpoint_choose_shift_bound n j)

private theorem tail_ratio_eq_tsum (n : ℕ) :
    (endpointCount n : ℝ)/(n.choose (endpointCutoff n) : ℝ) = ∑' j, binomialRatio n j := by
  rw [endpointCount_eq_tail, Nat.cast_sum, sum_Ico_eq_sum_range, sum_div]
  symm
  apply tsum_eq_sum
  intro j hj
  have hj' : n+1-endpointCutoff n ≤ j := by simpa only [mem_range, not_lt] using hj
  unfold binomialRatio
  rw [Nat.choose_eq_zero_of_lt (by omega : n < endpointCutoff n+j)]
  simp

/-- The strict binomial tail divided by its first term converges to the
geometric-tail factor. Domination is uniform over all subsequent terms. -/
theorem endpoint_binomial_tail_ratio_limit :
    Tendsto (fun n : ℕ => (endpointCount n : ℝ)/(n.choose (endpointCutoff n) : ℝ))
      atTop (𝓝 (1/(1-terminalRatio))) := by
  have h := tendsto_tsum_of_dominated_convergence
    (summable_geometric_of_abs_lt_one (by norm_num : |(3/5 : ℝ)| < 1))
    binomialRatio_limit (Eventually.of_forall fun n j => by
      simpa only [Real.norm_eq_abs] using binomialRatio_bound n j)
  rw [tsum_geometric_of_abs_lt_one (by simpa [abs_of_pos ratio_bounds.1] using ratio_bounds.2)] at h
  simpa only [← tail_ratio_eq_tsum, one_div] using h

/-- The finer terminal phase asymptotic for the actual endpoint counts.
Both the Stirling correction and the geometric tail have been proved here;
there are no counting or asymptotic premises. -/
theorem endpoint_phase_asymptotic : EndpointPhaseAsymptotic := by
  let R (n : ℕ) : ℝ := (endpointCount n : ℝ)/(n.choose (endpointCutoff n) : ℝ)
  let P (n : ℕ) : ℝ := terminalAmplitude*terminalRatio^(1-Int.fract (n*beta))
  have ha : 0 < terminalAmplitude := by
    have hb := beta_pos
    have hq := q_pos
    unfold terminalAmplitude
    positivity
  have hR (n : ℕ) : |R n| ≤ 5/2 := by
    dsimp [R]
    rw [abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
    by_cases hn : n=0
    · subst n; norm_num [endpointCount]
    · have hc : (0 : ℝ) < n.choose (endpointCutoff n) := by
        exact_mod_cast Nat.choose_pos (endpointCutoff_le (Nat.pos_of_ne_zero hn))
      exact (div_le_iff₀ hc).2 (endpointCount_first_term_bounds (Nat.pos_of_ne_zero hn)).2
  have hP (n : ℕ) : |P n| ≤ terminalAmplitude := by
    dsimp [P]
    rw [abs_mul, abs_of_pos ha, abs_of_pos (Real.rpow_pos_of_pos ratio_bounds.1 _)]
    exact mul_le_of_le_one_right ha.le (Real.rpow_le_one ratio_bounds.1.le ratio_bounds.2.le
      (by linarith [Int.fract_lt_one ((n : ℝ)*beta)]))
  have h1 := zero_mul_bounded endpoint_first_term_phase_limit hR
  have h2 := zero_mul_bounded
    (by simpa using endpoint_binomial_tail_ratio_limit.sub_const (1/(1-terminalRatio))) hP
  have h := h1.add h2
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hc : (n.choose (endpointCutoff n) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (endpointCutoff_le (by omega))).ne'
  dsimp [R, P, endpointFirstTermScaled, endpointNormalized, terminalPhase]
  field_simp
  ring

/-- The actual survivor counts have the explicit moving phase profile, with
additive error tending to zero after the sharp three-halves normalization. -/
theorem survivor_phase_limit_unconditional :
    Tendsto (fun n : ℕ => (n : ℝ)*Real.sqrt n*survivorNormalized n -
      survivorPhase ((n : ℝ)*beta)) atTop (𝓝 0) :=
  survivor_phase_limit survivor_exponential_identity endpoint_phase_asymptotic

/-- The explicit convolution profile satisfies the existing relative
survivor asymptotic predicate without any unproved classical input. -/
theorem meanderShape_survivorPhase_unconditional :
    PaperBSurvivorAsymptotic.MeanderShape survivorPhase :=
  meanderShape_survivorPhase survivor_exponential_identity endpoint_phase_asymptotic

end Problems.Juggler.BeattyPhase

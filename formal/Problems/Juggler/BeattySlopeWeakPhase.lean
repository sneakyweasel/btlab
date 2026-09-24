import Problems.Juggler.BeattySlopeWeakCounting

/-!
# The weak tilted endpoint and survivor phases at every boundary

The weak endpoint sum differs from the strict one only when `n*β` is an
integer, by the tie term `C(n, n*β) z^(n*β)`. Relative to the first strict
term this tie has ratio `(n*β+1)/((n-n*β)*z)`, which tends to two under the
chosen tilt. Hence the weak first term, taken at `⌈n*β⌉`, has the
left-continuous phase `A*(1/2)^fract(-n*β)`, and the weak endpoint phase is the
left-continuous version of the strict one. The weak renewal recurrence then
transfers this phase to the actual survivors at every `0 < β < 1`.
-/

namespace Problems.Juggler.BeattySlope

open Finset Filter Topology

/-- The weak binomial cutoff `⌈n*β⌉`, the least odd count allowed at depth `n`. -/
noncomputable def weakCutoff (β : ℝ) (n : ℕ) : ℕ := ⌈(n : ℝ)*β⌉₊

/-- Square-root normalization of the first weak tilted binomial term. -/
noncomputable def weakFirstTermScaled (β : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt n*(n.choose (weakCutoff β n) : ℝ)*
    tiltedOddWeight β^weakCutoff β n / tiltedBase β^n

/-- Left-continuous periodic endpoint phase; it equals `tiltedTerminalPhase`
off the integers and takes the left-limit value `2*A` at integers. -/
noncomputable def weakTerminalPhase (β t : ℝ) : ℝ :=
  tiltedAmplitude β*(2 : ℝ)^(1-Int.fract (-t))

/-- Weak endpoint weights with an exponential normalization. -/
noncomputable def normalizedWeakEndpoint (β z v : ℝ) (n : ℕ) : ℝ :=
  weakEndpointWeight β z n / v^n

private noncomputable def firstErr (β : ℝ) (n : ℕ) : ℝ :=
  tiltedFirstTermScaled β n - tiltedAmplitude β*(1/2 : ℝ)^(1-Int.fract ((n : ℝ)*β))

private noncomputable def tieRatio (β : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ)*β+1)/(((n : ℝ)-n*β)*tiltedOddWeight β)

private theorem fract_eq_sub_floor {x : ℝ} (hx : 0 ≤ x) : Int.fract x = x - ⌊x⌋₊ := by
  rw [Int.fract, ← natCast_floor_eq_intCast_floor hx]

private theorem tieRatio_limit {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Tendsto (tieRatio β) atTop (𝓝 2) := by
  have hz := tiltedOddWeight_pos hβ0 hβ1
  have hq : 0 < 1-β := sub_pos.mpr hβ1
  have hi : Tendsto (fun n : ℕ => (1 : ℝ)/n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h := (hi.const_add β).div_const ((1-β)*tiltedOddWeight β)
  have h2 : (β + 0)/((1-β)*tiltedOddWeight β) = 2 := by
    unfold tiltedOddWeight
    field_simp
    ring
  rw [h2] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  unfold tieRatio
  field_simp

private theorem weak_first_term_bound {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {n : ℕ} (hn : 0 < n) :
    |weakFirstTermScaled β n - tiltedAmplitude β*(1/2 : ℝ)^Int.fract (-((n : ℝ)*β))| ≤
      |firstErr β n| + |firstErr β n| * |tieRatio β n| +
        tiltedAmplitude β/2*|tieRatio β n - 2| := by
  have hA := tiltedAmplitude_pos hβ0 hβ1
  have hz := tiltedOddWeight_pos hβ0 hβ1
  have hv := tiltedBase_pos β
  have hx0 : 0 ≤ (n : ℝ)*β := by positivity
  have hp1 := mul_nonneg (abs_nonneg (firstErr β n)) (abs_nonneg (tieRatio β n))
  have hp2 := mul_nonneg (by positivity : 0 ≤ tiltedAmplitude β/2)
    (abs_nonneg (tieRatio β n - 2))
  by_cases hf : Int.fract ((n : ℝ)*β) = 0
  · set k := ⌊(n : ℝ)*β⌋₊ with hk
    have hxk : (n : ℝ)*β = k := by
      have := fract_eq_sub_floor hx0
      linarith
    have hwc : weakCutoff β n = k := by
      unfold weakCutoff
      rw [hxk, Nat.ceil_natCast]
    have hec : endpointCutoff β n = k+1 := rfl
    have hkn : k < n := by
      have : (k : ℝ) < n := by
        rw [← hxk]
        exact mul_lt_of_lt_one_right (by exact_mod_cast hn) hβ1
      exact_mod_cast this
    have hneg : Int.fract (-((n : ℝ)*β)) = 0 := Int.fract_neg_eq_zero.2 hf
    have hchoose : (n.choose (k+1) : ℝ)*((k : ℝ)+1) = (n.choose k : ℝ)*((n : ℝ)-k) := by
      have h := Nat.choose_succ_right_eq n k
      have h' : ((n.choose (k+1) * (k+1) : ℕ) : ℝ) = ((n.choose k * (n-k) : ℕ) : ℝ) := by
        rw [h]
      push_cast [Nat.cast_sub hkn.le] at h'
      exact h'
    have hnk : (n : ℝ) - k ≠ 0 := by
      have : (k : ℝ) < n := by exact_mod_cast hkn
      linarith
    have hW : weakFirstTermScaled β n = tiltedFirstTermScaled β n * tieRatio β n := by
      unfold weakFirstTermScaled tiltedFirstTermScaled tieRatio
      rw [hwc, hec, hxk, pow_succ]
      have hck : (n.choose k : ℝ) = (n.choose (k+1) : ℝ)*((k : ℝ)+1)/((n : ℝ)-k) := by
        rw [eq_div_iff hnk, hchoose]
      rw [hck]
      field_simp
    have hF : tiltedFirstTermScaled β n = firstErr β n + tiltedAmplitude β/2 := by
      unfold firstErr
      rw [hf]
      norm_num
      ring
    rw [hW, hneg, Real.rpow_zero, hF]
    have he : (firstErr β n + tiltedAmplitude β/2)*tieRatio β n - tiltedAmplitude β*1 =
        firstErr β n * tieRatio β n + tiltedAmplitude β/2*(tieRatio β n - 2) := by ring
    rw [he]
    calc
      _ ≤ |firstErr β n * tieRatio β n| + |tiltedAmplitude β/2*(tieRatio β n - 2)| :=
        abs_add_le _ _
      _ = |firstErr β n| * |tieRatio β n| + tiltedAmplitude β/2*|tieRatio β n - 2| := by
        rw [abs_mul, abs_mul, abs_of_pos (by positivity : 0 < tiltedAmplitude β/2)]
      _ ≤ _ := by linarith [abs_nonneg (firstErr β n)]
  · have hwc : weakCutoff β n = endpointCutoff β n := by
      unfold weakCutoff endpointCutoff
      apply (Nat.ceil_eq_iff (by omega)).2
      have hfl := fract_eq_sub_floor hx0
      have hpos : 0 < Int.fract ((n : ℝ)*β) :=
        lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm hf)
      constructor
      · simp only [Nat.add_sub_cancel]
        linarith
      · push_cast
        linarith [Nat.lt_floor_add_one ((n : ℝ)*β)]
    have hW : weakFirstTermScaled β n = tiltedFirstTermScaled β n := by
      unfold weakFirstTermScaled tiltedFirstTermScaled
      rw [hwc]
    rw [hW, Int.fract_neg hf]
    have he : tiltedFirstTermScaled β n -
        tiltedAmplitude β*(1/2 : ℝ)^(1-Int.fract ((n : ℝ)*β)) = firstErr β n := rfl
    rw [he]
    linarith [le_abs_self (firstErr β n), abs_nonneg (firstErr β n)]

/-- For every fixed boundary in `(0,1)`, the first weak tilted binomial term
has the left-continuous moving Stirling phase `A*(1/2)^fract(-n*β)`. -/
theorem weak_first_term_phase_limit {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun n : ℕ => weakFirstTermScaled β n -
      tiltedAmplitude β*(1/2 : ℝ)^Int.fract (-((n : ℝ)*β))) atTop (𝓝 0) := by
  have he : Tendsto (firstErr β) atTop (𝓝 0) := tilted_first_term_phase_limit hβ0 hβ1
  have hρ := tieRatio_limit hβ0 hβ1
  have hlim : Tendsto (fun n => |firstErr β n| + |firstErr β n| * |tieRatio β n| +
      tiltedAmplitude β/2*|tieRatio β n - 2|) atTop (𝓝 0) := by
    have h := (he.abs.add (he.abs.mul hρ.abs)).add
      ((hρ.sub_const 2).abs.const_mul (tiltedAmplitude β/2))
    simpa using h
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [Real.norm_eq_abs]
  exact weak_first_term_bound hβ0 hβ1 (by omega)

private theorem weak_sub_strict (β z : ℝ) (n : ℕ) :
    weakEndpointWeight β z n - endpointWeight β z n =
      ∑ k ∈ range (n+1), if (n : ℝ)*β = k then (n.choose k : ℝ)*z^k else 0 := by
  unfold weakEndpointWeight endpointWeight
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro k _
  by_cases h1 : (n : ℝ)*β < k
  · simp [h1, h1.le, h1.ne]
  · by_cases h2 : (n : ℝ)*β = k
    · simp [h2]
    · have h3 : ¬ (n : ℝ)*β ≤ k := fun h => h1 (lt_of_le_of_ne h h2)
      simp [h1, h2, h3]

private theorem weak_endpoint_bound {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {n : ℕ} (hn : 0 < n) :
    |(Real.sqrt n*normalizedWeakEndpoint β (tiltedOddWeight β) (tiltedBase β) n -
        weakTerminalPhase β (n*β)) -
      (Real.sqrt n*normalizedEndpoint β (tiltedOddWeight β) (tiltedBase β) n -
        tiltedTerminalPhase β (n*β))| ≤
    |weakFirstTermScaled β n - tiltedAmplitude β*(1/2 : ℝ)^Int.fract (-((n : ℝ)*β))| := by
  have he : (Real.sqrt n*normalizedWeakEndpoint β (tiltedOddWeight β) (tiltedBase β) n -
        weakTerminalPhase β (n*β)) -
      (Real.sqrt n*normalizedEndpoint β (tiltedOddWeight β) (tiltedBase β) n -
        tiltedTerminalPhase β (n*β)) =
      Real.sqrt n*(weakEndpointWeight β (tiltedOddWeight β) n -
        endpointWeight β (tiltedOddWeight β) n)/tiltedBase β^n -
        (weakTerminalPhase β (n*β) - tiltedTerminalPhase β (n*β)) := by
    unfold normalizedWeakEndpoint normalizedEndpoint
    ring
  rw [he, weak_sub_strict]
  have hx0 : 0 ≤ (n : ℝ)*β := by positivity
  by_cases hf : Int.fract ((n : ℝ)*β) = 0
  · set k := ⌊(n : ℝ)*β⌋₊ with hk
    have hxk : (n : ℝ)*β = k := by
      have := fract_eq_sub_floor hx0
      linarith
    have hkn : k < n+1 := by
      have : (k : ℝ) ≤ n := by
        rw [← hxk]
        exact mul_le_of_le_one_right (Nat.cast_nonneg n) hβ1.le
      have : k ≤ n := by exact_mod_cast this
      omega
    have hwc : weakCutoff β n = k := by
      unfold weakCutoff
      rw [hxk, Nat.ceil_natCast]
    have hs : (∑ j ∈ range (n+1), if (n : ℝ)*β = j then
        (n.choose j : ℝ)*tiltedOddWeight β^j else 0) =
        (n.choose k : ℝ)*tiltedOddWeight β^k := by
      rw [hxk]
      simp only [Nat.cast_inj]
      rw [sum_ite_eq]
      simp [hkn]
    rw [hs]
    simp only [weakTerminalPhase, tiltedTerminalPhase_eq, hf, Int.fract_neg_eq_zero.2 hf,
      sub_zero, Real.rpow_one, Real.rpow_zero]
    unfold weakFirstTermScaled
    rw [hwc]
    apply le_of_eq
    congr 1
    ring
  · have hs : (∑ j ∈ range (n+1), if (n : ℝ)*β = j then
        (n.choose j : ℝ)*tiltedOddWeight β^j else 0) = 0 := by
      apply sum_eq_zero
      intro j _
      rw [if_neg]
      intro h
      apply hf
      rw [h]
      simp
    rw [hs]
    simp only [weakTerminalPhase, tiltedTerminalPhase_eq, Int.fract_neg hf, sub_sub_cancel,
      sub_self, mul_zero, zero_div, abs_zero]
    exact abs_nonneg _

/-- The weak tilted endpoint sums have the left-continuous periodic phase
`weakTerminalPhase` for every real `0 < β < 1`, rational boundaries included. -/
theorem weak_endpoint_phase_limit {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun n : ℕ => Real.sqrt n*
      normalizedWeakEndpoint β (tiltedOddWeight β) (tiltedBase β) n -
      weakTerminalPhase β (n*β)) atTop (𝓝 0) := by
  have h1 := tilted_endpoint_phase_limit hβ0 hβ1
  have h2 : Tendsto (fun n : ℕ =>
      (Real.sqrt n*normalizedWeakEndpoint β (tiltedOddWeight β) (tiltedBase β) n -
        weakTerminalPhase β (n*β)) -
      (Real.sqrt n*normalizedEndpoint β (tiltedOddWeight β) (tiltedBase β) n -
        tiltedTerminalPhase β (n*β))) atTop (𝓝 0) := by
    have h3 : Tendsto (fun n : ℕ => |weakFirstTermScaled β n -
        tiltedAmplitude β*(1/2 : ℝ)^Int.fract (-((n : ℝ)*β))|) atTop (𝓝 0) := by
      have h4 := (weak_first_term_phase_limit hβ0 hβ1).abs
      rw [abs_zero] at h4
      exact h4
    refine squeeze_zero_norm' ?_ h3
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [Real.norm_eq_abs]
    exact weak_endpoint_bound hβ0 hβ1 (n := n) (by omega)
  have h := h1.add h2
  rw [add_zero] at h
  exact h.congr fun n => by ring

/-- The weak terminal phase lies between `A` and `2*A` at every real argument. -/
theorem weakTerminalPhase_bounds {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (t : ℝ) :
    tiltedAmplitude β ≤ weakTerminalPhase β t ∧
      weakTerminalPhase β t ≤ 2*tiltedAmplitude β := by
  have hA := tiltedAmplitude_pos hβ0 hβ1
  have h0 := Int.fract_nonneg (-t)
  have h1 := Int.fract_lt_one (-t)
  unfold weakTerminalPhase
  constructor
  · exact le_mul_of_one_le_right hA.le (Real.one_le_rpow (by norm_num) (by linarith))
  · rw [mul_comm]
    apply mul_le_mul_of_nonneg_right _ hA.le
    calc
      (2 : ℝ)^(1-Int.fract (-t)) ≤ (2 : ℝ)^(1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one 2

/-- The weak terminal phase is bounded in absolute value by `2*A`. -/
theorem weakTerminalPhase_abs_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (t : ℝ) :
    |weakTerminalPhase β t| ≤ 2*tiltedAmplitude β := by
  have h := weakTerminalPhase_bounds hβ0 hβ1 t
  rw [abs_of_nonneg ((tiltedAmplitude_pos hβ0 hβ1).le.trans h.1)]
  exact h.2

/-- The weak terminal phase has period one. -/
theorem weakTerminalPhase_periodic (β : ℝ) : Function.Periodic (weakTerminalPhase β) 1 := by
  intro t
  unfold weakTerminalPhase
  rw [show -(t+1) = -t - 1 by ring, Int.fract_sub_one]

/-- Nonnegative letter weights and base give nonnegative weak endpoints. -/
theorem normalizedWeakEndpoint_nonneg (β : ℝ) {z v : ℝ} (hz : 0 ≤ z) (hv : 0 ≤ v)
    (n : ℕ) : 0 ≤ normalizedWeakEndpoint β z v n :=
  div_nonneg (weakEndpointWeight_nonneg β hz n) (pow_nonneg hv n)

/-- At every real boundary, the normalized survivors are the formal renewal
exponential of the normalized weak endpoint sums. -/
theorem survivor_eq_weak_renewal (β z v : ℝ) :
    normalizedSurvivor β z v = BeattyPhase.renewalCoeff (normalizedWeakEndpoint β z v) := by
  apply BeattyPhase.eq_renewalCoeff_of_recurrence (normalizedSurvivor_zero β z v)
  intro n
  unfold normalizedSurvivor normalizedWeakEndpoint
  calc
    _ = ((n : ℝ)*survivorWeight β z n)/v^n := by ring
    _ = (∑ j ∈ range n, weakEndpointWeight β z (n-j)*survivorWeight β z j)/v^n := by
      rw [survivorWeight_weak_recurrence β]
    _ = ∑ j ∈ range n, (weakEndpointWeight β z (n-j)*survivorWeight β z j)/v^n := by
      rw [sum_div]
    _ = _ := by
      apply sum_congr rfl
      intro j hj
      rw [div_mul_div_comm, ← pow_add, Nat.sub_add_cancel (mem_range.mp hj).le]

private theorem survivor_nonneg {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (n : ℕ) :
    0 ≤ normalizedSurvivor β (tiltedOddWeight β) (tiltedBase β) n := by
  unfold normalizedSurvivor survivorWeight
  exact div_nonneg (sum_nonneg fun _ _ => pow_nonneg (tiltedOddWeight_pos hβ0 hβ1).le _)
    (pow_nonneg (tiltedBase_pos β).le _)

/-- The normalized tilted survivor weights are summable at every boundary
in `(0,1)`, rational boundaries included. -/
theorem summable_weak_survivor {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Summable (normalizedSurvivor β (tiltedOddWeight β) (tiltedBase β)) := by
  obtain ⟨K, -, hK⟩ := BeattyPhase.exists_terminal_sqrt_bound_of_phase_limit
    (weakTerminalPhase_abs_le hβ0 hβ1) (weak_endpoint_phase_limit hβ0 hβ1)
  rw [survivor_eq_weak_renewal β]
  exact BeattyPhase.summable_renewalCoeff
    (normalizedWeakEndpoint_nonneg β (tiltedOddWeight_pos hβ0 hβ1).le (tiltedBase_pos β).le)
    (BeattyPhase.summable_renewalLogCoeff_of_bound hK)

/-- Convolution survivor phase built from the weak terminal phase. -/
noncomputable def weakSurvivorPhase (β t : ℝ) : ℝ :=
  ∑' j : ℕ, normalizedSurvivor β (tiltedOddWeight β) (tiltedBase β) j *
    weakTerminalPhase β (t-j*β)

/-- The terms of the weak survivor phase, shifted by `a`, are summable. -/
theorem summable_weak_phase_terms {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (t : ℝ) (a : ℕ) :
    Summable (fun j : ℕ => normalizedSurvivor β (tiltedOddWeight β) (tiltedBase β) (j+a) *
      weakTerminalPhase β (t-j*β)) := by
  have hu := (summable_weak_survivor hβ0 hβ1).comp_injective (add_left_injective a)
  apply (hu.mul_left (2*tiltedAmplitude β)).of_norm_bounded
  intro j
  have hp := survivor_nonneg hβ0 hβ1 (j+a)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left (weakTerminalPhase_abs_le hβ0 hβ1 _) hp

/-- The weak survivor phase lies between `A` and `2*A*∑ u_j`. -/
theorem weakSurvivorPhase_bounds {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (t : ℝ) :
    tiltedAmplitude β ≤ weakSurvivorPhase β t ∧
      weakSurvivorPhase β t ≤ 2*tiltedAmplitude β*
        (∑' j, normalizedSurvivor β (tiltedOddWeight β) (tiltedBase β) j) := by
  have hs := summable_weak_phase_terms hβ0 hβ1 t 0
  simp only [add_zero] at hs
  have hu := summable_weak_survivor hβ0 hβ1
  have ha := tiltedAmplitude_pos hβ0 hβ1
  constructor
  · have h := hs.le_tsum 0 (fun j _ =>
      mul_nonneg (survivor_nonneg hβ0 hβ1 j)
        (ha.le.trans (weakTerminalPhase_bounds hβ0 hβ1 _).1))
    simp only [normalizedSurvivor_zero, Nat.cast_zero, zero_mul, sub_zero, one_mul] at h
    exact (weakTerminalPhase_bounds hβ0 hβ1 t).1.trans h
  · calc
      _ ≤ ∑' j, (2*tiltedAmplitude β)*
          normalizedSurvivor β (tiltedOddWeight β) (tiltedBase β) j :=
        hs.tsum_le_tsum (fun j => by
          simpa [mul_comm] using mul_le_mul_of_nonneg_left
            ((le_abs_self _).trans (weakTerminalPhase_abs_le hβ0 hβ1 (t-j*β)))
            (survivor_nonneg hβ0 hβ1 j)) (hu.mul_left _)
      _ = _ := tsum_mul_left

/-- The weak survivor phase has period one. -/
theorem weakSurvivorPhase_periodic (β : ℝ) : Function.Periodic (weakSurvivorPhase β) 1 := by
  intro t
  unfold weakSurvivorPhase
  apply tsum_congr
  intro j
  rw [show t+1-j*β = (t-j*β)+1 by ring, weakTerminalPhase_periodic]

/-- At every boundary in `(0,1)`, rational or irrational, the actual tilted
survivors have the weak convolution phase after three-halves normalization. -/
theorem weak_survivor_phase_limit {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun n : ℕ => (n : ℝ)*Real.sqrt n*
      normalizedSurvivor β (tiltedOddWeight β) (tiltedBase β) n -
      weakSurvivorPhase β (n*β)) atTop (𝓝 0) := by
  have h := BeattyPhase.renewalCoeff_phase_limit
    (normalizedWeakEndpoint_nonneg β (tiltedOddWeight_pos hβ0 hβ1).le (tiltedBase_pos β).le)
    (weakTerminalPhase_abs_le hβ0 hβ1) (weak_endpoint_phase_limit hβ0 hβ1)
  rw [← survivor_eq_weak_renewal] at h
  simpa only [weakSurvivorPhase, sub_mul] using h

end Problems.Juggler.BeattySlope

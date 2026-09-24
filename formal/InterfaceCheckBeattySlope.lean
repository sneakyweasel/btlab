import Problems.Juggler.BeattyCounting
import Problems.Juggler.BeattySlopeAsymptotic

/-!
Expanded consumers for arbitrary-boundary counting and the exact logarithmic
specialization. The final consumers expose the unconditional tilted terminal
and survivor phase limits, critical first-passage mass one and the exact
Beatty jump-weight normalization, exact profile identification and the original
integer count asymptotic, including the full reciprocal-slope range. They do
not yet assert the geometric family theorem or a convergence rate.
The companion Python consumer test checks the exact standard dependency set.
-/

namespace Problems.Juggler.BeattySlopeChecks

open Finset BeattySlope Filter Topology

/-- The one-step counting partition quantifies over every real boundary. -/
theorem actual_count_partition : ∀ β : ℝ, ∀ n : ℕ,
    survivorCount β (n+1) + passageCount β (n+1) = 2*survivorCount β n :=
  survivorCount_add_passageCount

/-- The integer recurrence with the terminal binomial sum expanded and the
irrational parameter explicitly universally quantified. -/
theorem actual_count_recurrence : ∀ β : ℝ, Irrational β → ∀ n : ℕ,
    n * survivorCount β n = ∑ j ∈ range n,
      (∑ k ∈ range (n-j+1), if ((n-j : ℕ) : ℝ)*β < k then (n-j).choose k else 0) *
        survivorCount β j :=
  survivorCount_recurrence

/-- In the paper's reciprocal parameter the same recurrence holds for every
irrational `α`, without imposing the later large-deviation interval. -/
theorem actual_count_recurrence_reciprocal (α : ℝ) (hα : Irrational α) (n : ℕ) :
    n * survivorCount (1/α) n = ∑ j ∈ range n,
      (∑ k ∈ range (n-j+1), if ((n-j : ℕ) : ℝ)/α < k then (n-j).choose k else 0) *
        survivorCount (1/α) j := by
  simpa only [div_eq_mul_inv, one_mul] using actual_count_recurrence α⁻¹ hα.inv n

/-- The prefix inequalities retain the strict/weak convention at each actual
positive prefix, rather than an abstractly specified count sequence. -/
theorem actual_prefix_convention (β : ℝ) (hβ : Irrational β) (w : List Branch) :
    (∀ k : ℕ, k ≤ w.length → β*k ≤ (oddCount (w.take k) : ℝ)) ↔
      ∀ k : ℕ, 0 < k → k ≤ w.length → β*k < (oddCount (w.take k) : ℝ) :=
  survives_iff_strict hβ w

/-- The first-crossing location has its floor and all boundary assumptions
expanded, and its last letter is even; rational slopes in this interval
are also covered. -/
theorem actual_crossing_edge (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (w : List Branch) (hw : FirstPassage β w) :
    w.length = ⌊(oddCount w : ℝ)/β⌋₊ + 1 ∧ ∃ v, w = v ++ [Branch.even] := by
  obtain ⟨v, hv, -⟩ := hw.exists_even_prefix hβ1
  exact ⟨hw.length_eq_crossingDepth hβ0 hβ1, v, hv⟩

/-- The old and general models agree as actual finite sets at every depth. -/
theorem actual_logarithmic_word_sets (n : ℕ) :
    survivorWords PaperBThreshold.beta n = neverNegWords n ∧
    passageWords PaperBThreshold.beta n = minimalCertWords n :=
  ⟨survivorWords_logarithmic n, passageWords_logarithmic n⟩

/-- The weighted recurrence expands both the actual word sums and the terminal
binomial sum, with an arbitrary real weight and an arbitrary irrational slope. -/
theorem actual_weighted_recurrence (β : ℝ) (hβ : Irrational β) (z : ℝ) (n : ℕ) :
    (n : ℝ)*(∑ w ∈ survivorWords β n, z^oddCount w) =
      ∑ j ∈ range n,
        (∑ k ∈ range (n-j+1),
          if ((n-j : ℕ) : ℝ)*β < k then ((n-j).choose k : ℝ)*z^k else 0)*
        (∑ w ∈ survivorWords β j, z^oddCount w) :=
  survivorWeight_recurrence β hβ z n

/-- At the expanded crossing depth, division by the tilt recovers the exact
integer first-passage count. The only weight restriction is nonvanishing. -/
theorem actual_crossing_weight (β z : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hz : z ≠ 0) (r : ℕ) :
    (passageCount β (⌊(r : ℝ)/β⌋₊+1) : ℝ) =
      (∑ w ∈ passageWords β (⌊(r : ℝ)/β⌋₊+1), z^oddCount w)/z^r :=
  passageCount_eq_weight_div hβ0 hβ1 hz r

/-- The exponential coefficient equals the normalized actual word sum, with
no assumed generating identity or terminal estimate. -/
theorem actual_weighted_renewal (β : ℝ) (hβ : Irrational β) (z v : ℝ) (n : ℕ) :
    (∑ w ∈ survivorWords β n, z^oddCount w)/v^n =
      BeattyPhase.renewalCoeff (fun m =>
        (∑ k ∈ range (m+1), if (m : ℝ)*β < k then (m.choose k : ℝ)*z^k else 0)/v^m) n :=
  congrFun (normalizedSurvivor_eq_renewalCoeff β hβ z v) n

/-- The conditional analytic consumer exposes the terminal binomial estimate
and actual survivor sums. In particular the estimate is a premise, not an axiom
hidden behind the normalized-sequence definition. -/
theorem actual_weighted_phase_transfer (β : ℝ) (hβ : Irrational β)
    (z v P : ℝ) (Phi : ℝ → ℝ) (hz : 0 ≤ z) (hv : 0 ≤ v)
    (hPhi : ∀ x, |Phi x| ≤ P)
    (hA : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)*
      ((∑ k ∈ range (n+1), if (n : ℝ)*β < k then (n.choose k : ℝ)*z^k else 0)/v^n) -
      Phi (n*β)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (n : ℝ)*Real.sqrt n*
      ((∑ w ∈ survivorWords β n, z^oddCount w)/v^n) -
      ∑' j, ((∑ w ∈ survivorWords β j, z^oddCount w)/v^j)*
        Phi (((n : ℝ)-j)*β)) atTop (𝓝 0) :=
  normalizedSurvivor_phase_limit β hβ hz hv hPhi hA

/-- The useful bias exists on the entire interval `(0,1)`; no fair-walk
restriction `1/2 < β` is present. The fixed ratio is algebraic only. -/
theorem actual_tilt_bounds (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    0 < β/(2*(1-β)) ∧
    β/(2-β) = (β/(2*(1-β)))/(1+β/(2*(1-β))) ∧
    0 < β/(2-β) ∧ β/(2-β) < β ∧ (β/(2*(1-β)))*(1-β)/β = 1/2 := by
  obtain ⟨hp0, hpβ⟩ := tiltedBernoulliBias_bounds hβ0 hβ1
  exact ⟨tiltedOddWeight_pos hβ0 hβ1, tiltedBernoulliBias_eq hβ1,
    hp0, hpβ, tiltedOddWeight_terminal_ratio hβ0 hβ1⟩

/-- The half-ratio majorant holds at every finite depth and offset, with both
the tilt and strict cutoff expanded. Rational boundaries are included. -/
theorem actual_tilted_tail_majorant (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (n j : ℕ) :
    let k : ℕ := ⌊(n : ℝ)*β⌋₊+1
    let z : ℝ := β/(2*(1-β))
    (n.choose (k+j) : ℝ)*z^(k+j) ≤ ((n.choose k : ℝ)*z^k)*(1/2 : ℝ)^j :=
  tilted_choose_shift_bound hβ0 hβ1 n j

/-- The complete finite endpoint binomial sum is between its first term and
twice that term. The universal quantifiers include every positive depth. -/
theorem actual_tilted_tail_comparison (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (n : ℕ) (hn : 0 < n) :
    let k : ℕ := ⌊(n : ℝ)*β⌋₊+1
    let z : ℝ := β/(2*(1-β))
    let A : ℝ := ∑ j ∈ range (n+1), if (n : ℝ)*β < j then (n.choose j : ℝ)*z^j else 0
    (n.choose k : ℝ)*z^k ≤ A ∧ A ≤ 2*((n.choose k : ℝ)*z^k) :=
  tilted_endpoint_first_term_bounds hβ0 hβ1 hn

/-- The unconditional endpoint theorem expands the weighted binomial sum,
normalization, amplitude and phase. Every real boundary in `(0,1)` is covered. -/
theorem actual_tilted_endpoint_limit (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    let z : ℝ := β/(2*(1-β))
    let v : ℝ := (2 : ℝ)^(-β)/(1-β)
    let C : ℝ := (Real.sqrt (2*Real.pi*β*(1-β)))⁻¹
    Tendsto (fun n : ℕ => Real.sqrt n*
      ((∑ k ∈ range (n+1), if (n : ℝ)*β < k then (n.choose k : ℝ)*z^k else 0)/v^n) -
      C*(2 : ℝ)^Int.fract (n*β)) atTop (𝓝 0) := by
  simpa only [normalizedEndpoint, endpointWeight, tiltedOddWeight, tiltedBase_eq hβ1,
    tiltedTerminalPhase_eq, tiltedAmplitude] using tilted_endpoint_phase_limit hβ0 hβ1

/-- The unconditional survivor theorem uses actual finite word sums and
explicit phase coefficients. No terminal-limit or generating-identity premise occurs. -/
theorem actual_tilted_survivor_limit (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβ : Irrational β) :
    let z : ℝ := β/(2*(1-β))
    let v : ℝ := (2 : ℝ)^(-β)/(1-β)
    let C : ℝ := (Real.sqrt (2*Real.pi*β*(1-β)))⁻¹
    let u : ℕ → ℝ := fun n => (∑ w ∈ survivorWords β n, z^oddCount w)/v^n
    Tendsto (fun n : ℕ => (n : ℝ)*Real.sqrt n*u n -
      ∑' j : ℕ, u j*(C*(2 : ℝ)^Int.fract (((n : ℝ)-j)*β))) atTop (𝓝 0) := by
  simpa only [tiltedSurvivorPhase, normalizedSurvivor, survivorWeight,
    tiltedOddWeight, tiltedBase_eq hβ1, tiltedTerminalPhase_eq, tiltedAmplitude, sub_mul] using
      tilted_survivor_phase_limit hβ0 hβ1 hβ

/-- The quantifier over every irrational reciprocal slope has no upper slope
cutoff; the weights and profile are the same ones expanded in the preceding consumer. -/
theorem actual_tilted_survivor_reciprocal : ∀ α : ℝ, 1 < α → Irrational α →
    Tendsto (fun n : ℕ => (n : ℝ)*Real.sqrt n*
      normalizedSurvivor (1/α) (tiltedOddWeight (1/α)) (tiltedBase (1/α)) n -
      tiltedSurvivorPhase (1/α) (n/α)) atTop (𝓝 0) :=
  fun _ hα1 hα => tilted_survivor_phase_limit_reciprocal hα1 hα

/-- The explicit profile series is summable at every real phase, with the
actual survivor words and normalization expanded. -/
theorem actual_tilted_phase_series (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβ : Irrational β) (t : ℝ) :
    let z : ℝ := β/(2*(1-β))
    let v : ℝ := (2 : ℝ)^(-β)/(1-β)
    let C : ℝ := (Real.sqrt (2*Real.pi*β*(1-β)))⁻¹
    Summable (fun j : ℕ => ((∑ w ∈ survivorWords β j, z^oddCount w)/v^j)*
      (C*(2 : ℝ)^Int.fract (t-j*β))) := by
  simpa only [normalizedSurvivor, survivorWeight, tiltedOddWeight, tiltedBase_eq hβ1,
    tiltedTerminalPhase_eq, tiltedAmplitude] using summable_tiltedSurvivorPhase_terms hβ0 hβ1 hβ t

/-- The same expanded profile is bounded above and bounded away from zero;
the positive amplitude is explicit, rather than an assumed profile bound. -/
theorem actual_tilted_phase_bounds (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβ : Irrational β) (t : ℝ) :
    let z : ℝ := β/(2*(1-β))
    let v : ℝ := (2 : ℝ)^(-β)/(1-β)
    let C : ℝ := (Real.sqrt (2*Real.pi*β*(1-β)))⁻¹
    let u : ℕ → ℝ := fun n => (∑ w ∈ survivorWords β n, z^oddCount w)/v^n
    let psi : ℝ := ∑' j : ℕ, u j*(C*(2 : ℝ)^Int.fract (t-j*β))
    C ≤ psi ∧ psi ≤ 2*C*(∑' j, u j) := by
  simpa only [tiltedSurvivorPhase, normalizedSurvivor, survivorWeight,
    tiltedOddWeight, tiltedBase_eq hβ1, tiltedTerminalPhase_eq, tiltedAmplitude] using
      tiltedSurvivorPhase_bounds hβ0 hβ1 hβ t

/-- The exact critical/subcritical word-weight identity has every base and
height factor expanded. No probabilistic or asymptotic premise is required. -/
theorem actual_critical_word_tilt (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (n k : ℕ) :
    (1-β)^n*(β/(1-β))^k =
      (β/(2*(1-β)))^k*Real.exp (((k : ℝ)-(n : ℝ)*β)*Real.log 2)/
        ((2 : ℝ)^(-β)/(1-β))^n := by
  simpa only [criticalWordMass, tiltedOddWeight, tiltedBase_eq hβ1] using
    criticalWordMass_eq_exp hβ0 hβ1 n k

/-- All actual first passages through a finite depth, together with the
surviving words, conserve critical Bernoulli mass exactly. -/
theorem actual_critical_partial_mass (β : ℝ) (hβ1 : β < 1) (n : ℕ) :
    (∑ j ∈ range (n+1), ∑ w ∈ passageWords β j, (1-β)^j*(β/(1-β))^oddCount w) +
      (∑ w ∈ survivorWords β n, (1-β)^n*(β/(1-β))^oddCount w) = 1 :=
  criticalMass_partial_sum hβ1 n

/-- Critical survival tends to zero for every irrational boundary in `(0,1)`;
the sequence is the explicit finite sum of actual surviving word weights. -/
theorem actual_critical_survival_limit (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβ : Irrational β) :
    Tendsto (fun n : ℕ => ∑ w ∈ survivorWords β n,
      (1-β)^n*(β/(1-β))^oddCount w) atTop (𝓝 0) :=
  survivorCriticalMass_tendsto_zero hβ0 hβ1 hβ

/-- The expanded total-mass theorem sums over the actual first-crossing word
sets, at every depth, and states convergence to exactly one. -/
theorem actual_critical_passage_mass (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβ : Irrational β) :
    HasSum (fun n : ℕ => ∑ w ∈ passageWords β n,
      (1-β)^n*(β/(1-β))^oddCount w) 1 :=
  passageCriticalMass_hasSum hβ0 hβ1 hβ

/-- At each crossing edge the expanded critical probability is exactly the
integer first-passage count times its Bernoulli weight. -/
theorem actual_beatty_crossing_mass (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (r : ℕ) :
    let m : ℕ := ⌊(r : ℝ)/β⌋₊
    (∑ w ∈ passageWords β (m+1), (1-β)^(m+1)*(β/(1-β))^oddCount w) =
      (1-β)*((passageCount β (m+1) : ℝ)*β^r*(1-β)^(m-r)) := by
  simpa only [passageCriticalMass, criticalWordMass, passageJumpWeight_eq hβ0 hβ1,
    passageIndex, crossingDepth] using passageCriticalMass_crossingDepth hβ0 hβ1 r

/-- The exact series of actual positive-index count weights has the stated
sum; every floor, natural exponent and slope hypothesis is exposed. -/
theorem actual_beatty_jump_mass (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβ : Irrational β) :
    HasSum (fun j : ℕ => let r := j+1; let m := ⌊(r : ℝ)/β⌋₊;
      (passageCount β (m+1) : ℝ)*β^r*(1-β)^(m-r)) (β/(1-β)) := by
  simpa only [passageJumpWeight_eq hβ0 hβ1, passageIndex] using
    passage_jump_weights_hasSum hβ0 hβ1 hβ

/-- For every irrational slope above one, the actual weights have total mass
`1/(α-1)`, without a restriction such as `α<2`. -/
theorem actual_beatty_jump_mass_reciprocal : ∀ α : ℝ, 1 < α → Irrational α →
    HasSum (fun j : ℕ => let r := j+1; let m := ⌊(r : ℝ)/(1/α)⌋₊;
      (passageCount (1/α) (m+1) : ℝ)*(1/α)^r*(1-1/α)^(m-r)) (1/(α-1)) := by
  intro α hα1 hα
  have hα0 : 0 < α := by linarith
  simpa only [passageJumpWeight_eq (one_div_pos.mpr hα0) ((div_lt_one hα0).mpr hα1),
    passageIndex] using passage_jump_weights_hasSum_reciprocal hα1 hα

/-- The profile identity exposes the actual survivor and first-passage word
sums, floor phases and strict inequality at every atom. -/
theorem actual_beatty_profile_identification (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβ : Irrational β) (δ : ℝ) (hd0 : 0 < δ) (hd1 : δ < 1) :
    let z : ℝ := β/(2*(1-β))
    let v : ℝ := (2 : ℝ)^(-β)/(1-β)
    let C : ℝ := (Real.sqrt (2*Real.pi*β*(1-β)))⁻¹
    let psi : ℝ → ℝ := fun t => ∑' j : ℕ,
      ((∑ w ∈ survivorWords β j, z^oddCount w)/v^j)*(C*(2 : ℝ)^Int.fract (t-j*β))
    (1+z)*psi (-β*δ)-v*psi (-β*δ+β) = C*(2 : ℝ)^(-β*δ)*
      (1+∑' j : ℕ, let r := j+1; let m := ⌊(r : ℝ)/β⌋₊;
        if (r : ℝ)/β-m < δ then (passageCount β (m+1) : ℝ)*β^r*(1-β)^(m-r) else 0) := by
  simpa only [tiltedOddWeight, tiltedBase_eq hβ1, tiltedAmplitude, tiltedSurvivorPhase,
    normalizedSurvivor, survivorWeight, tiltedTerminalPhase_eq, passageProfile,
    BeattyPhase.jumpProfile, passagePhase, passageJumpWeight_eq hβ0 hβ1, passageIndex] using
    passageProfile_eq_transfer hβ0 hβ1 hβ hd0 hd1

/-- Every irrational reciprocal slope is admitted in the exact profile identity;
the count/profile definitions are expanded in the preceding consumer. -/
theorem actual_beatty_profile_reciprocal : ∀ α : ℝ, 1 < α → Irrational α →
    ∀ δ : ℝ, 0 < δ → δ < 1 →
    (1+tiltedOddWeight (1/α))*tiltedSurvivorPhase (1/α) (-(1/α)*δ)-
      tiltedBase (1/α)*tiltedSurvivorPhase (1/α) (-(1/α)*δ+1/α) =
      (tiltedAmplitude (1/α)*(2 : ℝ)^(-(1/α)*δ))*passageProfile (1/α) δ :=
  fun _ hα1 hα _ hd0 hd1 => passageProfile_eq_transfer_reciprocal hα1 hα hd0 hd1

/-- The same actual-count profile is monotone, has the exact endpoint values,
and is bounded on the whole real line by those values. -/
theorem actual_beatty_profile_envelope (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβ : Irrational β) :
    Monotone (passageProfile β) ∧ passageProfile β 0 = 1 ∧ passageProfile β 1 = 1/(1-β) ∧
      ∀ t : ℝ, 1 ≤ passageProfile β t ∧ passageProfile β t ≤ 1/(1-β) :=
  ⟨passageProfile_monotone hβ0 hβ1 hβ, (passageProfile_endpoints hβ0 hβ1 hβ).1,
    (passageProfile_endpoints hβ0 hβ1 hβ).2, passageProfile_bounds hβ0 hβ1 hβ⟩

/-- The original depth-normalized integer counts approach the fully expanded
strict jump series at every irrational boundary, without an asymptotic premise. -/
theorem actual_beatty_count_phase_limit (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβ : Irrational β) :
    Tendsto (fun r : ℕ => let m := ⌊(r : ℝ)/β⌋₊;
      (m : ℝ)*(passageCount β (m+1) : ℝ)/(m.choose r : ℝ) -
        (1+∑' j : ℕ, let s := j+1; let k := ⌊(s : ℝ)/β⌋₊;
          if (s : ℝ)/β-k < (r : ℝ)/β-m then
            (passageCount β (k+1) : ℝ)*β^s*(1-β)^(k-s) else 0)) atTop (𝓝 0) := by
  simpa only [passageProfile, BeattyPhase.jumpProfile, passagePhase,
    passageJumpWeight_eq hβ0 hβ1, passageIndex] using passage_phase_asymptotic hβ0 hβ1 hβ

/-- The full theorem explicitly quantifies over every irrational `α>1` and
uses `floor(α*r)`, the original odd-count ratio, and the strict actual-count series. -/
theorem actual_beatty_count_phase_reciprocal : ∀ α : ℝ, 1 < α → Irrational α →
    Tendsto (fun r : ℕ => let m := ⌊α*(r : ℝ)⌋₊;
      (r : ℝ)*(passageCount (1/α) (m+1) : ℝ)/((m-1).choose (r-1) : ℝ) -
        (1+∑' j : ℕ, let s := j+1; let k := ⌊α*(s : ℝ)⌋₊;
          if α*(s : ℝ)-k < α*(r : ℝ)-m then
            (passageCount (1/α) (k+1) : ℝ)*(1/α)^s*(1-1/α)^(k-s) else 0)) atTop (𝓝 0) := by
  intro α hα1 hα
  have hα0 : 0 < α := by linarith
  have hβ0 : 0 < 1/α := one_div_pos.mpr hα0
  have hβ1 : 1/α < 1 := (div_lt_one hα0).mpr hα1
  have hh := passage_phase_asymptotic_reciprocal hα1 hα
  simp only [passageProfile, BeattyPhase.jumpProfile, passagePhase,
    passageJumpWeight_eq hβ0 hβ1, passageIndex] at hh
  simpa only [one_div, div_inv_eq_mul, mul_comm] using hh

#print axioms actual_count_partition
#print axioms actual_count_recurrence
#print axioms actual_count_recurrence_reciprocal
#print axioms actual_prefix_convention
#print axioms actual_crossing_edge
#print axioms actual_logarithmic_word_sets
#print axioms actual_weighted_recurrence
#print axioms actual_crossing_weight
#print axioms actual_weighted_renewal
#print axioms actual_weighted_phase_transfer
#print axioms actual_tilt_bounds
#print axioms actual_tilted_tail_majorant
#print axioms actual_tilted_tail_comparison
#print axioms actual_tilted_endpoint_limit
#print axioms actual_tilted_survivor_limit
#print axioms actual_tilted_survivor_reciprocal
#print axioms actual_tilted_phase_series
#print axioms actual_tilted_phase_bounds
#print axioms actual_critical_word_tilt
#print axioms actual_critical_partial_mass
#print axioms actual_critical_survival_limit
#print axioms actual_critical_passage_mass
#print axioms actual_beatty_crossing_mass
#print axioms actual_beatty_jump_mass
#print axioms actual_beatty_jump_mass_reciprocal
#print axioms actual_beatty_profile_identification
#print axioms actual_beatty_profile_reciprocal
#print axioms actual_beatty_profile_envelope
#print axioms actual_beatty_count_phase_limit
#print axioms actual_beatty_count_phase_reciprocal


end Problems.Juggler.BeattySlopeChecks

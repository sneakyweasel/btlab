import Problems.Juggler.BeattyCertificateMass

/-!
# Beatty-indexed certificate weights

The first-passage probabilities are reindexed by their unique odd count.
The zeroth atom is the immediate even descent; removing it gives the
positive-index jump weights with total mass `1 / terminalRatio`.
-/

namespace Problems.Juggler.BeattyPhase

open Finset Filter Topology PaperBThreshold PaperBCertificates

private theorem beta_pos : 0 < beta := by linarith [beta_gt_five_eighths]
private theorem q_pos : 0 < 1-beta := sub_pos.2 beta_lt_one

/-- Length just before the unique certificate crossing with `r` odd letters. -/
noncomputable def certificateIndex (r : ℕ) : ℕ := ⌊(r : ℝ)/beta⌋₊

/-- Fractional Beatty phase of the crossing with `r` odd letters. -/
noncomputable def certificatePhase (r : ℕ) : ℝ := (r : ℝ)/beta-certificateIndex r

/-- Exact certificate jump weight. Index zero is retained internally and
equals one; the jump profile uses indices `r+1`. -/
noncomputable def certificateWeight (r : ℕ) : ℝ :=
  (minimalCertCount (certificateIndex r+1) : ℝ)*criticalWordMass (certificateIndex r) r

/-- The proposed left-continuous profile, built from the actual certificate counts. -/
noncomputable def certificateProfile : ℝ → ℝ :=
  jumpProfile (fun r => certificatePhase (r+1)) (fun r => certificateWeight (r+1))

private theorem index_bounds (r : ℕ) :
    (certificateIndex r : ℝ) ≤ (r : ℝ)/beta ∧ (r : ℝ)/beta < certificateIndex r+1 :=
  ⟨Nat.floor_le (div_nonneg (Nat.cast_nonneg r) beta_pos.le), Nat.lt_floor_add_one _⟩

/-- Every Beatty crossing is a genuine certificate window, including the
immediate even descent at index zero. -/
theorem certificateIndex_window (r : ℕ) : CertWindow (certificateIndex r+1) r := by
  apply (certWindow_iff_endpoint _ _).2
  have h := index_bounds r
  constructor
  · exact (le_div_iff₀ beta_pos).1 h.1
  · have hh := (div_lt_iff₀ beta_pos).1 h.2
    simpa only [Nat.cast_add, Nat.cast_one] using hh

private theorem window_index {n r : ℕ} (hw : CertWindow (n+1) r) : certificateIndex r = n := by
  have h := (certWindow_iff_endpoint n r).1 hw
  apply Nat.floor_eq_iff (div_nonneg (Nat.cast_nonneg r) beta_pos.le) |>.2
  constructor
  · exact (le_div_iff₀ beta_pos).2 h.1
  · apply (div_lt_iff₀ beta_pos).2
    simpa only [Nat.cast_add, Nat.cast_one] using h.2

/-- The Beatty index is exactly the unique certificate window for its odd count. -/
theorem certificateIndex_eq_iff_window (n r : ℕ) :
    certificateIndex r = n ↔ CertWindow (n+1) r := by
  constructor
  · intro h; simpa [h] using certificateIndex_window r
  · exact window_index

/-- Distinct odd counts give strictly increasing certificate crossing lengths. -/
theorem certificateIndex_strictMono : StrictMono certificateIndex := by
  apply strictMono_nat_of_lt_succ
  intro r
  have h0 := (index_bounds r).1
  have h1 := (index_bounds (r+1)).2
  have hr : (r : ℝ)/beta+1 ≤ (r+1 : ℕ)/beta := by
    rw [Nat.cast_add, Nat.cast_one, add_div]
    have hb : 1 < 1/beta := (one_lt_div beta_pos).2 beta_lt_one
    linarith
  have he : (certificateIndex r : ℝ) < certificateIndex (r+1) := by linarith
  exact_mod_cast he

private theorem index_ge (r : ℕ) : r ≤ certificateIndex r := by
  apply Nat.le_floor
  exact (le_div_iff₀ beta_pos).2 (mul_le_of_le_one_right (Nat.cast_nonneg r) beta_lt_one.le)

/-- The exact weights in ordinary Bernoulli powers, with a natural exponent
because every crossing index is at least its odd count. -/
theorem certificateWeight_eq (r : ℕ) : certificateWeight r =
    (minimalCertCount (certificateIndex r+1) : ℝ)*beta^r*(1-beta)^(certificateIndex r-r) := by
  unfold certificateWeight criticalWordMass
  rw [div_pow, ← Nat.sub_add_cancel (index_ge r), pow_add]
  field_simp [ne_of_gt q_pos]
  simp only [Nat.add_sub_cancel_right]
  ring

private theorem mass_index (r : ℕ) : certificateCriticalMass (certificateIndex r+1) =
    (1-beta)*certificateWeight r := by
  rw [certificateCriticalMass_of_window (certificateIndex_window r)]
  unfold certificateWeight criticalWordMass
  rw [pow_succ]
  ring

private theorem mass_off_range {n : ℕ}
    (hn : n ∉ Set.range (fun r => certificateIndex r+1)) : certificateCriticalMass n = 0 := by
  cases n with
  | zero => exact certificateCriticalMass_zero
  | succ n =>
    unfold certificateCriticalMass
    apply sum_eq_zero
    intro w hw
    have hwin := minimalCert_window (mem_filter.1 hw).2
    have hlen := mem_allWords.1 (mem_filter.1 hw).1
    rw [hlen] at hwin
    have he := window_index hwin
    exact False.elim (hn ⟨oddCount w, by dsimp; rw [he]⟩)

/-- The Beatty weights, including the immediate descent at zero, sum to `1/q`. -/
theorem certificateWeight_hasSum : HasSum certificateWeight (1/(1-beta)) := by
  have hi : Function.Injective (fun r => certificateIndex r+1) := by
    intro r s h
    apply certificateIndex_strictMono.injective
    change certificateIndex r+1 = certificateIndex s+1 at h
    omega
  have h := (hi.hasSum_iff (fun n hn => mass_off_range hn)).2 certificateCriticalMass_hasSum
  have h' : HasSum (fun r => (1-beta)*certificateWeight r) 1 := by
    simpa only [Function.comp_def, mass_index] using h
  have hh := h'.div_const (1-beta)
  simpa [ne_of_gt q_pos] using hh

/-- The auxiliary zeroth weight is the immediate even descent. -/
theorem certificateWeight_zero : certificateWeight 0 = 1 := by
  have hc : minimalCertCount 1 = 1 := by decide +kernel
  simp [certificateWeight, certificateIndex, criticalWordMass, hc]

/-- The actual positive-index jump weights have total mass `beta/q`, or
equivalently `1/terminalRatio`. There is no unfixed normalization constant. -/
theorem certificate_jump_weights_hasSum :
    HasSum (fun r => certificateWeight (r+1)) (1/terminalRatio) := by
  have hh : HasSum (fun r => certificateWeight (r+1)) (1/(1-beta)-1) := by
    apply (hasSum_nat_add_iff 1).2
    simpa [certificateWeight_zero] using certificateWeight_hasSum
  convert hh using 1
  unfold terminalRatio
  field_simp [ne_of_gt q_pos, ne_of_gt beta_pos]
  ring

/-- Every certificate jump weight is nonnegative. -/
theorem certificateWeight_nonneg (r : ℕ) : 0 ≤ certificateWeight r :=
  mul_nonneg (Nat.cast_nonneg _) (criticalWordMass_pos _ _).le

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

/-- The auxiliary zeroth phase is zero; all phases are fractional parts. -/
theorem certificatePhase_mem_Ico (r : ℕ) : 0 ≤ certificatePhase r ∧ certificatePhase r < 1 := by
  have h := index_bounds r
  unfold certificatePhase
  constructor <;> linarith

/-- Every positive-index atom lies strictly inside the unit phase interval. -/
theorem certificatePhase_pos {r : ℕ} (hr : 0 < r) : 0 < certificatePhase r := by
  have h0 := (certificatePhase_mem_Ico r).1
  apply lt_of_le_of_ne h0
  intro he
  have hm : 0 < certificateIndex r := lt_of_lt_of_le hr (index_ge r)
  apply slope_ne_integer hm r
  dsimp [certificatePhase] at he
  have hh : (r : ℝ)/beta = certificateIndex r := by linarith
  exact ((div_eq_iff (ne_of_gt beta_pos)).1 hh).symm

/-- Irrationality prevents distinct certificate indices from sharing a phase. -/
theorem certificatePhase_injective : Function.Injective certificatePhase := by
  have hne {r s : ℕ} (hrs : r < s) : certificatePhase r ≠ certificatePhase s := by
    intro he
    have hm := certificateIndex_strictMono hrs
    apply slope_ne_integer (show 0 < certificateIndex s-certificateIndex r by omega) (s-r)
    rw [Nat.cast_sub hm.le, Nat.cast_sub hrs.le]
    unfold certificatePhase at he
    have hb : beta ≠ 0 := ne_of_gt beta_pos
    field_simp at he
    linarith
  intro r s he
  rcases lt_trichotomy r s with h | h | h
  · exact False.elim (hne h he)
  · exact h
  · exact False.elim (hne h he.symm)

/-- Every listed atom has strictly positive mass, witnessed by the word with
all odd letters before its even letters. -/
theorem certificateWeight_pos (r : ℕ) : 0 < certificateWeight r := by
  have hm : r ≤ certificateIndex r+1 := by have h := index_ge r; omega
  have hc : 0 < minimalCertCount (certificateIndex r+1) := by
    apply Finset.card_pos.2
    refine ⟨blockWord (certificateIndex r+1) r, mem_filter.2 ⟨?_, ?_⟩⟩
    · exact mem_allWords.2 (blockWord_length hm)
    · exact blockWord_isMinimalCertificate (by omega) hm (certificateIndex_window r)
  exact mul_pos (by exact_mod_cast hc) (criticalWordMass_pos _ _)

/-- The first jump has the exact amplitude `beta = log 2 / log 3`. -/
theorem certificateWeight_one : certificateWeight 1 = beta := by
  have hi : certificateIndex 1 = 1 := by
    simp only [certificateIndex, Nat.cast_one]
    apply (Nat.floor_eq_iff (div_pos zero_lt_one beta_pos).le).2
    norm_num only [Nat.cast_one]
    constructor
    · exact (le_div_iff₀ beta_pos).2 (by linarith [beta_lt_one])
    · exact (div_lt_iff₀ beta_pos).2 (by linarith [beta_gt_five_eighths])
  rw [certificateWeight_eq, hi, minimalCertCount_two]
  norm_num

/-- The concrete profile is nondecreasing and has the exact normalization bounds. -/
theorem certificateProfile_bounds (x : ℝ) :
    1 ≤ certificateProfile x ∧ certificateProfile x ≤ 1+1/terminalRatio :=
  jumpProfile_envelope certificate_jump_weights_hasSum.summable
    (fun r => certificateWeight_nonneg (r+1)) certificate_jump_weights_hasSum.tsum_eq x

/-- The concrete certificate profile is nondecreasing. -/
theorem certificateProfile_monotone : Monotone certificateProfile :=
  jumpProfile_monotone certificate_jump_weights_hasSum.summable
    (fun r => certificateWeight_nonneg (r+1))

/-- The lower endpoint trace is exactly one. -/
theorem certificateProfile_tendsto_zero :
    Tendsto certificateProfile (𝓝[>] 0) (𝓝 1) :=
  jumpProfile_tendsto_zero certificate_jump_weights_hasSum.summable
    (fun r => certificateWeight_nonneg (r+1)) (fun _ => certificatePhase_pos (by omega))

/-- The upper endpoint trace is `1+1/s = alpha/(alpha-1)`. -/
theorem certificateProfile_tendsto_one :
    Tendsto certificateProfile (𝓝[<] 1) (𝓝 (1+1/terminalRatio)) := by
  unfold certificateProfile
  have h := jumpProfile_tendsto_one certificate_jump_weights_hasSum.summable
    (fun r => certificateWeight_nonneg (r+1)) (fun r => (certificatePhase_mem_Ico (r+1)).2)
  simpa only [certificate_jump_weights_hasSum.tsum_eq] using h

/-- The strict-inequality profile is left-continuous, including at its atoms. -/
theorem certificateProfile_tendsto_left (x : ℝ) :
    Tendsto certificateProfile (𝓝[<] x) (𝓝 (certificateProfile x)) :=
  jumpProfile_tendsto_left certificate_jump_weights_hasSum.summable
    (fun r => certificateWeight_nonneg (r+1)) x

/-- Each right trace exceeds the left trace by precisely its certificate weight. -/
theorem certificateProfile_jump (r : ℕ) :
    jumpProfileRight (fun j => certificatePhase (j+1)) (fun j => certificateWeight (j+1))
      (certificatePhase (r+1)) - certificateProfile (certificatePhase (r+1)) =
      certificateWeight (r+1) :=
  jumpProfile_jump certificate_jump_weights_hasSum.summable
    (fun j => certificateWeight_nonneg (j+1))
    (certificatePhase_injective.comp (add_left_injective 1)) r

end Problems.Juggler.BeattyPhase

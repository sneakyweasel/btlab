import Problems.Juggler.BeattyCertificateSeries

/-!
# Identification of the certificate jump series

Consecutive survivor kernels telescope into the first-descent coefficients.
Reindexing by the certificate windows turns each kernel into a single strict
step. The critical total-mass theorem fixes the remaining constant exactly.
-/

namespace Problems.Juggler.BeattyPhase

open Finset Filter Topology PaperBThreshold PaperBCertificates

private theorem beta_pos : 0 < beta := by linarith [beta_gt_five_eighths]
private theorem q_pos : 0 < 1-beta := sub_pos.2 beta_lt_one
private theorem ratio_bounds : 0 < terminalRatio ∧ terminalRatio < 1 := by
  constructor
  · exact div_pos q_pos beta_pos
  · exact (div_lt_one beta_pos).2 (by linarith [beta_gt_five_eighths])
private theorem amplitude_pos : 0 < terminalAmplitude := by
  have hb := beta_pos
  have hq := q_pos
  unfold terminalAmplitude
  positivity

private theorem terminal_abs_bound (x : ℝ) :
    |terminalPhase x| ≤ terminalAmplitude/(1-terminalRatio) := by
  have hp : 0 ≤ terminalPhase x := (div_nonneg
    (mul_nonneg amplitude_pos.le ratio_bounds.1.le) (sub_pos.2 ratio_bounds.2).le).trans
      (terminalPhase_bounds x).1
  rw [abs_of_nonneg hp]
  exact (terminalPhase_bounds x).2

private theorem kernel_summable (x : ℝ) (a : ℕ) :
    Summable (fun j => survivorNormalized (j+a)*terminalPhase (x-(j : ℝ)*beta)) := by
  have hu := summable_survivorNormalized_unconditional.comp_injective (add_left_injective a)
  apply (hu.mul_left (terminalAmplitude/(1-terminalRatio))).of_norm_bounded
  intro j
  have hp : 0 ≤ survivorNormalized (j+a) := div_nonneg (Nat.cast_nonneg _)
    (pow_pos survivorBase_pos _).le
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left (terminal_abs_bound _) hp

private theorem shifted_survivor_series (x : ℝ) :
    survivorPhase (x+beta) = terminalPhase (x+beta) +
      ∑' j, survivorNormalized (j+1)*terminalPhase (x-(j : ℝ)*beta) := by
  have hs := (kernel_summable (x+beta) 0).sum_add_tsum_nat_add 1
  have hz : survivorNormalized 0 = 1 := by
    have hc : neverNegCount 0 = 1 := by decide +kernel
    simp [survivorNormalized, hc]
  simp only [Nat.add_zero, sum_range_one, hz, Nat.cast_zero, zero_mul, sub_zero, one_mul] at hs
  rw [survivorPhase, ← hs]
  congr 1
  apply tsum_congr
  intro j
  congr 2
  push_cast
  ring

private theorem descent_kernel_series (x : ℝ) :
    (∑' j : ℕ, (minimalCertCount (j+1) : ℝ)/(2*survivorBase^j)*terminalPhase (x-j*beta)) =
      survivorPhase x-(survivorBase/2)*survivorPhase (x+beta) +
        (survivorBase/2)*terminalPhase (x+beta) := by
  have he (j : ℕ) : (minimalCertCount (j+1) : ℝ)/(2*survivorBase^j) =
      survivorNormalized j-(survivorBase/2)*survivorNormalized (j+1) := by
    simpa [survivorNormalized] using (survivor_jump_difference (ne_of_gt survivorBase_pos)
      (a := (1 : ℝ)) j).symm
  simp_rw [he, sub_mul, mul_assoc]
  have hsub := (kernel_summable x 0).tsum_sub ((kernel_summable x 1).mul_left (survivorBase/2))
  simp only [Nat.add_zero] at hsub
  rw [hsub]
  rw [tsum_mul_left]
  rw [shifted_survivor_series]
  unfold survivorPhase
  ring

private theorem count_support {n : ℕ} (hn : minimalCertCount (n+1) ≠ 0) :
    n ∈ Set.range certificateIndex := by
  obtain ⟨w, hw⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero hn)
  have hwin := minimalCert_window (mem_filter.1 hw).2
  rw [mem_allWords.1 (mem_filter.1 hw).1] at hwin
  exact ⟨oddCount w, (certificateIndex_eq_iff_window n _).2 hwin⟩

private theorem descent_kernel_reindex (x : ℝ) :
    (∑' j : ℕ, (minimalCertCount (j+1) : ℝ)/(2*survivorBase^j)*terminalPhase (x-j*beta)) =
    ∑' r : ℕ, (minimalCertCount (certificateIndex r+1) : ℝ)/(2*survivorBase^certificateIndex r)*
      terminalPhase (x-(certificateIndex r : ℝ)*beta) := by
  symm
  apply certificateIndex_strictMono.injective.tsum_eq (f := fun j : ℕ =>
    (minimalCertCount (j+1) : ℝ)/(2*survivorBase^j)*terminalPhase (x-j*beta))
  intro n hn
  apply count_support
  intro hzero
  apply hn
  simp [hzero]

private theorem log_ratio : Real.log terminalRatio = Real.log (1-beta)-Real.log beta :=
  Real.log_div (ne_of_gt q_pos) (ne_of_gt beta_pos)

private theorem weight_rpow (r : ℕ) : certificateWeight r =
    (minimalCertCount (certificateIndex r+1) : ℝ)/survivorBase^certificateIndex r *
      terminalRatio^(-beta*certificatePhase r) := by
  rw [certificateWeight, criticalWordMass_eq_exp]
  have he : Real.exp (((r : ℝ)-(certificateIndex r : ℝ)*beta)*Real.log (beta/(1-beta))) =
      terminalRatio^(-beta*certificatePhase r) := by
    rw [Real.rpow_def_of_pos ratio_bounds.1, Real.log_div (ne_of_gt beta_pos) (ne_of_gt q_pos),
      log_ratio, certificatePhase]
    congr 1
    field_simp [ne_of_gt beta_pos]
    ring
  rw [he]
  ring

private theorem crossing_kernel_fract {δ : ℝ} (hd0 : 0 < δ) (hd1 : δ < 1) (r : ℕ) :
    Int.fract (1-beta*δ-(certificateIndex r : ℝ)*beta) =
      if certificatePhase r < δ then 1+beta*(certificatePhase r-δ)
      else beta*(certificatePhase r-δ) := by
  have hp := certificatePhase_mem_Ico r
  have he : (r : ℝ) = beta*(certificatePhase r+certificateIndex r) := by
    unfold certificatePhase
    field_simp [ne_of_gt beta_pos]
    ring
  split_ifs with h
  · apply Int.fract_eq_iff.2
    refine ⟨?_, ?_, -(r : ℤ), ?_⟩
    · have hb := mul_lt_mul_of_pos_left (show δ-certificatePhase r < 1 by linarith) beta_pos
      nlinarith [beta_lt_one]
    · have hb := mul_neg_of_pos_of_neg beta_pos (sub_neg.2 h)
      linarith
    · push_cast
      nlinarith [he]
  · apply Int.fract_eq_iff.2
    refine ⟨mul_nonneg beta_pos.le (by linarith), ?_, (1 : ℤ)-r, ?_⟩
    · have hb := mul_lt_mul_of_pos_left (show certificatePhase r-δ < 1 by linarith) beta_pos
      linarith [beta_lt_one]
    · push_cast
      nlinarith [he]

private theorem scaled_kernel_step {δ : ℝ} (hd0 : 0 < δ) (hd1 : δ < 1) (r : ℕ) :
    (2/terminalAmplitude*terminalRatio^(-beta*δ))*
      ((minimalCertCount (certificateIndex r+1) : ℝ)/(2*survivorBase^certificateIndex r)*
        terminalPhase (1-beta*δ-(certificateIndex r : ℝ)*beta)) =
      terminalRatio/(1-terminalRatio)*certificateWeight r +
        (if certificatePhase r < δ then certificateWeight r else 0) := by
  rw [terminalPhase, crossing_kernel_fract hd0 hd1 r, weight_rpow]
  have ha := ne_of_gt amplitude_pos
  have hs := ne_of_gt ratio_bounds.1
  have hd := ne_of_gt (sub_pos.2 ratio_bounds.2)
  split_ifs with h
  · have he : terminalRatio^(-beta*δ)*terminalRatio^(1-(1+beta*(certificatePhase r-δ))) =
        terminalRatio^(-beta*certificatePhase r) := by
      rw [← Real.rpow_add ratio_bounds.1]
      congr 1
      ring
    calc
      _ = (minimalCertCount (certificateIndex r+1) : ℝ)/
          (survivorBase^certificateIndex r*(1-terminalRatio)) *
          (terminalRatio^(-beta*δ)*terminalRatio^(1-(1+beta*(certificatePhase r-δ)))) := by
        field_simp
      _ = _ := by rw [he]; field_simp; ring
  · have he : terminalRatio^(-beta*δ)*terminalRatio^(1-beta*(certificatePhase r-δ)) =
        terminalRatio*terminalRatio^(-beta*certificatePhase r) := by
      calc
        _ = terminalRatio^(1+(-beta*certificatePhase r)) := by
          rw [← Real.rpow_add ratio_bounds.1]
          congr 1
          ring
        _ = _ := by rw [Real.rpow_add ratio_bounds.1, Real.rpow_one]
    calc
      _ = (minimalCertCount (certificateIndex r+1) : ℝ)/
          (survivorBase^certificateIndex r*(1-terminalRatio)) *
          (terminalRatio^(-beta*δ)*terminalRatio^(1-beta*(certificatePhase r-δ))) := by
        field_simp
      _ = _ := by rw [he]; field_simp; ring

private theorem base_ratio_identity : survivorBase*terminalRatio^(1-beta) = 1/beta := by
  apply Real.log_injOn_pos (mul_pos survivorBase_pos (Real.rpow_pos_of_pos ratio_bounds.1 _))
    (div_pos zero_lt_one beta_pos)
  rw [Real.log_mul (ne_of_gt survivorBase_pos)
      (ne_of_gt (Real.rpow_pos_of_pos ratio_bounds.1 _)),
    Real.log_rpow ratio_bounds.1, log_survivorBase, log_ratio,
    Real.log_div one_ne_zero (ne_of_gt beta_pos), Real.log_one]
  ring

private theorem scaled_wrap_term {δ : ℝ} (hd0 : 0 < δ) (hd1 : δ < 1) :
    (2/terminalAmplitude*terminalRatio^(-beta*δ))*(survivorBase/2)*
      terminalPhase (1-beta*δ+beta) = 1/(beta*(1-terminalRatio)) := by
  have hy : 0 ≤ beta*(1-δ) := mul_nonneg beta_pos.le (by linarith)
  have hy1 : beta*(1-δ) < 1 := by nlinarith [beta_lt_one]
  have hf : Int.fract (1-beta*δ+beta) = beta*(1-δ) := by
    apply Int.fract_eq_iff.2
    exact ⟨hy, hy1, 1, by push_cast; ring⟩
  have he : terminalRatio^(-beta*δ)*terminalRatio^(1-beta*(1-δ)) = terminalRatio^(1-beta) := by
    rw [← Real.rpow_add ratio_bounds.1]
    congr 1
    ring
  rw [terminalPhase, hf]
  have ha := ne_of_gt amplitude_pos
  calc
    _ = survivorBase*(terminalRatio^(-beta*δ)*terminalRatio^(1-beta*(1-δ)))/(1-terminalRatio) := by
      field_simp
    _ = _ := by rw [he, base_ratio_identity]; field_simp

private theorem restricted_weights_summable (δ : ℝ) :
    Summable (fun r => if certificatePhase r < δ then certificateWeight r else 0) := by
  apply certificateWeight_hasSum.summable.of_norm_bounded
  intro r
  split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg (certificateWeight_nonneg r),
    certificateWeight_nonneg r]

private theorem all_atoms_profile {δ : ℝ} (hd : 0 < δ) :
    (∑' r, if certificatePhase r < δ then certificateWeight r else 0) = certificateProfile δ := by
  have h := (restricted_weights_summable δ).sum_add_tsum_nat_add 1
  have hz : certificatePhase 0 = 0 := by simp [certificatePhase, certificateIndex]
  simp only [sum_range_one, hz, hd, if_true, certificateWeight_zero] at h
  exact h.symm

/-- Exact identification of the consecutive-survivor transfer with the
certificate jump series. The strict inequality fixes the value at every atom;
this equality holds throughout the open phase interval, not just off the orbit. -/
theorem certificateProfile_eq_transfer {δ : ℝ} (hd0 : 0 < δ) (hd1 : δ < 1) :
    certificateProfile δ = (2/terminalAmplitude*terminalRatio^(-beta*δ))*
      (survivorPhase (1-beta*δ)-(survivorBase/2)*survivorPhase (1-beta*δ+beta)) := by
  let scale := 2/terminalAmplitude*terminalRatio^(-beta*δ)
  have he := congrArg (fun z : ℝ => scale*z) (descent_kernel_series (1-beta*δ))
  rw [descent_kernel_reindex, ← tsum_mul_left] at he
  have hstep (r : ℕ) := scaled_kernel_step hd0 hd1 r
  change ∀ r, scale*((minimalCertCount (certificateIndex r+1) : ℝ)/
      (2*survivorBase^certificateIndex r)*terminalPhase (1-beta*δ-(certificateIndex r : ℝ)*beta)) = _
    at hstep
  simp_rw [hstep] at he
  rw [(certificateWeight_hasSum.summable.mul_left (terminalRatio/(1-terminalRatio))).tsum_add
    (restricted_weights_summable δ), tsum_mul_left, certificateWeight_hasSum.tsum_eq,
    all_atoms_profile hd0] at he
  have hc : terminalRatio/(1-terminalRatio)*(1/(1-beta)) = 1/(beta*(1-terminalRatio)) := by
    unfold terminalRatio
    field_simp [ne_of_gt beta_pos, ne_of_gt q_pos]
  have hw := scaled_wrap_term hd0 hd1
  change scale*(survivorBase/2)*terminalPhase (1-beta*δ+beta) = _ at hw
  rw [hc] at he
  nlinarith [he, hw]

end Problems.Juggler.BeattyPhase

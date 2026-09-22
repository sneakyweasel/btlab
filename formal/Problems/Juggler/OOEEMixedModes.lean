import Problems.Juggler.OOEESmoothModes

/-! # Fixed mixed-mode cancellation on the actual OOEE source scale

Finite differencing is applied to the original nested-floor phase. The
overlap length is exactly `N-d`; short sums below the differencing cutoff
are handled by their cardinality.
-/

noncomputable section

namespace Problems.Juggler.OOEEMixedModes

open Finset BTCalculus.WeylDifferencing BTCalculus.SecondDerivative
open OOEECurvature OOEECarryFourier OOEEPhaseComparison

def correlationConstant (u L : ℝ) : ℝ :=
  (3*L+2)*(4*(64*L*Real.sqrt u+16/Real.sqrt u+1)+420*(64*L+17)+20*L)+10*Real.pi*u*L

def mixedConstant (u L : ℝ) : ℝ :=
  Real.sqrt (4*L^2+4*L*correlationConstant u L)+1

theorem original_correlation_bound {P a h u v w L : ℝ} (N : ℕ)
    (hP : 1 ≤ P) (ha : P ≤ a) (hb : a+2*N ≤ 2*P)
    (hh : 1 ≤ h) (hhP : h ≤ P^(1/16:ℝ)) (hsize : 1024 ≤ P^(15/16:ℝ))
    (hu : 0 < u) (hfreq : |v| + |w| ≤ u*P^(3/4:ℝ)/1024)
    (hcut : 3 ≤ P^(1/4:ℝ)) (hdom : 32*u ≤ P^(3/16:ℝ))
    (hL : 0 ≤ L) (hN : (N:ℝ) ≤ L*P^(7/16:ℝ)) :
    ‖∑ n ∈ range N, phase (originalPhase u v w (a+2*n+2*h)-originalPhase u v w (a+2*n))‖ ≤
      correlationConstant u L*P^(3/8:ℝ) := by
  have hc := retained_correlation_bound N hP ha hb hh hhP hsize hu hfreq hcut hdom hL hN
  have he := correlation_comparison (u := u) (v := v) (w := w) N hP ha (by linarith) hhP hL hN
  rw [abs_of_pos hu] at he
  have hp := Real.rpow_le_rpow_of_exponent_le hP (by norm_num : (1/4:ℝ) ≤ 3/8)
  have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ 10*Real.pi*u*L by positivity)
  have hn := norm_add_le
    ((∑ n ∈ range N, phase (originalPhase u v w (a+2*n+2*h)-originalPhase u v w (a+2*n)))-
      ∑ n ∈ range N, phase (retainedPhase h u v w (a+2*n)))
    (∑ n ∈ range N, phase (retainedPhase h u v w (a+2*n)))
  rw [sub_add_cancel] at hn
  dsimp [correlationConstant]
  nlinarith

theorem mixed_sum_positive {P a u v w L : ℝ} (N : ℕ)
    (hP : 1 ≤ P) (ha : P ≤ a) (hb : a+2*N ≤ 2*P)
    (hsize : 1024 ≤ P^(15/16:ℝ)) (hu : 0 < u)
    (hfreq : |v| + |w| ≤ u*P^(3/4:ℝ)/1024)
    (hcut : 3 ≤ P^(1/4:ℝ)) (hdom : 32*u ≤ P^(3/16:ℝ))
    (hL : 0 ≤ L) (hN : (N:ℝ) ≤ L*P^(7/16:ℝ)) :
    ‖∑ n ∈ range N, phase (originalPhase u v w (a+2*n))‖ ≤
      mixedConstant u L*P^(13/32:ℝ) := by
  have hP0 : 0 < P := by linarith
  let H := ⌊P^(1/16:ℝ)⌋₊
  have hH : 1 ≤ H := by
    apply Nat.le_floor
    simpa using (Real.one_le_rpow hP (by norm_num : (0:ℝ) ≤ 1/16))
  have hH0 : (0:ℝ) < H := by exact_mod_cast hH
  have hHP : (H:ℝ) ≤ P^(1/16:ℝ) := Nat.floor_le (by positivity)
  have hPH : P^(1/16:ℝ) ≤ 2*(H:ℝ) := by
    have hh := (Nat.lt_floor_add_one (P^(1/16:ℝ))).le
    have hh1 : (1:ℝ) ≤ H := by exact_mod_cast hH
    linarith
  have hC : 0 ≤ correlationConstant u L := by dsimp [correlationConstant]; positivity
  have hD : 0 ≤ 4*L^2+4*L*correlationConstant u L := by positivity
  have hB : 1 ≤ mixedConstant u L := by
    dsimp [mixedConstant]
    linarith [Real.sqrt_nonneg (4*L^2+4*L*correlationConstant u L)]
  by_cases hHN : H ≤ N
  · let z : ℕ → ℂ := fun n => phase (originalPhase u v w (a+2*n))
    have hc (d : ℕ) (hd : d ∈ Ico 1 H) :
        ‖correlation z N d‖ ≤ correlationConstant u L*P^(3/8:ℝ) := by
      have hd1 : (1:ℝ) ≤ d := by exact_mod_cast (mem_Ico.mp hd).1
      have hdH : (d:ℝ) ≤ H := by exact_mod_cast (mem_Ico.mp hd).2.le
      have hNd : (N-d:ℕ) ≤ N := Nat.sub_le _ _
      have hNd' : ((N-d:ℕ):ℝ) ≤ N := by exact_mod_cast hNd
      have hc := original_correlation_bound (N-d) hP ha (by linarith) hd1 (hdH.trans hHP)
        hsize hu hfreq hcut hdom hL (hNd'.trans hN)
      simpa only [correlation, z, phase_mul_conj, Nat.cast_add, mul_add, add_assoc] using hc
    have hsum : (∑ d ∈ Ico 1 H, ‖correlation z N d‖) ≤
        (H:ℝ)*(correlationConstant u L*P^(3/8:ℝ)) := by
      calc _ ≤ ∑ _d ∈ Ico 1 H, correlationConstant u L*P^(3/8:ℝ) := sum_le_sum hc
        _ = ((H-1:ℕ):ℝ)*(correlationConstant u L*P^(3/8:ℝ)) := by simp
        _ ≤ _ := by gcongr; exact_mod_cast Nat.sub_le H 1
    have hd := van_der_corput hH hHN (z := z) (fun n _ => (phase_norm _).le)
    have hp1 : P^(13/16:ℝ)*P^(1/16:ℝ) = (P^(7/16:ℝ))^2 := by
      rw [← Real.rpow_add hP0, ← Real.rpow_natCast, ← Real.rpow_mul hP0.le]
      norm_num
    have hp2 : P^(7/16:ℝ)*P^(3/8:ℝ) = P^(13/16:ℝ) := by
      rw [← Real.rpow_add hP0]
      norm_num
    have hfirst : 2*(N:ℝ)^2/H ≤ 4*L^2*P^(13/16:ℝ) := by
      apply (div_le_iff₀ hH0).mpr
      have hs : (N:ℝ)^2 ≤ (L*P^(7/16:ℝ))^2 := by gcongr
      have hm := mul_le_mul_of_nonneg_left hPH (show 0 ≤ 2*L^2*P^(13/16:ℝ) by positivity)
      have he : 2*L^2*P^(13/16:ℝ)*P^(1/16:ℝ) = 2*(L*P^(7/16:ℝ))^2 := by
        rw [mul_assoc, mul_assoc, hp1]
        ring
      nlinarith
    have hsecond : (4*(N:ℝ)/H)*(∑ d ∈ Ico 1 H, ‖correlation z N d‖) ≤
        4*L*correlationConstant u L*P^(13/16:ℝ) := by
      calc _ ≤ (4*(N:ℝ)/H)*((H:ℝ)*(correlationConstant u L*P^(3/8:ℝ))) := by gcongr
        _ = 4*(N:ℝ)*correlationConstant u L*P^(3/8:ℝ) := by field_simp
        _ ≤ 4*(L*P^(7/16:ℝ))*correlationConstant u L*P^(3/8:ℝ) := by gcongr
        _ = _ := by rw [← hp2]; ring
    have hs : ‖∑ n ∈ range N, z n‖^2 ≤
        (4*L^2+4*L*correlationConstant u L)*P^(13/16:ℝ) := by linarith
    have hp3 : (P^(13/32:ℝ))^2 = P^(13/16:ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hP0.le]
      norm_num
    have hb2 : (Real.sqrt (4*L^2+4*L*correlationConstant u L)*P^(13/32:ℝ))^2 =
        (4*L^2+4*L*correlationConstant u L)*P^(13/16:ℝ) := by
      rw [mul_pow, Real.sq_sqrt hD, hp3]
    have hroot : ‖∑ n ∈ range N, z n‖ ≤
        Real.sqrt (4*L^2+4*L*correlationConstant u L)*P^(13/32:ℝ) := by
      nlinarith [norm_nonneg (∑ n ∈ range N, z n),
        show 0 ≤ Real.sqrt (4*L^2+4*L*correlationConstant u L)*P^(13/32:ℝ) by positivity]
    exact hroot.trans (by dsimp [mixedConstant]; nlinarith [Real.rpow_pos_of_pos hP0 (13/32)])
  · have hNH : (N:ℝ) ≤ H := by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hHN))
    have hs := norm_phase_sum_le_card (fun n => originalPhase u v w (a+2*n)) (range N)
    simp only [card_range] at hs
    calc _ ≤ (N:ℝ) := hs
      _ ≤ P^(1/16:ℝ) := hNH.trans hHP
      _ ≤ P^(13/32:ℝ) := Real.rpow_le_rpow_of_exponent_le hP (by norm_num)
      _ ≤ _ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hB (by positivity : 0 ≤ P^(13/32:ℝ))

theorem mixed_sum_positive_eventually {u : ℝ} (hu : 0 < u) (v w : ℝ)
    {L : ℝ} (hL : 0 ≤ L) :
    ∃ B : ℝ, 0 < B ∧ ∃ P0 : ℝ, ∀ P : ℝ, P0 ≤ P → ∀ a : ℝ, ∀ N : ℕ,
      P ≤ a → a+2*N ≤ 2*P → (N:ℝ) ≤ L*P^(7/16:ℝ) →
      ‖∑ n ∈ range N, phase (originalPhase u v w (a+2*n))‖ ≤ B*P^(13/32:ℝ) := by
  obtain ⟨P0, hp⟩ := carry_size_conditions_eventually hu v w
  refine ⟨mixedConstant u L, by dsimp [mixedConstant]; positivity, P0, ?_⟩
  intro P hP a N ha hb hN
  obtain ⟨hP1, hs, hf, hc, hd⟩ := hp P hP
  exact mixed_sum_positive N hP1 ha hb hs hu hf hc hd hL hN

theorem originalPhase_neg (u v w x : ℝ) :
    originalPhase (-u) (-v) (-w) x = -originalPhase u v w x := by
  dsimp [originalPhase]
  ring

theorem mixed_sum_nonzero_eventually {u : ℝ} (hu : u ≠ 0) (v w : ℝ)
    {L : ℝ} (hL : 0 ≤ L) :
    ∃ B : ℝ, 0 < B ∧ ∃ P0 : ℝ, ∀ P : ℝ, P0 ≤ P → ∀ a : ℝ, ∀ N : ℕ,
      P ≤ a → a+2*N ≤ 2*P → (N:ℝ) ≤ L*P^(7/16:ℝ) →
      ‖∑ n ∈ range N, phase (originalPhase u v w (a+2*n))‖ ≤ B*P^(13/32:ℝ) := by
  rcases lt_or_gt_of_ne hu with hu | hu
  · obtain ⟨B, hB, P0, hp⟩ := mixed_sum_positive_eventually (neg_pos.mpr hu) (-v) (-w) hL
    refine ⟨B, hB, P0, ?_⟩
    intro P hP a N ha hb hN
    have h := hp P hP a N ha hb hN
    simpa only [originalPhase_neg, phase_neg, ← map_sum, Complex.norm_conj] using h
  · exact mixed_sum_positive_eventually hu v w hL

/-- Every fixed integer Fourier mode except the pure slow modes has a power saving. -/
theorem fixed_mixed_mode (i j k : ℤ) (hij : i ≠ 0 ∨ j ≠ 0)
    {L : ℝ} (hL : 0 ≤ L) :
    ∃ B : ℝ, 0 < B ∧ ∃ P0 : ℝ, ∀ P : ℝ, P0 ≤ P → ∀ a : ℝ, ∀ N : ℕ,
      P ≤ a → a+2*N ≤ 2*P → (N:ℝ) ≤ L*P^(7/16:ℝ) →
      ‖∑ n ∈ range N, phase (originalPhase ((j:ℝ)/2) i k (a+2*n))‖ ≤ B*P^(13/32:ℝ) := by
  by_cases hj : j = 0
  · subst j
    have hi : i ≠ 0 := hij.resolve_right (by simp)
    rcases lt_or_gt_of_ne hi with hi | hi
    · have hiv : (1:ℝ) ≤ -(i:ℝ) := by exact_mod_cast (show (1:ℤ) ≤ -i by omega)
      obtain ⟨P0, hp⟩ := OOEESmoothModes.smooth_sum_positive_eventually hiv (-(k:ℝ)) hL
      refine ⟨64*L+16, by positivity, P0, ?_⟩
      intro P hP a N ha hb hN
      have h := hp P hP a N ha hb hN
      have hid (x : ℝ) : originalPhase 0 (-(i:ℝ)) (-(k:ℝ)) x =
          -originalPhase 0 i k x := by simpa only [neg_zero] using originalPhase_neg 0 i k x
      simpa only [Int.cast_zero, zero_div, hid, phase_neg, ← map_sum, Complex.norm_conj] using h
    · have hiv : (1:ℝ) ≤ i := by exact_mod_cast (show (1:ℤ) ≤ i by omega)
      obtain ⟨P0, hp⟩ := OOEESmoothModes.smooth_sum_positive_eventually hiv (k:ℝ) hL
      refine ⟨64*L+16, by positivity, P0, ?_⟩
      simpa only [Int.cast_zero, zero_div] using hp
  · exact mixed_sum_nonzero_eventually
      (div_ne_zero (Int.cast_ne_zero.mpr hj) (by norm_num)) (i:ℝ) (k:ℝ) hL

/-- One pair of constants works for any fixed finite family of mixed modes. -/
theorem finite_mixed_modes (s : Finset (ℤ × ℤ × ℤ)) {L : ℝ} (hL : 0 ≤ L) :
    ∃ B : ℝ, 0 < B ∧ ∃ P0 : ℝ, ∀ P : ℝ, P0 ≤ P → ∀ a : ℝ, ∀ N : ℕ,
      P ≤ a → a+2*N ≤ 2*P → (N:ℝ) ≤ L*P^(7/16:ℝ) →
      ∀ q ∈ s, q.1 ≠ 0 ∨ q.2.1 ≠ 0 →
      ‖∑ n ∈ range N, phase (originalPhase ((q.2.1:ℝ)/2) q.1 q.2.2 (a+2*n))‖ ≤ B*P^(13/32:ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, 1, by simp⟩
  | @insert q s hqs ih =>
    obtain ⟨B, hB, P0, hp⟩ := ih
    by_cases hq : q.1 ≠ 0 ∨ q.2.1 ≠ 0
    · obtain ⟨C, hC, Q0, hq'⟩ := fixed_mixed_mode q.1 q.2.1 q.2.2 hq hL
      refine ⟨max B C, hB.trans_le (le_max_left _ _), max 1 (max P0 Q0), ?_⟩
      intro P hP a N ha hb hN r hr hrmix
      have hP0 : 0 < P := by linarith [le_max_left (1:ℝ) (max P0 Q0)]
      have hPP : P0 ≤ P := (le_max_left P0 Q0).trans ((le_max_right 1 (max P0 Q0)).trans hP)
      have hPQ : Q0 ≤ P := (le_max_right P0 Q0).trans ((le_max_right 1 (max P0 Q0)).trans hP)
      rcases mem_insert.mp hr with hr | hr
      · subst r
        exact (hq' P hPQ a N ha hb hN).trans
          (mul_le_mul_of_nonneg_right (le_max_right B C) (Real.rpow_pos_of_pos hP0 _).le)
      · exact (hp P hPP a N ha hb hN r hr hrmix).trans
          (mul_le_mul_of_nonneg_right (le_max_left B C) (Real.rpow_pos_of_pos hP0 _).le)
    · refine ⟨B, hB, P0, ?_⟩
      intro P hP a N ha hb hN r hr hrmix
      rcases mem_insert.mp hr with hr | hr
      · subst r
        exact False.elim (hq hrmix)
      · exact hp P hP a N ha hb hN r hr hrmix

end Problems.Juggler.OOEEMixedModes
end Problems.Juggler.OOEEMixedModes

import Problems.Juggler.OOEECarryCells

/-! # Fourier perturbations of the actual OOEE carry-cell phases -/

noncomputable section

namespace Problems.Juggler.OOEEFourierModes

open Finset BTCalculus.WeylDifferencing BTCalculus.SecondDerivative
open Problems.Juggler.OOEECurvature Problems.Juggler.OOEECarryCells

def perturbedPhase (h u v w c r t x : ℝ) : ℝ :=
  cellPhase (2*h) u v w c x + r*(x+t)^(3/2:ℝ)

def perturbedD1 (h u v w c r t x : ℝ) : ℝ :=
  cellPhaseD1 (2*h) u v w c x + (3/2:ℝ)*r*(x+t)^(1/2:ℝ)

def perturbedD2 (h u v w c r t x : ℝ) : ℝ :=
  cellPhaseD2 (2*h) u v w c x + (3/4:ℝ)*r*(x+t)^(-1/2:ℝ)

theorem deriv_perturbed {x h t : ℝ} (hx : 0 < x) (hh : 0 ≤ h)
    (ht : 0 ≤ t) (u v w c r : ℝ) :
    HasDerivAt (perturbedPhase h u v w c r t) (perturbedD1 h u v w c r t x) x := by
  have hd := (deriv_cellPhase (s := 2*h) hx (by linarith) u v w c).fun_add
    ((deriv_shift_power (show 0 < x+t by linarith) (3/2)).const_mul r)
  apply hd.congr_deriv
  norm_num [perturbedD1]
  ring

theorem deriv_perturbedD1 {x h t : ℝ} (hx : 0 < x) (hh : 0 ≤ h)
    (ht : 0 ≤ t) (u v w c r : ℝ) :
    HasDerivAt (perturbedD1 h u v w c r t) (perturbedD2 h u v w c r t x) x := by
  have hd := (deriv_cellPhaseD1 (s := 2*h) hx (by linarith) u v w c).fun_add
    ((deriv_shift_power (show 0 < x+t by linarith) (1/2)).const_mul ((3/2)*r))
  apply hd.congr_deriv
  norm_num [perturbedD2]
  ring

/-- A deliberately coarse constant covers both the original and translated powers. -/
theorem power_curvature_scale {P y : ℝ} (hP : 0 < P) (hy : P ≤ y) (hyP : y ≤ 4*P) :
    P^(-1/2:ℝ)/4 ≤ y^(-1/2:ℝ) ∧ y^(-1/2:ℝ) ≤ P^(-1/2:ℝ) := by
  constructor
  · have hfour : (1/4:ℝ) ≤ (4:ℝ)^(-1/2:ℝ) := by
      have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 4)
        (by norm_num : (-1:ℝ) ≤ -1/2)
      norm_num at h ⊢
    calc P^(-1/2:ℝ)/4 = (1/4:ℝ)*P^(-1/2:ℝ) := by ring
         _ ≤ (4:ℝ)^(-1/2:ℝ)*P^(-1/2:ℝ) := by gcongr
         _ = (4*P)^(-1/2:ℝ) := (Real.mul_rpow (by norm_num) hP.le).symm
         _ ≤ y^(-1/2:ℝ) := Real.rpow_le_rpow_of_nonpos (hP.trans_le hy) hyP (by norm_num)
  · exact Real.rpow_le_rpow_of_nonpos hP hy (by norm_num)

/-- A nonzero Fourier mode dominates the negative carry curvature uniformly. -/
theorem perturbed_curvature {P x h u v w G eps r t : ℝ}
    (hP : 1 ≤ P) (hPx : P ≤ x) (hxP : x ≤ 2*P)
    (hh : 1 ≤ h) (hhP : h ≤ P^(1/16:ℝ)) (hsize : 1024 ≤ P^(15/16:ℝ))
    (hu : 0 < u) (hfreq : |v| + |w| ≤ u*P^(3/4:ℝ)/1024)
    (hG : G ≤ powerDiff (2*h) (3/2) x ∧ powerDiff (2*h) (3/2) x ≤ G+1)
    (heps : 0 ≤ eps ∧ eps ≤ 1) (ht : 0 ≤ t ∧ t ≤ 2*P)
    (hdom : 32*u*h ≤ |r| * P^(1/4:ℝ)) :
    (0 ≤ r → |r| * P^(-1/2:ℝ)/8 ≤ perturbedD2 h u v w (G+eps) r t x ∧
      perturbedD2 h u v w (G+eps) r t x ≤ |r| * P^(-1/2:ℝ)) ∧
    (r ≤ 0 → -(|r| * P^(-1/2:ℝ)) ≤ perturbedD2 h u v w (G+eps) r t x ∧
      perturbedD2 h u v w (G+eps) r t x ≤ -(|r| * P^(-1/2:ℝ)/8)) := by
  have hP0 : 0 < P := by linarith
  have hc := cell_curvature_uniform hP hPx hxP hh hhP hsize hu hfreq hG heps
  have hp := power_curvature_scale hP0 (show P ≤ x+t by linarith [ht.1])
    (show x+t ≤ 4*P by linarith [ht.2])
  have hpow : P^(1/4:ℝ)*P^(-3/4:ℝ) = P^(-1/2:ℝ) := by
    rw [← Real.rpow_add hP0]
    norm_num
  have he : 2*u*h*P^(-3/4:ℝ) ≤ |r| * P^(-1/2:ℝ)/16 := by
    calc _ = (32*u*h*P^(-3/4:ℝ))/16 := by ring
         _ ≤ (|r| * P^(1/4:ℝ)*P^(-3/4:ℝ))/16 := by gcongr
         _ = _ := by rw [mul_assoc, hpow]
  have hp0 : 0 ≤ P^(-1/2:ℝ) := by positivity
  dsimp [perturbedD2]
  constructor
  · intro hr
    rw [abs_of_nonneg hr] at he ⊢
    have hl := mul_le_mul_of_nonneg_left hp.1 hr
    have hu' := mul_le_mul_of_nonneg_left hp.2 hr
    constructor <;> nlinarith [hc.1, hc.2]
  · intro hr
    rw [abs_of_nonpos hr] at he ⊢
    have hl := mul_le_mul_of_nonneg_left hp.1 (neg_nonneg.mpr hr)
    have hu' := mul_le_mul_of_nonneg_left hp.2 (neg_nonneg.mpr hr)
    constructor <;> nlinarith [hc.1, hc.2]

theorem perturbed_cell_sum {P a h u v w eps r t : ℝ} {G : ℤ} (N : ℕ)
    (hP : 1 ≤ P) (ha : P ≤ a) (hb : a+2*N ≤ 2*P)
    (hh : 1 ≤ h) (hhP : h ≤ P^(1/16:ℝ)) (hsize : 1024 ≤ P^(15/16:ℝ))
    (hu : 0 < u) (hfreq : |v| + |w| ≤ u*P^(3/4:ℝ)/1024)
    (hcell : ∀ x ∈ Set.Icc a (a+2*N),
      (G:ℝ) ≤ powerDiff (2*h) (3/2) x ∧ powerDiff (2*h) (3/2) x ≤ (G:ℝ)+1)
    (heps : 0 ≤ eps ∧ eps ≤ 1) (ht : 0 ≤ t ∧ t ≤ 2*P)
    (hr : r ≠ 0) (hdom : 32*u*h ≤ |r| * P^(1/4:ℝ)) :
    ‖∑ n ∈ range N, phase (perturbedPhase h u v w (G+eps) r t (a+2*n))‖ ≤
      64*N*Real.sqrt (|r| * P^(-1/2:ℝ)/8) + 4/Real.sqrt (|r| * P^(-1/2:ℝ)/8) := by
  have hP0 : 0 < P := by linarith
  have hh0 : 0 ≤ h := by linarith
  have hpos (x : ℝ) (hx : x ∈ Set.Icc a (a+2*N)) : 0 < x := by linarith [hx.1]
  have bound := odd_lattice_second_derivative_sum_bound
    (perturbedPhase h u v w (G+eps) r t) (perturbedD1 h u v w (G+eps) r t)
    (perturbedD2 h u v w (G+eps) r t) a N
    (lam := |r| * P^(-1/2:ℝ)/8) (C := 8) (by positivity) (by norm_num)
    (fun x hx => deriv_perturbed (hpos x hx) hh0 ht.1 _ _ _ _ _)
    (fun x hx => deriv_perturbedD1 (hpos x hx) hh0 ht.1 _ _ _ _ _)
    (by
      rcases le_total 0 r with hr' | hr'
      · left
        intro x hx
        have hc := (perturbed_curvature hP (ha.trans hx.1) (hx.2.trans hb)
          hh hhP hsize hu hfreq (hcell x hx) heps ht hdom).1 hr'
        constructor <;> linarith [hc.1, hc.2]
      · right
        intro x hx
        have hc := (perturbed_curvature hP (ha.trans hx.1) (hx.2.trans hb)
          hh hhP hsize hu hfreq (hcell x hx) heps ht hdom).2 hr'
        constructor <;> linarith [hc.1, hc.2])
  simpa only [show (8:ℝ)*8 = 64 by norm_num] using bound

theorem curvature_bound_at_cutoff {P L lam S : ℝ} (N : ℕ)
    (hP : 1 ≤ P) (hL : 0 ≤ L) (hN : (N:ℝ) ≤ L*P^(7/16:ℝ))
    (hl : P^(-1/2:ℝ)/16 ≤ lam) (hu : lam ≤ P^(-1/4:ℝ))
    (hs : S ≤ 64*N*Real.sqrt lam+4/Real.sqrt lam) :
    S ≤ (64*L+16)*P^(5/16:ℝ) := by
  have hP0 : 0 < P := by linarith
  have hlam : 0 < lam := lt_of_lt_of_le (by positivity) hl
  have hroot (q : ℝ) : Real.sqrt (P^q) = P^(q/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hP0.le]
    congr 1
    ring
  have hs16 : Real.sqrt (16:ℝ) = 4 := by norm_num
  have hlo : P^(-1/4:ℝ)/4 ≤ Real.sqrt lam := by
    have h := Real.sqrt_le_sqrt hl
    rw [Real.sqrt_div (by positivity), hroot, hs16] at h
    convert h using 1
    norm_num
  have hhi : Real.sqrt lam ≤ P^(-1/8:ℝ) := by
    have h := Real.sqrt_le_sqrt hu
    rw [hroot] at h
    convert h using 1
    norm_num
  have hprod : P^(7/16:ℝ)*P^(-1/8:ℝ) = P^(5/16:ℝ) := by
    rw [← Real.rpow_add hP0]
    norm_num
  have hfirst : 64*N*Real.sqrt lam ≤ 64*L*P^(5/16:ℝ) := by
    calc _ ≤ 64*(L*P^(7/16:ℝ))*P^(-1/8:ℝ) := by gcongr
         _ = _ := by rw [← hprod]; ring
  have hsecond : 4/Real.sqrt lam ≤ 16*P^(5/16:ℝ) := by
    calc _ ≤ 4/(P^(-1/4:ℝ)/4) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hlo
         _ = 16*P^(1/4:ℝ) := by
           rw [show (-1/4:ℝ) = -(1/4) by norm_num, Real.rpow_neg hP0.le]
           field_simp
           norm_num
         _ ≤ _ := mul_le_mul_of_nonneg_left
           (Real.rpow_le_rpow_of_exponent_le hP (by norm_num)) (by norm_num)
  nlinarith

theorem perturbed_cell_power_bound {P a h u v w eps r t L : ℝ} {G : ℤ} (N : ℕ)
    (hP : 1 ≤ P) (ha : P ≤ a) (hb : a+2*N ≤ 2*P)
    (hh : 1 ≤ h) (hhP : h ≤ P^(1/16:ℝ)) (hsize : 1024 ≤ P^(15/16:ℝ))
    (hu : 0 < u) (hfreq : |v| + |w| ≤ u*P^(3/4:ℝ)/1024)
    (hcell : ∀ x ∈ Set.Icc a (a+2*N),
      (G:ℝ) ≤ powerDiff (2*h) (3/2) x ∧ powerDiff (2*h) (3/2) x ≤ (G:ℝ)+1)
    (heps : 0 ≤ eps ∧ eps ≤ 1) (ht : 0 ≤ t ∧ t ≤ 2*P)
    (hr : 1 ≤ |r|) (hrP : |r| ≤ P^(1/4:ℝ)) (hdom : 32*u ≤ P^(3/16:ℝ))
    (hL : 0 ≤ L) (hN : (N:ℝ) ≤ L*P^(7/16:ℝ)) :
    ‖∑ n ∈ range N, phase (perturbedPhase h u v w (G+eps) r t (a+2*n))‖ ≤
      (64*L+16)*P^(5/16:ℝ) := by
  have hP0 : 0 < P := by linarith
  have hdom' : 32*u*h ≤ |r| * P^(1/4:ℝ) := by
    calc _ ≤ P^(3/16:ℝ)*P^(1/16:ℝ) := by gcongr
         _ = P^(1/4:ℝ) := by rw [← Real.rpow_add hP0]; norm_num
         _ ≤ _ := by simpa using mul_le_mul_of_nonneg_right hr (Real.rpow_pos_of_pos hP0 (1/4)).le
  have hlo : P^(-1/2:ℝ)/16 ≤ |r| * P^(-1/2:ℝ)/8 := by
    have hm := mul_le_mul_of_nonneg_right hr (Real.rpow_pos_of_pos hP0 (-1/2)).le
    nlinarith [Real.rpow_pos_of_pos hP0 (-1/2)]
  have hhi : |r| * P^(-1/2:ℝ)/8 ≤ P^(-1/4:ℝ) := by
    calc _ ≤ P^(1/4:ℝ)*P^(-1/2:ℝ)/8 := by gcongr
         _ = P^(-1/4:ℝ)/8 := by rw [← Real.rpow_add hP0]; norm_num
         _ ≤ _ := by linarith [Real.rpow_pos_of_pos hP0 (-1/4)]
  exact curvature_bound_at_cutoff N hP hL hN hlo hhi
    (perturbed_cell_sum N hP ha hb hh hhP hsize hu hfreq hcell heps ht
      (abs_pos.mp (by linarith)) hdom')

/-- The unweighted power modes used to count smoothing errors on these same samples. -/
theorem power_mode_sum {P a r t L : ℝ} (N : ℕ)
    (hP : 1 ≤ P) (ha : P ≤ a) (hb : a+2*N ≤ 2*P)
    (ht : 0 ≤ t ∧ t ≤ 2*P) (hr : 1 ≤ |r|) (hrP : |r| ≤ P^(1/4:ℝ))
    (hL : 0 ≤ L) (hN : (N:ℝ) ≤ L*P^(7/16:ℝ)) :
    ‖∑ n ∈ range N, phase (r*(a+2*n+t)^(3/2:ℝ))‖ ≤ (64*L+16)*P^(5/16:ℝ) := by
  have hP0 : 0 < P := by linarith
  have hr0 : 0 < |r| := by linarith
  have hpos (x : ℝ) (hx : x ∈ Set.Icc a (a+2*N)) : 0 < x+t := by linarith [hx.1, ht.1]
  have hf (x : ℝ) (hx : x ∈ Set.Icc a (a+2*N)) :
      HasDerivAt (fun y => r*(y+t)^(3/2:ℝ)) ((3/2)*r*(x+t)^(1/2:ℝ)) x := by
    have hd := (deriv_shift_power (hpos x hx) (3/2)).const_mul r
    apply hd.congr_deriv
    norm_num
    ring
  have hg (x : ℝ) (hx : x ∈ Set.Icc a (a+2*N)) :
      HasDerivAt (fun y => (3/2)*r*(y+t)^(1/2:ℝ)) ((3/4)*r*(x+t)^(-1/2:ℝ)) x := by
    have hd := (deriv_shift_power (hpos x hx) (1/2)).const_mul ((3/2)*r)
    apply hd.congr_deriv
    norm_num
    ring
  have bounds := odd_lattice_second_derivative_sum_bound _ _ _ a N
    (lam := |r| * P^(-1/2:ℝ)/8) (C := 8) (by positivity) (by norm_num) hf hg
    (by
      rcases le_total 0 r with hrs | hrs
      · left
        intro x hx
        have hp := power_curvature_scale hP0 (show P ≤ x+t by linarith [hx.1, ht.1])
          (show x+t ≤ 4*P by linarith [hx.2, ht.2])
        rw [abs_of_nonneg hrs]
        have hl := mul_le_mul_of_nonneg_left hp.1 hrs
        have hu := mul_le_mul_of_nonneg_left hp.2 hrs
        constructor <;> nlinarith [mul_nonneg hrs (Real.rpow_pos_of_pos hP0 (-1/2)).le]
      · right
        intro x hx
        have hp := power_curvature_scale hP0 (show P ≤ x+t by linarith [hx.1, ht.1])
          (show x+t ≤ 4*P by linarith [hx.2, ht.2])
        rw [abs_of_nonpos hrs]
        have hl := mul_le_mul_of_nonneg_left hp.1 (neg_nonneg.mpr hrs)
        have hu := mul_le_mul_of_nonneg_left hp.2 (neg_nonneg.mpr hrs)
        constructor <;> nlinarith [mul_nonneg (neg_nonneg.mpr hrs) (Real.rpow_pos_of_pos hP0 (-1/2)).le])
  have hlo : P^(-1/2:ℝ)/16 ≤ |r| * P^(-1/2:ℝ)/8 := by
    have hm := mul_le_mul_of_nonneg_right hr (Real.rpow_pos_of_pos hP0 (-1/2)).le
    nlinarith [Real.rpow_pos_of_pos hP0 (-1/2)]
  have hhi : |r| * P^(-1/2:ℝ)/8 ≤ P^(-1/4:ℝ) := by
    calc _ ≤ P^(1/4:ℝ)*P^(-1/2:ℝ)/8 := by gcongr
         _ = P^(-1/4:ℝ)/8 := by rw [← Real.rpow_add hP0]; norm_num
         _ ≤ _ := by linarith [Real.rpow_pos_of_pos hP0 (-1/4)]
  apply curvature_bound_at_cutoff N hP hL hN hlo hhi
  simpa only [show (8:ℝ)*8 = 64 by norm_num] using bounds

/-- Sampled cells require no extra equality at the unsampled right endpoint. -/
theorem perturbed_samples_bound {P a h u v w eps r t L : ℝ} {G : ℤ} (N : ℕ)
    (hP : 1 ≤ P) (ha : P ≤ a) (hb : a+2*N ≤ 2*P)
    (hh : 1 ≤ h) (hhP : h ≤ P^(1/16:ℝ)) (hsize : 1024 ≤ P^(15/16:ℝ))
    (hu : 0 < u) (hfreq : |v| + |w| ≤ u*P^(3/4:ℝ)/1024)
    (hcell : ∀ n < N, ⌊gap h (a+2*n)⌋ = G)
    (heps : 0 ≤ eps ∧ eps ≤ 1) (ht : 0 ≤ t ∧ t ≤ 2*P)
    (hr : 1 ≤ |r|) (hrP : |r| ≤ P^(1/4:ℝ)) (hdom : 32*u ≤ P^(3/16:ℝ))
    (hL : 0 ≤ L) (hN : (N:ℝ) ≤ L*P^(7/16:ℝ)) :
    ‖∑ n ∈ range N, phase (perturbedPhase h u v w (G+eps) r t (a+2*n))‖ ≤
      (64*L+16)*P^(5/16:ℝ)+1 := by
  cases N with
  | zero => simp only [sum_range_zero, norm_zero]; positivity
  | succ N =>
    have hP0 : 0 < P := by linarith
    have hh0 : 0 ≤ h := by linarith
    have hclosed (x : ℝ) (hx : x ∈ Set.Icc a (a+2*N)) :
        (G:ℝ) ≤ powerDiff (2*h) (3/2) x ∧ powerDiff (2*h) (3/2) x ≤ (G:ℝ)+1 := by
      have hlo := Int.floor_le (gap h a)
      have hhi := Int.lt_floor_add_one (gap h (a+2*N))
      have h0 := hcell 0 (by omega)
      simp only [Nat.cast_zero, mul_zero, add_zero] at h0
      rw [h0] at hlo
      rw [hcell N (by omega)] at hhi
      have hm1 := gap_mono hP0 ha hx.1 hh0
      have hm2 := gap_mono hP0 (ha.trans hx.1) hx.2 hh0
      change (G:ℝ) ≤ gap h x ∧ gap h x ≤ (G:ℝ)+1
      constructor <;> linarith
    have hs := perturbed_cell_power_bound N hP ha (by push_cast at hb; linarith)
      hh hhP hsize hu hfreq hclosed heps ht hr hrP hdom hL (by push_cast at hN; linarith)
    rw [sum_range_succ]
    exact (norm_add_le _ _).trans (by rw [phase_norm]; linarith)

end Problems.Juggler.OOEEFourierModes

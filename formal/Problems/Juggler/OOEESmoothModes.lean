import Problems.Juggler.OOEEPhaseComparison

/-! # The OOEE modes with zero nested-power coefficient

These modes have ordinary second-derivative cancellation. Pure slow
modes, whose three-halves coefficient also vanishes, are excluded.
-/

noncomputable section

namespace Problems.Juggler.OOEESmoothModes

open Finset BTCalculus.WeylDifferencing BTCalculus.SecondDerivative
open OOEECurvature OOEEFourierModes OOEEPhaseComparison

theorem smooth_sum_positive {P a v w L : ℝ} (N : ℕ)
    (hP : 1 ≤ P) (ha : P ≤ a) (hb : a+2*N ≤ 2*P)
    (hv : 1 ≤ v) (hvP : v ≤ P^(1/4:ℝ))
    (hw : |w| ≤ v*P^(3/8:ℝ)/16) (hL : 0 ≤ L)
    (hN : (N:ℝ) ≤ L*P^(7/16:ℝ)) :
    ‖∑ n ∈ range N, phase (originalPhase 0 v w (a+2*n))‖ ≤
      (64*L+16)*P^(5/16:ℝ) := by
  have hP0 : 0 < P := by linarith
  have hv0 : 0 < v := by linarith
  let f : ℝ → ℝ := fun x => (v/2)*x^(3/2:ℝ)+(w/2)*x^(9/8:ℝ)
  let g : ℝ → ℝ := fun x => (3/4)*v*x^(1/2:ℝ)+(9/16)*w*x^(1/8:ℝ)
  let q : ℝ → ℝ := fun x => (3/8)*v*x^(-1/2:ℝ)+(9/128)*w*x^(-7/8:ℝ)
  have hx0 (x : ℝ) (hx : x ∈ Set.Icc a (a+2*N)) : 0 < x := by linarith [hx.1]
  have hf (x : ℝ) (hx : x ∈ Set.Icc a (a+2*N)) : HasDerivAt f (g x) x := by
    have hd := ((deriv_power (hx0 x hx) (3/2)).const_mul (v/2)).fun_add
      ((deriv_power (hx0 x hx) (9/8)).const_mul (w/2))
    apply hd.congr_deriv
    norm_num [g]
    ring
  have hg (x : ℝ) (hx : x ∈ Set.Icc a (a+2*N)) : HasDerivAt g (q x) x := by
    have hd := ((deriv_power (hx0 x hx) (1/2)).const_mul ((3/4)*v)).fun_add
      ((deriv_power (hx0 x hx) (1/8)).const_mul ((9/16)*w))
    apply hd.congr_deriv
    norm_num [q]
    ring
  have hcurv (x : ℝ) (hx : x ∈ Set.Icc a (a+2*N)) :
      v*P^(-1/2:ℝ)/16 ≤ q x ∧ q x ≤ 8*(v*P^(-1/2:ℝ)/16) := by
    have hp := power_curvature_scale hP0 (show P ≤ x by linarith [hx.1])
      (show x ≤ 4*P by linarith [hx.2])
    have hxp := Real.rpow_le_rpow_of_nonpos hP0 (show P ≤ x by linarith [hx.1])
      (by norm_num : (-7/8:ℝ) ≤ 0)
    have hid : P^(3/8:ℝ)*P^(-7/8:ℝ) = P^(-1/2:ℝ) := by
      rw [← Real.rpow_add hP0]
      norm_num
    have he : |(9/128:ℝ)*w*x^(-7/8:ℝ)| ≤ (9/2048)*v*P^(-1/2:ℝ) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_pos_of_pos (hx0 x hx) _).le]
      rw [abs_of_pos (by norm_num : (0:ℝ) < 9/128)]
      calc (9/128:ℝ)*|w| *x^(-7/8:ℝ)
          ≤ (9/128:ℝ)*(v*P^(3/8:ℝ)/16)*P^(-7/8:ℝ) := by
            gcongr
            exact (Real.rpow_pos_of_pos (hx0 x hx) _).le
        _ = _ := by rw [← hid]; ring
    have he' := abs_le.mp he
    have hlo := mul_le_mul_of_nonneg_left hp.1 hv0.le
    have hhi := mul_le_mul_of_nonneg_left hp.2 hv0.le
    dsimp [q]
    constructor <;> nlinarith [show 0 ≤ v*P^(-1/2:ℝ) by positivity]
  have hs := odd_lattice_second_derivative_sum_bound f g q a N
    (lam := v*P^(-1/2:ℝ)/16) (C := 8) (by positivity) (by norm_num)
    hf hg (Or.inl hcurv)
  have hlo : P^(-1/2:ℝ)/16 ≤ v*P^(-1/2:ℝ)/16 := by
    have := mul_le_mul_of_nonneg_right hv (Real.rpow_pos_of_pos hP0 (-1/2)).le
    linarith
  have hhi : v*P^(-1/2:ℝ)/16 ≤ P^(-1/4:ℝ) := by
    calc _ ≤ P^(1/4:ℝ)*P^(-1/2:ℝ)/16 := by gcongr
      _ = P^(-1/4:ℝ)/16 := by rw [← Real.rpow_add hP0]; norm_num
      _ ≤ _ := by linarith [Real.rpow_pos_of_pos hP0 (-1/4)]
  have hc := curvature_bound_at_cutoff N hP hL hN hlo hhi
    (by simpa only [show (8:ℝ)*8 = 64 by norm_num] using hs)
  simpa only [f, originalPhase, zero_mul, zero_add] using hc

theorem smooth_sum_positive_eventually {v : ℝ} (hv : 1 ≤ v) (w : ℝ)
    {L : ℝ} (hL : 0 ≤ L) :
    ∃ P0 : ℝ, ∀ P : ℝ, P0 ≤ P → ∀ a : ℝ, ∀ N : ℕ,
      P ≤ a → a+2*N ≤ 2*P → (N:ℝ) ≤ L*P^(7/16:ℝ) →
      ‖∑ n ∈ range N, phase (originalPhase 0 v w (a+2*n))‖ ≤
        (64*L+16)*P^(13/32:ℝ) := by
  have hv0 : 0 < v := by linarith
  have hvP := (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/4)).eventually_ge_atTop v
  have hwP := (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 3/8)).eventually_ge_atTop (16*|w| /v)
  have he : ∀ᶠ P : ℝ in Filter.atTop, 1 ≤ P ∧ v ≤ P^(1/4:ℝ) ∧ |w| ≤ v*P^(3/8:ℝ)/16 := by
    filter_upwards [Filter.eventually_ge_atTop (1:ℝ), hvP, hwP] with P hP hvP hwP
    refine ⟨hP, hvP, ?_⟩
    have hm := (div_le_iff₀ hv0).mp hwP
    nlinarith
  obtain ⟨P0, hp⟩ := Filter.eventually_atTop.1 he
  refine ⟨P0, ?_⟩
  intro P hP a N ha hb hN
  obtain ⟨hP1, hvP, hwP⟩ := hp P hP
  exact (smooth_sum_positive N hP1 ha hb hv hvP hwP hL hN).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hP1 (by norm_num)) (by positivity))

end Problems.Juggler.OOEESmoothModes

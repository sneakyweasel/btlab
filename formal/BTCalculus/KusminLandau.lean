import BTCalculus.WeylCancellation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! # Cancellation from monotone phase increments

An elementary summation-by-parts proof of the finite first-derivative
estimate, with an explicit gap from integral phase increments.
-/

noncomputable section

namespace BTCalculus.KusminLandau

open Finset Filter
open scoped Topology ComplexConjugate
open BTCalculus.WeylDifferencing

/-- The imaginary part of the reciprocal of `phase t - 1`. -/
def cotWeight (t : ℝ) : ℝ := -(Real.cos (Real.pi * t) / (2 * Real.sin (Real.pi * t)))

/-- The reciprocal chord coefficient, written with a constant real part. -/
def chordWeight (t : ℝ) : ℂ := ⟨-1 / 2, cotWeight t⟩

theorem phase_re (t : ℝ) : (phase t).re = Real.cos (2 * Real.pi * t) :=
  Complex.exp_ofReal_mul_I_re _

theorem phase_im (t : ℝ) : (phase t).im = Real.sin (2 * Real.pi * t) :=
  Complex.exp_ofReal_mul_I_im _

theorem sin_pi_mul_pos {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    0 < Real.sin (Real.pi * t) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · positivity
  · nlinarith [Real.pi_pos]

theorem cotWeight_mono {x y : ℝ} (hx : 0 < x) (hy : y < 1) (hxy : x ≤ y) :
    cotWeight x ≤ cotWeight y := by
  have hsx := sin_pi_mul_pos hx (hxy.trans_lt hy)
  have hsy := sin_pi_mul_pos (hx.trans_le hxy) hy
  have hs : 0 ≤ Real.sin (Real.pi * y - Real.pi * x) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · exact sub_nonneg.mpr (mul_le_mul_of_nonneg_left hxy Real.pi_pos.le)
    · nlinarith [Real.pi_pos, mul_pos Real.pi_pos hx]
  unfold cotWeight
  rw [neg_le_neg_iff, div_le_div_iff₀ (by positivity) (by positivity)]
  rw [Real.sin_sub] at hs
  nlinarith

theorem chordWeight_mul {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    chordWeight t * (phase t - 1) = 1 := by
  have hs : Real.sin (Real.pi * t) ≠ 0 := ne_of_gt (sin_pi_mul_pos ht ht1)
  have htrig := Real.sin_sq_add_cos_sq (Real.pi * t)
  have hp : 2 * Real.pi * t = 2 * (Real.pi * t) := by ring
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im, chordWeight, cotWeight, phase_re, phase_im,
      hp, Real.cos_two_mul, Real.sin_two_mul]
  · field_simp [hs]
    ring
  · field_simp [hs]
    nlinarith [congrArg (fun x : ℝ => x * Real.cos (Real.pi * t)) htrig]

theorem sin_pi_mul_lower {t δ : ℝ} (hδ : 0 < δ) (ht : δ ≤ t) (ht1 : t ≤ 1 - δ) :
    2 * δ ≤ Real.sin (Real.pi * t) := by
  have hpi := Real.pi_pos
  have hlow (u : ℝ) (hu : 0 ≤ u) (hu2 : u ≤ 1 / 2) :
      2 * u ≤ Real.sin (Real.pi * u) := by
    have h := Real.mul_le_sin (x := Real.pi * u) (by positivity) (by nlinarith)
    have he : 2 / Real.pi * (Real.pi * u) = 2 * u := by field_simp
    rwa [he] at h
  by_cases hh : t ≤ 1 / 2
  · exact (by linarith : 2 * δ ≤ 2 * t).trans (hlow t (by linarith) hh)
  · have h := hlow (1 - t) (by linarith) (by linarith)
    rw [show Real.pi * (1 - t) = Real.pi - Real.pi * t by ring, Real.sin_pi_sub] at h
    linarith

theorem phase_chord_lower {t δ : ℝ} (hδ : 0 < δ) (ht : δ ≤ t) (ht1 : t ≤ 1 - δ) :
    4 * δ ≤ ‖phase t - 1‖ := by
  have hnorm : ‖phase t - 1‖ = |2 * Real.sin (Real.pi * t)| := by
    unfold phase
    rw [mul_comm _ Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one]
    rw [show 2 * Real.pi * t / 2 = Real.pi * t by ring, Real.norm_eq_abs]
  have hs : 0 < Real.sin (Real.pi * t) := by linarith [sin_pi_mul_lower hδ ht ht1]
  rw [hnorm, abs_of_pos (mul_pos (by norm_num) hs)]
  linarith [sin_pi_mul_lower hδ ht ht1]

theorem chordWeight_norm_le {t δ : ℝ} (hδ : 0 < δ) (ht : δ ≤ t) (ht1 : t ≤ 1 - δ) :
    ‖chordWeight t‖ ≤ 1 / (4 * δ) := by
  have he := congrArg norm (chordWeight_mul (hδ.trans_le ht) (by linarith : t < 1))
  rw [norm_mul, norm_one] at he
  have hm := mul_le_mul_of_nonneg_left (phase_chord_lower hδ ht ht1)
    (norm_nonneg (chordWeight t))
  apply (le_div_iff₀ (by positivity : 0 < 4 * δ)).2
  nlinarith

/-- Discrete summation by parts with both endpoints retained. -/
theorem weighted_difference_sum (z a : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ range (N + 1), a n * (z (n + 1) - z n)) =
      a N * z (N + 1) - a 0 * z 0 +
        ∑ n ∈ range N, (a n - a (n + 1)) * z (n + 1) := by
  induction N with
  | zero => simp; ring
  | succ N ih =>
    rw [sum_range_succ, ih, sum_range_succ]
    ring

/-- A monotone real sequence has no variation beyond its endpoint difference. -/
theorem variation_le_endpoints (u : ℕ → ℝ) (N : ℕ)
    (hmono : (∀ n < N, u n ≤ u (n + 1)) ∨ (∀ n < N, u (n + 1) ≤ u n)) :
    ∑ n ∈ range N, |u n - u (n + 1)| ≤ |u 0| + |u N| := by
  rcases hmono with hm | hm
  · have he : (∑ n ∈ range N, |u n - u (n + 1)|) = u N - u 0 := by
      calc (∑ n ∈ range N, |u n - u (n + 1)|)
          = ∑ n ∈ range N, (u (n + 1) - u n) := by
            apply sum_congr rfl
            intro n hn
            rw [abs_of_nonpos (sub_nonpos.mpr (hm n (mem_range.mp hn)))]
            ring
        _ = _ := sum_range_sub u N
    rw [he]
    linarith [le_abs_self (u N), neg_le_abs (u 0)]
  · have he : (∑ n ∈ range N, |u n - u (n + 1)|) = u 0 - u N := by
      calc (∑ n ∈ range N, |u n - u (n + 1)|)
          = ∑ n ∈ range N, (u n - u (n + 1)) := by
            apply sum_congr rfl
            intro n hn
            exact abs_of_nonneg (sub_nonneg.mpr (hm n (mem_range.mp hn)))
        _ = _ := sum_range_sub' u N
    rw [he]
    linarith [le_abs_self (u 0), neg_le_abs (u N)]

theorem chordWeight_sub_norm (x y : ℝ) :
    ‖chordWeight x - chordWeight y‖ = |cotWeight x - cotWeight y| := by
  have he : chordWeight x - chordWeight y =
      ((cotWeight x - cotWeight y : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [chordWeight]
  rw [he, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

theorem cotWeight_abs_le_norm (t : ℝ) : |cotWeight t| ≤ ‖chordWeight t‖ :=
  Complex.abs_im_le_norm (chordWeight t)

theorem phase_step (f : ℕ → ℝ) (n : ℕ) :
    phase (f (n + 1)) - phase (f n) = phase (f n) * (phase (f (n + 1) - f n) - 1) := by
  have he (x y : ℝ) : phase x * phase y = phase (x + y) := by
    unfold phase
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [mul_sub, he, mul_one]
  congr 1
  congr 1
  ring

/-- A finite first-derivative estimate for monotone increments in `[δ,1-δ]`. -/
theorem kusmin_landau_sum_range_succ (f : ℕ → ℝ) (N : ℕ) {δ : ℝ}
    (hδ : 0 < δ)
    (hgap : ∀ n ≤ N, δ ≤ f (n + 1) - f n ∧ f (n + 1) - f n ≤ 1 - δ)
    (hmono : (∀ n < N, f (n + 1) - f n ≤ f (n + 2) - f (n + 1)) ∨
      (∀ n < N, f (n + 2) - f (n + 1) ≤ f (n + 1) - f n)) :
    ‖∑ n ∈ range (N + 1), phase (f n)‖ ≤ 1 / δ := by
  let d : ℕ → ℝ := fun n => f (n + 1) - f n
  let a : ℕ → ℂ := fun n => chordWeight (d n)
  let z : ℕ → ℂ := fun n => phase (f n)
  have ha (n : ℕ) (hn : n ≤ N) : ‖a n‖ ≤ 1 / (4 * δ) :=
    chordWeight_norm_le hδ (hgap n hn).1 (hgap n hn).2
  have hweight (n : ℕ) (hn : n ≤ N) : a n * (z (n + 1) - z n) = z n := by
    dsimp [a, z, d]
    rw [phase_step]
    have he := chordWeight_mul (hδ.trans_le (hgap n hn).1)
      (by linarith [(hgap n hn).2] : f (n + 1) - f n < 1)
    calc chordWeight (f (n + 1) - f n) *
          (phase (f n) * (phase (f (n + 1) - f n) - 1))
        = phase (f n) * (chordWeight (f (n + 1) - f n) *
          (phase (f (n + 1) - f n) - 1)) := by ring
      _ = phase (f n) := by rw [he, mul_one]
  have hvar : ∑ n ∈ range N, ‖a n - a (n + 1)‖ ≤ ‖a 0‖ + ‖a N‖ := by
    simp_rw [a, chordWeight_sub_norm]
    apply (variation_le_endpoints (fun n => cotWeight (d n)) N ?_).trans
      (add_le_add (cotWeight_abs_le_norm (d 0)) (cotWeight_abs_le_norm (d N)))
    rcases hmono with hm | hm
    · left
      intro n hn
      exact cotWeight_mono (hδ.trans_le (hgap n (by omega)).1)
        (by dsimp [d]; have := (hgap (n + 1) (by omega)).2; simp only [Nat.add_assoc] at this; linarith)
        (hm n hn)
    · right
      intro n hn
      exact cotWeight_mono (hδ.trans_le (hgap (n + 1) (by omega)).1)
        (by dsimp [d]; linarith [(hgap n (by omega)).2]) (hm n hn)
  have hrepr : (∑ n ∈ range (N + 1), z n) =
      a N * z (N + 1) - a 0 * z 0 +
        ∑ n ∈ range N, (a n - a (n + 1)) * z (n + 1) := by
    rw [← weighted_difference_sum]
    apply sum_congr rfl
    intro n hn
    exact (hweight n (by simpa using mem_range.mp hn)).symm
  change ‖∑ n ∈ range (N + 1), z n‖ ≤ _
  rw [hrepr]
  calc ‖a N * z (N + 1) - a 0 * z 0 +
        ∑ n ∈ range N, (a n - a (n + 1)) * z (n + 1)‖
      ≤ ‖a N * z (N + 1) - a 0 * z 0‖ +
        ‖∑ n ∈ range N, (a n - a (n + 1)) * z (n + 1)‖ := norm_add_le _ _
    _ ≤ (‖a N * z (N + 1)‖ + ‖a 0 * z 0‖) +
        ∑ n ∈ range N, ‖(a n - a (n + 1)) * z (n + 1)‖ :=
      add_le_add (norm_sub_le _ _) (norm_sum_le _ _)
    _ = (‖a N‖ + ‖a 0‖) + ∑ n ∈ range N, ‖a n - a (n + 1)‖ := by
      simp only [norm_mul, z, phase_norm, mul_one]
    _ ≤ (‖a N‖ + ‖a 0‖) + (‖a 0‖ + ‖a N‖) := add_le_add le_rfl hvar
    _ ≤ 1 / δ := by
      have h0 := ha 0 (Nat.zero_le N)
      have hN := ha N le_rfl
      have he : (4 : ℝ) * (1 / (4 * δ)) = 1 / δ := by ring
      linarith

/-- The length-zero case is included; increments are checked on the actual support. -/
theorem kusmin_landau_sum_range (f : ℕ → ℝ) (N : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ n < N, δ ≤ f (n + 1) - f n ∧ f (n + 1) - f n ≤ 1 - δ)
    (hmono : (∀ n, n + 1 < N → f (n + 1) - f n ≤ f (n + 2) - f (n + 1)) ∨
      (∀ n, n + 1 < N → f (n + 2) - f (n + 1) ≤ f (n + 1) - f n)) :
    ‖∑ n ∈ range N, phase (f n)‖ ≤ 1 / δ := by
  cases N with
  | zero => simpa using (le_of_lt (one_div_pos.mpr hδ))
  | succ N =>
    apply kusmin_landau_sum_range_succ f N hδ
    · intro n hn
      exact hgap n (by omega)
    · rcases hmono with hm | hm
      · exact Or.inl (fun n hn => hm n (by omega))
      · exact Or.inr (fun n hn => hm n (by omega))

/-- A varying gap still gives cancellation when length times gap tends to infinity. -/
theorem tendsto_phase_average_zero_of_gap (f : ℕ → ℝ) (δ : ℕ → ℝ)
    (hδ : ∀ N, 0 < N → 0 < δ N)
    (hgap : ∀ N, 0 < N → ∀ n < N,
      δ N ≤ f (n + 1) - f n ∧ f (n + 1) - f n ≤ 1 - δ N)
    (hmono : (∀ n, f (n + 1) - f n ≤ f (n + 2) - f (n + 1)) ∨
      (∀ n, f (n + 2) - f (n + 1) ≤ f (n + 1) - f n))
    (hscale : Tendsto (fun N : ℕ => (N : ℝ) * δ N) atTop atTop) :
    Tendsto (average (fun n => phase (f n))) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun N : ℕ => ((N : ℝ) * δ N)⁻¹)
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hNp : 0 < N := by omega
    have hbound := kusmin_landau_sum_range f N (hδ N hNp) (hgap N hNp)
      (hmono.imp (fun hm n _ => hm n) (fun hm n _ => hm n))
    rw [norm_average]
    calc ‖∑ n ∈ range N, phase (f n)‖ / (N : ℝ)
        ≤ (1 / δ N) / (N : ℝ) := div_le_div_of_nonneg_right hbound (by positivity)
      _ = ((N : ℝ) * δ N)⁻¹ := by ring
  · exact tendsto_inv_atTop_zero.comp hscale

/-- The mean value point for one lattice increment stays in the whole open interval. -/
theorem exists_increment_deriv (f g : ℝ → ℝ) (a : ℝ) (N n : ℕ) (hn : n < N)
    (hc : ContinuousOn f (Set.Icc a (a + N)))
    (hd : ∀ x ∈ Set.Ioo a (a + N), HasDerivAt f (g x) x) :
    ∃ x ∈ Set.Ioo (a + n) (a + n + 1), x ∈ Set.Ioo a (a + N) ∧
      g x = f (a + (n + 1 : ℕ)) - f (a + n) := by
  have hnR : (n : ℝ) + 1 ≤ N := by exact_mod_cast hn
  have hnonneg : (0 : ℝ) ≤ n := by positivity
  have hsub : Set.Icc (a + n) (a + n + 1) ⊆ Set.Icc a (a + N) := by
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hsub' : Set.Ioo (a + n) (a + n + 1) ⊆ Set.Ioo a (a + N) := by
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  obtain ⟨x, hx, he⟩ := exists_hasDerivAt_eq_slope f g
    (by linarith : a + (n : ℝ) < a + n + 1) (hc.mono hsub)
    (fun x hx => hd x (hsub' hx))
  refine ⟨x, hx, hsub' hx, ?_⟩
  simpa [Nat.cast_add, Nat.cast_one, add_assoc] using he

/-- The continuous first-derivative form on a translated lattice interval. -/
theorem first_derivative_sum_bound (f g : ℝ → ℝ) (a : ℝ) (N : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hc : ContinuousOn f (Set.Icc a (a + N)))
    (hd : ∀ x ∈ Set.Ioo a (a + N), HasDerivAt f (g x) x)
    (hgap : ∀ x ∈ Set.Ioo a (a + N), δ ≤ g x ∧ g x ≤ 1 - δ)
    (hm : MonotoneOn g (Set.Ioo a (a + N)) ∨ AntitoneOn g (Set.Ioo a (a + N))) :
    ‖∑ n ∈ range N, phase (f (a + n))‖ ≤ 1 / δ := by
  apply kusmin_landau_sum_range (fun n => f (a + n)) N hδ
  · intro n hn
    obtain ⟨x, _, hx, he⟩ := exists_increment_deriv f g a N n hn hc hd
    simpa only [he] using hgap x hx
  · have hstep (n : ℕ) (hn : n + 1 < N) :
        ∃ x ∈ Set.Ioo a (a + N), ∃ y ∈ Set.Ioo a (a + N), x ≤ y ∧
          g x = f (a + (n + 1 : ℕ)) - f (a + n) ∧
          g y = f (a + (n + 2 : ℕ)) - f (a + (n + 1 : ℕ)) := by
      obtain ⟨x, hx, hx', hex⟩ := exists_increment_deriv f g a N n (by omega) hc hd
      obtain ⟨y, hy, hy', hey⟩ := exists_increment_deriv f g a N (n + 1) hn hc hd
      refine ⟨x, hx', y, hy', ?_, hex, ?_⟩
      · have := hx.2
        have := hy.1
        push_cast at *
        linarith
      · simpa only [Nat.add_assoc] using hey
    rcases hm with hm | hm
    · left
      intro n hn
      obtain ⟨x, hx, y, hy, hxy, hex, hey⟩ := hstep n hn
      simpa only [hex, hey] using hm hx hy hxy
    · right
      intro n hn
      obtain ⟨x, hx, y, hy, hxy, hex, hey⟩ := hstep n hn
      simpa only [hex, hey] using hm hx hy hxy

end BTCalculus.KusminLandau

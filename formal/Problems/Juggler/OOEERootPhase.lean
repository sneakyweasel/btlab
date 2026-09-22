import Problems.Juggler.OOEEMixedModes

/-! # The actual square-root phase in the last OOEE guard

Both integer floors are retained. A difference-of-squares argument
controls the last square root using the one-sided first-floor remainder.
-/

noncomputable section

namespace Problems.Juggler.OOEERootPhase

open Finset BTCalculus.WeylDifferencing BTCalculus.SecondDerivative
open OOEEPhaseComparison OOEEMixedModes

def secondFloor (x : ℝ) : ℝ := (⌊nestedPower x⌋ : ℤ)

def actualRoot (x : ℝ) : ℝ := Real.sqrt (secondFloor x)

def actualPhase (u v w x : ℝ) : ℝ :=
  u*nestedPower x+(v/2)*x^(3/2:ℝ)+(w/2)*actualRoot x

theorem firstFloor_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ firstFloor x := by
  unfold firstFloor
  exact_mod_cast Int.floor_nonneg.mpr (Real.rpow_nonneg hx _)

theorem secondFloor_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ secondFloor x := by
  unfold secondFloor
  exact_mod_cast Int.floor_nonneg.mpr (Real.rpow_nonneg (firstFloor_nonneg hx) _)

theorem nestedPower_le {x : ℝ} (hx : 0 ≤ x) : nestedPower x ≤ x^(9/4:ℝ) := by
  have h := Real.rpow_le_rpow (firstFloor_nonneg hx)
    (Int.floor_le (x^(3/2:ℝ))) (by norm_num : (0:ℝ) ≤ 3/2)
  change nestedPower x ≤ (x^(3/2:ℝ))^(3/2:ℝ) at h
  rw [← Real.rpow_mul hx] at h
  convert h using 1; norm_num

/-- An exact one-sided bound, including integer and square boundary hits. -/
theorem actualRoot_error {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ x^(9/8:ℝ)-actualRoot x ∧
      x^(9/8:ℝ)-actualRoot x ≤ 3*x^(-3/8:ℝ) := by
  have hx0 : 0 < x := by linarith
  have hV0 := secondFloor_nonneg hx0.le
  have hV : secondFloor x ≤ nestedPower x := Int.floor_le _
  have hY := nestedPower_le hx0.le
  have hV1 : nestedPower x ≤ secondFloor x+1 := (Int.lt_floor_add_one _).le
  have hW : 0 ≤ actualRoot x := Real.sqrt_nonneg _
  have hW2 : (actualRoot x)^2 = secondFloor x := Real.sq_sqrt hV0
  have hz : 0 < x^(9/8:ℝ) := Real.rpow_pos_of_pos hx0 _
  have hz2 : (x^(9/8:ℝ))^2 = x^(9/4:ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have hgap : 0 ≤ x^(9/8:ℝ)-actualRoot x := by nlinarith
  have hE := (remainder_bounds hx0).1
  have hfrac := (Int.fract_lt_one (x^(3/2:ℝ))).le
  have hpow : 1 ≤ x^(3/4:ℝ) := Real.one_le_rpow hx (by norm_num)
  have hp : x^(3/2:ℝ)*x^(3/4:ℝ) = x^(9/4:ℝ) := by
    rw [← Real.rpow_add hx0]
    norm_num
  have hfloor : firstFloor x*x^(3/4:ℝ)+Int.fract (x^(3/2:ℝ))*x^(3/4:ℝ) = x^(9/4:ℝ) := by
    rw [← add_mul, show firstFloor x+Int.fract (x^(3/2:ℝ)) = x^(3/2:ℝ) from Int.floor_add_fract _]
    exact hp
  have hfracmul := mul_le_mul_of_nonneg_right hfrac (by positivity : 0 ≤ x^(3/4:ℝ))
  have hsq : x^(9/4:ℝ)-secondFloor x ≤ 3*x^(3/4:ℝ) := by
    dsimp [remainder] at hE
    nlinarith
  have hprod : (x^(9/8:ℝ)-actualRoot x)*x^(9/8:ℝ) ≤ 3*x^(3/4:ℝ) := by
    nlinarith [mul_nonneg hgap hW]
  have hi : x^(-3/8:ℝ)*x^(9/8:ℝ) = x^(3/4:ℝ) := by
    rw [← Real.rpow_add hx0]
    norm_num
  refine ⟨hgap, (mul_le_mul_iff_left₀ hz).mp ?_⟩
  calc _ ≤ 3*x^(3/4:ℝ) := hprod
    _ = _ := by rw [← hi]; ring

theorem actualRoot_abs_error {P x : ℝ} (hP : 1 ≤ P) (hx : P ≤ x) :
    |actualRoot x-x^(9/8:ℝ)| ≤ 3*P^(-3/8:ℝ) := by
  have he := actualRoot_error (hP.trans hx)
  rw [abs_sub_comm, abs_of_nonneg he.1]
  exact he.2.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos (by linarith) hx (by norm_num)) (by norm_num))

theorem actual_phase_difference (u v w x : ℝ) :
    actualPhase u v w x-originalPhase u v w x =
      (w/2)*(actualRoot x-x^(9/8:ℝ)) := by
  dsimp [actualPhase, originalPhase]
  ring

theorem actual_phase_comparison {P a u v w L : ℝ} (N : ℕ)
    (hP : 1 ≤ P) (ha : P ≤ a) (_hL : 0 ≤ L)
    (hN : (N:ℝ) ≤ L*P^(7/16:ℝ)) :
    ‖(∑ n ∈ range N, phase (actualPhase u v w (a+2*n))) -
      ∑ n ∈ range N, phase (originalPhase u v w (a+2*n))‖ ≤
      3*Real.pi*|w| *L*P^(1/16:ℝ) := by
  have hP0 : 0 < P := by linarith
  have he (n : ℕ) : ‖phase (actualPhase u v w (a+2*n))-
      phase (originalPhase u v w (a+2*n))‖ ≤ 3*Real.pi*|w| *P^(-3/8:ℝ) := by
    have hr := actualRoot_abs_error hP (show P ≤ a+2*n by linarith [Nat.cast_nonneg (α := ℝ) n])
    apply (phase_sub_le _ _).trans
    rw [actual_phase_difference, abs_mul, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    calc _ ≤ 2*Real.pi*(|w| /2*(3*P^(-3/8:ℝ))) := by gcongr
      _ = _ := by ring
  have hp : P^(7/16:ℝ)*P^(-3/8:ℝ) = P^(1/16:ℝ) := by
    rw [← Real.rpow_add hP0]
    norm_num
  rw [← sum_sub_distrib]
  calc _ ≤ ∑ n ∈ range N, ‖phase (actualPhase u v w (a+2*n))-
      phase (originalPhase u v w (a+2*n))‖ := norm_sum_le _ _
    _ ≤ (N:ℝ)*(3*Real.pi*|w| *P^(-3/8:ℝ)) := by
      simpa using sum_le_sum (fun n (_ : n ∈ range N) => he n)
    _ ≤ (L*P^(7/16:ℝ))*(3*Real.pi*|w| *P^(-3/8:ℝ)) := by gcongr
    _ = _ := by rw [← hp]; ring

/-- The mixed-mode theorem now uses the actual square root in the last guard. -/
theorem finite_actual_mixed_modes (s : Finset (ℤ × ℤ × ℤ)) {L : ℝ} (hL : 0 ≤ L) :
    ∃ B : ℝ, 0 < B ∧ ∃ P0 : ℝ, ∀ P : ℝ, P0 ≤ P → ∀ a : ℝ, ∀ N : ℕ,
      (∀ n < N, P ≤ a+2*n ∧ a+2*n ≤ 2*P) → (N:ℝ) ≤ L*P^(7/16:ℝ) →
      ∀ q ∈ s, q.1 ≠ 0 ∨ q.2.1 ≠ 0 →
      ‖∑ n ∈ range N, phase (actualPhase ((q.2.1:ℝ)/2) q.1 q.2.2 (a+2*n))‖ ≤ B*P^(13/32:ℝ) := by
  obtain ⟨B, hB, P0, hp⟩ := finite_mixed_modes_samples s hL
  let K : ℝ := ∑ q ∈ s, |(q.2.2:ℝ)|
  have hK : 0 ≤ K := sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨B+3*Real.pi*K*L, by positivity, max 1 P0, ?_⟩
  intro P hP a N hpoints hN q hq hmix
  have hP1 : 1 ≤ P := (le_max_left _ _).trans hP
  have hP0 : 0 < P := by linarith
  have hPP : P0 ≤ P := (le_max_right _ _).trans hP
  have hqK : |(q.2.2:ℝ)| ≤ K :=
    single_le_sum (f := fun r : ℤ × ℤ × ℤ => |(r.2.2:ℝ)|) (fun _ _ => abs_nonneg _) hq
  cases N with
  | zero => simp only [sum_range_zero, norm_zero]; positivity
  | succ N =>
    have ha : P ≤ a := by simpa using (hpoints 0 (by omega)).1
    have hc := actual_phase_comparison (u := (q.2.1:ℝ)/2) (v := (q.1:ℝ))
      (w := (q.2.2:ℝ)) (N+1) hP1 ha hL hN
    have hs := hp P hPP a (N+1) hpoints hN q hq hmix
    have hpow := Real.rpow_le_rpow_of_exponent_le hP1 (by norm_num : (1/16:ℝ) ≤ 13/32)
    have hc' : 3*Real.pi*|(q.2.2:ℝ)| *L*P^(1/16:ℝ) ≤
        3*Real.pi*K*L*P^(13/32:ℝ) := by gcongr
    have hn := norm_add_le
      ((∑ n ∈ range (N+1), phase (actualPhase ((q.2.1:ℝ)/2) q.1 q.2.2 (a+2*n)))-
        ∑ n ∈ range (N+1), phase (originalPhase ((q.2.1:ℝ)/2) q.1 q.2.2 (a+2*n)))
      (∑ n ∈ range (N+1), phase (originalPhase ((q.2.1:ℝ)/2) q.1 q.2.2 (a+2*n)))
    rw [sub_add_cancel] at hn
    nlinarith

end Problems.Juggler.OOEERootPhase

import Problems.Juggler.OOEEFibreGeometry

/-! # Actual OOEE fibre counts outside slow resonances

All source-window and candidate-length conditions are supplied by the exact
fibre geometry. The explicit normalized error separates the two fixed cutoffs
from the terms that vanish with the target.
-/

noncomputable section

namespace Problems.Juggler.OOEEFibreParity

open OOEEFibreGeometry BTCalculus.FejerWeighted

theorem base_rpow (m : ℕ) (p : ℝ) : (base m)^p = (m:ℝ)^((16/9)*p) := by
  rw [base, ← Real.rpow_mul (by positivity)]

/-- The remaining source-length division has an explicit vanishing bound. -/
theorem normalized_error_bound {m : ℕ} (hm : 64 ≤ m) {B C : ℝ}
    (hB : 0 ≤ B) (hC : 0 < C) (H : ℕ) :
    (B*(m:ℝ)^(13/18:ℝ)+(2/C)*(m:ℝ)^(7/9:ℝ)+
      9*Real.pi*H*(m:ℝ)^(1/9:ℝ)+1) / candidateCount m ≤
      2*B*(m:ℝ)^(-1/18:ℝ)+4/C+18*Real.pi*H*(m:ℝ)^(-2/3:ℝ)+
        2*(m:ℝ)^(-7/9:ℝ) := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hs : 0 < scale m := Real.rpow_pos_of_pos hm0 _
  have hn : scale m/2 ≤ (candidateCount m:ℝ) := (candidate_count_scale hm).1
  have hdiv := div_le_div_of_nonneg_left
    (show 0 ≤ B*(m:ℝ)^(13/18:ℝ)+(2/C)*(m:ℝ)^(7/9:ℝ)+
      9*Real.pi*H*(m:ℝ)^(1/9:ℝ)+1 by positivity)
    (show 0 < scale m/2 by positivity) hn
  apply hdiv.trans_eq
  have h1 : (m:ℝ)^(13/18:ℝ)/(m:ℝ)^(7/9:ℝ) = (m:ℝ)^(-1/18:ℝ) := by
    rw [← Real.rpow_sub hm0]; norm_num
  have h2 : (m:ℝ)^(1/9:ℝ)/(m:ℝ)^(7/9:ℝ) = (m:ℝ)^(-2/3:ℝ) := by
    rw [← Real.rpow_sub hm0]; norm_num
  have h3 : 1/(m:ℝ)^(7/9:ℝ) = (m:ℝ)^(-7/9:ℝ) := by
    rw [show (-7/9:ℝ) = -(7/9) by norm_num, Real.rpow_neg hm0.le, one_div]
  dsimp [scale]
  rw [show (B*(m:ℝ)^(13/18:ℝ)+(2/C)*(m:ℝ)^(7/9:ℝ)+
        9*Real.pi*H*(m:ℝ)^(1/9:ℝ)+1) / ((m:ℝ)^(7/9:ℝ)/2) =
      2*B*((m:ℝ)^(13/18:ℝ)/(m:ℝ)^(7/9:ℝ))+4/C+
        18*Real.pi*H*((m:ℝ)^(1/9:ℝ)/(m:ℝ)^(7/9:ℝ))+
          2*(1/(m:ℝ)^(7/9:ℝ)) by field_simp; ring]
  rw [h1,h2,h3]

/-- The unnormalized estimate on the exact finite target fibre. -/
theorem nonresonant_fibre_discrepancy (H : ℕ) (hH : 3 ≤ H) :
    ∃ B : ℝ, 0 < B ∧ ∃ M0 : ℕ, 64 ≤ M0 ∧ ∀ m : ℕ, M0 ≤ m → ∀ C : ℝ,
      0 < C → (27/32)*(H:ℝ) ≤ C →
      (∀ k : ℤ, |k| ≤ H → k ≠ 0 → ∀ z : ℤ,
        C*(m:ℝ)^(-7/9:ℝ) ≤ |(k:ℝ)*((9/8)*(m:ℝ)^(2/9:ℝ))-(z:ℝ)|) →
      |((fibre m).card:ℝ)/candidateCount m-1/8| ≤
        15/Real.sqrt ((H:ℝ)+1)+((mass H)^3+6*mass H)*
          ((B*(m:ℝ)^(13/18:ℝ)+(2/C)*(m:ℝ)^(7/9:ℝ)+
            9*Real.pi*H*(m:ℝ)^(1/9:ℝ)+1)/candidateCount m) := by
  obtain ⟨B,hB,P0,hparity⟩ := OOEEParity.nonresonant_guard_discrepancy H hH (D := 3) (by norm_num)
  refine ⟨B,hB,max 64 ⌈P0⌉₊,le_max_left _ _,?_⟩
  intro m hm C hC hdom hnr
  have hm64 : 64 ≤ m := (le_max_left _ _).trans hm
  have hmP : P0 ≤ (m:ℝ) := (Nat.le_ceil P0).trans
    (by exact_mod_cast ((le_max_right 64 ⌈P0⌉₊).trans hm))
  have hS := scale_ge_eight hm64
  have hm0 : (0:ℝ) ≤ m := by positivity
  have hmb : (m:ℝ) ≤ base m := by rw [base_eq_mul_scale]; nlinarith
  have hpoints (j : ℕ) (hj : j < candidateCount m) :
      base m ≤ (firstOdd m:ℝ)+2*j ∧ (firstOdd m:ℝ)+2*j ≤ 2*base m ∧
        (firstOdd m:ℝ)+2*j ≤ base m+3*(base m)^(7/16:ℝ) := by
    have h := source_window hm64 (sample_mem hj)
    simpa only [sample, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, base_rpow,
      show (16/9:ℝ)*(7/16) = 7/9 by norm_num, scale] using h
  have hlen : (candidateCount m:ℝ) ≤ 3*(base m)^(7/16:ℝ) := by
    simpa only [base_rpow, show (16/9:ℝ)*(7/16) = 7/9 by norm_num, scale]
      using (candidate_count_scale hm64).2
  have hnres (k : ℤ) (hk : |k| ≤ H) (hk0 : k ≠ 0) :
      OOEESlowModes.Nonresonant (base m) C k := by
    simpa only [OOEESlowModes.Nonresonant, OOEESlowModes.slowSlope, base_rpow,
      show (16/9:ℝ)*(-7/16) = -7/9 by norm_num,
      show (16/9:ℝ)*(1/8) = 2/9 by norm_num] using hnr k hk hk0
  have ha : firstOdd m % 2 = 1 := by dsimp [firstOdd]; omega
  have h := hparity (base m) (hmP.trans hmb) (firstOdd m) (candidateCount m) C
    ha (candidate_count_pos hm64) hC hpoints hlen (by nlinarith) hnres
  rw [← fibre_card_count] at h
  simp only [base_rpow,
    show (16/9:ℝ)*(13/32) = 13/18 by norm_num,
    show (16/9:ℝ)*(7/16) = 7/9 by norm_num,
    show (16/9:ℝ)*(1/16) = 1/9 by norm_num] at h
  convert h using 1; ring

/-- H is chosen first, C second; all other errors vanish as m grows. -/
theorem normalized_fibre_discrepancy (H : ℕ) (hH : 3 ≤ H) :
    ∃ B : ℝ, 0 < B ∧ ∃ M0 : ℕ, 64 ≤ M0 ∧ ∀ m : ℕ, M0 ≤ m → ∀ C : ℝ,
      0 < C → (27/32)*(H:ℝ) ≤ C →
      (∀ k : ℤ, |k| ≤ H → k ≠ 0 → ∀ z : ℤ,
        C*(m:ℝ)^(-7/9:ℝ) ≤ |(k:ℝ)*((9/8)*(m:ℝ)^(2/9:ℝ))-(z:ℝ)|) →
      |((fibre m).card:ℝ)/candidateCount m-1/8| ≤
        15/Real.sqrt ((H:ℝ)+1)+((mass H)^3+6*mass H)*
          (2*B*(m:ℝ)^(-1/18:ℝ)+4/C+18*Real.pi*H*(m:ℝ)^(-2/3:ℝ)+
            2*(m:ℝ)^(-7/9:ℝ)) := by
  obtain ⟨B,hB,M0,hM0,hcount⟩ := nonresonant_fibre_discrepancy H hH
  refine ⟨B,hB,M0,hM0,?_⟩
  intro m hm C hC hdom hnr
  apply (hcount m hm C hC hdom hnr).trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left (normalized_error_bound (hM0.trans hm) hB.le hC H)
  have hharm : (0:ℝ) ≤ (harmonic H:ℝ) := by
    exact_mod_cast (show (0:ℚ) ≤ harmonic H by unfold harmonic; positivity)
  have hmass : 0 ≤ mass H := by unfold mass; positivity
  positivity

end Problems.Juggler.OOEEFibreParity

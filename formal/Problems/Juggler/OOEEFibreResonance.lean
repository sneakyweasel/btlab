import Problems.Juggler.OOEEFibreParity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # A fixed OOEE count deficit forces a slow resonance -/

noncomputable section

namespace Problems.Juggler.OOEEFibreResonance

open Filter OOEEFibreGeometry BTCalculus.FejerWeighted
open scoped Topology

def alpha (m : ℕ) : ℝ := (9/8)*(m:ℝ)^(2/9:ℝ)
def decay (m : ℕ) : ℝ := (m:ℝ)^(-7/9:ℝ)
def Resonant (H : ℕ) (C : ℝ) (m : ℕ) : Prop :=
  ∃ q : ℕ, 1 ≤ q ∧ q ≤ H ∧ ∃ z : ℤ, |(q:ℝ)*alpha m-(z:ℝ)| ≤ C*decay m
def CountPoor (η : ℝ) (m : ℕ) : Prop :=
  η ≤ |((fibre m).card:ℝ)/candidateCount m-1/8|

theorem signed_resonant {H m : ℕ} {C : ℝ} {k z : ℤ}
    (hk : k ≠ 0) (hH : |k| ≤ (H:ℤ))
    (hz : |(k:ℝ)*alpha m-(z:ℝ)| ≤ C*decay m) : Resonant H C m := by
  have hq1 : 1 ≤ k.natAbs := by omega
  have hqH : k.natAbs ≤ H := by exact_mod_cast (show (k.natAbs:ℤ) ≤ H by simpa using hH)
  refine ⟨k.natAbs,hq1,hqH,?_⟩
  have he : (k.natAbs:ℝ) = |(k:ℝ)| := by
    simpa only [Int.cast_natCast,Int.cast_abs] using
      congrArg (fun n : ℤ => (n:ℝ)) (Int.natCast_natAbs k)
  by_cases hk0 : (0:ℝ) ≤ k
  · exact ⟨z,by simpa only [he,abs_of_nonneg hk0] using hz⟩
  · refine ⟨-z,?_⟩
    rw [he,abs_of_neg (lt_of_not_ge hk0),Int.cast_neg,
      show -(k:ℝ)*alpha m- -(z:ℝ) = -((k:ℝ)*alpha m-(z:ℝ)) by ring,abs_neg]
    exact hz

theorem nonresonant_signed {H m : ℕ} {C : ℝ} (hn : ¬Resonant H C m)
    (k : ℤ) (hk : |k| ≤ H) (hk0 : k ≠ 0) (z : ℤ) :
    C*(m:ℝ)^(-7/9:ℝ) ≤ |(k:ℝ)*((9/8)*(m:ℝ)^(2/9:ℝ))-(z:ℝ)| := by
  by_contra h
  exact hn (signed_resonant hk0 hk (le_of_lt (lt_of_not_ge h)))

theorem negative_power_small {p ε : ℝ} (hp : 0 < p) (hε : 0 < ε) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m → (m:ℝ)^(-p) < ε := by
  have ht : Tendsto (fun m : ℕ => (m:ℝ)^(-p)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hp).comp tendsto_natCast_atTop_atTop
  exact eventually_atTop.mp (ht.eventually (Iio_mem_nhds hε))

theorem smoothing_cutoff {ε : ℝ} (hε : 0 < ε) :
    ∃ H : ℕ, 3 ≤ H ∧ 15/Real.sqrt ((H:ℝ)+1) < ε/4 := by
  obtain ⟨N,hN⟩ := exists_nat_gt ((60/ε)^2)
  refine ⟨max 3 N,le_max_left _ _,?_⟩
  have hn : (N:ℝ) ≤ max 3 N := by exact_mod_cast (le_max_right 3 N)
  have hp : (0:ℝ) < (max 3 N:ℕ)+1 := by positivity
  have hs := Real.sq_sqrt hp.le
  have hs0 := Real.sqrt_nonneg ((max 3 N:ℕ)+1:ℝ)
  have hlarge : 60/ε < Real.sqrt ((max 3 N:ℕ)+1:ℝ) := by
    have h60 : (0:ℝ) < 60/ε := by positivity
    nlinarith
  have hmul := (div_lt_iff₀ hε).mp hlarge
  rw [div_lt_iff₀ (Real.sqrt_pos.mpr hp)]
  nlinarith

/-- Fixed H, then fixed C, then a target threshold: no cutoff depends on m. -/
theorem nonresonant_count_close {ε : ℝ} (hε : 0 < ε) :
    ∃ H : ℕ, 3 ≤ H ∧ ∃ C : ℝ, 0 < C ∧ ∃ M : ℕ, 64 ≤ M ∧
      ∀ m : ℕ, M ≤ m → ¬Resonant H C m →
        |((fibre m).card:ℝ)/candidateCount m-1/8| < ε := by
  obtain ⟨H,hH,hsmooth⟩ := smoothing_cutoff hε
  obtain ⟨B,hB,M0,hM0,hcount⟩ := OOEEFibreParity.normalized_fibre_discrepancy H hH
  let A : ℝ := (mass H)^3+6*mass H
  have hmass : 0 ≤ mass H := by
    have hh : (0:ℝ) ≤ (harmonic H:ℝ) := by
      exact_mod_cast (show (0:ℚ) ≤ harmonic H by unfold harmonic; positivity)
    unfold mass
    positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let C : ℝ := max ((27/32)*H) (16*A/ε+1)
  have hdom : (27/32)*(H:ℝ) ≤ C := le_max_left _ _
  have hClarge : 16*A/ε+1 ≤ C := le_max_right _ _
  have hC : 0 < C := by
    have : 0 ≤ 16*A/ε := by positivity
    linarith
  have hconst : A*(4/C) < ε/4 := by
    have h16 : 16*A < C*ε := (div_lt_iff₀ hε).mp (by linarith : 16*A/ε < C)
    rw [show A*(4/C) = (4*A)/C by ring,div_lt_iff₀ hC]
    nlinarith
  let R : ℝ := 2*B+18*Real.pi*H+2
  have hR : 0 ≤ R := by dsimp [R]; positivity
  obtain ⟨M1,hsmall⟩ := negative_power_small (p := (1/18:ℝ)) (by norm_num)
    (show 0 < ε/(4*(A*R+1)) by positivity)
  refine ⟨H,hH,C,hC,max M0 M1,hM0.trans (le_max_left _ _),?_⟩
  intro m hm hnr
  have hm0 : M0 ≤ m := (le_max_left _ _).trans hm
  have hm1 : M1 ≤ m := (le_max_right _ _).trans hm
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have h2 : (m:ℝ)^(-2/3:ℝ) ≤ (m:ℝ)^(-1/18:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hmR (by norm_num)
  have h7 : (m:ℝ)^(-7/9:ℝ) ≤ (m:ℝ)^(-1/18:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hmR (by norm_num)
  have hrem : 2*B*(m:ℝ)^(-1/18:ℝ)+18*Real.pi*H*(m:ℝ)^(-2/3:ℝ)+
      2*(m:ℝ)^(-7/9:ℝ) ≤ R*(m:ℝ)^(-1/18:ℝ) := by
    have hpi : 0 ≤ 18*Real.pi*(H:ℝ) := by positivity
    have hmul := mul_le_mul_of_nonneg_left h2 hpi
    dsimp [R]
    nlinarith
  have hsmall' := (lt_div_iff₀ (show 0 < 4*(A*R+1) by positivity)).mp (hsmall m hm1)
  have hvanish : A*(R*(m:ℝ)^(-1/18:ℝ)) < ε/4 := by
    have hp : 0 ≤ (m:ℝ)^(-1/18:ℝ) := by positivity
    nlinarith
  have hc := hcount m hm0 C hC hdom (nonresonant_signed hnr)
  have hmul := mul_le_mul_of_nonneg_left hrem hA
  change _ ≤ 15/Real.sqrt ((H:ℝ)+1)+A*_ at hc
  nlinarith

/-- Every fixed absolute count deviation is contained in a fixed resonance family. -/
theorem count_poor_resonant {η : ℝ} (hη : 0 < η) :
    ∃ H : ℕ, 3 ≤ H ∧ ∃ C : ℝ, 0 < C ∧ ∃ M : ℕ, 64 ≤ M ∧
      ∀ m : ℕ, M ≤ m → CountPoor η m → Resonant H C m := by
  obtain ⟨H,hH,C,hC,M,hM,hclose⟩ := nonresonant_count_close hη
  refine ⟨H,hH,C,hC,M,hM,?_⟩
  intro m hm hp
  by_contra hnr
  exact (not_lt_of_ge hp) (hclose m hm hnr)

end Problems.Juggler.OOEEFibreResonance

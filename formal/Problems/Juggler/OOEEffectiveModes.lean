import BTCalculus.HigherDerivative
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # Explicit Fourier modes for the effective OOE return

The phases are the actual powers used by the parity and residue box.
Derivative chains retain the extra right support needed by the finite test.
-/

noncomputable section

namespace Problems.Juggler.OOEEffectiveModes

open Finset BTCalculus.HigherDerivative BTCalculus.WeylDifferencing

def falling (p : ℝ) (k : ℕ) : ℝ := ∏ j ∈ range k, (p-j)

def powerChain (M p : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  (2*M)^k * falling p k * (1+2*M*x)^(p-k)

def modeChain (M u v : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  (u/2)*powerChain M (9/2) k x + (v/(2*M))*powerChain M (9/4) k x

def mode (M u v x : ℝ) : ℝ :=
  (u/2)*(1+2*M*x)^(9/2:ℝ) + (v/(2*M))*(1+2*M*x)^(9/4:ℝ)

theorem modeChain_zero (M u v x : ℝ) : modeChain M u v 0 x = mode M u v x := by
  simp [modeChain, powerChain, falling, mode]

theorem deriv_powerChain {M x : ℝ} (hx : 0 < 1+2*M*x) (p : ℝ) (k : ℕ) :
    HasDerivAt (powerChain M p k) (powerChain M p (k+1) x) x := by
  have ha : HasDerivAt (fun y : ℝ => 1+2*M*y) (2*M) x := by
    simpa using ((hasDerivAt_id x).const_mul (2*M)).const_add 1
  have h := (((Real.hasDerivAt_rpow_const (p := p-k) (Or.inl hx.ne')).comp x ha).const_mul
    ((2*M)^k * falling p k))
  apply h.congr_deriv
  simp only [powerChain, falling, prod_range_succ, Nat.cast_add, Nat.cast_one, pow_succ]
  rw [show p-((k:ℝ)+1) = p-k-1 by ring]
  ring

theorem modeChain_deriv {M x : ℝ} (hx : 0 < 1+2*M*x) (u v : ℝ) (k : ℕ) :
    HasDerivAt (modeChain M u v k) (modeChain M u v (k+1) x) x := by
  exact ((deriv_powerChain hx (9/2) k).const_mul (u/2)).fun_add
    ((deriv_powerChain hx (9/4) k).const_mul (v/(2*M)))

theorem modeChain_five {M : ℝ} (hM : M ≠ 0) (u v x : ℝ) :
    modeChain M u v 5 x = (945/2:ℝ)*u*M^5*(1+2*M*x)^(-1/2:ℝ) +
      (945/64:ℝ)*v*M^4*(1+2*M*x)^(-11/4:ℝ) := by
  norm_num [modeChain, powerChain, falling, prod_range_succ]
  field_simp
  ring

theorem modeChain_three_axis {M : ℝ} (hM : M ≠ 0) (v x : ℝ) :
    modeChain M 0 v 3 x = (45/16:ℝ)*v*M^2*(1+2*M*x)^(-3/4:ℝ) := by
  norm_num [modeChain, powerChain, falling, prod_range_succ]
  field_simp
  ring

theorem modeChain_neg (M u v : ℝ) (k : ℕ) (x : ℝ) :
    modeChain M (-u) (-v) k x = -modeChain M u v k x := by
  unfold modeChain
  ring

/-- The support includes the final increment beyond the last sampled integer. -/
theorem support_scale {M P x : ℝ} (hM : 1 ≤ M) (hP : 6 ≤ P)
    (hx : x ∈ Set.Icc P (2*P+1)) :
    2*M*P ≤ 1+2*M*x ∧ 1+2*M*x ≤ 5*M*P := by
  have hMP : M ≤ M*P := by nlinarith
  constructor
  · nlinarith [mul_nonneg (by linarith : 0 ≤ M) (sub_nonneg.mpr hx.1)]
  · have h := mul_le_mul_of_nonneg_left hx.2 (by linarith : 0 ≤ 2*M)
    nlinarith

theorem modeChain_support {M P : ℝ} (hM : 1 ≤ M) (hP : 6 ≤ P)
    (u v : ℝ) (r : ℕ) : Chain (modeChain M u v) r P (2*P+1) := by
  intro j _ x hx
  apply modeChain_deriv
  have h := (support_scale hM hP hx).1
  nlinarith

theorem scale_product {M P : ℝ} (hM : 0 < M) (hP : 0 < P) (k : ℕ) (p : ℝ) :
    M^k*(M*P)^p = M^((k:ℝ)+p)*P^p := by
  rw [Real.mul_rpow hM.le hP.le, Real.rpow_add hM, Real.rpow_natCast]
  ring

theorem inverse_half_scale {s Q : ℝ} (hQ : 0 < Q) (hs : Q ≤ s) (hcap : s ≤ 5*Q) :
    (1/3:ℝ)*Q^(-1/2:ℝ) ≤ s^(-1/2:ℝ) ∧ s^(-1/2:ℝ) ≤ Q^(-1/2:ℝ) := by
  have h3 : (1/3:ℝ) = (9:ℝ)^(-1/2:ℝ) := by
    rw [show (9:ℝ) = 3^(2:ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  constructor
  · rw [h3, ← Real.mul_rpow (by norm_num) hQ.le]
    exact Real.rpow_le_rpow_of_nonpos (hQ.trans_le hs) (by linarith) (by norm_num)
  · exact Real.rpow_le_rpow_of_nonpos hQ hs (by norm_num)

theorem inverse_three_quarters_scale {s Q : ℝ} (hQ : 0 < Q)
    (hs : 2*Q ≤ s) (hcap : s ≤ 5*Q) :
    (1/5:ℝ)*Q^(-3/4:ℝ) ≤ s^(-3/4:ℝ) ∧
      s^(-3/4:ℝ) ≤ (2/3:ℝ)*Q^(-3/4:ℝ) := by
  have h5 : (1/5:ℝ) ≤ (5:ℝ)^(-3/4:ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 5)
      (by norm_num : (-1:ℝ) ≤ -3/4)
    norm_num at h ⊢
    exact h
  have h2 : (2:ℝ)^(-3/4:ℝ) ≤ 2/3 := by
    apply (Real.rpow_le_rpow_iff (by positivity) (by norm_num) (by norm_num : (0:ℝ)<4)).mp
    rw [← Real.rpow_mul (by norm_num)]
    norm_num
  constructor
  · calc (1/5:ℝ)*Q^(-3/4:ℝ) ≤ (5:ℝ)^(-3/4:ℝ)*Q^(-3/4:ℝ) := by gcongr
         _ = (5*Q)^(-3/4:ℝ) := (Real.mul_rpow (by norm_num) hQ.le).symm
         _ ≤ s^(-3/4:ℝ) := Real.rpow_le_rpow_of_nonpos (by linarith) hcap (by norm_num)
  · calc s^(-3/4:ℝ) ≤ (2*Q)^(-3/4:ℝ) :=
           Real.rpow_le_rpow_of_nonpos (by positivity) hs (by norm_num)
         _ = (2:ℝ)^(-3/4:ℝ)*Q^(-3/4:ℝ) := Real.mul_rpow (by norm_num) hQ.le
         _ ≤ (2/3:ℝ)*Q^(-3/4:ℝ) := by gcongr

def highScale (M P u : ℝ) : ℝ := u*M^(9/2:ℝ)*P^(-1/2:ℝ)
def lowScale (M P v : ℝ) : ℝ := v*M^(5/4:ℝ)*P^(-3/4:ℝ)

/-- Lower-power interference cannot reverse the fifth derivative. -/
theorem fifth_derivative_positive {M P H u v x : ℝ}
    (hM : 1 ≤ M) (hP : 6 ≤ P) (hHP : H ≤ P) (hu : 1 ≤ u) (hv : |v| ≤ H)
    (hx : x ∈ Set.Icc P (2*P+1)) :
    100*highScale M P u ≤ modeChain M u v 5 x ∧
      modeChain M u v 5 x ≤ 600*highScale M P u := by
  have hM0 : 0 < M := by linarith
  have hP0 : 0 < P := by linarith
  let s := 1+2*M*x
  obtain ⟨hslo, hshi⟩ := support_scale hM hP hx
  change 2*M*P ≤ s at hslo
  change s ≤ 5*M*P at hshi
  have hsP : P ≤ s := by nlinarith
  have hs1 : 1 ≤ s := by linarith
  have hs0 : 0 < s := by linarith
  obtain ⟨hl, hh⟩ := inverse_half_scale (mul_pos hM0 hP0)
    (show M*P ≤ s by nlinarith) (by nlinarith : s ≤ 5*(M*P))
  have hmain : highScale M P u / 3 ≤ u*M^5*s^(-1/2:ℝ) ∧
      u*M^5*s^(-1/2:ℝ) ≤ highScale M P u := by
    have he : u*M^5*(M*P)^(-1/2:ℝ) = highScale M P u := by
      rw [mul_assoc, scale_product hM0 hP0]
      norm_num [highScale]
      ring
    constructor
    · have h := mul_le_mul_of_nonneg_left hl (show 0 ≤ u*M^5 by positivity)
      rw [show u*M^5*((1/3:ℝ)*(M*P)^(-1/2:ℝ)) =
        (u*M^5*(M*P)^(-1/2:ℝ))/3 by ring, he] at h
      exact h
    · simpa only [he] using mul_le_mul_of_nonneg_left hh (show 0 ≤ u*M^5 by positivity)
  have hvpow : |v|*s^(-11/4:ℝ) ≤ s^(-1/2:ℝ) := by
    calc |v|*s^(-11/4:ℝ) ≤ s*s^(-11/4:ℝ) := by gcongr; exact hv.trans (hHP.trans hsP)
         _ = s^(-7/4:ℝ) := by rw [← Real.rpow_one s, ← Real.rpow_add hs0]; norm_num
         _ ≤ s^(-1/2:ℝ) := Real.rpow_le_rpow_of_exponent_le hs1 (by norm_num)
  have hMpow : M^4 ≤ u*M^5 := by
    have h1 : M^4 ≤ M^5 := by
      calc M^4 = M^4*1 := by ring
           _ ≤ M^4*M := by gcongr
           _ = M^5 := by ring
    exact h1.trans (le_mul_of_one_le_left (by positivity) hu)
  have herr : |(945/64:ℝ)*v*M^4*s^(-11/4:ℝ)| ≤
      (945/64:ℝ)*(u*M^5*s^(-1/2:ℝ)) := by
    calc |(945/64:ℝ)*v*M^4*s^(-11/4:ℝ)| =
          (945/64:ℝ)*M^4*(|v|*s^(-11/4:ℝ)) := by
            simp only [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 945/64),
              abs_of_nonneg (by positivity : 0 ≤ M^4),
              abs_of_pos (Real.rpow_pos_of_pos hs0 _)]
            ring
         _ ≤ (945/64:ℝ)*M^4*s^(-1/2:ℝ) := by gcongr
         _ ≤ (945/64:ℝ)*(u*M^5*s^(-1/2:ℝ)) := by
           have h := mul_le_mul_of_nonneg_right hMpow
             (show 0 ≤ (945/64:ℝ)*s^(-1/2:ℝ) by positivity)
           nlinarith
  rw [modeChain_five hM0.ne']
  change 100*highScale M P u ≤ (945/2:ℝ)*u*M^5*s^(-1/2:ℝ) +
    (945/64:ℝ)*v*M^4*s^(-11/4:ℝ) ∧
    (945/2:ℝ)*u*M^5*s^(-1/2:ℝ) + (945/64:ℝ)*v*M^4*s^(-11/4:ℝ) ≤ 600*highScale M P u
  have hscl : 0 ≤ highScale M P u := by unfold highScale; positivity
  have he := abs_le.mp herr
  constructor <;> nlinarith [hmain.1, hmain.2, he.1, he.2]

theorem third_derivative_positive {M P v x : ℝ}
    (hM : 1 ≤ M) (hP : 6 ≤ P) (hv : 0 ≤ v)
    (hx : x ∈ Set.Icc P (2*P+1)) :
    (1/2:ℝ)*lowScale M P v ≤ modeChain M 0 v 3 x ∧
      modeChain M 0 v 3 x ≤ 2*lowScale M P v := by
  have hM0 : 0 < M := by linarith
  have hP0 : 0 < P := by linarith
  obtain ⟨hl, hh⟩ := support_scale hM hP hx
  obtain ⟨hp, hq⟩ := inverse_three_quarters_scale (mul_pos hM0 hP0)
    (by nlinarith : 2*(M*P) ≤ 1+2*M*x) (by nlinarith : 1+2*M*x ≤ 5*(M*P))
  have he : v*M^2*(M*P)^(-3/4:ℝ) = lowScale M P v := by
    rw [mul_assoc, scale_product hM0 hP0]
    norm_num [lowScale]
    ring
  have hlo := mul_le_mul_of_nonneg_left hp (show 0 ≤ v*M^2 by positivity)
  have hhi := mul_le_mul_of_nonneg_left hq (show 0 ≤ v*M^2 by positivity)
  rw [show v*M^2*((1/5:ℝ)*(M*P)^(-3/4:ℝ)) =
    (v*M^2*(M*P)^(-3/4:ℝ))/5 by ring, he] at hlo
  rw [show v*M^2*((2/3:ℝ)*(M*P)^(-3/4:ℝ)) =
    (2/3:ℝ)*(v*M^2*(M*P)^(-3/4:ℝ)) by ring, he] at hhi
  have hscl : 0 ≤ lowScale M P v := by unfold lowScale; positivity
  rw [modeChain_three_axis hM0.ne']
  constructor <;> nlinarith

theorem fifth_derivative_signed {M P H u v : ℝ}
    (hM : 1 ≤ M) (hP : 6 ≤ P) (hHP : H ≤ P) (hu : 1 ≤ |u|) (hv : |v| ≤ H) :
    (∀ x ∈ Set.Icc P (2*P+1), 100*highScale M P |u| ≤ modeChain M u v 5 x ∧
      modeChain M u v 5 x ≤ 6*(100*highScale M P |u|)) ∨
    (∀ x ∈ Set.Icc P (2*P+1), -6*(100*highScale M P |u|) ≤ modeChain M u v 5 x ∧
      modeChain M u v 5 x ≤ -(100*highScale M P |u|)) := by
  by_cases hu0 : 0 ≤ u
  · left
    rw [abs_of_nonneg hu0] at hu ⊢
    intro x hx
    simpa only [show (6:ℝ)*100 = 600 by norm_num, ← mul_assoc] using
      fifth_derivative_positive hM hP hHP hu hv hx
  · right
    rw [abs_of_neg (not_le.mp hu0)] at hu ⊢
    intro x hx
    have h := fifth_derivative_positive hM hP hHP hu (by simpa using hv : |-v| ≤ H) hx
    rw [modeChain_neg] at h
    constructor <;> nlinarith [h.1, h.2]

theorem third_derivative_signed {M P v : ℝ} (hM : 1 ≤ M) (hP : 6 ≤ P) :
    (∀ x ∈ Set.Icc P (2*P+1), (1/2:ℝ)*lowScale M P |v| ≤ modeChain M 0 v 3 x ∧
      modeChain M 0 v 3 x ≤ 4*((1/2:ℝ)*lowScale M P |v|)) ∨
    (∀ x ∈ Set.Icc P (2*P+1), -4*((1/2:ℝ)*lowScale M P |v|) ≤ modeChain M 0 v 3 x ∧
      modeChain M 0 v 3 x ≤ -((1/2:ℝ)*lowScale M P |v|)) := by
  by_cases hv0 : 0 ≤ v
  · left
    rw [abs_of_nonneg hv0]
    intro x hx
    have h := third_derivative_positive hM hP hv0 hx
    constructor <;> nlinarith [h.1, h.2]
  · right
    rw [abs_of_neg (not_le.mp hv0)]
    intro x hx
    have h := third_derivative_positive hM hP (show 0 ≤ -v by linarith) hx
    have he : modeChain M 0 (-v) 3 x = -modeChain M 0 v 3 x := by
      simpa using modeChain_neg M 0 v 3 x
    rw [he] at h
    constructor <;> nlinarith [h.1, h.2]

end Problems.Juggler.OOEEffectiveModes

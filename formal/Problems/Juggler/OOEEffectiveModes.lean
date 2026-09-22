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
  have hvpow : |v| * s^(-11/4:ℝ) ≤ s^(-1/2:ℝ) := by
    calc |v| * s^(-11/4:ℝ) ≤ s*s^(-11/4:ℝ) := by gcongr; exact hv.trans (hHP.trans hsP)
         _ = s^(-7/4:ℝ) := by
           convert (Real.rpow_add hs0 1 (-11/4)).symm using 1 <;> norm_num
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
          (945/64:ℝ)*M^4*(|v| * s^(-11/4:ℝ)) := by
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

def frequencyScale (M H P : ℝ) : ℝ := H^(1/30:ℝ)*M^(1/4:ℝ)*P^(-1/60:ℝ)

theorem power_le_frequencyScale {M H P p : ℝ} (hM : 1 ≤ M) (hH : 1 ≤ H)
    (hP : 1 ≤ P) (hp : p ≤ -1/60) : P^p ≤ frequencyScale M H P := by
  have h1 : 1 ≤ H^(1/30:ℝ) := Real.one_le_rpow hH (by norm_num)
  have h2 : 1 ≤ M^(1/4:ℝ) := Real.one_le_rpow hM (by norm_num)
  have h3 := Real.rpow_le_rpow_of_exponent_le hP hp
  have hw : 1 ≤ H^(1/30:ℝ)*M^(1/4:ℝ) := by nlinarith
  exact h3.trans (le_mul_of_one_le_left (by positivity) hw)

theorem low_power_le_frequencyScale {M H P : ℝ} (hM : 1 ≤ M) (hH : 1 ≤ H)
    (hP : 1 ≤ P) (hHP : H^2 ≤ P) :
    H^(1/6:ℝ)*M^(5/24:ℝ)*P^(-1/8:ℝ) ≤ frequencyScale M H P := by
  have hH0 : 0 < H := by linarith
  have hP0 : 0 < P := by linarith
  have hr := Real.rpow_le_rpow (by positivity : 0 ≤ H^2) hHP (by norm_num : (0:ℝ) ≤ 1/15)
  rw [← Real.rpow_natCast H 2, ← Real.rpow_mul hH0.le] at hr
  norm_num at hr
  have hMpow := Real.rpow_le_rpow_of_exponent_le hM (by norm_num : (5/24:ℝ) ≤ 1/4)
  have hPpow := Real.rpow_le_rpow_of_exponent_le hP (by norm_num : (-7/120:ℝ) ≤ -1/60)
  have he : H^(1/6:ℝ) = H^(1/30:ℝ)*H^(2/15:ℝ) := by
    rw [← Real.rpow_add hH0]; norm_num
  rw [he]
  calc H^(1/30:ℝ)*H^(2/15:ℝ)*M^(5/24:ℝ)*P^(-1/8:ℝ) ≤
        H^(1/30:ℝ)*P^(1/15:ℝ)*M^(1/4:ℝ)*P^(-1/8:ℝ) := by gcongr
       _ = H^(1/30:ℝ)*M^(1/4:ℝ)*P^(-7/120:ℝ) := by
         rw [show H^(1/30:ℝ)*P^(1/15:ℝ)*M^(1/4:ℝ)*P^(-1/8:ℝ) =
           H^(1/30:ℝ)*M^(1/4:ℝ)*(P^(1/15:ℝ)*P^(-1/8:ℝ)) by ring,
           ← Real.rpow_add hP0]
         norm_num
       _ ≤ frequencyScale M H P := by unfold frequencyScale; gcongr

theorem high_leading_rate {M H P u : ℝ} (hM : 1 ≤ M) (hH : 1 ≤ H)
    (hP : 1 ≤ P) (hu : 1 ≤ u) (huH : u ≤ H) :
    (100*highScale M P u)^(1/30:ℝ) ≤ 2*frequencyScale M H P := by
  have hM0 : 0 < M := by linarith
  have hP0 : 0 < P := by linarith
  have hu0 : 0 < u := by linarith
  have h100 : (100:ℝ)^(1/30:ℝ) ≤ 2 := by
    apply (Real.rpow_le_rpow_iff (by positivity) (by norm_num) (by norm_num : (0:ℝ)<30)).mp
    rw [← Real.rpow_mul (by norm_num)]
    norm_num
  have huH' := Real.rpow_le_rpow hu0.le huH (by norm_num : (0:ℝ) ≤ 1/30)
  have hM' := Real.rpow_le_rpow_of_exponent_le hM (by norm_num : (3/20:ℝ) ≤ 1/4)
  unfold highScale frequencyScale
  rw [Real.mul_rpow (by norm_num) (by positivity),
    Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow hu0.le (by positivity),
    ← Real.rpow_mul hM0.le, ← Real.rpow_mul hP0.le]
  norm_num
  gcongr

theorem low_leading_rate {M H P v : ℝ} (hM : 1 ≤ M) (hH : 1 ≤ H)
    (hP : 1 ≤ P) (hv : 1 ≤ v) (hvH : v ≤ H) (hHP : H^2 ≤ P) :
    ((1/2:ℝ)*lowScale M P v)^(1/6:ℝ) ≤ frequencyScale M H P := by
  have hM0 : 0 < M := by linarith
  have hP0 : 0 < P := by linarith
  have hv0 : 0 < v := by linarith
  have hhalf : (1/2:ℝ)^(1/6:ℝ) ≤ 1 := Real.rpow_le_one (by norm_num) (by norm_num) (by norm_num)
  have hvH' := Real.rpow_le_rpow hv0.le hvH (by norm_num : (0:ℝ) ≤ 1/6)
  unfold lowScale
  rw [Real.mul_rpow (by norm_num) (by positivity),
    Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow hv0.le (by positivity),
    ← Real.rpow_mul hM0.le, ← Real.rpow_mul hP0.le]
  norm_num
  have hb := low_power_le_frequencyScale hM hH hP hHP
  apply le_trans _ hb
  calc (1/2:ℝ)^(1/6:ℝ)*(v^(1/6:ℝ)*M^(5/24:ℝ)*P^(-(1/8:ℝ))) ≤
         1*(H^(1/6:ℝ)*M^(5/24:ℝ)*P^(-(1/8:ℝ))) := by gcongr
       _ = _ := by simp only [one_mul, neg_div]

theorem sqrt_tail_lower {N P lam c b : ℝ} (hP : 0 < P) (hc : 0 ≤ c)
    (hN : P/2 ≤ N) (hlam : c^2*P^(2*b) ≤ lam) :
    (c/2)*P^(1+b) ≤ N*Real.sqrt lam := by
  have he : (c*P^b)^2 = c^2*P^(2*b) := by
    rw [mul_pow, ← Real.rpow_natCast (P^b) 2, ← Real.rpow_mul hP.le]
    congr 2
    ring
  rw [← he] at hlam
  have hroot := Real.sqrt_le_sqrt hlam
  rw [Real.sqrt_sq (by positivity)] at hroot
  have hN0 : 0 ≤ N := by linarith
  calc (c/2)*P^(1+b) = (P/2)*(c*P^b) := by rw [Real.rpow_add hP, Real.rpow_one]; ring
       _ ≤ N*Real.sqrt lam := by gcongr

theorem inverse_scaled_power {x P c b a : ℝ} (hP : 0 < P) (hc : 0 < c)
    (ha : 0 ≤ a) (hx : c*P^b ≤ x) :
    x^(-a) ≤ c^(-a)*P^(-a*b) := by
  calc x^(-a) ≤ (c*P^b)^(-a) :=
         Real.rpow_le_rpow_of_nonpos (by positivity) hx (by linarith)
       _ = c^(-a)*P^(-a*b) := by
         rw [Real.mul_rpow hc.le (by positivity), ← Real.rpow_mul hP.le]
         congr 2
         ring

theorem quarter_inverse_half : (1/4:ℝ)^(-1/2:ℝ) = 2 := by
  rw [show (1/4:ℝ) = (1/2:ℝ)^(2:ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
  norm_num

theorem twelfth_inverse_eighth : (1/12:ℝ)^(-1/8:ℝ) ≤ 2 := by
  apply (Real.rpow_le_rpow_iff (by positivity) (by norm_num) (by norm_num : (0:ℝ)<8)).mp
  rw [← Real.rpow_mul (by norm_num)]
  norm_num

theorem high_rate_terms {M H P u N : ℝ} (hM : 1 ≤ M) (hH : 1 ≤ H)
    (hP : 1 ≤ P) (hu : 1 ≤ u) (hN : P/2 ≤ N) :
    (N/6)^(-1/8:ℝ) ≤ 2*frequencyScale M H P ∧
      (N*Real.sqrt (100*highScale M P u))^(-1/8:ℝ) ≤ 2*frequencyScale M H P := by
  have hP0 : 0 < P := by linarith
  have hp1 := power_le_frequencyScale hM hH hP (by norm_num : (-1/8:ℝ) ≤ -1/60)
  have hp2 := power_le_frequencyScale hM hH hP (by norm_num : (-3/32:ℝ) ≤ -1/60)
  have hlo : (2:ℝ)^2*P^(2*(-1/4:ℝ)) ≤ 100*highScale M P u := by
    have hMp := Real.one_le_rpow hM (by norm_num : (0:ℝ) ≤ 9/2)
    have huM : 1 ≤ u*M^(9/2:ℝ) := by nlinarith
    norm_num
    unfold highScale
    nlinarith [Real.rpow_pos_of_pos hP0 (-1/2)]
  have ht := sqrt_tail_lower hP0 (by norm_num : (0:ℝ) ≤ 2) hN hlo
  norm_num only at ht
  have hterm := inverse_scaled_power hP0 (by norm_num : (0:ℝ)<1/12)
    (by norm_num : (0:ℝ) ≤ 1/8) (show (1/12:ℝ)*P^1 ≤ N/6 by rw [Real.rpow_one]; linarith)
  norm_num only at hterm
  have htail := inverse_scaled_power hP0 (by norm_num : (0:ℝ)<1)
    (by norm_num : (0:ℝ) ≤ 1/8) (show 1*P^(3/4:ℝ) ≤ N*Real.sqrt (100*highScale M P u) by simpa using ht)
  norm_num only at htail
  have h12 := twelfth_inverse_eighth
  norm_num only at h12 hp1 hp2 ⊢
  constructor
  · exact hterm.trans (mul_le_mul h12 hp1 (by positivity) (by norm_num))
  · have hg : 0 ≤ frequencyScale M H P := by unfold frequencyScale; positivity
    linarith

theorem low_rate_terms {M H P v N : ℝ} (hM : 1 ≤ M) (hH : 1 ≤ H)
    (hP : 1 ≤ P) (hv : 1 ≤ v) (hN : P/2 ≤ N) :
    (N/2)^(-1/2:ℝ) ≤ 2*frequencyScale M H P ∧
      (N*Real.sqrt ((1/2:ℝ)*lowScale M P v))^(-1/2:ℝ) ≤ 2*frequencyScale M H P := by
  have hP0 : 0 < P := by linarith
  have hp1 := power_le_frequencyScale hM hH hP (by norm_num : (-1/2:ℝ) ≤ -1/60)
  have hp2 := power_le_frequencyScale hM hH hP (by norm_num : (-5/16:ℝ) ≤ -1/60)
  have hlo : (1/2:ℝ)^2*P^(2*(-3/8:ℝ)) ≤ (1/2:ℝ)*lowScale M P v := by
    have hMp := Real.one_le_rpow hM (by norm_num : (0:ℝ) ≤ 5/4)
    have hvM : 1 ≤ v*M^(5/4:ℝ) := by nlinarith
    norm_num
    unfold lowScale
    nlinarith [Real.rpow_pos_of_pos hP0 (-3/4)]
  have ht := sqrt_tail_lower hP0 (by norm_num : (0:ℝ) ≤ 1/2) hN hlo
  norm_num only at ht
  have hterm := inverse_scaled_power hP0 (by norm_num : (0:ℝ)<1/4)
    (by norm_num : (0:ℝ) ≤ 1/2) (show (1/4:ℝ)*P^1 ≤ N/2 by rw [Real.rpow_one]; linarith)
  have htail := inverse_scaled_power hP0 (by norm_num : (0:ℝ)<1/4)
    (by norm_num : (0:ℝ) ≤ 1/2) (show (1/4:ℝ)*P^(5/8:ℝ) ≤ N*Real.sqrt ((1/2:ℝ)*lowScale M P v) by simpa using ht)
  norm_num at hterm htail hp1 hp2 ⊢
  constructor <;> linarith

/-- The number of sampled integers is comparable to the real dyadic length. -/
theorem dyadic_count_bounds {P : ℝ} (hP : 6 ≤ P) :
    0 < integerCount P (2*P) ∧ P/2 ≤ (integerCount P (2*P) : ℝ) ∧
      (integerCount P (2*P) : ℝ) ≤ (7/6:ℝ)*P := by
  have hf : ⌊P⌋ ≤ ⌊2*P⌋ := Int.floor_mono (by linarith)
  have he : ((integerCount P (2*P) : ℕ) : ℤ) = ⌊2*P⌋-⌊P⌋ :=
    Int.toNat_of_nonneg (sub_nonneg.mpr hf)
  have heR : (integerCount P (2*P) : ℝ) = (⌊2*P⌋:ℝ)-(⌊P⌋:ℝ) := by exact_mod_cast he
  have hlow : P-1 < (integerCount P (2*P) : ℝ) := by
    rw [heR]
    linarith [Int.lt_floor_add_one (2*P), Int.floor_le P]
  have hhigh : (integerCount P (2*P) : ℝ) ≤ P+1 := by
    rw [heR]
    linarith [Int.floor_le (2*P), Int.lt_floor_add_one P]
  refine ⟨?_, by linarith, by linarith⟩
  exact_mod_cast (show (0:ℝ) < integerCount P (2*P) by linarith)

theorem dyadic_high_mode {M H P u v : ℝ} (hM : 1 ≤ M) (hH : 1 ≤ H)
    (hP : 6 ≤ P) (hHP : H^2 ≤ P) (hu : 1 ≤ |u|) (huH : |u| ≤ H) (hvH : |v| ≤ H) :
    ‖∑ n ∈ Finset.Ioc ⌊P⌋ ⌊2*P⌋, phase (mode M u v (n:ℝ))‖ ≤
      32*P*frequencyScale M H P := by
  have hM0 : 0 < M := by linarith
  have hP0 : 0 < P := by linarith
  have hHP' : H ≤ P := by nlinarith
  have hg : 0 ≤ frequencyScale M H P := by unfold frequencyScale; positivity
  obtain ⟨hN, hlo, hhi⟩ := dyadic_count_bounds hP
  have hlam : 0 < 100*highScale M P |u| := by unfold highScale; positivity
  have hf := modeChain_support hM hP u v 5
  have htop := fifth_derivative_signed hM hP hHP' hu hvH
  have hb := fifth_derivative_rate (modeChain M u v) (integerStart P) hN hlam
    (fun j hj x hx => hf j hj x (integer_support (by linarith : P ≤ 2*P) hx))
    (htop.imp (fun h x hx => h x (integer_support (by linarith : P ≤ 2*P) hx))
      (fun h x hx => h x (integer_support (by linarith : P ≤ 2*P) hx)))
  have hlead := high_leading_rate hM hH (by linarith : 1 ≤ P) hu huH
  have hterms := high_rate_terms hM hH (by linarith : 1 ≤ P) hu hlo
  have hm := max_le hlead (max_le hterms.1 hterms.2)
  rw [integer_sum_eq_range]
  simp only [modeChain_zero] at hb
  calc ‖∑ n ∈ range (integerCount P (2*P)), phase (mode M u v (integerStart P+n))‖ ≤
         7*integerCount P (2*P) * max ((100*highScale M P |u|)^(1/30:ℝ))
           (max (((integerCount P (2*P):ℝ)/6)^(-1/8:ℝ))
             (((integerCount P (2*P):ℝ)*Real.sqrt (100*highScale M P |u|))^(-1/8:ℝ))) := by
               simpa only [neg_div] using hb
       _ ≤ 7*integerCount P (2*P)*(2*frequencyScale M H P) := by gcongr
       _ ≤ 32*P*frequencyScale M H P := by
         nlinarith [mul_le_mul_of_nonneg_right hhi hg]

theorem dyadic_low_mode {M H P v : ℝ} (hM : 1 ≤ M) (hH : 1 ≤ H)
    (hP : 6 ≤ P) (hHP : H^2 ≤ P) (hv : 1 ≤ |v|) (hvH : |v| ≤ H) :
    ‖∑ n ∈ Finset.Ioc ⌊P⌋ ⌊2*P⌋, phase (mode M 0 v (n:ℝ))‖ ≤
      32*P*frequencyScale M H P := by
  have hM0 : 0 < M := by linarith
  have hP0 : 0 < P := by linarith
  have hg : 0 ≤ frequencyScale M H P := by unfold frequencyScale; positivity
  obtain ⟨hN, hlo, hhi⟩ := dyadic_count_bounds hP
  have hlam : 0 < (1/2:ℝ)*lowScale M P |v| := by unfold lowScale; positivity
  have hf := modeChain_support hM hP 0 v 3
  have htop := third_derivative_signed (v := v) hM hP
  have hb := third_derivative_rate (modeChain M 0 v) (integerStart P) hN hlam
    (fun j hj x hx => hf j hj x (integer_support (by linarith : P ≤ 2*P) hx))
    (htop.imp (fun h x hx => h x (integer_support (by linarith : P ≤ 2*P) hx))
      (fun h x hx => h x (integer_support (by linarith : P ≤ 2*P) hx)))
  have hlead := low_leading_rate hM hH (by linarith : 1 ≤ P) hv hvH hHP
  have hterms := low_rate_terms hM hH (by linarith : 1 ≤ P) hv hlo
  have hm : max (((1/2:ℝ)*lowScale M P |v|)^(1/6:ℝ))
      (max (((integerCount P (2*P):ℝ)/2)^(-1/2:ℝ))
        (((integerCount P (2*P):ℝ)*Real.sqrt ((1/2:ℝ)*lowScale M P |v|))^(-1/2:ℝ))) ≤
      2*frequencyScale M H P := max_le (by linarith) (max_le hterms.1 hterms.2)
  rw [integer_sum_eq_range]
  simp only [modeChain_zero] at hb
  calc ‖∑ n ∈ range (integerCount P (2*P)), phase (mode M 0 v (integerStart P+n))‖ ≤
         12*integerCount P (2*P) * max (((1/2:ℝ)*lowScale M P |v|)^(1/6:ℝ))
           (max (((integerCount P (2*P):ℝ)/2)^(-1/2:ℝ))
             (((integerCount P (2*P):ℝ)*Real.sqrt ((1/2:ℝ)*lowScale M P |v|))^(-1/2:ℝ))) := by
               simpa only [neg_div] using hb
       _ ≤ 12*integerCount P (2*P)*(2*frequencyScale M H P) := by gcongr
       _ ≤ 32*P*frequencyScale M H P := by
         nlinarith [mul_le_mul_of_nonneg_right hhi hg]

/-- Every nonzero integer Fourier mode, on real dyadic intervals, with the explicit constant 32. -/
theorem dyadic_mode_bound {M H P : ℝ} (u v : ℤ) (hM : 1 ≤ M) (hH : 1 ≤ H)
    (hP : 6 ≤ P) (hHP : H^2 ≤ P) (huH : |(u:ℝ)| ≤ H) (hvH : |(v:ℝ)| ≤ H)
    (hne : u ≠ 0 ∨ v ≠ 0) :
    ‖∑ n ∈ Finset.Ioc ⌊P⌋ ⌊2*P⌋, phase (mode M u v (n:ℝ))‖ ≤
      32*P*frequencyScale M H P := by
  by_cases hu : u = 0
  · subst u
    have hv : v ≠ 0 := hne.resolve_left (by simp)
    have hv1 : (1:ℤ) ≤ |v| := by have h := abs_pos.mpr hv; omega
    have hv' : (1:ℝ) ≤ |(v:ℝ)| := by exact_mod_cast hv1
    simpa only [Int.cast_zero] using dyadic_low_mode hM hH hP hHP hv' hvH
  · have hu1 : (1:ℤ) ≤ |u| := by have h := abs_pos.mpr hu; omega
    have hu' : (1:ℝ) ≤ |(u:ℝ)| := by exact_mod_cast hu1
    exact dyadic_high_mode hM hH hP hHP hu' huH hvH

def amplitude (M H : ℝ) : ℝ := H^(1/30:ℝ)*M^(1/4:ℝ)

theorem dyadic_mode_power {M H P : ℝ} (u v : ℤ) (hM : 1 ≤ M) (hH : 1 ≤ H)
    (hP : 6 ≤ P) (hHP : H^2 ≤ P) (huH : |(u:ℝ)| ≤ H) (hvH : |(v:ℝ)| ≤ H)
    (hne : u ≠ 0 ∨ v ≠ 0) :
    ‖∑ n ∈ Finset.Ioc ⌊P⌋ ⌊2*P⌋, phase (mode M u v (n:ℝ))‖ ≤
      32*amplitude M H*P^(59/60:ℝ) := by
  have h := dyadic_mode_bound u v hM hH hP hHP huH hvH hne
  have hp : P*P^(-1/60:ℝ) = P^(59/60:ℝ) := by
    convert (Real.rpow_add (by linarith : 0 < P) 1 (-1/60)).symm using 1 <;> norm_num
  apply h.trans_eq
  unfold frequencyScale amplitude
  rw [show 32*P*(H^(1/30:ℝ)*M^(1/4:ℝ)*P^(-1/60:ℝ)) =
    32*(H^(1/30:ℝ)*M^(1/4:ℝ))*(P*P^(-1/60:ℝ)) by ring, hp]

def positiveSum (M : ℝ) (u v : ℤ) (T : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioc (0:ℤ) (T:ℤ), phase (mode M u v (n:ℝ))

theorem positiveSum_trivial (M : ℝ) (u v : ℤ) (T : ℕ) :
    ‖positiveSum M u v T‖ ≤ T := by
  unfold positiveSum
  calc ‖∑ n ∈ Finset.Ioc (0:ℤ) (T:ℤ), phase (mode M u v (n:ℝ))‖ ≤
         ∑ n ∈ Finset.Ioc (0:ℤ) (T:ℤ), ‖phase (mode M u v (n:ℝ))‖ := norm_sum_le _ _
       _ = T := by simp [phase_norm, Int.card_Ioc]

theorem dyadic_power_margin : (3/2:ℝ) ≤ (2:ℝ)^(59/60:ℝ) := by
  have h : (3/2:ℝ) ≤ (2:ℝ)^(3/4:ℝ) := by
    apply (Real.rpow_le_rpow_iff (by norm_num) (by positivity) (by norm_num : (0:ℝ)<4)).mp
    rw [← Real.rpow_mul (by norm_num)]
    norm_num
  exact h.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num))

/-- Finite strong induction performs the dyadic decomposition, retaining its initial segment. -/
theorem positiveSum_bound {M H : ℝ} (u v : ℤ) (hM : 1 ≤ M) (hH : 1 ≤ H)
    (huH : |(u:ℝ)| ≤ H) (hvH : |(v:ℝ)| ≤ H) (hne : u ≠ 0 ∨ v ≠ 0) (T : ℕ) :
    ‖positiveSum M u v T‖ ≤ 64*amplitude M H*(T:ℝ)^(59/60:ℝ)+14*H^2 := by
  have hA : 0 ≤ amplitude M H := by unfold amplitude; positivity
  induction T using Nat.strong_induction_on with
  | h T ih =>
    by_cases hlarge : max (H^2) 6 ≤ (T:ℝ)/2
    · let P : ℝ := (T:ℝ)/2
      have hP : 6 ≤ P := (le_max_right _ _).trans hlarge
      have hHP : H^2 ≤ P := (le_max_left _ _).trans hlarge
      have hP0 : 0 < P := by linarith
      let K : ℕ := ⌊P⌋₊
      have hK : (K:ℝ) ≤ P := Nat.floor_le hP0.le
      have hKlt : K < T := by
        have he : (K:ℝ) < T := by dsimp [P] at hP hK; linarith
        exact_mod_cast he
      have hKint : (K:ℤ) = ⌊P⌋ := Int.natCast_floor_eq_floor hP0.le
      have hPT : 2*P = (T:ℝ) := by dsimp [P]; ring
      have hKT : (K:ℤ) ≤ T := by exact_mod_cast hKlt.le
      have hsplit : positiveSum M u v T = positiveSum M u v K +
          ∑ n ∈ Finset.Ioc ⌊P⌋ ⌊2*P⌋, phase (mode M u v (n:ℝ)) := by
        rw [hPT, Int.floor_natCast, ← hKint]
        unfold positiveSum
        rw [← Finset.Ioc_union_Ioc_eq_Ioc (show (0:ℤ) ≤ K by omega) hKT,
          sum_union (Finset.Ioc_disjoint_Ioc_of_le le_rfl)]
      have hi := ih K hKlt
      have hd := dyadic_mode_power u v hM hH hP hHP huH hvH hne
      have hkpow := Real.rpow_le_rpow (Nat.cast_nonneg K) hK (by norm_num : (0:ℝ) ≤ 59/60)
      have hgeo : (3/2:ℝ)*P^(59/60:ℝ) ≤ (T:ℝ)^(59/60:ℝ) := by
        calc (3/2:ℝ)*P^(59/60:ℝ) ≤ (2:ℝ)^(59/60:ℝ)*P^(59/60:ℝ) := by
               gcongr; exact dyadic_power_margin
             _ = (T:ℝ)^(59/60:ℝ) := by rw [← Real.mul_rpow (by norm_num) hP0.le, hPT]
      rw [hsplit]
      have hn := norm_add_le (positiveSum M u v K)
        (∑ n ∈ Finset.Ioc ⌊P⌋ ⌊2*P⌋, phase (mode M u v (n:ℝ)))
      nlinarith [mul_le_mul_of_nonneg_left hkpow hA, mul_le_mul_of_nonneg_left hgeo hA]
    · have hsmall : (T:ℝ) ≤ 14*H^2 := by
        have ht : (T:ℝ)/2 < max (H^2) 6 := not_le.mp hlarge
        have hH2 : 1 ≤ H^2 := by nlinarith
        rcases le_total (H^2) 6 with hh | hh
        · rw [max_eq_right hh] at ht
          linarith
        · rw [max_eq_left hh] at ht
          nlinarith
      exact (positiveSum_trivial M u v T).trans
        (hsmall.trans (le_add_of_nonneg_left (by positivity)))

theorem range_endpoint_bound (M : ℝ) (u v : ℤ) (T : ℕ) :
    ‖∑ n ∈ range T, phase (mode M u v (n:ℝ))‖ ≤ ‖positiveSum M u v T‖+2 := by
  have hs := integer_sum_eq_range (mode M u v) 0 (T:ℝ)
  simp only [Int.floor_zero, Int.floor_natCast] at hs
  have hc : integerCount 0 (T:ℝ) = T := by simp [integerCount]
  rw [hc] at hs
  have hpos : positiveSum M u v T = ∑ n ∈ range T, phase (mode M u v ((n+1:ℕ):ℝ)) := by
    simpa [positiveSum, integerStart, add_comm] using hs
  have he : (∑ n ∈ range T, phase (mode M u v (n:ℝ))) = positiveSum M u v T +
      phase (mode M u v 0) - phase (mode M u v T) := by
    have h := Finset.sum_range_succ' (fun n : ℕ => phase (mode M u v (n:ℝ))) T
    rw [sum_range_succ, ← hpos] at h
    simp only [Nat.cast_zero] at h
    exact eq_sub_iff_add_eq.mpr h
  rw [he]
  calc ‖positiveSum M u v T + phase (mode M u v 0) - phase (mode M u v T)‖ ≤
         ‖positiveSum M u v T + phase (mode M u v 0)‖ + ‖phase (mode M u v T)‖ := norm_sub_le _ _
       _ ≤ ‖positiveSum M u v T‖+2 := by
         have h := norm_add_le (positiveSum M u v T) (phase (mode M u v 0))
         simp only [phase_norm] at h ⊢
         linarith

/-- The all-length bound includes the small initial segment and the two endpoint terms. -/
theorem initial_mode_bound {M H : ℝ} (u v : ℤ) (hM : 1 ≤ M) (hH : 1 ≤ H)
    (huH : |(u:ℝ)| ≤ H) (hvH : |(v:ℝ)| ≤ H) (hne : u ≠ 0 ∨ v ≠ 0)
    (T : ℕ) (hT : 1 ≤ T) (hHT : H ≤ (T:ℝ)^(1/4:ℝ)) :
    ‖∑ n ∈ range T, phase (mode M u v (n:ℝ))‖ ≤
      128*amplitude M H*(T:ℝ)^(59/60:ℝ) := by
  have hT1 : (1:ℝ) ≤ T := by exact_mod_cast hT
  have hT0 : (0:ℝ) < T := by linarith
  have hH0 : 0 ≤ H := by linarith
  have hH2 : 1 ≤ H^2 := by nlinarith
  have hA1 : 1 ≤ amplitude M H :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hH (by norm_num))
      (Real.one_le_rpow hM (by norm_num))
  have hA : 0 ≤ amplitude M H := by linarith
  have hh := pow_le_pow_left₀ hH0 hHT 2
  rw [← Real.rpow_natCast ((T:ℝ)^(1/4:ℝ)) 2, ← Real.rpow_mul hT0.le] at hh
  norm_num only at hh
  have hp := Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num : (1/2:ℝ) ≤ 59/60)
  have hb := positiveSum_bound u v hM hH huH hvH hne T
  have he := range_endpoint_bound M u v T
  have hc : H^2 ≤ amplitude M H*(T:ℝ)^(59/60:ℝ) :=
    hh.trans (hp.trans (le_mul_of_one_le_left (by positivity) hA1))
  nlinarith [Real.rpow_pos_of_pos hT0 (59/60)]

/-- The precise uniform cutoff-mode input of the effective OOE counting theorem. -/
theorem normalized_mode_bound {M H : ℝ} (u v : ℤ) (hM : 1 ≤ M) (hH : 1 ≤ H)
    (huH : |(u:ℝ)| ≤ H) (hvH : |(v:ℝ)| ≤ H) (hne : u ≠ 0 ∨ v ≠ 0)
    (T : ℕ) (hT : 1 ≤ T) (hHT : H ≤ (T:ℝ)^(1/4:ℝ)) :
    ‖∑ n ∈ range T, phase (mode M u v (n:ℝ))‖/(T:ℝ) ≤
      128*M^(1/4:ℝ)*H^(1/30:ℝ)*(T:ℝ)^(-1/60:ℝ) := by
  have hT0 : (0:ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hp : (T:ℝ)^(59/60:ℝ)/(T:ℝ) = (T:ℝ)^(-1/60:ℝ) := by
    convert (Real.rpow_sub hT0 (59/60) 1).symm using 1 <;> norm_num
  calc ‖∑ n ∈ range T, phase (mode M u v (n:ℝ))‖/(T:ℝ) ≤
         (128*amplitude M H*(T:ℝ)^(59/60:ℝ))/(T:ℝ) :=
           div_le_div_of_nonneg_right (initial_mode_bound u v hM hH huH hvH hne T hT hHT) hT0.le
       _ = 128*M^(1/4:ℝ)*H^(1/30:ℝ)*(T:ℝ)^(-1/60:ℝ) := by
         rw [show (128*amplitude M H*(T:ℝ)^(59/60:ℝ))/(T:ℝ) =
           128*amplitude M H*((T:ℝ)^(59/60:ℝ)/(T:ℝ)) by ring, hp]
         unfold amplitude
         ring

end Problems.Juggler.OOEEffectiveModes

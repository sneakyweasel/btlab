import Problems.Juggler.CubicReturnHeight
import Problems.Juggler.CubicReturn
import Mathlib.Tactic

namespace Problems.Juggler.ReturnGapHeight

/-- A strict affine estimate gives a loss of two on positive even gaps. -/
theorem even_gap_drop {a b : ℕ} {k e : ℝ}
    (ha : 0 < a) (hao : a % 2 = 0) (hbo : b % 2 = 0)
    (hk : k ≤ 1) (he : 2*k+e < 2)
    (hstep : (b : ℝ) < k*a+e) : b+2 ≤ a := by
  have ha2 : 2 ≤ a := by omega
  have ha2r : (2 : ℝ) ≤ a := by exact_mod_cast ha2
  have hlt : (b : ℝ) < a := NumericBridge.affine_gap_lt ha2r hk he.le hstep
  have hltN : b < a := by exact_mod_cast hlt
  omega

/-- Every strict step between even natural gaps consumes at least two. -/
theorem even_transfers_sum (d : ℕ → ℕ) (n : ℕ)
    (heven : ∀ i ≤ n, d i % 2 = 0)
    (hstep : ∀ i < n, d (i + 1) < d i) :
    d n + 2 * n ≤ d 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hn := ih (fun i hi => heven i (by omega))
        (fun i hi => hstep i (by omega))
      have ha := heven n (by omega)
      have hb := heven (n + 1) (by omega)
      have hs := hstep n (by omega)
      omega

/-- A positive final gap gives the usual finite transfer lower bound. -/
theorem even_transfers_positive (d : ℕ → ℕ) (n : ℕ)
    (heven : ∀ i ≤ n, d i % 2 = 0)
    (hstep : ∀ i < n, d (i + 1) < d i)
    (hpositive : 0 < d n) :
    2 * (n + 1) ≤ d 0 := by
  have h := even_transfers_sum d n heven hstep
  have hn := heven n (by omega)
  omega

theorem two_even_transfers {d0 d1 d2 : ℕ}
    (h0 : d0 % 2 = 0) (h1 : d1 % 2 = 0) (h2 : d2 % 2 = 0)
    (hp : 0 < d2) (hs1 : d1 < d0) (hs2 : d2 < d1) : 6 ≤ d0 := by
  let d : ℕ → ℕ := fun i => if i = 0 then d0 else if i = 1 then d1 else d2
  have he : ∀ i ≤ 2, d i % 2 = 0 := by
    intro i hi
    interval_cases i <;> simp_all [d]
  have hs : ∀ i < 2, d (i + 1) < d i := by
    intro i hi
    interval_cases i <;> simp_all [d]
  simpa [d] using even_transfers_positive d 2 he hs (by simpa [d] using hp)

theorem three_even_transfers {d0 d1 d2 d3 : ℕ}
    (h0 : d0 % 2 = 0) (h1 : d1 % 2 = 0)
    (h2 : d2 % 2 = 0) (h3 : d3 % 2 = 0)
    (hp : 0 < d3) (hs1 : d1 < d0) (hs2 : d2 < d1) (hs3 : d3 < d2) :
    8 ≤ d0 := by
  let d : ℕ → ℕ := fun i => if i = 0 then d0 else if i = 1 then d1 else if i = 2 then d2 else d3
  have he : ∀ i ≤ 3, d i % 2 = 0 := by
    intro i hi
    interval_cases i <;> simp_all [d]
  have hs : ∀ i < 3, d (i + 1) < d i := by
    intro i hi
    interval_cases i <;> simp_all [d]
  simpa [d] using even_transfers_positive d 3 he hs (by simpa [d] using hp)

/-- The two-step affine estimate retains the exact positive numerator. -/
theorem two_affine_gap {k d0 d1 d2 : ℝ}
    (hk0 : 0 < k) (hk : k ≤ 27/64)
    (hd2 : 2 ≤ d2) (h1 : d1 < k*d0+9/8) (h2 : d2 < k*d1+9/8) :
    (205/512 : ℝ) < k^2*d0 := by
  have hm := mul_lt_mul_of_pos_left h1 hk0
  nlinarith

/-- A scale identity converts the affine numerator into the DC power coefficient. -/
theorem two_affine_scaled_gap {k x d0 d1 d2 : ℝ}
    (hk0 : 0 < k) (hk : k ≤ 27/64) (hx : 0 < x)
    (hscale : k^2*x = (243/256 : ℝ)^2)
    (hd2 : 2 ≤ d2) (h1 : d1 < k*d0+9/8) (h2 : d2 < k*d1+9/8) :
    (26240/59049 : ℝ)*x < d0 := by
  have hnum := two_affine_gap hk0 hk hd2 h1 h2
  have hm := mul_lt_mul_of_pos_right hnum hx
  have hpos : 0 < k^2 := sq_pos_of_pos hk0
  have he : (k^2*d0)*x = (243/256 : ℝ)^2*d0 := by nlinarith [hscale]
  nlinarith

theorem three_affine_gap {k l d0 d1 d2 d3 : ℝ}
    (hk0 : 0 < k) (hl0 : 0 < l) (hk : k ≤ 1/64) (hl : l ≤ 3/8)
    (hd3 : 2 ≤ d3) (h1 : d1 < k*d0+9/8) (h2 : d2 < k*d1+9/8)
    (h3 : d3 < l*d2+6/5) : (7609/20480 : ℝ) < l*k^2*d0 := by
  have h12 : d2 < k^2*d0+(9/8)*(1+k) := by
    have hh := mul_lt_mul_of_pos_left h1 hk0
    nlinarith
  have h23 := mul_lt_mul_of_pos_left h12 hl0
  have hbound : l*(1+k) ≤ (3/8 : ℝ)*(1+1/64) := by
    apply mul_le_mul hl (by linarith) (by linarith) (by norm_num)
  nlinarith

theorem three_affine_scaled_gap {k l rho x d0 d1 d2 d3 : ℝ}
    (hk0 : 0 < k) (hl0 : 0 < l) (hk : k ≤ 1/64) (hl : l ≤ 3/8)
    (hrho : rho < 1) (hx : 0 < x)
    (hscale : l*k^2*x = rho*(243/256 : ℝ)^2)
    (hd3 : 2 ≤ d3) (h1 : d1 < k*d0+9/8) (h2 : d2 < k*d1+9/8)
    (h3 : d3 < l*d2+6/5) : (2/5 : ℝ)*x < d0 := by
  have hnum := three_affine_gap hk0 hl0 hk hl hd3 h1 h2 h3
  have hp : 0 < l*k^2 := mul_pos hl0 (sq_pos_of_pos hk0)
  have hd0 : 0 < d0 := by nlinarith
  have hm := mul_lt_mul_of_pos_right hnum hx
  have he : (l*k^2*d0)*x = rho*(243/256 : ℝ)^2*d0 := by nlinarith [hscale]
  have hb := mul_lt_mul_of_pos_right hrho (by positivity : 0 < (243/256 : ℝ)^2*d0)
  nlinarith

/-- Polynomial transport of a positive seam gap through the extremal cells. -/
theorem height_core {r H t w z M : ℝ}
    (hr : 0 ≤ r) (hH : 0 ≤ H) (ht0 : 0 ≤ t) (hw : 0 ≤ w+1)
    (hz : z ≤ r^3) (hgap : H ≤ z-w-1)
    (ht : t^3 < (w+1)^4) (hM : M+2 ≤ (t+1)^2)
    (hR8 : 8 ≤ r*H) (hRa : r*H ≤ r^4/4) :
    M < r^8-(3/2)*r^5*H := by
  have hwr : w+1 ≤ r^3-H := by linarith
  have hRH : 0 ≤ r^3-H := hw.trans hwr
  have htop0 : 0 ≤ r^4-r*H := by nlinarith [mul_nonneg hr hRH]
  have hpow := pow_le_pow_left₀ hw hwr 4
  have hid : (r^4-r*H)^3-(r^3-H)^4 = H*(r^3-H)^3 := by ring
  have hcell : (w+1)^4 ≤ (r^4-r*H)^3 := by
    nlinarith only [hpow,hid,mul_nonneg hH (pow_nonneg hRH 3)]
  have htr : t < r^4-r*H :=
    lt_of_pow_lt_pow_left₀ 3 htop0 (ht.trans_le hcell)
  have hsq : (t+1)^2 < (r^4-r*H+1)^2 :=
    pow_lt_pow_left₀ (by linarith) (by linarith) (by norm_num : (2:ℕ) ≠ 0)
  have hR0 : 0 ≤ r*H := mul_nonneg hr hH
  have hR2 : (r*H)^2 ≤ r^4*(r*H)/4 := by nlinarith [mul_nonneg hR0 (sub_nonneg.mpr hRa)]
  have h2a : 2*r^4 ≤ r^4*(r*H)/4 := by
    nlinarith [mul_nonneg (pow_nonneg hr 4) (sub_nonneg.mpr hR8)]
  nlinarith [show r^4*(r*H)=r^5*H by ring]


/-- A power-sized odd seam gap gives a strict strip below the cubic boundary. -/
theorem height_of_power_gap {m t w z M : ℕ} {sigma : ℝ}
    (hm : 2^24 ≤ m) (hs0 : 0 ≤ sigma) (hs : sigma ≤ 1/8)
    (hz : z^8 ≤ m^9) (ht : t^3+2 ≤ (w*(w+2))^2)
    (hM : M+2 ≤ (t+1)^2)
    (hgap : (1/3 : ℝ)*(m : ℝ)^sigma ≤ (z : ℝ)-w-1) :
    (M : ℝ) < (m : ℝ)^3-(1/2 : ℝ)*(m : ℝ)^(15/8+sigma) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  have hmp : 0 < (m : ℝ) := by linarith
  let r : ℝ := (m : ℝ)^(3/8 : ℝ)
  let H : ℝ := (1/3 : ℝ)*(m : ℝ)^sigma
  have hr : 0 ≤ r := Real.rpow_nonneg hm0 _
  have hr8 : r^8 = (m : ℝ)^3 := by
    dsimp [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm0]
    norm_num
  have hr64 : 64 ≤ r := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) hr
    rw [hr8]
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2^24)
      (show (2^24 : ℝ) ≤ m by exact_mod_cast hm) 3
    norm_num at hh ⊢
    linarith
  have hHlo : (1/3 : ℝ) ≤ H := by
    have hh := Real.rpow_le_rpow_of_exponent_le hm1 hs0
    simp only [Real.rpow_zero] at hh
    dsimp [H]
    linarith
  have hHhi : H ≤ r/3 := by
    have hh := Real.rpow_le_rpow_of_exponent_le hm1
      (show sigma ≤ (3/8 : ℝ) by linarith)
    dsimp [H, r]
    linarith
  have hR8 : 8 ≤ r*H := by
    have hh := mul_le_mul_of_nonneg_left hHlo hr
    nlinarith
  have hRa : r*H ≤ r^4/4 := by
    have hh := mul_le_mul_of_nonneg_left hHhi hr
    have hr2 : 4 ≤ r^2 := by nlinarith
    have hp := mul_nonneg (sq_nonneg r) (show 0 ≤ r^2-4/3 by linarith)
    nlinarith
  have hzr : (z : ℝ) ≤ r^3 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (pow_nonneg hr _)
    have hh : (r^3)^8 = (m : ℝ)^9 := by
      calc (r^3)^8 = (r^8)^3 := by ring
           _ = (m : ℝ)^9 := by rw [hr8]; ring
    rw [hh]
    exact_mod_cast hz
  have htr : (t : ℝ)^3 < ((w : ℝ)+1)^4 := by
    have hh : (t : ℝ)^3+2 ≤ ((w : ℝ)*(w+2))^2 := by exact_mod_cast ht
    nlinarith [sq_nonneg ((w : ℝ)+1)]
  have hMr : (M : ℝ)+2 ≤ ((t : ℝ)+1)^2 := by exact_mod_cast hM
  have hcore := height_core hr (by linarith : 0 ≤ H) (Nat.cast_nonneg t)
    (by positivity : 0 ≤ (w : ℝ)+1) hzr hgap htr hMr hR8 hRa
  have hprod : r^5*H = (1/3 : ℝ)*(m : ℝ)^(15/8+sigma) := by
    dsimp [r, H]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm0]
    norm_num
    rw [Real.rpow_add hmp]
    ring
  rw [hr8] at hcore
  nlinarith only [hcore, hprod]

/-- The coarse DC coefficient still dominates the one-third seam constant. -/
theorem dc_seam_gap {d : ℕ} {x : ℝ} (hd : 6 ≤ d) (_hx : 0 < x)
    (hquant : (26240/59049 : ℝ)*x < d) :
    (1/3 : ℝ)*x < (d : ℝ)-1 := by
  have hdR : (6 : ℝ) ≤ d := by exact_mod_cast hd
  nlinarith

/-- The LR coefficient and the even-gap minimum give the same seam constant. -/
theorem lr_seam_gap {d : ℕ} {x : ℝ} (hd : 8 ≤ d) (_hx : 0 < x)
    (hquant : (2/5 : ℝ)*x < d) :
    (1/3 : ℝ)*x < (d : ℝ)-1 := by
  have hdR : (8 : ℝ) ≤ d := by exact_mod_cast hd
  nlinarith


/-- Exact normalization of the C slope against its growing reciprocal scale. -/
theorem c_slope_scale {m : ℝ} (hm : 0 < m) :
    ((243/256 : ℝ)*m^(-13/256 : ℝ))^2*m^(13/128 : ℝ) = (243/256 : ℝ)^2 := by
  rw [mul_pow, ← Real.rpow_natCast (m^(-13/256 : ℝ)) 2, ← Real.rpow_mul hm.le]
  rw [mul_assoc, ← Real.rpow_add hm]
  norm_num

/-- Exact normalization for the third, W, gap transfer. -/
theorem cw_slope_scale {m rho : ℝ} (hm : 0 < m) :
    (rho*m^(rho-1))*((243/256 : ℝ)*m^(-13/256 : ℝ))^2 *
      m^(13/128+1-rho) = rho*(243/256 : ℝ)^2 := by
  rw [mul_pow, ← Real.rpow_natCast (m^(-13/256 : ℝ)) 2, ← Real.rpow_mul hm.le]
  calc
    _ = (rho*(243/256 : ℝ)^2) *
        ((m^(rho-1)*m^((-13/256 : ℝ)*2))*m^(13/128+1-rho)) := by ac_rfl
    _ = _ := by rw [← Real.rpow_add hm, ← Real.rpow_add hm]; ring_nf; simp

/-- Clear a rational height exponent without losing the strict inequality. -/
theorem power_strip_of_real_strip {m M a b : ℕ} (hm : 0 < m) (hb : 0 < b)
    (h : (M : ℝ) < (m : ℝ)^3-(1/2 : ℝ)*(m : ℝ)^((a : ℝ)/b)) :
    m^a < (2*(m^3-M))^b :=
  NumericBridge.power_strip_of_real_strip hm hb (by decide : 0 < 2) h

theorem dc_height_of_gap {m t w z M d : ℕ}
    (hm : 2^24 ≤ m) (hz : z^8 ≤ m^9) (ht : t^3+2 ≤ (w*(w+2))^2)
    (hM : M+2 ≤ (t+1)^2) (hwz : w ≤ z) (hd : d = z-w)
    (hmin : 6 ≤ d) (hquant : (26240/59049 : ℝ)*(m : ℝ)^(13/128 : ℝ) < d) :
    (M : ℝ) < (m : ℝ)^3-(1/2 : ℝ)*(m : ℝ)^(253/128 : ℝ) ∧
      m^253 < (2*(m^3-M))^128 := by
  have hm0 : 0 < m := by omega
  have hgap := dc_seam_gap hmin (Real.rpow_pos_of_pos (by exact_mod_cast hm0) _) hquant
  have hcast : (d : ℝ) = (z : ℝ)-w := by rw [hd, Nat.cast_sub hwz]
  rw [hcast] at hgap
  have hh := height_of_power_gap hm (by norm_num : (0 : ℝ) ≤ 13/128)
    (by norm_num : (13/128 : ℝ) ≤ 1/8) hz ht hM hgap.le
  norm_num at hh
  exact ⟨hh, power_strip_of_real_strip hm0 (by norm_num : 0 < (128 : ℕ)) hh⟩

/-- The exact exponent left after the W transfer lies in the required interval. -/
theorem lr_sigma_bounds :
    (7/64 : ℝ) < 13/128+1-(3:ℝ)^41/2^65 ∧
    (13/128+1-(3:ℝ)^41/2^65) ≤ 1/8 := by norm_num

/-- The LR gap yields both its exact exponent and the clean 127/64 strip. -/
theorem lr_height_of_gap {m t w z M d : ℕ}
    (hm : 2^24 ≤ m) (hz : z^8 ≤ m^9) (ht : t^3+2 ≤ (w*(w+2))^2)
    (hM : M+2 ≤ (t+1)^2) (hwz : w ≤ z) (hd : d = z-w)
    (hmin : 8 ≤ d)
    (hquant : (2/5 : ℝ)*(m : ℝ)^(13/128+1-(3:ℝ)^41/2^65) < d) :
    (M : ℝ) < (m : ℝ)^3-(1/2 : ℝ)*(m : ℝ)^(381/128-(3:ℝ)^41/2^65) ∧
    (M : ℝ) < (m : ℝ)^3-(1/2 : ℝ)*(m : ℝ)^(127/64 : ℝ) ∧
      m^127 < (2*(m^3-M))^64 := by
  have hm0 : 0 < m := by omega
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hgap := lr_seam_gap hmin (Real.rpow_pos_of_pos (by exact_mod_cast hm0) _) hquant
  have hcast : (d : ℝ) = (z : ℝ)-w := by rw [hd, Nat.cast_sub hwz]
  rw [hcast] at hgap
  have hh := height_of_power_gap hm (by linarith [lr_sigma_bounds.1])
    lr_sigma_bounds.2 hz ht hM hgap.le
  have he : (15/8 : ℝ)+(13/128+1-(3:ℝ)^41/2^65) = 381/128-(3:ℝ)^41/2^65 := by ring
  rw [he] at hh
  have hpow := Real.rpow_le_rpow_of_exponent_le hm1
    (show (127/64 : ℝ) ≤ 381/128-(3:ℝ)^41/2^65 by linarith [lr_sigma_bounds.1])
  have hclean : (M : ℝ) < (m : ℝ)^3-(1/2 : ℝ)*(m : ℝ)^(127/64 : ℝ) := by linarith
  exact ⟨hh,hclean,power_strip_of_real_strip hm0 (by norm_num : 0 < (64 : ℕ)) hclean⟩


/-- A genuine pair of C transfers gives both the integer and power gap bounds. -/
theorem dc_two_transfer_bounds {m d0 d1 d2 : ℕ}
    (hm : 0 < m) (h0p : 0 < d0) (h1p : 0 < d1) (h2p : 0 < d2)
    (h0 : d0 % 2 = 0) (h1 : d1 % 2 = 0) (h2 : d2 % 2 = 0)
    (hk : (243/256 : ℝ)*(m : ℝ)^(-13/256 : ℝ) ≤ 27/64)
    (ht1 : (d1 : ℝ) < (243/256 : ℝ)*(m : ℝ)^(-13/256 : ℝ)*d0+9/8)
    (ht2 : (d2 : ℝ) < (243/256 : ℝ)*(m : ℝ)^(-13/256 : ℝ)*d1+9/8) :
    6 ≤ d0 ∧ (26240/59049 : ℝ)*(m : ℝ)^(13/128 : ℝ) < d0 := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hkp : 0 < (243/256 : ℝ)*(m : ℝ)^(-13/256 : ℝ) := by positivity
  have hs1 := even_gap_drop h0p h0 h1 (by linarith :
    (243/256 : ℝ)*(m : ℝ)^(-13/256 : ℝ) ≤ 1) (by linarith) ht1
  have hs2 := even_gap_drop h1p h1 h2 (by linarith :
    (243/256 : ℝ)*(m : ℝ)^(-13/256 : ℝ) ≤ 1) (by linarith) ht2
  have hd2 : (2 : ℝ) ≤ d2 := by exact_mod_cast (show 2 ≤ d2 by omega)
  exact ⟨two_even_transfers h0 h1 h2 h2p (by omega) (by omega),
    two_affine_scaled_gap hkp hk (Real.rpow_pos_of_pos hmR _)
      (c_slope_scale hmR) hd2 ht1 ht2⟩

/-- Two C transfers followed by W give the exact LR gap exponent. -/
theorem lr_three_transfer_bounds {m d0 d1 d2 d3 : ℕ}
    (hm : 0 < m) (h0p : 0 < d0) (h1p : 0 < d1) (h2p : 0 < d2) (h3p : 0 < d3)
    (h0 : d0 % 2 = 0) (h1 : d1 % 2 = 0) (h2 : d2 % 2 = 0) (h3 : d3 % 2 = 0)
    (hk : (243/256 : ℝ)*(m : ℝ)^(-13/256 : ℝ) ≤ 1/64)
    (hl : ((3:ℝ)^41/2^65)*(m : ℝ)^((3:ℝ)^41/2^65-1) ≤ 3/8)
    (ht1 : (d1 : ℝ) < (243/256 : ℝ)*(m : ℝ)^(-13/256 : ℝ)*d0+9/8)
    (ht2 : (d2 : ℝ) < (243/256 : ℝ)*(m : ℝ)^(-13/256 : ℝ)*d1+9/8)
    (ht3 : (d3 : ℝ) < ((3:ℝ)^41/2^65)*(m : ℝ)^((3:ℝ)^41/2^65-1)*d2+6/5) :
    8 ≤ d0 ∧ (2/5 : ℝ)*(m : ℝ)^(13/128+1-(3:ℝ)^41/2^65) < d0 := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hkp : 0 < (243/256 : ℝ)*(m : ℝ)^(-13/256 : ℝ) := by positivity
  have hlp : 0 < ((3:ℝ)^41/2^65)*(m : ℝ)^((3:ℝ)^41/2^65-1) := by positivity
  have hs1 := even_gap_drop h0p h0 h1 (by linarith :
    (243/256 : ℝ)*(m : ℝ)^(-13/256 : ℝ) ≤ 1) (by linarith) ht1
  have hs2 := even_gap_drop h1p h1 h2 (by linarith :
    (243/256 : ℝ)*(m : ℝ)^(-13/256 : ℝ) ≤ 1) (by linarith) ht2
  have hs3 := even_gap_drop h2p h2 h3 (by linarith :
    ((3:ℝ)^41/2^65)*(m : ℝ)^((3:ℝ)^41/2^65-1) ≤ 1) (by linarith) ht3
  have hd3 : (2 : ℝ) ≤ d3 := by exact_mod_cast (show 2 ≤ d3 by omega)
  exact ⟨three_even_transfers h0 h1 h2 h3 h3p (by omega) (by omega) (by omega),
    three_affine_scaled_gap hkp hlp hk hl (by norm_num : (3:ℝ)^41/2^65 < 1)
      (Real.rpow_pos_of_pos hmR _) (cw_slope_scale hmR) hd3 ht1 ht2 ht3⟩


/-- Actual cubic cycles give the original, unweakened pair of parity cells. -/
theorem periodic_extrema_cells {C : Set ℕ} {m M : ℕ}
    (D : CubicReturn.PeriodicExtrema C m M) (hm : 5 ≤ m) (hM : M < m^3) :
    (ReturnCells.ooe m)^8 ≤ m^9 ∧
    (M.sqrt)^3+2 ≤ (ReturnCells.oe M.sqrt*(ReturnCells.oe M.sqrt+2))^2 ∧
    M+2 ≤ (M.sqrt+1)^2 ∧ ReturnCells.oe M.sqrt+2 ≤ ReturnCells.ooe m := by
  obtain ⟨htodd,hpeven,hwodd,_,hgap⟩ := CubicReturn.return_endpoint_gap D hm hM
  let t := M.sqrt
  let p := CubicReturn.O t
  let w := ReturnCells.oe t
  change t % 2 = 1 at htodd
  change p % 2 = 0 at hpeven
  change w % 2 = 1 at hwodd
  have hp : p < (w+1)^2 := by
    simpa [w,ReturnCells.oe,p,CubicReturn.O,pow_two] using Nat.lt_succ_sqrt p
  have hpm : (w+1)^2 % 2 = 0 := by simp [Nat.pow_mod,Nat.add_mod,hwodd]
  have hp2 : p+2 ≤ (w+1)^2 := by omega
  have hpend : p+1 ≤ w*(w+2) := by nlinarith
  have htcell : t^3 < (p+1)^2 := CubicReturn.lt_O_succ_sq t
  have htm : t^3 % 2 = 1 := by simp [Nat.pow_mod,htodd]
  have hpm1 : (p+1)^2 % 2 = 1 := by simp [Nat.pow_mod,Nat.add_mod,hpeven]
  have ht2 : t^3+2 ≤ (p+1)^2 := by omega
  have hs := ht2.trans (Nat.pow_le_pow_left hpend 2)
  exact ⟨ReturnCells.ooe_upper_pow m,hs,(CubicReturn.exact_return_seam D hm hM).2.1,hgap⟩

/-- A DC gap certificate on the actual extremal seam gives the stronger strip. -/
theorem periodic_extrema_dc_height {C : Set ℕ} {m M : ℕ}
    (D : CubicReturn.PeriodicExtrema C m M) (hm : 2^24 ≤ m) (hM : M < m^3)
    (hmin : 6 ≤ ReturnCells.ooe m-ReturnCells.oe M.sqrt)
    (hquant : (26240/59049 : ℝ)*(m : ℝ)^(13/128 : ℝ) <
      (ReturnCells.ooe m-ReturnCells.oe M.sqrt : ℕ)) :
    (M : ℝ) < (m : ℝ)^3-(1/2 : ℝ)*(m : ℝ)^(253/128 : ℝ) ∧
      m^253 < (2*(m^3-M))^128 := by
  obtain ⟨hz,ht,hMc,hwz⟩ := periodic_extrema_cells D (by omega) hM
  exact dc_height_of_gap hm hz ht hMc (by omega) rfl hmin hquant

/-- An LR gap certificate on the same actual seam gives both later-return strips. -/
theorem periodic_extrema_lr_height {C : Set ℕ} {m M : ℕ}
    (D : CubicReturn.PeriodicExtrema C m M) (hm : 2^24 ≤ m) (hM : M < m^3)
    (hmin : 8 ≤ ReturnCells.ooe m-ReturnCells.oe M.sqrt)
    (hquant : (2/5 : ℝ)*(m : ℝ)^(13/128+1-(3:ℝ)^41/2^65) <
      (ReturnCells.ooe m-ReturnCells.oe M.sqrt : ℕ)) :
    (M : ℝ) < (m : ℝ)^3-(1/2 : ℝ)*(m : ℝ)^(381/128-(3:ℝ)^41/2^65) ∧
    (M : ℝ) < (m : ℝ)^3-(1/2 : ℝ)*(m : ℝ)^(127/64 : ℝ) ∧
      m^127 < (2*(m^3-M))^64 := by
  obtain ⟨hz,ht,hMc,hwz⟩ := periodic_extrema_cells D (by omega) hM
  exact lr_height_of_gap hm hz ht hMc (by omega) rfl hmin hquant

end Problems.Juggler.ReturnGapHeight





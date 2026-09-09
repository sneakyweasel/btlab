import Problems.Juggler.LandingValuation
import Mathlib.Tactic

namespace Problems.Juggler

def ooeFamilySource (r : ℕ) : ℕ := r ^ 8 + 8
def ooeFamilyFirst (r : ℕ) : ℕ := r ^ 12 + 12 * r ^ 4
def ooeFamilySecond (r : ℕ) : ℕ := r ^ 18 + 18 * r ^ 10 + 54 * r ^ 2 - 1
def ooeFamilyExit (r : ℕ) : ℕ := r ^ 9 + 9 * r - 1

theorem ooeFamily_square_cells {r : ℕ} (hr : 3 ≤ r) :
    ooeFamilyFirst r ^ 2 ≤ ooeFamilySource r ^ 3 ∧
    ooeFamilySource r ^ 3 < (ooeFamilyFirst r + 1) ^ 2 ∧
    ooeFamilySecond r ^ 2 ≤ ooeFamilyFirst r ^ 3 ∧
    ooeFamilyFirst r ^ 3 < (ooeFamilySecond r + 1) ^ 2 ∧
    ooeFamilyExit r ^ 2 ≤ ooeFamilySecond r ∧
    ooeFamilySecond r < (ooeFamilyExit r + 1) ^ 2 := by
  have h4 : 81 ≤ r ^ 4 := by
    have := Nat.pow_le_pow_left hr 4
    norm_num at this
    exact this
  have h6 : 729 ≤ r ^ 6 := by
    have := Nat.pow_le_pow_left hr 6
    norm_num at this
    exact this
  have h8 : 6561 ≤ r ^ 8 := by
    have := Nat.pow_le_pow_left hr 8
    norm_num at this
    exact this
  have h7 : 2187 ≤ r ^ 7 := by
    have := Nat.pow_le_pow_left hr 7
    norm_num at this
    exact this
  have h12 : 81 * r ^ 8 ≤ r ^ 12 := by
    nlinarith [Nat.mul_le_mul_left (r ^ 8) h4]
  have h18 : 729 * r ^ 12 ≤ r ^ 18 := by
    nlinarith [Nat.mul_le_mul_left (r ^ 12) h6]
  have h124 : 6561 * r ^ 4 ≤ r ^ 12 := by
    nlinarith [Nat.mul_le_mul_left (r ^ 4) h8]
  have h9 : 2187 * r ^ 2 ≤ r ^ 9 := by
    nlinarith [Nat.mul_le_mul_left (r ^ 2) h7]
  have hv : ooeFamilySecond r + 1 = r ^ 18 + 18 * r ^ 10 + 54 * r ^ 2 := by
    unfold ooeFamilySecond
    have : 1 ≤ r ^ 2 := by nlinarith
    omega
  have hz : ooeFamilyExit r + 1 = r ^ 9 + 9 * r := by
    unfold ooeFamilyExit
    omega
  have hv2 := congrArg (fun n : ℕ => n ^ 2) hv
  have hz2 := congrArg (fun n : ℕ => n ^ 2) hz
  dsimp [ooeFamilyFirst, ooeFamilySource]
  refine ⟨by nlinarith, by nlinarith, ?_, ?_, ?_, ?_⟩
  · nlinarith [hv, hv2]
  · nlinarith [hv2]
  · nlinarith [hv, hz, hz2]
  · nlinarith [hv, hz2]

theorem ooeFamily_parities {r : ℕ} (hr : 3 ≤ r) (ho : r % 2 = 1) :
    ooeFamilySource r % 2 = 1 ∧ ooeFamilyFirst r % 2 = 1 ∧
    ooeFamilySecond r % 2 = 0 ∧ ooeFamilyExit r % 2 = 1 := by
  have hp (k : ℕ) : r ^ k % 2 = 1 := by simp [Nat.pow_mod, ho]
  have hv : ooeFamilySecond r + 1 = r ^ 18 + 18 * r ^ 10 + 54 * r ^ 2 := by
    unfold ooeFamilySecond
    have : 1 ≤ r ^ 2 := by nlinarith
    omega
  have hz : ooeFamilyExit r + 1 = r ^ 9 + 9 * r := by
    unfold ooeFamilyExit
    omega
  have hvmod := congrArg (fun n : ℕ => n % 2) hv
  have hzmod := congrArg (fun n : ℕ => n % 2) hz
  have h18 := hp 18
  have h9 := hp 9
  refine ⟨?_, ?_, by omega, by omega⟩
  · have h8 := hp 8
    unfold ooeFamilySource
    omega
  · have h12 := hp 12
    unfold ooeFamilyFirst
    omega

theorem ooeFamily_juggler_block {r : ℕ} (hr : 3 ≤ r) (ho : r % 2 = 1) :
    floorPower (ooeFamilySource r) = ooeFamilyFirst r ∧
    floorPower (ooeFamilyFirst r) = ooeFamilySecond r ∧
    floorPower (ooeFamilySecond r) = ooeFamilyExit r := by
  obtain ⟨h1,h2,h3,h4,h5,h6⟩ := ooeFamily_square_cells hr
  obtain ⟨p1,p2,p3,_⟩ := ooeFamily_parities hr ho
  refine ⟨?_,?_,?_⟩
  · rw [floorPower_odd_eq p1]
    exact (Nat.eq_sqrt.mpr ⟨by simpa only [pow_two] using h1,
      by simpa only [pow_two] using h2⟩).symm
  · rw [floorPower_odd_eq p2]
    exact (Nat.eq_sqrt.mpr ⟨by simpa only [pow_two] using h3,
      by simpa only [pow_two] using h4⟩).symm
  · rw [floorPower_even_eq p3]
    exact (Nat.eq_sqrt.mpr ⟨by simpa only [pow_two] using h5,
      by simpa only [pow_two] using h6⟩).symm

def ooeFamilyReturn (r s : ℕ) : Prop := s ^ 8 + 9 = r ^ 9 + 9 * r

theorem ooeFamilyReturn_iff {r s : ℕ} (hr : 3 ≤ r) :
    ooeFamilyExit r = ooeFamilySource s ↔ ooeFamilyReturn r s := by
  unfold ooeFamilyExit ooeFamilySource ooeFamilyReturn
  omega

theorem odd_eighth_mod_thirtytwo {n : ℕ} (hn : n % 2 = 1) :
    n ^ 8 % 32 = 1 := by
  have hlt := Nat.mod_lt n (by decide : 0 < 32)
  have hp : n % 32 % 2 = 1 := by omega
  rw [Nat.pow_mod]
  interval_cases h : n % 32 <;> norm_num [h] at *

theorem ooeFamilyReturn_mod_sixteen {r s : ℕ}
    (hr : r % 2 = 1) (hs : s % 2 = 1) (h : ooeFamilyReturn r s) :
    r % 16 = 1 := by
  have hr8 := odd_eighth_mod_thirtytwo hr
  have hs8 := odd_eighth_mod_thirtytwo hs
  have hr9 : r ^ 9 % 32 = r % 32 := by
    rw [show r ^ 9 = r ^ 8 * r by ring, Nat.mul_mod, hr8]
    simp
  have hm := congrArg (fun n : ℕ => n % 32) h
  change (s ^ 8 + 9) % 32 = (r ^ 9 + 9 * r) % 32 at hm
  omega

theorem ooeFamilyReturn_mod_three {r s : ℕ} (h : ooeFamilyReturn r s) :
    r % 3 = 1 := by
  have hrlt := Nat.mod_lt r (by decide : 0 < 3)
  have hslt := Nat.mod_lt s (by decide : 0 < 3)
  have hr9 : r ^ 9 % 3 = r % 3 := by
    rw [Nat.pow_mod]
    interval_cases hm : r % 3 <;> norm_num
  have hs8 : s ^ 8 % 3 = if s % 3 = 0 then 0 else 1 := by
    rw [Nat.pow_mod]
    interval_cases hm : s % 3 <;> norm_num
  have hm := congrArg (fun n : ℕ => n % 3) h
  change (s ^ 8 + 9) % 3 = (r ^ 9 + 9 * r) % 3 at hm
  by_cases hr0 : r % 3 = 0
  · have hs0 : s % 3 = 0 := by
      split_ifs at hs8 <;> omega
    obtain ⟨a, ha⟩ : ∃ a, r = 3 * a := ⟨r / 3, by omega⟩
    obtain ⟨b, hb⟩ : ∃ b, s = 3 * b := ⟨s / 3, by omega⟩
    have hr27 : r ^ 9 % 27 = 0 := by
      rw [ha, mul_pow, Nat.mul_mod]
      norm_num
    have hs27 : s ^ 8 % 27 = 0 := by
      rw [hb, mul_pow, Nat.mul_mod]
      norm_num
    have hm27 := congrArg (fun n : ℕ => n % 27) h
    change (s ^ 8 + 9) % 27 = (r ^ 9 + 9 * r) % 27 at hm27
    omega
  · split_ifs at hs8 <;> omega

theorem ooeFamilyReturn_mod_fortyeight {r s : ℕ}
    (hr : r % 2 = 1) (hs : s % 2 = 1) (h : ooeFamilyReturn r s) :
    r % 48 = 1 := by
  have := ooeFamilyReturn_mod_sixteen hr hs h
  have := ooeFamilyReturn_mod_three h
  omega

def ooeFamilyFactor (r : ℕ) : ℕ :=
  r ^ 8 + r ^ 7 + r ^ 6 + r ^ 5 + r ^ 4 + r ^ 3 + r ^ 2 + r + 10

theorem ooeFamilyReturn_factor {r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s)
    (h : ooeFamilyReturn r s) :
    s ^ 8 - 1 = (r - 1) * ooeFamilyFactor r := by
  have hpoly : (r - 1) * ooeFamilyFactor r + 10 = r ^ 9 + 9 * r := by
    have he : r = (r - 1) + 1 := by omega
    conv_lhs => rw [he]
    conv_rhs => rw [he]
    simp only [Nat.add_sub_cancel]
    unfold ooeFamilyFactor
    ring
  have hp : 1 ≤ s ^ 8 := Nat.one_le_pow _ _ hs
  unfold ooeFamilyReturn at h
  omega

theorem ooeFamilyFactor_valuation {r : ℕ} (hr : r % 16 = 1) :
    padicValNat 2 (ooeFamilyFactor r) = 1 := by
  have hm : r % 8 = 1 := by omega
  apply padicValNat_two_eq_one_of_mod_eight
  left
  norm_num [ooeFamilyFactor, Nat.add_mod, Nat.pow_mod, hm]

theorem eighth_minus_one_valuation {s : ℕ} (hs : 3 ≤ s) (hm : s % 16 = 1) :
    padicValNat 2 (s ^ 8 - 1) = padicValNat 2 (s - 1) + 3 := by
  have he : s = s - 1 + 1 := by omega
  have hfac : s ^ 8 - 1 = (s - 1) * (s + 1) * (s ^ 2 + 1) * (s ^ 4 + 1) := by
    have hp : (s - 1) * (s + 1) * (s ^ 2 + 1) * (s ^ 4 + 1) + 1 = s ^ 8 := by
      conv_lhs => rw [he]
      conv_rhs => rw [he]
      simp only [Nat.add_sub_cancel]
      ring
    omega
  have h8 : s % 8 = 1 := by omega
  have h1 : padicValNat 2 (s + 1) = 1 :=
    padicValNat_two_eq_one_of_mod_eight (Or.inl (by omega))
  have h2 : padicValNat 2 (s ^ 2 + 1) = 1 := by
    apply padicValNat_two_eq_one_of_mod_eight
    left
    norm_num [Nat.add_mod, Nat.pow_mod, h8]
  have h4 : padicValNat 2 (s ^ 4 + 1) = 1 := by
    apply padicValNat_two_eq_one_of_mod_eight
    left
    norm_num [Nat.add_mod, Nat.pow_mod, h8]
  have hsp : 0 < s - 1 := by omega
  rw [hfac, padicValNat.mul (by positivity) (by positivity),
    padicValNat.mul (by positivity) (by positivity),
    padicValNat.mul (by omega) (by positivity), h1, h2, h4]
  try omega

theorem ooeFamilyReturn_valuation_drop {r s : ℕ} (hr : 3 ≤ r) (hs : 3 ≤ s)
    (hrm : r % 16 = 1) (hsm : s % 16 = 1) (h : ooeFamilyReturn r s) :
    padicValNat 2 (s - 1) + 2 = padicValNat 2 (r - 1) := by
  have hf := ooeFamilyReturn_factor (by omega : 1 ≤ r) (by omega : 1 ≤ s) h
  have hv := eighth_minus_one_valuation hs hsm
  rw [hf, padicValNat.mul (by omega) (by
    unfold ooeFamilyFactor
    positivity), ooeFamilyFactor_valuation hrm] at hv
  omega

theorem ooeFamilyReturn_valuation_ge_four {r s : ℕ}
    (hr : 3 ≤ r) (hro : r % 2 = 1) (hso : s % 2 = 1)
    (h : ooeFamilyReturn r s) : 4 ≤ padicValNat 2 (r - 1) := by
  have hm := ooeFamilyReturn_mod_sixteen hro hso h
  apply le_padicValNat_two_of_pow_dvd (by omega)
  norm_num
  omega

theorem ooeFamily_chain_bound (r : ℕ → ℕ) (k : ℕ)
    (hr : ∀ i, i ≤ k → 3 ≤ r i)
    (ho : ∀ i, i ≤ k → r i % 2 = 1)
    (hstep : ∀ i, i < k → ooeFamilyReturn (r i) (r (i + 1))) :
    k ≤ (padicValNat 2 (r 0 - 1) - 2) / 2 := by
  have hmod (i : ℕ) (hi : i < k) : r i % 16 = 1 :=
    ooeFamilyReturn_mod_sixteen (ho i (by omega)) (ho (i+1) (by omega)) (hstep i hi)
  have hinv : ∀ i, i < k →
      padicValNat 2 (r i - 1) + 2 * i = padicValNat 2 (r 0 - 1) := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      have he := ooeFamilyReturn_valuation_drop (hr i (by omega))
        (hr (i+1) (by omega)) (hmod i (by omega)) (hmod (i+1) hi)
        (hstep i (by omega))
      have hv := ih (by omega)
      omega
  by_cases hk : k = 0
  · subst k
    omega
  · have hi : k - 1 < k := by omega
    have hv := hinv (k-1) hi
    have hlo := ooeFamilyReturn_valuation_ge_four (hr (k-1) (by omega))
      (ho (k-1) (by omega)) (ho (k-1+1) (by omega)) (hstep (k-1) hi)
    omega

theorem ooeFamily_no_infinite_chain (r : ℕ → ℕ)
    (hr : ∀ i, 3 ≤ r i) (ho : ∀ i, r i % 2 = 1) :
    ¬ ∀ i, ooeFamilyReturn (r i) (r (i+1)) := by
  intro h
  have hb := ooeFamily_chain_bound r (padicValNat 2 (r 0 - 1) + 1)
    (fun i _ => hr i) (fun i _ => ho i) (fun i _ => h i)
  omega

end Problems.Juggler

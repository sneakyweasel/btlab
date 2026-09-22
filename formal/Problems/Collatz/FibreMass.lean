import Problems.Collatz.PreimageBalance
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Complete signed odd-return fibres and finite periodic weights

The coefficient operator below includes every positive halving exponent.
It concerns homogeneous reciprocal coefficients, before the affine height error.
-/

noncomputable section

namespace Problems.Collatz.FibreMass

open Finset
open scoped Classical

abbrev Level (r : ℕ) := Fin (3^r)

def doubleEquiv (r : ℕ) : Level r ≃ Level r :=
  Equiv.ofBijective (PreimageBalance.affine (by positivity) 2 0)
    (PreimageBalance.affine_bijective (by positivity) 2 0
      ((by norm_num : Nat.Coprime 3 2).pow_left r))

theorem doubleEquiv_val (r : ℕ) (a : Level r) :
    (doubleEquiv r a).val = (2*a.val) % 3^r := by
  simp [doubleEquiv, PreimageBalance.affine]

/-- `true` denotes `3n+1`; `false` denotes `3n-1`. -/
def offset (plus : Bool) (r : ℕ) : ℕ := if plus then 1 else 3^(r+1)-1

def embed (plus : Bool) (r : ℕ) (b : Level r) : Level (r+1) :=
  ⟨(3*b.val+offset plus r) % 3^(r+1), Nat.mod_lt _ (by positivity)⟩

/-- The unique parent residue for child `b` and halving exponent `k+1`. -/
def parent (plus : Bool) (r k : ℕ) (b : Level r) : Level (r+1) :=
  ((doubleEquiv (r+1)).symm^[k+1]) (embed plus r b)

theorem double_iterate_val (r k : ℕ) (a : Level r) :
    ((doubleEquiv r)^[k] a).val = (2^k*a.val) % 3^r := by
  induction k with
  | zero => simp [Nat.mod_eq_of_lt a.isLt]
  | succ k ih =>
      rw [Function.iterate_succ_apply', doubleEquiv_val, ih]
      simp only [Nat.mul_mod_mod, pow_succ]
      congr 1
      ring

theorem parent_iff (plus : Bool) (r k : ℕ) (a : Level (r+1)) (b : Level r) :
    parent plus r k b = a ↔
      2^(k+1)*a.val ≡ 3*b.val+offset plus r [MOD 3^(r+1)] := by
  have hi : Function.LeftInverse (doubleEquiv (r+1)) (doubleEquiv (r+1)).symm :=
    (doubleEquiv (r+1)).apply_symm_apply
  have hj : Function.RightInverse (doubleEquiv (r+1)) (doubleEquiv (r+1)).symm :=
    (doubleEquiv (r+1)).symm_apply_apply
  constructor
  · intro h
    have ht := congrArg ((doubleEquiv (r+1))^[k+1]) h
    rw [parent, hi.iterate] at ht
    have hv := congrArg Fin.val ht
    rw [double_iterate_val] at hv
    exact hv.symm
  · intro h
    have ht : (doubleEquiv (r+1))^[k+1] a = embed plus r b := by
      apply Fin.ext
      rw [double_iterate_val]
      exact h
    have hu := congrArg ((doubleEquiv (r+1)).symm^[k+1]) ht
    rw [hj.iterate] at hu
    exact hu.symm

def sign (plus : Bool) : ℤ := if plus then 1 else -1

theorem offset_congr (plus : Bool) (r : ℕ) :
    (offset plus r : ℤ) ≡ sign plus [ZMOD (3:ℤ)^(r+1)] := by
  cases plus
  · have hp : 1 ≤ 3^(r+1) := by
      have : 0 < 3^(r+1) := by positivity
      omega
    rw [Int.modEq_iff_dvd]
    refine ⟨-1, ?_⟩
    simp only [offset, sign, Bool.false_eq_true, ↓reduceIte, Int.natCast_sub hp,
      Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, mul_neg_one]
    ring
  · simp [offset, sign]

/-- The branch relation is exactly `2^(k+1) a = 3 b + s` modulo the
parent modulus, for the ordinary signs `s=1` and `s=-1`. -/
theorem parent_signed_iff (plus : Bool) (r k : ℕ) (a : Level (r+1)) (b : Level r) :
    parent plus r k b = a ↔ (2:ℤ)^(k+1)*(a.val:ℤ) ≡
      3*(b.val:ℤ)+sign plus [ZMOD (3:ℤ)^(r+1)] := by
  rw [parent_iff, ← Int.natCast_modEq_iff]
  push_cast
  have ho := (Int.ModEq.refl ((3:ℤ)*b.val)).add (offset_congr plus r)
  exact ⟨fun h => h.trans ho, fun h => h.trans ho.symm⟩

theorem parent_injective (plus : Bool) (r k : ℕ) :
    Function.Injective (parent plus r k) := by
  intro b c h
  have hb := (parent_iff plus r k (parent plus r k b) b).mp rfl
  have hc := (parent_iff plus r k (parent plus r k b) c).mp h.symm
  have ht := (hb.symm.trans hc).add_right_cancel' (offset plus r)
  rw [pow_succ, Nat.mul_comm (3^r) 3] at ht
  have he : b.val ≡ c.val [MOD 3^r] := Nat.ModEq.mul_left_cancel' (by norm_num : 3 ≠ 0) ht
  exact Fin.ext (he.eq_of_lt_of_lt b.isLt c.isLt)

def coefficient (k : ℕ) : ℝ := (3/2)*(1/2)^k

theorem coefficient_eq (k : ℕ) : coefficient k = 3/(2:ℝ)^(k+1) := by
  simp only [coefficient, div_pow, one_pow, pow_succ]
  ring

def row (plus : Bool) (r k : ℕ) (h : Level r → ℝ) (a : Level (r+1)) : ℝ :=
  coefficient k * ∑ b, if parent plus r k b = a then h b else 0

theorem row_at_parent (plus : Bool) (r k : ℕ) (h : Level r → ℝ) (b : Level r) :
    row plus r k h (parent plus r k b) = (3/(2:ℝ)^(k+1))*h b := by
  simp [row, (parent_injective plus r k).eq_iff, coefficient_eq]

def transfer (plus : Bool) (r : ℕ) (h : Level r → ℝ) (a : Level (r+1)) : ℝ :=
  ∑' k, row plus r k h a

/-- An explicit congruence formula includes every positive halving exponent;
`parent_injective` ensures at most one child in each inner sum. -/
theorem transfer_formula (plus : Bool) (r : ℕ) (h : Level r → ℝ) (a : Level (r+1)) :
    transfer plus r h a = ∑' k : ℕ, (3/(2:ℝ)^(k+1))*
      ∑ b : Level r, if (2:ℤ)^(k+1)*(a.val:ℤ) ≡
        3*(b.val:ℤ)+sign plus [ZMOD (3:ℤ)^(r+1)] then h b else 0 := by
  simp only [transfer, row, coefficient_eq, parent_signed_iff]

theorem row_nonneg (plus : Bool) (r k : ℕ) {h : Level r → ℝ}
    (hh : ∀ b, 0 ≤ h b) (a : Level (r+1)) : 0 ≤ row plus r k h a := by
  unfold row coefficient
  apply mul_nonneg (by positivity)
  apply sum_nonneg
  intro b _
  split_ifs <;> simp_all

theorem row_le (plus : Bool) (r k : ℕ) {h : Level r → ℝ}
    (hh : ∀ b, 0 ≤ h b) (a : Level (r+1)) :
    row plus r k h a ≤ coefficient k * ∑ b, h b := by
  apply mul_le_mul_of_nonneg_left _ (by unfold coefficient; positivity)
  apply sum_le_sum
  intro b _
  split_ifs <;> simp_all

theorem row_summable (plus : Bool) (r : ℕ) {h : Level r → ℝ}
    (hh : ∀ b, 0 ≤ h b) (a : Level (r+1)) :
    Summable (fun k => row plus r k h a) := by
  exact Summable.of_nonneg_of_le (fun k => row_nonneg plus r k hh a)
    (fun k => row_le plus r k hh a)
    ((summable_geometric_two.mul_left (3/2)).mul_right (∑ b, h b))

theorem transfer_nonneg (plus : Bool) (r : ℕ) {h : Level r → ℝ}
    (hh : ∀ b, 0 ≤ h b) (a : Level (r+1)) : 0 ≤ transfer plus r h a :=
  tsum_nonneg (fun k => row_nonneg plus r k hh a)

theorem row_sum (plus : Bool) (r k : ℕ) (h : Level r → ℝ) :
    ∑ a, row plus r k h a = coefficient k * ∑ b, h b := by
  simp only [row, ← mul_sum]
  rw [sum_comm]
  simp

theorem transfer_sum (plus : Bool) (r : ℕ) {h : Level r → ℝ}
    (hh : ∀ b, 0 ≤ h b) : ∑ a, transfer plus r h a = 3 * ∑ b, h b := by
  unfold transfer
  rw [← Summable.tsum_finsetSum (fun a _ => row_summable plus r hh a)]
  simp_rw [row_sum, coefficient]
  rw [tsum_mul_right, tsum_mul_left, tsum_geometric_two]
  ring

theorem offset_unit (plus : Bool) (r : ℕ) : offset plus r % 3 ≠ 0 := by
  have hp : 0 < 3^r := by positivity
  cases plus
  · have he : 3^(r+1)-1 = 3*(3^r-1)+2 := by rw [pow_succ]; omega
    simp [offset, he, Nat.add_mod]
  · norm_num [offset]

theorem parent_unit (plus : Bool) (r k : ℕ) (b : Level r) :
    (parent plus r k b).val % 3 ≠ 0 := by
  intro hz
  have hd : 3 ∣ 3^(r+1) := by exact ⟨3^r, by rw [pow_succ]; ring⟩
  have hm := ((parent_iff plus r k (parent plus r k b) b).mp rfl).of_dvd hd
  have ho : offset plus r % 3 = 0 := by
    simpa [Nat.ModEq, Nat.mul_mod, Nat.add_mod, hz] using hm.symm
  exact offset_unit plus r ho

theorem transfer_zero (plus : Bool) (r : ℕ) (h : Level r → ℝ)
    (a : Level (r+1)) (ha : a.val % 3 = 0) : transfer plus r h a = 0 := by
  have he (k : ℕ) (b : Level r) : parent plus r k b ≠ a := by
    intro h
    have hu := parent_unit plus r k b
    rw [h, ha] at hu
    exact hu rfl
  simp [transfer, row, he]

def spike (plus : Bool) (r : ℕ) : Level r :=
  ⟨(if plus then 3^r-1 else 1) % 3^r, Nat.mod_lt _ (by positivity)⟩

theorem level_large {r : ℕ} (hr : 1 ≤ r) : 3 ≤ 3^r := by
  simpa using (Nat.pow_le_pow_right (by norm_num : 1 ≤ 3) hr)

theorem spike_val (plus : Bool) {r : ℕ} (hr : 1 ≤ r) :
    (spike plus r).val = if plus then 3^r-1 else 1 := by
  have hp := level_large hr
  cases plus <;> simp [spike, Nat.mod_eq_of_lt (show 1 < 3^r by omega),
    Nat.mod_eq_of_lt (show 3^r-1 < 3^r by omega)]

theorem spike_unit (plus : Bool) {r : ℕ} (hr : 1 ≤ r) :
    (spike plus r).val % 3 ≠ 0 := by
  rw [spike_val plus hr]
  cases plus
  · norm_num
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
    simpa [offset] using offset_unit false t

theorem parent_spike (plus : Bool) {r : ℕ} (hr : 1 ≤ r) :
    parent plus r 0 (spike plus r) = spike plus (r+1) := by
  apply (parent_iff plus r 0 _ _).mpr
  rw [spike_val plus hr, spike_val plus (by omega)]
  have hp := level_large hr
  cases plus
  · have he : 3+(3^(r+1)-1) = 2+3^(r+1) := by
      have : 0 < 3^(r+1) := by positivity
      omega
    simp only [offset, Bool.false_eq_true, ↓reduceIte, mul_one]
    change 2 % 3^(r+1) = (3+(3^(r+1)-1)) % 3^(r+1)
    rw [he, Nat.add_mod_right]
  · have he : 2*(3^(r+1)-1) = 3*(3^r-1)+1+3^(r+1) := by rw [pow_succ]; omega
    simp only [offset, ↓reduceIte]
    change (2*(3^(r+1)-1)) % 3^(r+1) = (3*(3^r-1)+1) % 3^(r+1)
    rw [he, Nat.add_mod_right]

theorem transfer_spike (plus : Bool) {r : ℕ} (hr : 1 ≤ r)
    {h : Level r → ℝ} (hh : ∀ b, 0 ≤ h b) :
    (3/2)*h (spike plus r) ≤ transfer plus r h (spike plus (r+1)) := by
  have hs : h (spike plus r) ≤
      ∑ b, if parent plus r 0 b = spike plus (r+1) then h b else 0 := by
    have ht := single_le_sum (f := fun b =>
      if parent plus r 0 b = spike plus (r+1) then h b else 0)
      (s := univ) (a := spike plus r)
      (fun b _ => by split_ifs <;> simp_all) (mem_univ _)
    simpa [parent_spike plus hr] using ht
  have ht := (row_summable plus r hh (spike plus (r+1))).le_tsum 0
    (fun k _ => row_nonneg plus r k hh _)
  change row plus r 0 h (spike plus (r+1)) ≤ _ at ht
  unfold row coefficient at ht
  simp only [pow_zero, mul_one] at ht
  exact (mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ) ≤ 3/2)).trans ht

def iterate (plus : Bool) (r : ℕ) (h : Level r → ℝ) :
    (d : ℕ) → Level (r+d) → ℝ
  | 0 => h
  | d+1 => transfer plus (r+d) (iterate plus r h d)

theorem iterate_nonneg (plus : Bool) (r : ℕ) {h : Level r → ℝ}
    (hh : ∀ b, 0 ≤ h b) (d : ℕ) : ∀ a, 0 ≤ iterate plus r h d a := by
  induction d with
  | zero => exact hh
  | succ d ih => exact transfer_nonneg plus (r+d) ih

theorem iterate_sum (plus : Bool) (r : ℕ) {h : Level r → ℝ}
    (hh : ∀ b, 0 ≤ h b) (d : ℕ) :
    ∑ a, iterate plus r h d a = (3:ℝ)^d * ∑ b, h b := by
  induction d with
  | zero => simp [iterate]
  | succ d ih =>
      change ∑ a, transfer plus (r+d) (iterate plus r h d) a = _
      rw [transfer_sum plus (r+d) (iterate_nonneg plus r hh d), ih, pow_succ]
      ring

theorem iterate_spike (plus : Bool) {r : ℕ} (hr : 1 ≤ r)
    {h : Level r → ℝ} (hh : ∀ b, 0 ≤ h b) (d : ℕ) :
    (3/2:ℝ)^d * h (spike plus r) ≤ iterate plus r h d (spike plus (r+d)) := by
  induction d with
  | zero => simp [iterate]
  | succ d ih =>
      have hs := transfer_spike plus (show 1 ≤ r+d by omega) (iterate_nonneg plus r hh d)
      have hm := mul_le_mul_of_nonneg_left ih (by norm_num : (0:ℝ) ≤ 3/2)
      change _ ≤ transfer plus (r+d) (iterate plus r h d) (spike plus (r+d+1))
      calc (3/2:ℝ)^(d+1)*h (spike plus r)
          = (3/2)*((3/2)^d*h (spike plus r)) := by rw [pow_succ]; ring
        _ ≤ _ := hm.trans hs

def project (r d : ℕ) (a : Level (r+d)) : Level r :=
  ⟨a.val % 3^r, Nat.mod_lt _ (by positivity)⟩

theorem project_sum (r d : ℕ) (h : Level r → ℝ) :
    ∑ a, h (project r d a) = (3:ℝ)^d * ∑ b, h b := by
  let e : Fin (3^d) × Level r ≃ Level (r+d) :=
    finProdFinEquiv.trans (finCongr (by rw [pow_add]; ring))
  have hp (i : Fin (3^d) × Level r) : project r d (e i) = i.2 := by
    apply Fin.ext
    change (i.2.val+3^r*i.1.val) % 3^r = i.2.val
    simp [Nat.add_mod, Nat.mod_eq_of_lt i.2.isLt]
  rw [← e.sum_comp (fun a => h (project r d a))]
  simp_rw [hp]
  simp [Fintype.sum_prod_type, Level]

theorem project_spike (plus : Bool) {r : ℕ} (hr : 1 ≤ r) (d : ℕ) :
    project r d (spike plus (r+d)) = spike plus r := by
  apply Fin.ext
  change (spike plus (r+d)).val % 3^r = (spike plus r).val
  rw [spike_val plus (by omega), spike_val plus hr]
  have hM := level_large hr
  have hQ : 1 ≤ 3^d := by
    have : 0 < 3^d := by positivity
    omega
  cases plus
  · simp [Nat.mod_eq_of_lt (show 1 < 3^r by omega)]
  · simp only [↓reduceIte]
    rw [pow_add]
    have he : 3^r*3^d-1 = 3^r*(3^d-1)+(3^r-1) := by
      have hq : 3^d-1+1 = 3^d := Nat.sub_add_cancel hQ
      have hm : 3^r-1+1 = 3^r := Nat.sub_add_cancel (by omega)
      have hp : 1 ≤ 3^r*3^d := by
        have : 0 < 3^r*3^d := by positivity
        omega
      have ht := Nat.sub_add_cancel hp
      nlinarith
    rw [he, Nat.add_mod]
    simp [Nat.mod_eq_of_lt (show 3^r-1 < 3^r by omega)]

theorem project_nonunit {r : ℕ} (hr : 1 ≤ r) (d : ℕ) (a : Level (r+d))
    (ha : a.val % 3 = 0) : (project r d a).val % 3 = 0 := by
  have hd : 3 ∣ 3^r := by simpa using Nat.pow_dvd_pow 3 hr
  exact (Nat.mod_mod_of_dvd a.val hd).trans ha

/-- A nonnegative finite table supported on units cannot reproduce everywhere
if its value at the repeated one-halving residue is positive. -/
theorem exists_deficit (plus : Bool) {r : ℕ} (hr : 1 ≤ r)
    {h : Level r → ℝ} (hh : ∀ b, 0 ≤ h b)
    (hz : ∀ b, b.val % 3 = 0 → h b = 0) (hs : 0 < h (spike plus r))
    {d : ℕ} (hd : 1 ≤ d) :
    ∃ a : Level (r+d), a.val % 3 ≠ 0 ∧ iterate plus r h d a < h (project r d a) := by
  by_contra! hno
  have hle (a : Level (r+d)) : h (project r d a) ≤ iterate plus r h d a := by
    by_cases ha : a.val % 3 = 0
    · rw [hz _ (project_nonunit hr d a ha)]
      exact iterate_nonneg plus r hh d a
    · exact hno a ha
  have hp : (1:ℝ) < (3/2:ℝ)^d := one_lt_pow₀ (by norm_num) (by omega)
  have hstrict : h (project r d (spike plus (r+d))) <
      iterate plus r h d (spike plus (r+d)) := by
    rw [project_spike plus hr]
    have hm : h (spike plus r) < (3/2:ℝ)^d*h (spike plus r) := by nlinarith
    exact hm.trans_le (iterate_spike plus hr hh d)
  have hsum := sum_lt_sum (fun a _ => hle a)
    ⟨spike plus (r+d), mem_univ _, hstrict⟩
  rw [project_sum, iterate_sum plus r hh] at hsum
  exact (lt_irrefl _ hsum)

/-- Both signs, every ternary level, every strictly positive unit weight,
and every fixed positive number of full odd-return generations. -/
theorem finite_weight_obstruction (plus : Bool) {r : ℕ} (hr : 1 ≤ r)
    (h : Level r → ℝ) (hz : ∀ b, b.val % 3 = 0 → h b = 0)
    (hp : ∀ b, b.val % 3 ≠ 0 → 0 < h b) {d : ℕ} (hd : 1 ≤ d) :
    ∃ a : Level (r+d), a.val % 3 ≠ 0 ∧ iterate plus r h d a < h (project r d a) := by
  have hh (b : Level r) : 0 ≤ h b := by
    by_cases hb : b.val % 3 = 0
    · rw [hz b hb]
    · exact (hp b hb).le
  exact exists_deficit plus hr hh hz (hp _ (spike_unit plus hr)) hd

end Problems.Collatz.FibreMass

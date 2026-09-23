import Problems.Collatz.FibreMass
import Problems.Collatz.Accelerated

/-! # Actual positive signed odd-return predecessors

All positive halving exponents are enumerated without truncation. The
target is odd, so the displayed exponent removes every factor of two.
-/

noncomputable section

namespace Problems.Collatz.FibreActual

open Finset FibreMass
open scoped Classical

/-- The positive signed Collatz numerator; `true` selects plus and `false` minus. -/
def numerator (plus : Bool) (n : ℕ) : ℕ := if plus then 3*n+1 else 3*n-1

/-- Remove every factor of two from the signed numerator of a natural input. -/
def oddReturn (plus : Bool) (n : ℕ) : ℕ :=
  numerator plus n / 2^padicValNat 2 (numerator plus n)

/-- The plus specialization is the existing accelerated Collatz map. -/
theorem oddReturn_plus (n : ℕ) : oddReturn true n = acceleratedT n := rfl

/-- Both signed numerators are positive at every positive input. -/
theorem numerator_pos (plus : Bool) {n : ℕ} (hn : 1 ≤ n) : 0 < numerator plus n := by
  cases plus <;> simp only [numerator, Bool.false_eq_true, ↓reduceIte] <;> omega

/-- Natural subtraction agrees with the signed integer formula at positive inputs. -/
theorem numerator_cast (plus : Bool) {n : ℕ} (hn : 1 ≤ n) :
    (numerator plus n : ℤ) = 3*(n:ℤ)+sign plus := by
  cases plus
  · simp [numerator, sign, Int.natCast_sub (show 1 ≤ 3*n by omega), sub_eq_add_neg]
  · simp [numerator, sign]

/-- A positive odd input has an even numerator for either sign. -/
theorem numerator_even (plus : Bool) {n : ℕ} (hn : 1 ≤ n) (ho : Odd n) :
    2 ∣ numerator plus n := by
  have hm := Nat.odd_iff.mp ho
  rw [Nat.dvd_iff_mod_eq_zero]
  cases plus <;> simp only [numerator, Bool.false_eq_true, ↓reduceIte] <;> omega

/-- The inverse numerator for halving exponent `k+1`, before division by three. -/
def raw (plus : Bool) (k m : ℕ) : ℕ :=
  if plus then 2^(k+1)*m-1 else 2^(k+1)*m+1

/-- The candidate predecessor obtained by dividing the inverse numerator by three. -/
def child (plus : Bool) (k m : ℕ) : ℕ := raw plus k m / 3

/-- The inverse numerator is divisible by three, so the candidate is integral. -/
def Admissible (plus : Bool) (k m : ℕ) : Prop := 3 ∣ raw plus k m

/-- The canonical residue of a natural number at ternary level `r`. -/
def residue (r n : ℕ) : Level r := ⟨n % 3^r, Nat.mod_lt _ (by positivity)⟩

/-- A positive halving exponent gives a power of two at least two. -/
theorem pow_two_lower (k : ℕ) : 2 ≤ 2^(k+1) := by
  simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (show 1 ≤ k+1 by omega)

/-- Every inverse numerator at a positive target is strictly positive. -/
theorem raw_pos (plus : Bool) (k : ℕ) {m : ℕ} (hm : 1 ≤ m) : 0 < raw plus k m := by
  have hp := pow_two_lower k
  have hp' : 2 ≤ 2^(k+1)*m := by nlinarith
  cases plus <;> simp only [raw, Bool.false_eq_true, ↓reduceIte] <;> omega

/-- The inverse numerator is exactly the signed integer affine expression. -/
theorem raw_cast (plus : Bool) (k : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    (raw plus k m : ℤ) = (2:ℤ)^(k+1)*(m:ℤ)-sign plus := by
  have hp := pow_two_lower k
  have hp' : 1 ≤ 2^(k+1)*m := by nlinarith
  cases plus <;> simp [raw, sign, Int.natCast_sub hp']

/-- Every inverse numerator at a positive target is odd. -/
theorem raw_odd (plus : Bool) (k : ℕ) {m : ℕ} (hm : 1 ≤ m) : Odd (raw plus k m) := by
  have he : (2^(k+1)*m) % 2 = 0 := by simp [pow_succ, Nat.mul_mod]
  have hp : 2 ≤ 2^(k+1)*m := by nlinarith [pow_two_lower k]
  rw [Nat.odd_iff]
  cases plus <;> simp only [raw, Bool.false_eq_true, ↓reduceIte] <;> omega

/-- Admissibility makes division by three exact. -/
theorem child_mul (plus : Bool) (k m : ℕ) (ha : Admissible plus k m) :
    3*child plus k m = raw plus k m := Nat.mul_div_cancel' ha

/-- An admissible candidate at a positive target is positive. -/
theorem child_pos (plus : Bool) (k : ℕ) {m : ℕ} (hm : 1 ≤ m)
    (ha : Admissible plus k m) : 1 ≤ child plus k m := by
  have := child_mul plus k m ha
  have := raw_pos plus k hm
  omega

/-- An admissible candidate at a positive target is odd. -/
theorem child_odd (plus : Bool) (k : ℕ) {m : ℕ} (hm : 1 ≤ m)
    (ha : Admissible plus k m) : Odd (child plus k m) := by
  have h := Nat.odd_iff.mp (raw_odd plus k hm)
  have he := child_mul plus k m ha
  rw [Nat.odd_iff]
  omega

/-- The forward signed numerator of an admissible child is the prescribed power times its target. -/
theorem child_equation (plus : Bool) (k : ℕ) {m : ℕ} (hm : 1 ≤ m)
    (ha : Admissible plus k m) :
    numerator plus (child plus k m) = 2^(k+1)*m := by
  have he : (3:ℤ)*child plus k m = (2:ℤ)^(k+1)*(m:ℤ)-sign plus := by
    rw [← raw_cast plus k hm]
    exact_mod_cast child_mul plus k m ha
  have hn := numerator_cast plus (child_pos plus k hm ha)
  exact_mod_cast (show (numerator plus (child plus k m):ℤ) =
    (2:ℤ)^(k+1)*(m:ℤ) by linarith)

/-- For a positive odd target, the prescribed exponent removes all powers of two. -/
theorem valuation_of_odd_target (k : ℕ) {m : ℕ} (hm : 1 ≤ m) (ho : Odd m) :
    padicValNat 2 (2^(k+1)*m) = k+1 := by
  have hv : padicValNat 2 m = 0 := padicValNat.eq_zero_of_not_dvd
    (by simp [Nat.dvd_iff_mod_eq_zero, Nat.odd_iff.mp ho])
  rw [padicValNat.mul (by positivity) (by omega), padicValNat.prime_pow, hv, add_zero]

/-- Every admissible candidate returns to its positive odd target under the actual map. -/
theorem child_returns (plus : Bool) (k : ℕ) {m : ℕ} (hm : 1 ≤ m) (ho : Odd m)
    (ha : Admissible plus k m) : oddReturn plus (child plus k m) = m := by
  rw [oddReturn, child_equation plus k hm ha, valuation_of_odd_target k hm ho]
  exact Nat.mul_div_right _ (by positivity)

/-- Multiplying the odd return by the removed power of two recovers the numerator. -/
theorem oddReturn_mul (plus : Bool) (n : ℕ) :
    oddReturn plus n * 2^padicValNat 2 (numerator plus n) = numerator plus n := by
  rw [oddReturn, Nat.mul_comm]
  exact Nat.mul_div_cancel' pow_padicValNat_dvd

/-- Removing powers of two from either signed numerator preserves positivity. -/
theorem oddReturn_pos (plus : Bool) {n : ℕ} (hn : 1 ≤ n) : 0 < oddReturn plus n := by
  have h := numerator_pos plus hn
  rw [← oddReturn_mul plus n] at h
  exact Nat.pos_of_mul_pos_right h

/-- At every positive input, the signed odd return has removed all factors of two. -/
theorem oddReturn_odd (plus : Bool) {n : ℕ} (hn : 1 ≤ n) : Odd (oddReturn plus n) := by
  have hne : numerator plus n ≠ 0 := (numerator_pos plus hn).ne'
  by_contra he
  have hd : 2 ∣ oddReturn plus n := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp he)
  have hdiv : 2 * 2 ^ padicValNat 2 (numerator plus n) ∣
      oddReturn plus n * 2 ^ padicValNat 2 (numerator plus n) :=
    mul_dvd_mul_right hd _
  have hp : 2 ^ (padicValNat 2 (numerator plus n) + 1) ∣ numerator plus n := by
    convert hdiv using 1
    · rw [pow_succ, Nat.mul_comm]
    · exact (oddReturn_mul plus n).symm
  exact (pow_succ_padicValNat_not_dvd hne) hp

/-- An actual positive solution of the affine equation is exactly its admissible candidate. -/
theorem child_of_equation (plus : Bool) (k : ℕ) {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (he : numerator plus n = 2^(k+1)*m) :
    Admissible plus k m ∧ child plus k m = n := by
  have hi : (raw plus k m : ℤ) = 3*(n:ℤ) := by
    rw [raw_cast plus k hm]
    have h := numerator_cast plus hn
    rw [he] at h
    push_cast at h
    linarith
  have hr : raw plus k m = 3*n := by exact_mod_cast hi
  exact ⟨by simp [Admissible, hr], by simp [child, hr]⟩

/-- Admissible positive halving exponents enumerate all actual positive odd predecessors. -/
theorem predecessor_iff (plus : Bool) {m n : ℕ} (hm : 1 ≤ m) (hmo : Odd m) :
    (1 ≤ n ∧ Odd n ∧ oddReturn plus n = m) ↔
      ∃ k : ℕ, Admissible plus k m ∧ child plus k m = n := by
  constructor
  · rintro ⟨hn, hno, he⟩
    have hv : 1 ≤ padicValNat 2 (numerator plus n) :=
      one_le_padicValNat_of_dvd (by have := numerator_pos plus hn; omega)
        (numerator_even plus hn hno)
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : padicValNat 2 (numerator plus n) ≠ 0)
    have hmul := oddReturn_mul plus n
    rw [he, hk, Nat.mul_comm] at hmul
    exact ⟨k, child_of_equation plus k hm hn hmul.symm⟩
  · rintro ⟨k, ha, rfl⟩
    exact ⟨child_pos plus k hm ha, child_odd plus k hm ha, child_returns plus k hm hmo ha⟩

/-- Distinct admissible halving exponents give distinct predecessors of a positive odd target. -/
theorem child_injective (plus : Bool) {m : ℕ} (hm : 1 ≤ m) (hmo : Odd m)
    {k l : ℕ} (hk : Admissible plus k m) (hl : Admissible plus l m)
    (he : child plus k m = child plus l m) : k = l := by
  have h1 := congrArg (fun n => padicValNat 2 (numerator plus n)) he
  rw [child_equation plus k hm hk, child_equation plus l hm hl,
    valuation_of_odd_target k hm hmo, valuation_of_odd_target l hm hmo] at h1
  omega

/-- The canonical natural residue satisfies the corresponding signed integer congruence. -/
theorem residue_congr (r m : ℕ) :
    ((residue r m).val:ℤ) ≡ (m:ℤ) [ZMOD (3:ℤ)^r] := by
  have hn : (residue r m).val ≡ m [MOD 3^r] := by simp [residue, Nat.ModEq]
  exact_mod_cast (Int.natCast_modEq_iff.mpr hn)

/-- The coefficient parent relation is the inverse-numerator congruence at a positive target. -/
theorem parent_raw_iff (plus : Bool) (r k : ℕ) {m : ℕ} (hm : 1 ≤ m) (b : Level r) :
    parent plus r k b = residue (r+1) m ↔
      raw plus k m ≡ 3*b.val [MOD 3^(r+1)] := by
  rw [parent_signed_iff]
  have hc := (residue_congr (r+1) m).mul_left ((2:ℤ)^(k+1))
  constructor
  · intro h
    have ht := (hc.symm.trans h).sub (Int.ModEq.refl (sign plus))
    have hi : (raw plus k m:ℤ) ≡ 3*(b.val:ℤ) [ZMOD (3:ℤ)^(r+1)] := by
      simpa [raw_cast plus k hm] using ht
    exact Int.natCast_modEq_iff.mp (by simpa using hi)
  · intro h
    have hi : (raw plus k m:ℤ) ≡ 3*(b.val:ℤ) [ZMOD (3:ℤ)^(r+1)] := by
      exact_mod_cast (Int.natCast_modEq_iff.mpr h)
    have ht := hi.add (Int.ModEq.refl (sign plus))
    have he : (2:ℤ)^(k+1)*(m:ℤ) ≡ 3*(b.val:ℤ)+sign plus [ZMOD (3:ℤ)^(r+1)] := by
      simpa [raw_cast plus k hm] using ht
    exact hc.trans he

/-- A coefficient branch exists exactly for an admissible actual child with the specified residue. -/
theorem parent_child_iff (plus : Bool) (r k : ℕ) {m : ℕ} (hm : 1 ≤ m) (b : Level r) :
    parent plus r k b = residue (r+1) m ↔
      Admissible plus k m ∧ residue r (child plus k m) = b := by
  rw [parent_raw_iff plus r k hm]
  constructor
  · intro h
    have hd : 3 ∣ 3^(r+1) := by exact ⟨3^r, by rw [pow_succ]; ring⟩
    have ht := h.of_dvd hd
    have ha : Admissible plus k m := by
      rw [Admissible, Nat.dvd_iff_mod_eq_zero]
      simpa [Nat.ModEq] using ht
    refine ⟨ha, ?_⟩
    rw [← child_mul plus k m ha, pow_succ, Nat.mul_comm (3^r) 3] at h
    have hc : child plus k m ≡ b.val [MOD 3^r] :=
      Nat.ModEq.mul_left_cancel' (by norm_num : 3 ≠ 0) h
    apply Fin.ext
    exact Eq.trans hc (Nat.mod_eq_of_lt b.isLt)
  · rintro ⟨ha, hb⟩
    have hc : child plus k m ≡ b.val [MOD 3^r] := by
      simpa [residue, Nat.ModEq, Nat.mod_eq_of_lt b.isLt] using congrArg Fin.val hb
    have ht := hc.mul_left' 3
    simpa [child_mul plus k m ha, pow_succ, Nat.mul_comm (3^r) 3] using ht

/-- The periodic child weight on an admissible branch, and zero otherwise. -/
def branchWeight (plus : Bool) (r k : ℕ) (h : Level r → ℝ) (m : ℕ) : ℝ :=
  if Admissible plus k m then h (residue r (child plus k m)) else 0

/-- The homogeneous row equals its coefficient times the actual child weight. -/
theorem row_eq_branchWeight (plus : Bool) (r k : ℕ) (h : Level r → ℝ)
    {m : ℕ} (hm : 1 ≤ m) :
    row plus r k h (residue (r+1) m) = coefficient k * branchWeight plus r k h m := by
  unfold row branchWeight
  simp_rw [parent_child_iff plus r k hm]
  by_cases ha : Admissible plus k m <;> simp [ha]

/-- The reciprocal-weighted candidate at one admissible exponent, and zero otherwise. -/
def actualTerm (plus : Bool) (r : ℕ) (h : Level r → ℝ) (m k : ℕ) : ℝ :=
  if Admissible plus k m then h (residue r (child plus k m)) / child plus k m else 0

/-- Sum over all positive halving exponents; at positive odd targets this is actual predecessor mass. -/
def actualMass (plus : Bool) (r : ℕ) (h : Level r → ℝ) (m : ℕ) : ℝ :=
  ∑' k, actualTerm plus r h m k

/-- A bijection between admissible exponents and all actual positive odd predecessors. -/
def predecessorEquiv (plus : Bool) {m : ℕ} (hm : 1 ≤ m) (ho : Odd m) :
    {k : ℕ // Admissible plus k m} ≃ {n : ℕ // 1 ≤ n ∧ Odd n ∧ oddReturn plus n = m} :=
  Equiv.ofBijective (fun k => ⟨child plus k m,
    child_pos plus k hm k.property, child_odd plus k hm k.property,
    child_returns plus k hm ho k.property⟩) (by
      constructor
      · intro k l he
        exact Subtype.ext (child_injective plus hm ho k.property l.property (congrArg Subtype.val he))
      · intro n
        obtain ⟨k, hk, he⟩ := (predecessor_iff plus hm ho).mp n.property
        exact ⟨⟨k,hk⟩, Subtype.ext he⟩)

/-- The exponent-indexed mass equals the literal sum over actual predecessors, without multiplicity. -/
theorem actualMass_predecessors (plus : Bool) (r : ℕ) (h : Level r → ℝ)
    {m : ℕ} (hm : 1 ≤ m) (ho : Odd m) :
    actualMass plus r h m =
      ∑' n : {n : ℕ // 1 ≤ n ∧ Odd n ∧ oddReturn plus n = m}, h (residue r n.val)/n.val := by
  rw [← (predecessorEquiv plus hm ho).tsum_eq (fun n => h (residue r n.val)/(n.val:ℝ))]
  change (∑' k : ℕ, if Admissible plus k m then
    h (residue r (child plus k m)) / (child plus k m:ℝ) else 0) =
    ∑' k : {k : ℕ // Admissible plus k m}, h (residue r (child plus k.val m)) / (child plus k.val m:ℝ)
  simpa only [Set.coe_ofPred, Set.indicator_apply, Set.mem_ofPred_eq] using
    (_root_.tsum_subtype {k : ℕ | Admissible plus k m}
      (fun k : ℕ => h (residue r (child plus k m))/(child plus k m:ℝ))).symm

/-- The exact affine denominator of each weighted reciprocal predecessor term. -/
theorem actualTerm_formula (plus : Bool) (r k : ℕ) (h : Level r → ℝ)
    {m : ℕ} (hm : 1 ≤ m) :
    actualTerm plus r h m k =
      3*branchWeight plus r k h m / ((2:ℝ)^(k+1)*m-(sign plus:ℝ)) := by
  by_cases ha : Admissible plus k m
  · have he : (3:ℝ)*child plus k m = (2:ℝ)^(k+1)*m-(sign plus:ℝ) := by
      have hc : (3:ℤ)*child plus k m = (2:ℤ)^(k+1)*(m:ℤ)-sign plus := by
        rw [← raw_cast plus k hm]
        exact_mod_cast child_mul plus k m ha
      exact_mod_cast hc
    have hn : (0:ℝ) < child plus k m := by exact_mod_cast child_pos plus k hm ha
    simp only [actualTerm, branchWeight, ha, ↓reduceIte, ← he]
    field_simp
  · simp [actualTerm, branchWeight, ha]

/-- Projecting an integer residue to a lower ternary level recovers its residue there. -/
theorem project_residue (r d m : ℕ) : project r d (residue (r+d) m) = residue r m := by
  apply Fin.ext
  exact Nat.mod_mod_of_dvd m (Nat.pow_dvd_pow 3 (by omega))

/-- Pointwise comparison on positive integer representatives passes through
the complete signed inverse operator, even for different ternary levels. -/
theorem transfer_le_of_residue_le (plus : Bool) {r t : ℕ}
    {h : Level r → ℝ} {g : Level t → ℝ}
    (hh : ∀ b, 0 ≤ h b) (hg : ∀ b, 0 ≤ g b)
    (hle : ∀ n, 1 ≤ n → h (residue r n) ≤ g (residue t n))
    {m : ℕ} (hm : 1 ≤ m) :
    transfer plus r h (residue (r+1) m) ≤
      transfer plus t g (residue (t+1) m) := by
  apply Summable.tsum_le_tsum _ (row_summable plus r hh _) (row_summable plus t hg _)
  intro k
  rw [row_eq_branchWeight plus r k h hm, row_eq_branchWeight plus t k g hm]
  apply mul_le_mul_of_nonneg_left _ (by unfold coefficient; positivity)
  unfold branchWeight
  split_ifs with ha
  · exact hle _ (child_pos plus k hm ha)
  · exact le_rfl

end Problems.Collatz.FibreActual

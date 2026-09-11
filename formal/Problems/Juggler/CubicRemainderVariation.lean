import Mathlib

namespace Problems.Juggler.CubicRemainderVariation

open scoped BigOperators

/-- A positive zero-correction product transports the exact 2-adic valuation. -/
theorem valuation_balance {N B l l' : ℕ}
    (hN : 0 < N) (hB : 0 < B) (hl : 0 < l) (hl' : 0 < l')
    (hodd : N % 2 = 1) (heq : N * l = B * l') :
    padicValNat 2 l = padicValNat 2 B + padicValNat 2 l' := by
  have hndvd : ¬2 ∣ N := by omega
  have hval : padicValNat 2 N = 0 := padicValNat.eq_zero_of_not_dvd hndvd
  have h := congrArg (padicValNat 2) heq
  rw [padicValNat.mul (Nat.ne_of_gt hN) (Nat.ne_of_gt hl),
    padicValNat.mul (Nat.ne_of_gt hB) (Nat.ne_of_gt hl'), hval, zero_add] at h
  exact h

/-- An odd numerator cannot increase the target valuation in an exact product. -/
theorem valuation_target_le_source {N B l l' : ℕ}
    (hN : 0 < N) (hB : 0 < B) (hl : 0 < l) (hl' : 0 < l')
    (hodd : N % 2 = 1) (heq : N * l = B * l') :
    padicValNat 2 l' ≤ padicValNat 2 l := by
  have h := valuation_balance hN hB hl hl' hodd heq
  omega

/-- A positive even denominator forces a strict valuation drop. -/
theorem valuation_drop {N B l l' : ℕ}
    (hN : 0 < N) (hB : 0 < B) (hl : 0 < l) (hl' : 0 < l')
    (hodd : N % 2 = 1) (heven : B % 2 = 0)
    (heq : N * l = B * l') :
    padicValNat 2 l' < padicValNat 2 l := by
  have h := valuation_balance hN hB hl hl' hodd heq
  have hdiv : 2 ∣ B := Nat.dvd_of_mod_eq_zero heven
  have hpos : 1 ≤ padicValNat 2 B := one_le_padicValNat_of_dvd (by omega) hdiv
  omega

/-- Outside the reset set the potential never increases, and outside
both distinguished sets it drops by at least one. -/
theorem card_le_exception_add_reset {ι : Type*} [Fintype ι] [DecidableEq ι]
    (next : Equiv.Perm ι) (v : ι → ℕ) (H : ℕ) (E T : Finset ι)
    (hv : ∀ i, v i ≤ H)
    (hnoninc : ∀ i, i ∉ T → v (next i) ≤ v i)
    (hdrop : ∀ i, i ∉ E → i ∉ T → v (next i) + 1 ≤ v i) :
    Fintype.card ι ≤ E.card + (H + 1) * T.card := by
  have hpoint (i : ι) :
      1 + v (next i) ≤ v i + (if i ∈ E then 1 else 0) +
        (H + 1) * (if i ∈ T then 1 else 0) := by
    by_cases ht : i ∈ T
    · simp only [if_pos ht, mul_one]
      have h := hv (next i)
      omega
    · simp only [if_neg ht, mul_zero, add_zero]
      by_cases he : i ∈ E
      · simp only [if_pos he]
        have h := hnoninc i ht
        omega
      · simp only [if_neg he, add_zero]
        have h := hdrop i he ht
        omega
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpoint i)
  simp [Finset.sum_add_distrib, Finset.sum_ite_mem, Equiv.sum_comp] at hsum
  have hcomm : T.card * (H + 1) = (H + 1) * T.card := Nat.mul_comm _ _
  omega

/-- If every non-reset edge strictly drops, no exceptional allowance is needed. -/
theorem strict_off_reset_count {ι : Type*} [Fintype ι] [DecidableEq ι]
    (next : Equiv.Perm ι) (v : ι → ℕ) (H : ℕ) (T : Finset ι)
    (hv : ∀ i, v i ≤ H)
    (hdrop : ∀ i, i ∉ T → v (next i) + 1 ≤ v i) :
    Fintype.card ι ≤ (H + 1) * T.card := by
  have hnoninc : ∀ i, i ∉ T → v (next i) ≤ v i := by
    intro i hi
    have h := hdrop i hi
    omega
  simpa using card_le_exception_add_reset next v H ∅ T hv hnoninc
    (fun i _ hi => hdrop i hi)

/-- A deviation can affect its own edge and the edge preceding it. -/
theorem reset_card_le_boundary_add_twice {ι : Type*} [DecidableEq ι]
    (T boundary S : Finset ι) (pred : ι → ι)
    (hcover : T ⊆ boundary ∪ S ∪ S.image pred) :
    T.card ≤ boundary.card + 2 * S.card := by
  calc
    T.card ≤ (boundary ∪ S ∪ S.image pred).card := Finset.card_le_card hcover
    _ ≤ (boundary ∪ S).card + (S.image pred).card := Finset.card_union_le _ _
    _ ≤ (boundary.card + S.card) + S.card :=
      Nat.add_le_add (Finset.card_union_le _ _) Finset.card_image_le
    _ = boundary.card + 2 * S.card := by omega

/-- Two possible non-dropping edges and three block boundaries give a
quantitative lower bound on the number of remainder deviations. -/
theorem card_le_three_block_deviations {ι : Type*} [Fintype ι] [DecidableEq ι]
    (next : Equiv.Perm ι) (v : ι → ℕ) (H : ℕ)
    (E T boundary S : Finset ι) (pred : ι → ι)
    (hv : ∀ i, v i ≤ H)
    (hnoninc : ∀ i, i ∉ T → v (next i) ≤ v i)
    (hdrop : ∀ i, i ∉ E → i ∉ T → v (next i) + 1 ≤ v i)
    (hE : E.card ≤ 2) (hboundary : boundary.card ≤ 3)
    (hcover : T ⊆ boundary ∪ S ∪ S.image pred) :
    Fintype.card ι ≤ 2 + (H + 1) * (3 + 2 * S.card) := by
  have hT : T.card ≤ 3 + 2 * S.card := by
    exact (reset_card_le_boundary_add_twice T boundary S pred hcover).trans
      (Nat.add_le_add_right hboundary _)
  exact (card_le_exception_add_reset next v H E T hv hnoninc hdrop).trans
    (Nat.add_le_add hE (Nat.mul_le_mul_left (H + 1) hT))

/-- Strict drop off the reset set gives the three-block bound without an
exceptional-edge allowance. -/
theorem strict_three_block_deviations {ι : Type*} [Fintype ι] [DecidableEq ι]
    (next : Equiv.Perm ι) (v : ι → ℕ) (H : ℕ)
    (T boundary S : Finset ι) (pred : ι → ι)
    (hv : ∀ i, v i ≤ H)
    (hdrop : ∀ i, i ∉ T → v (next i) + 1 ≤ v i)
    (hboundary : boundary.card ≤ 3)
    (hcover : T ⊆ boundary ∪ S ∪ S.image pred) :
    Fintype.card ι ≤ (H + 1) * (3 + 2 * S.card) := by
  have hT : T.card ≤ 3 + 2 * S.card :=
    (reset_card_le_boundary_add_twice T boundary S pred hcover).trans
      (Nat.add_le_add_right hboundary _)
  exact (strict_off_reset_count next v H T hv hdrop).trans
    (Nat.mul_le_mul_left (H + 1) hT)

/-- Conditional arithmetic consumer: positive gaps satisfy the stated product
identities off T. No orbit extraction or floor-cell assembly is asserted. -/
theorem arithmetic_three_block_deviations {ι : Type*} [Fintype ι] [DecidableEq ι]
    (next : Equiv.Perm ι) (l N B : ι → ℕ) (H : ℕ)
    (T boundary S : Finset ι) (pred : ι → ι)
    (hl : ∀ i, 0 < l i) (hN : ∀ i, 0 < N i) (hB : ∀ i, 0 < B i)
    (hv : ∀ i, padicValNat 2 (l i) ≤ H)
    (hodd : ∀ i, i ∉ T → N i % 2 = 1)
    (heven : ∀ i, i ∉ T → B i % 2 = 0)
    (heq : ∀ i, i ∉ T → N i * l i = B i * l (next i))
    (hboundary : boundary.card ≤ 3)
    (hcover : T ⊆ boundary ∪ S ∪ S.image pred) :
    Fintype.card ι ≤ (H + 1) * (3 + 2 * S.card) := by
  apply strict_three_block_deviations next (fun i => padicValNat 2 (l i)) H
    T boundary S pred hv ?_ hboundary hcover
  intro i hi
  exact Nat.succ_le_of_lt (valuation_drop (hN i) (hB i) (hl i) (hl (next i))
    (hodd i hi) (heven i hi) (heq i hi))

/-- Numerical consequence at the fixed count tuple and valuation ceiling. -/
theorem fixed_count_reset_lower {H T : ℕ} (hH : H ≤ 86)
    (hcount : 780239 ≤ (H + 1) * T) : 8969 ≤ T := by
  by_contra h
  have hT : T ≤ 8968 := by omega
  have hprod : (H + 1) * T ≤ 87 * 8968 :=
    Nat.mul_le_mul (by omega) hT
  omega

/-- Numerical consequence for deviations from three arbitrary constants. -/
theorem fixed_count_deviation_lower {H S : ℕ} (hH : H ≤ 86)
    (hcount : 780239 ≤ (H + 1) * (3 + 2 * S)) : 4483 ≤ S := by
  by_contra h
  have hS : S ≤ 4482 := by omega
  have hprod : (H + 1) * (3 + 2 * S) ≤ 87 * 8967 :=
    Nat.mul_le_mul (by omega) (by omega)
  omega

end Problems.Juggler.CubicRemainderVariation

import Problems.Juggler.CubicRemainderVariation
import Mathlib

/-!
# Arithmetic kernels for filtered valuation resets

The signed difference retains its exact integer value. These lemmas concern
positive products and finite paths; cyclic placement and itinerary counts
are separate hypotheses in the written application.
-/

namespace Problems.Juggler.CubicConstraintFusion

open scoped BigOperators

/-- The signed correction has the same lowest nonzero binary place as the gap. -/
def Critical (l : ℕ) (r : ℤ) : Prop :=
  r ≠ 0 ∧ padicValInt 2 r = padicValNat 2 l

/-- A difference with unequal input valuations takes the smaller valuation. -/
theorem valuation_sub_of_lt {X Y : ℕ} (hX : 0 < X)
    (hlt : padicValNat 2 X < padicValNat 2 Y) :
    (X : ℤ) - Y ≠ 0 ∧
      padicValInt 2 ((X : ℤ) - Y) = padicValNat 2 X := by
  let k := padicValNat 2 X
  have hXdiv : (2 : ℤ) ^ k ∣ (X : ℤ) := by
    exact_mod_cast (pow_padicValNat_dvd (p := 2) (n := X))
  have hYdiv : (2 : ℤ) ^ (k + 1) ∣ (Y : ℤ) := by
    have hd : 2 ^ (k + 1) ∣ Y :=
      dvd_trans (pow_dvd_pow (2 : ℕ) (by omega)) pow_padicValNat_dvd
    exact_mod_cast hd
  have hXnot : ¬(2 : ℤ) ^ (k + 1) ∣ (X : ℤ) := by
    intro hd
    have hn : 2 ^ (k + 1) ∣ X := by exact_mod_cast hd
    exact pow_succ_padicValNat_not_dvd (Nat.ne_of_gt hX) hn
  have hrnot : ¬(2 : ℤ) ^ (k + 1) ∣ ((X : ℤ) - Y) := by
    intro hd
    have hsum := dvd_add hd hYdiv
    have heq : (X : ℤ) - Y + Y = X := by ring
    rw [heq] at hsum
    exact hXnot hsum
  have hrne : (X : ℤ) - Y ≠ 0 := by
    intro heq
    apply hrnot
    rw [heq]
    exact dvd_zero _
  have hrdiv : (2 : ℤ) ^ k ∣ ((X : ℤ) - Y) :=
    dvd_sub hXdiv (dvd_trans (pow_dvd_pow (2 : ℤ) (by omega)) hYdiv)
  have hlo : k ≤ padicValInt 2 ((X : ℤ) - Y) :=
    ((padicValInt_dvd_iff (p := 2) k ((X : ℤ) - Y)).mp hrdiv).resolve_left hrne
  have hhi : padicValInt 2 ((X : ℤ) - Y) < k + 1 := by
    by_contra hn
    apply hrnot
    exact (padicValInt_dvd_iff (p := 2) (k + 1) ((X : ℤ) - Y)).mpr
      (Or.inr (by omega))
  exact ⟨hrne, by omega⟩

/-- A noncritical correction retains the full denominator valuation budget. -/
theorem noncritical_valuation_budget {N B l l' : ℕ} {r : ℤ}
    (hN : 0 < N) (hB : 0 < B) (hl : 0 < l) (hl' : 0 < l')
    (hodd : N % 2 = 1)
    (hr : r = (N : ℤ) * l - (B : ℤ) * l')
    (hnoncritical : ¬Critical l r) :
    padicValNat 2 B + padicValNat 2 l' ≤ padicValNat 2 l := by
  have hndvd : ¬2 ∣ N := by omega
  have hzero : padicValNat 2 N = 0 := padicValNat.eq_zero_of_not_dvd hndvd
  have hleft : padicValNat 2 (N * l) = padicValNat 2 l := by
    rw [padicValNat.mul (Nat.ne_of_gt hN) (Nat.ne_of_gt hl), hzero, zero_add]
  have hright : padicValNat 2 (B * l') =
      padicValNat 2 B + padicValNat 2 l' :=
    padicValNat.mul (Nat.ne_of_gt hB) (Nat.ne_of_gt hl')
  by_contra hn
  have hlt : padicValNat 2 (N * l) < padicValNat 2 (B * l') := by
    rw [hleft, hright]
    omega
  have hc := valuation_sub_of_lt (Nat.mul_pos hN hl) hlt
  have heq : ((N * l : ℕ) : ℤ) - ((B * l' : ℕ) : ℤ) = r := by
    push_cast
    exact hr.symm
  rw [heq, hleft] at hc
  exact hnoncritical hc

/-- An even pair whose difference is divisible by four also has such a sum. -/
theorem even_sum_dvd_four_of_gap {a b : ℕ} (hab : a ≤ b)
    (heven : a % 2 = 0 ∧ b % 2 = 0) (hgap : 4 ∣ b - a) :
    4 ∣ a + b := by
  omega

/-- Per-edge unit drops and extra bonuses add along a finite path. -/
theorem weighted_run_budget (v bonus : ℕ → ℕ) (d : ℕ)
    (hstep : ∀ i < d, v (i + 1) + 1 + bonus i ≤ v i) :
    v d + d + ∑ i ∈ Finset.range d, bonus i ≤ v 0 := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hprev := ih (fun i hi => hstep i (by omega))
    have hlast := hstep d (by omega)
    rw [Finset.sum_range_succ]
    omega

/-- The marginal cost after the terminal even gap, at the fixed rank counts. -/
def runIncrement (t : ℕ) : ℕ := 2 ^ (t + 2 + t * 287963 / 780239)

/-- Lower cost of a block of even gaps; the empty block has cost zero. -/
def runCost (n : ℕ) : ℕ :=
  if n = 0 then 0 else 2 + ∑ t ∈ Finset.range (n - 1), runIncrement t

theorem runIncrement_monotone : Monotone runIncrement := by
  intro a b hab
  have hexp : a + 2 + a * 287963 / 780239 ≤
      b + 2 + b * 287963 / 780239 := by omega
  exact pow_le_pow_right' (by norm_num : 1 ≤ (2 : ℕ)) hexp

theorem runCost_succ {n : ℕ} (hn : 0 < n) :
    runCost (n + 1) = runCost n + runIncrement (n - 1) := by
  have hn' : n - 1 + 1 = n := by omega
  have hsum := Finset.sum_range_succ runIncrement (n - 1)
  rw [hn'] at hsum
  simp only [runCost, if_neg (by omega : n + 1 ≠ 0),
    if_neg (Nat.ne_of_gt hn), Nat.add_sub_cancel_right]
  rw [hsum]
  omega

/-- A supporting affine line touches the block cost at lengths 53 and 54. -/
theorem runCost_affine_53 {n : ℕ} (hn : 0 < n) :
    runCost 53 + n * runIncrement 52 ≤ runCost n + 53 * runIncrement 52 := by
  have hleft (n : ℕ) (hle : n ≤ 53) : 0 < n →
      runCost 53 + n * runIncrement 52 ≤ runCost n + 53 * runIncrement 52 := by
    apply Nat.decreasingInduction (n := 53)
      (motive := fun k _ => 0 < k →
        runCost 53 + k * runIncrement 52 ≤ runCost k + 53 * runIncrement 52)
      ?_ ?_ hle
    · intro k hk ih hkpos
      have hih := ih (by omega)
      rw [runCost_succ hkpos] at hih
      have hinc : runIncrement (k - 1) ≤ runIncrement 52 :=
        runIncrement_monotone (by omega)
      simp only [Nat.add_mul, one_mul] at hih
      omega
    · intro _
      omega
  have hright (n : ℕ) (hle : 53 ≤ n) :
      runCost 53 + n * runIncrement 52 ≤ runCost n + 53 * runIncrement 52 := by
    induction n, hle using Nat.le_induction with
    | base => omega
    | succ k hk ih =>
      rw [runCost_succ (by omega : 0 < k)]
      have hinc : runIncrement 52 ≤ runIncrement (k - 1) :=
        runIncrement_monotone (by omega)
      simp only [Nat.add_mul, one_mul]
      omega
  rcases le_total n 53 with h | h
  · exact hleft n h hn
  · exact hright n h

theorem runIncrement_52 : runIncrement 52 = 9444732965739290427392 := by
  norm_num [runIncrement]

theorem runCost_53 : runCost 53 = 4387864922893216308702 := by
  norm_num [runCost, runIncrement, Finset.sum_range_succ]

theorem runCost_54 : runCost 54 = 13832597888632506736094 := by
  rw [show 54 = 53 + 1 from rfl, runCost_succ (by omega), runCost_53,
    show 53 - 1 = 52 from rfl, runIncrement_52]

/-- Sum a supplied affine lower cost over one finite family of blocks. -/
theorem affine_block_cost_sum {ι : Type*} [Fintype ι]
    (length cost : ι → ℕ) (A slope q oddGap totalGap : ℕ)
    (hcost : ∀ i, A + length i * slope ≤ cost i + q * slope)
    (hbudget : oddGap + ∑ i, cost i ≤ totalGap) :
    Fintype.card ι * A + (∑ i, length i) * slope + oddGap ≤
      totalGap + Fintype.card ι * (q * slope) := by
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hcost i)
  simp [Finset.sum_add_distrib, ← Finset.sum_mul] at hs
  omega

/-- Consume actual block-cost lower bounds without assuming cyclic extraction. -/
theorem run_cost_affine_budget {ι : Type*} [Fintype ι]
    (length cost : ι → ℕ) (totalGap : ℕ)
    (hlength : ∀ i, 0 < length i)
    (hcost : ∀ i, runCost (length i) ≤ cost i)
    (hbudget : 4 + ∑ i, cost i ≤ totalGap) :
    Fintype.card ι * runCost 53 + (∑ i, length i) * runIncrement 52 + 4 ≤
      totalGap + Fintype.card ι * (53 * runIncrement 52) := by
  apply affine_block_cost_sum length cost (runCost 53) (runIncrement 52) 53
    4 totalGap ?_ hbudget
  intro i
  exact (runCost_affine_53 (hlength i)).trans
    (Nat.add_le_add_right (hcost i) _)

/-- The exact fixed-tuple scalar budget forces at least 14569 blocks. -/
theorem fixed_critical_count_lower {C totalGap : ℕ}
    (hgap : totalGap ≤ 519999999 ^ 3 - 519999999)
    (hcost : C * runCost 53 + 780237 * runIncrement 52 + 4 ≤
      totalGap + C * (53 * runIncrement 52)) : 14569 ≤ C := by
  rw [runCost_53, runIncrement_52] at hcost
  norm_num at hgap hcost
  omega

/-- Conditional arithmetic consumer for positive block lengths and gap costs. -/
theorem fixed_run_budget_critical_count_lower {ι : Type*} [Fintype ι]
    (length cost : ι → ℕ) (totalGap : ℕ)
    (hlength : ∀ i, 0 < length i) (hsum : ∑ i, length i = 780237)
    (hcost : ∀ i, runCost (length i) ≤ cost i)
    (hbudget : 4 + ∑ i, cost i ≤ totalGap)
    (hgap : totalGap ≤ 519999999 ^ 3 - 519999999) :
    14569 ≤ Fintype.card ι := by
  apply fixed_critical_count_lower hgap
  simpa only [hsum] using run_cost_affine_budget length cost totalGap
    hlength hcost hbudget

/-- Numerical support adapter; the support inequality is an explicit input. -/
theorem fixed_deviation_lower {C S : ℕ} (hC : 14569 ≤ C)
    (hcover : C ≤ 1 + 2 * S) : 7284 ≤ S := by
  omega

/-- Numerical filter adapter; the two additional corrections are explicit inputs. -/
theorem fixed_nonzero_lower {C T : ℕ} (hC : 14569 ≤ C)
    (hfilter : C + 2 ≤ T) : 14571 ≤ T := by
  omega

end Problems.Juggler.CubicConstraintFusion

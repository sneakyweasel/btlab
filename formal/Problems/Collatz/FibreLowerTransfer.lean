import Problems.Collatz.FibreLocalBounds

/-! # Transporting lower bounds from a fixed ternary class

Every positive odd unit has an actual one-step predecessor in any specified
class modulo `3^r`, with halving exponent at most `2*3^r`. Consequently a
lower bound uniform on one fixed class implies a global unit-root lower
bound after one depth shift and a fixed positive loss. This produces no
arithmetic lower bound at a fixed ordinary integer.
-/

noncomputable section

namespace Problems.Collatz.FibreLowerTransfer

open Finset FibreMass FibreActual FibreUnitComparison
open scoped Classical

/-- A uniform coefficient allowance for reaching a class modulo `3^r`
through one actual inverse step. It can be very small but is positive. -/
def stepCost (r : ℕ) : ℝ := 3 / (2:ℝ)^(2*3^r)

/-- The transport allowance is strictly positive at every fixed level. -/
theorem stepCost_pos (r : ℕ) : 0 < stepCost r := by
  unfold stepCost
  positivity

/-- Every positive odd unit target has an actual predecessor in every
ternary residue class. Its exact halving exponent is at most `2*3^r`.
The chosen exponent and predecessor do not depend on any later depth. -/
theorem exists_predecessor_in_residue (plus : Bool) (r : ℕ) (b : Level r)
    {a : ℕ} (ha : 1 ≤ a) (ho : Odd a) (hu : a % 3 ≠ 0) :
    ∃ k : ℕ, k < 2*3^r ∧ Admissible plus k a ∧
      residue r (child plus k a) = b ∧
      1 ≤ child plus k a ∧ Odd (child plus k a) ∧
      oddReturn plus (child plus k a) = a := by
  have h2 : (2*a) % 3 ≠ 0 := by omega
  have he : (3*b.val + offset plus r) % 3 ≠ 0 := by
    simpa using offset_unit plus r
  obtain ⟨k, hlt, hk⟩ := FibreLocalBounds.exists_bounded_power_mul r
    (2*a) (3*b.val + offset plus r) h2 he
  have hp : parent plus r k b = residue (r+1) a := by
    apply (parent_iff plus r k _ _).mpr
    have hk' : 2^(k+1)*a ≡ 3*b.val + offset plus r [MOD 3^(r+1)] := by
      simpa only [pow_succ, Nat.mul_assoc] using hk
    simpa only [residue, Nat.ModEq, Nat.mul_mod_mod] using hk'
  obtain ⟨had, hb⟩ := (parent_child_iff plus r k ha b).mp hp
  exact ⟨k, hlt, had, hb, child_pos plus k ha had,
    child_odd plus k ha had, child_returns plus k ha ho had⟩

/-- One admissible inverse branch gives a lower bound for the complete
coefficient at its target. Every other branch is retained by positivity. -/
theorem coarse_branch_lower (plus : Bool) (k d : ℕ) {a : ℕ}
    (ha : 1 ≤ a) (hk : Admissible plus k a) :
    coefficient k * coarse plus d (child plus k a) ≤ coarse plus (d+1) a := by
  have hf := iterate_nonneg plus 1 (fun _ => by norm_num : ∀ _ : Level 1, (0:ℝ) ≤ 1) d
  have ht := (row_summable plus (1+d) hf (residue (1+d+1) a)).le_tsum k
    (fun j _ => row_nonneg plus (1+d) j hf _)
  rw [row_eq_branchWeight plus (1+d) k _ ha, branchWeight, if_pos hk] at ht
  exact ht

private theorem stepCost_le_coefficient (r k : ℕ) (hk : k < 2*3^r) :
    stepCost r ≤ coefficient k := by
  rw [coefficient_eq]
  unfold stepCost
  have hp : (2:ℝ)^(k+1) ≤ (2:ℝ)^(2*3^r) := by
    exact pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega : k+1 ≤ 2*3^r)
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hp

/-- A single genuine predecessor in the prescribed class transports all
depth coefficients simultaneously, at a cost depending only on the class
modulus. No nonperiodicity or lower-count assumption is used. -/
theorem exists_coarse_lower_transport (plus : Bool) (r : ℕ) (b : Level r)
    {a : ℕ} (ha : 1 ≤ a) (ho : Odd a) (hu : a % 3 ≠ 0) :
    ∃ m : ℕ, 1 ≤ m ∧ Odd m ∧ residue r m = b ∧ oddReturn plus m = a ∧
      ∀ d : ℕ, stepCost r * coarse plus d m ≤ coarse plus (d+1) a := by
  obtain ⟨k, hk, had, hb, hm, hmo, hr⟩ := exists_predecessor_in_residue plus r b ha ho hu
  refine ⟨child plus k a, hm, hmo, hb, hr, fun d => ?_⟩
  exact (mul_le_mul_of_nonneg_right (stepCost_le_coefficient r k hk)
    (coarse_nonneg plus d _)).trans (coarse_branch_lower plus k d ha had)

/-- A coefficient-sum lower bound valid at every positive odd integer in
one fixed ternary class transfers to every positive odd unit root, with
the same depth set shifted by one. The premise is a uniform local bound. -/
theorem block_lower_transport (plus : Bool) (r : ℕ) (b : Level r)
    (I : Finset ℕ) (L : ℝ)
    (hL : ∀ m : ℕ, 1 ≤ m → Odd m → residue r m = b →
      L ≤ ∑ d ∈ I, coarse plus d m)
    {a : ℕ} (ha : 1 ≤ a) (ho : Odd a) (hu : a % 3 ≠ 0) :
    stepCost r * L ≤ ∑ d ∈ I, coarse plus (d+1) a := by
  obtain ⟨m, hm, hmo, hb, _, ht⟩ := exists_coarse_lower_transport plus r b ha ho hu
  calc
    stepCost r * L ≤ stepCost r * ∑ d ∈ I, coarse plus d m :=
      mul_le_mul_of_nonneg_left (hL m hm hmo hb) (stepCost_pos r).le
    _ = ∑ d ∈ I, stepCost r * coarse plus d m := by rw [mul_sum]
    _ ≤ ∑ d ∈ I, coarse plus (d+1) a := sum_le_sum (fun d _ => ht d)

private theorem predecessor_nonperiodic (plus : Bool) {m a : ℕ}
    (hr : oddReturn plus m = a)
    (ha : ∀ d : ℕ, 0 < d → (oddReturn plus)^[d] a ≠ a) :
    ∀ d : ℕ, 0 < d → (oddReturn plus)^[d] m ≠ m := by
  intro d hd he
  apply ha d hd
  rw [← hr, ← Function.iterate_succ_apply, Function.iterate_succ_apply', he]

private theorem summable_of_lower_transport {f g : ℕ → ℝ} {c : ℝ}
    (hc : 0 < c) (hf : ∀ d, 0 ≤ f d) (h : ∀ d, c * f d ≤ g (d+1))
    (hg : Summable g) : Summable f := by
  have hs : Summable (fun d => c * f d) :=
    Summable.of_nonneg_of_le (fun d => mul_nonneg hc.le (hf d)) h
      ((summable_nat_add_iff 1).mpr hg)
  simpa [hc.ne'] using hs.mul_left c⁻¹

/-- If the coefficient series diverges at every nonperiodic positive odd
integer in one fixed class, it diverges at every nonperiodic positive odd
unit root. This is a conditional transport; no local divergence is proved. -/
theorem nonsummable_of_residue (plus : Bool) (r : ℕ) (b : Level r)
    (hlocal : ∀ m : ℕ, 1 ≤ m → Odd m → residue r m = b →
      (∀ d : ℕ, 0 < d → (oddReturn plus)^[d] m ≠ m) →
      ¬Summable (fun d => coarse plus d m))
    {a : ℕ} (ha : 1 ≤ a) (ho : Odd a) (hu : a % 3 ≠ 0)
    (hnp : ∀ d : ℕ, 0 < d → (oddReturn plus)^[d] a ≠ a) :
    ¬Summable (fun d => coarse plus d a) := by
  obtain ⟨m, hm, hmo, hb, hr, ht⟩ := exists_coarse_lower_transport plus r b ha ho hu
  intro hs
  exact hlocal m hm hmo hb (predecessor_nonperiodic plus hr hnp)
    (summable_of_lower_transport (stepCost_pos r) (fun d => coarse_nonneg plus d m) ht hs)

/-- Divergence at every nonperiodic integer in a fixed unit class is
equivalent to divergence at all nonperiodic positive odd unit roots.
Local constants may depend on the integer; neither side is established here. -/
theorem nonsummable_on_residue_iff (plus : Bool) {r : ℕ} (hr : 1 ≤ r)
    (b : Level r) (hb : b.val % 3 ≠ 0) :
    (∀ m : ℕ, 1 ≤ m → Odd m → residue r m = b →
      (∀ d : ℕ, 0 < d → (oddReturn plus)^[d] m ≠ m) →
      ¬Summable (fun d => coarse plus d m)) ↔
    (∀ a : ℕ, 1 ≤ a → Odd a → a % 3 ≠ 0 →
      (∀ d : ℕ, 0 < d → (oddReturn plus)^[d] a ≠ a) →
      ¬Summable (fun d => coarse plus d a)) := by
  constructor
  · intro h a ha ho hu hnp
    exact nonsummable_of_residue plus r b h ha ho hu hnp
  · intro h m hm ho he hnp
    have hv := congrArg Fin.val he
    change m % 3^r = b.val at hv
    have ht := congrArg (fun n : ℕ => n % 3) hv
    rw [Nat.mod_mod_of_dvd _ (dvd_pow_self 3 (by omega : r ≠ 0))] at ht
    exact h m hm ho (by simpa only [ht] using hb) hnp

end Problems.Collatz.FibreLowerTransfer

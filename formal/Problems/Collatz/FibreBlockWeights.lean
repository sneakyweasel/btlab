import Problems.Collatz.FibreRootBounds

/-! # Normalization loss for positive generation blocks

The natural geometric sum of complete inverse generations has exponential
residue peaks. Its maximum-normalized value at a fixed nonperiodic integer
cannot retain the critical prefactor, even if the block rates approach one.
-/

noncomputable section

namespace Problems.Collatz.FibreBlockWeights

open Finset FibreMass FibreActual FibreHeightBudget FibreRootBounds Filter
open scoped Classical Topology

private theorem unit_nonneg : ∀ b, 0 ≤ FibreGeneration.unitWeight b := by
  intro b; unfold FibreGeneration.unitWeight; split_ifs <;> norm_num

private theorem unit_sum : (∑ b, FibreGeneration.unitWeight b) = 2 := by
  change (∑ b : Fin 3, if b.val % 3 = 0 then (0:ℝ) else 1) = 2
  norm_num [Fin.sum_univ_succ]

private def lowClass (plus : Bool) : Fin 3 := if plus then 1 else 2

private theorem coset_sum (r : ℕ) (c : Fin 3) (v : ℝ) :
    (∑ a : Level (r+1), if a.val % 3 = c.val then v else 0) = (3:ℝ)^r*v := by
  let e : Fin (3^r) × Fin 3 ≃ Level (r+1) :=
    finProdFinEquiv.trans (finCongr (by rw [pow_succ]))
  have he (i : Fin (3^r) × Fin 3) : (e i).val % 3 = i.2.val := by
    change (i.2.val+3*i.1.val) % 3 = i.2.val
    simp [Nat.add_mod, Nat.mod_eq_of_lt i.2.isLt]
  rw [← e.sum_comp (fun a => if a.val % 3 = c.val then v else 0)]
  simp_rw [he, Fin.val_inj]
  simp [Fintype.sum_prod_type]

private theorem small_rows_zero (plus : Bool) (r : ℕ) (h : Level r → ℝ)
    (a : Level (r+1)) (ha : a.val % 3 = (lowClass plus).val) :
    row plus r 0 h a = 0 ∧ row plus r 2 h a = 0 := by
  have hn (k : ℕ) (hk : k = 0 ∨ k = 2) (b : Level r) : parent plus r k b ≠ a := by
    intro he
    have hp := ((parent_iff plus r k a b).mp he).of_dvd
      (show 3 ∣ 3^(r+1) by exact ⟨3^r, by rw [pow_succ]; ring⟩)
    have hoff : offset plus r % 3 = (lowClass plus).val := by
      cases plus
      · have hpos : 0 < 3^(r+1) := by positivity
        have hmod : 3^(r+1) % 3 = 0 := by simp [pow_succ]
        simp only [offset, lowClass, Bool.false_eq_true, ↓reduceIte]
        norm_num
        omega
      · norm_num [offset, lowClass]
    rcases hk with rfl | rfl <;>
      norm_num [Nat.ModEq, Nat.add_mod, Nat.mul_mod, ha, hoff] at hp <;>
      cases plus <;> norm_num [lowClass] at hp
  constructor <;> simp [row, hn]

/-- A uniform lower bound on one complete unit-generation table is at most
three quarters. Two explicit odd-halving branches already force this deficit
in the opposite first-digit class; the exact class mean is not needed. -/
theorem block_floor_le (plus : Bool) (d : ℕ) {t : ℝ}
    (ht : ∀ a : Level (1+(d+1)), a.val % 3 ≠ 0 →
      t ≤ iterate plus 1 FibreGeneration.unitWeight (d+1) a) : t ≤ 3/4 := by
  let h := iterate plus 1 FibreGeneration.unitWeight d
  have hh := iterate_nonneg plus 1 unit_nonneg d
  have hl (a : Level (1+d+1)) :
      row plus (1+d) 0 h a + row plus (1+d) 2 h a +
        (if a.val % 3 = (lowClass plus).val then t else 0) ≤ transfer plus (1+d) h a := by
    by_cases ha : a.val % 3 = (lowClass plus).val
    · obtain ⟨h0,h2⟩ := small_rows_zero plus (1+d) h a ha
      rw [h0, h2, if_pos ha, zero_add, zero_add]
      apply ht a
      rw [ha]
      cases plus <;> norm_num [lowClass]
    · rw [if_neg ha, add_zero]
      have hb := (row_summable plus (1+d) hh a).sum_le_tsum ({0,2}:Finset ℕ)
        (fun k hk => row_nonneg plus (1+d) k hh a)
      simpa [transfer] using hb
  have hs := sum_le_sum (s := univ) (fun a _ => hl a)
  simp_rw [sum_add_distrib] at hs
  rw [row_sum, row_sum, coset_sum, transfer_sum plus (1+d) hh] at hs
  have he : ∑ a, h a = (3:ℝ)^d*2 := by
    exact (iterate_sum plus 1 unit_nonneg d).trans (by rw [unit_sum])
  rw [he] at hs
  norm_num [coefficient, pow_succ, pow_add] at hs
  have hp : (0:ℝ) < 3^d := by positivity
  nlinarith

/-- The geometric block of length `d+1`, before normalization. Its terminal
generation has coefficient one, so its residue peak grows exponentially. -/
def blockWeight (plus : Bool) (d : ℕ) (q : ℝ) (b : Level (d+1)) : ℝ :=
  ∑ k ∈ range (d+1), q^(d-k) * kernel plus k b.val

/-- The supremum norm is the maximum of this finite nonnegative table when
q is nonnegative. This is the normalizer used in the proposed construction. -/
def blockNormalizer (plus : Bool) (d : ℕ) (q : ℝ) : ℝ := ‖blockWeight plus d q‖

private theorem kernel_nonneg (plus : Bool) (d a : ℕ) : 0 ≤ kernel plus d a :=
  iterate_nonneg plus 1 unit_nonneg d _

private theorem block_nonneg (plus : Bool) (d : ℕ) {q : ℝ} (hq : 0 ≤ q)
    (a : Level (d+1)) : 0 ≤ blockWeight plus d q a := by
  apply sum_nonneg
  intro k hk
  exact mul_nonneg (pow_nonneg hq _) (kernel_nonneg plus k _)

/-- The normalization denominator is at least the repeated one-halving peak. -/
theorem peak_le_normalizer (plus : Bool) (d : ℕ) {q : ℝ} (hq : 0 ≤ q) :
    (3/2:ℝ)^d ≤ blockNormalizer plus d q := by
  let b := spike plus (d+1)
  have hk : kernel plus d b.val = iterate plus 1 FibreGeneration.unitWeight d
      (spike plus (1+d)) := by
    have hb : residue (1+d) b.val = spike plus (1+d) := by
      apply Fin.ext
      change b.val % 3^(1+d) = (spike plus (1+d)).val
      have hb' : b.val < 3^(1+d) := by simpa only [Nat.add_comm 1 d] using b.isLt
      exact (Nat.mod_eq_of_lt hb').trans
        (congrArg (fun r => (spike plus r).val) (Nat.add_comm d 1))
    exact congrArg (iterate plus 1 FibreGeneration.unitWeight d) hb
  have hpeak := iterate_spike plus (by omega : 1 ≤ 1) unit_nonneg d
  have hw : FibreGeneration.unitWeight (spike plus 1) = 1 := by
    simp [FibreGeneration.unitWeight, spike_unit plus (by omega : 1 ≤ 1)]
  rw [hw, mul_one, ← hk] at hpeak
  have hs : kernel plus d b.val ≤ blockWeight plus d q b := by
    have ht := single_le_sum (f := fun k => q^(d-k)*kernel plus k b.val)
      (s := range (d+1)) (a := d)
      (fun k hk => mul_nonneg (pow_nonneg hq _) (kernel_nonneg plus k _)) (by simp)
    simpa [blockWeight] using ht
  apply hpeak.trans (hs.trans _)
  exact (le_abs_self _).trans (norm_le_pi_norm (blockWeight plus d q) b)

private theorem block_at_root (plus : Bool) (d a : ℕ) (q : ℝ) :
    blockWeight plus d q (residue (d+1) a) =
      ∑ k ∈ range (d+1), q^(d-k)*kernel plus k a := by
  apply sum_congr rfl
  intro k hk
  congr 1
  unfold kernel
  congr 1
  apply Fin.ext
  exact Nat.mod_mod_of_dvd a (Nat.pow_dvd_pow 3 (by have := mem_range.mp hk; omega))

/-- At a fixed nonperiodic positive odd root the unnormalized block is at
most quadratic, uniformly in every rate between zero and one. -/
theorem block_at_root_le (plus : Bool) (d : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    {a : ℕ} (ha : 1 ≤ a) (ho : Odd a)
    (hnp : ∀ j : ℕ, 0 < j → (oddReturn plus)^[j] a ≠ a) :
    blockWeight plus d q (residue (d+1) a) ≤ rootAllowance plus a*(d+1)^2 := by
  rw [block_at_root]
  calc
    _ ≤ ∑ k ∈ range (d+1), rootAllowance plus a*(d+1) := by
      apply sum_le_sum
      intro k hk
      have hp := mul_le_mul_of_nonneg_right (pow_le_one₀ hq0 hq1 (n := d-k))
        (kernel_nonneg plus k a)
      have hl := FibreRootBounds.kernel_le_linear plus k ha ho hnp
      have hk' : (k:ℝ)+1 ≤ (d:ℝ)+1 := by exact_mod_cast (show k+1 ≤ d+1 by have := mem_range.mp hk; omega)
      have hr := mul_le_mul_of_nonneg_left hk' (le_trans (by norm_num) (one_le_rootAllowance plus ha))
      have hp' : q^(d-k)*kernel plus k a ≤ kernel plus k a := by simpa using hp
      exact hp'.trans (hl.trans hr)
    _ = _ := by simp [pow_two]; ring

private theorem power_deficit (d : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    1-q^d ≤ (d:ℝ)*(1-q) := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hp := mul_le_mul_of_nonneg_right (pow_le_one₀ hq0 hq1 (n := d))
        (sub_nonneg.mpr hq1)
      rw [pow_succ]
      push_cast
      nlinarith

/-- A rate certified by a complete block minimum has a deficit at least
`1/(4*(d+1))`. Increasing the block length cannot make this loss exponential. -/
theorem block_rate_deficit (plus : Bool) (d : ℕ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hblock : ∀ b : Level (1+(d+1)), b.val % 3 ≠ 0 →
      q^(d+1) ≤ iterate plus 1 FibreGeneration.unitWeight (d+1) b) :
    1 ≤ 4*(d+1:ℝ)*(1-q) := by
  have hf := block_floor_le plus d hblock
  have hp := power_deficit (d+1) hq0 hq1
  push_cast at hp
  nlinarith

/-- For geometric blocks certified by their complete generation minimum,
the normalized fixed-root prefactor divided by the rate deficit is at most
an explicit polynomial times `(2/3)^d`. Thus this construction cannot provide
the positive lower bound required by `FibreMinorants`. -/
theorem anchor_ratio_le (plus : Bool) (d : ℕ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hblock : ∀ b : Level (1+(d+1)), b.val % 3 ≠ 0 →
      q^(d+1) ≤ iterate plus 1 FibreGeneration.unitWeight (d+1) b)
    {a : ℕ} (ha : 1 ≤ a) (ho : Odd a)
    (hnp : ∀ j : ℕ, 0 < j → (oddReturn plus)^[j] a ≠ a) :
    (blockWeight plus d q (residue (d+1) a) / blockNormalizer plus d q) / (1-q) ≤
      4*rootAllowance plus a*(d+1)^3*(2/3:ℝ)^d := by
  have hp := peak_le_normalizer plus d hq0
  have hM : 0 < blockNormalizer plus d q := lt_of_lt_of_le (by positivity) hp
  have hgap : 0 < 1-q := sub_pos.mpr hq1
  have hB := block_at_root_le plus d hq0 hq1.le ha ho hnp
  have hD := block_rate_deficit plus d hq0 hq1.le hblock
  have hA : 0 ≤ rootAllowance plus a := le_trans (by norm_num) (one_le_rootAllowance plus ha)
  have hcancel : (2/3:ℝ)^d*(3/2:ℝ)^d = 1 := by rw [← mul_pow]; norm_num
  apply (div_le_iff₀ hgap).mpr
  apply (div_le_iff₀ hM).mpr
  have hn : (0:ℝ) ≤ 4*rootAllowance plus a*(d+1)^3*(2/3:ℝ)^d*(1-q) := by positivity
  have ht := mul_le_mul_of_nonneg_left hp hn
  have hh := mul_le_mul_of_nonneg_left hD (show 0 ≤ rootAllowance plus a*(d+1)^2 by positivity)
  have he : 4*rootAllowance plus a*(d+1)^3*(2/3:ℝ)^d*(1-q)*(3/2:ℝ)^d =
      rootAllowance plus a*(d+1)^2*(4*(d+1)*(1-q)) := by
    calc
      _ = rootAllowance plus a*(d+1)^2*(4*(d+1)*(1-q))*
          ((2/3:ℝ)^d*(3/2:ℝ)^d) := by ring
      _ = _ := by rw [hcancel, mul_one]
  rw [he] at ht
  have hh' : rootAllowance plus a*(d+1)^2 ≤
      rootAllowance plus a*(d+1)^2*(4*(d+1)*(1-q)) := by simpa using hh
  exact hB.trans (hh'.trans ht)

/-- Every family of these normalized geometric blocks loses its fixed-root
prefactor relative to `1-q`. This holds even if the certified block rates
approach one, and does not refute other periodic subsolution constructions. -/
theorem anchor_ratio_tendsto_zero (plus : Bool) (q : ℕ → ℝ)
    (hq0 : ∀ d, 0 ≤ q d) (hq1 : ∀ d, q d < 1)
    (hblock : ∀ d (b : Level (1+(d+1))), b.val % 3 ≠ 0 →
      (q d)^(d+1) ≤ iterate plus 1 FibreGeneration.unitWeight (d+1) b)
    {a : ℕ} (ha : 1 ≤ a) (ho : Odd a)
    (hnp : ∀ j : ℕ, 0 < j → (oddReturn plus)^[j] a ≠ a) :
    Tendsto (fun d => (blockWeight plus d (q d) (residue (d+1) a) /
      blockNormalizer plus d (q d)) / (1-q d)) atTop (𝓝 0) := by
  have hb := (tendsto_pow_const_mul_const_pow_of_lt_one 3
    (by norm_num : (0:ℝ) ≤ 2/3) (by norm_num)).comp (tendsto_add_atTop_nat 1)
  have hmajor : Tendsto (fun d : ℕ =>
      4*rootAllowance plus a*(d+1)^3*(2/3:ℝ)^d) atTop (𝓝 0) := by
    convert hb.const_mul (4*rootAllowance plus a/(2/3:ℝ)) using 1
    · funext d
      norm_num [Nat.cast_add, pow_succ, div_eq_mul_inv]
      ring
    · simp
  apply squeeze_zero _ (fun d => anchor_ratio_le plus d (hq0 d) (hq1 d) (hblock d) ha ho hnp) hmajor
  intro d
  exact div_nonneg (div_nonneg (block_nonneg plus d (hq0 d) _) (norm_nonneg _))
    (sub_nonneg.mpr (hq1 d).le)

end Problems.Collatz.FibreBlockWeights

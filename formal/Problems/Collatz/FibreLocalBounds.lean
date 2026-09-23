import Problems.Collatz.FibreUnitComparison
import Problems.Collatz.FibreDeficit
import Mathlib.NumberTheory.Multiplicity

/-! # Transported coefficient peaks in ternary unit neighborhoods

The actual signed inverse operator has unbounded peaks inside every fixed
unit residue neighborhood. The targets may vary with depth; this does not
give divergence of the coefficient series at a fixed ordinary integer.
-/

noncomputable section

namespace Problems.Collatz.FibreLocalBounds

open Finset FibreMass FibreActual FibreGeneration
open scoped Classical

private theorem four_pow_dvd (r t : ℕ) : 3^(r+1) ∣ 4^t-1 ↔ 3^r ∣ t := by
  by_cases ht : t = 0
  · simp [ht]
  have hp : 1 < 4^t := one_lt_pow₀ (by norm_num) ht
  have hv : padicValNat 3 (4^t-1) = 1+padicValNat 3 t := by
    simpa using padicValNat.pow_sub_pow (p := 3) (x := 4) (y := 1)
      (by decide) (by norm_num) (by norm_num) (by norm_num) ht
  rw [padicValNat_dvd_iff_le (by omega : 4^t-1 ≠ 0), hv,
    padicValNat_dvd_iff_le ht]
  omega

private theorem four_pow_injective (r : ℕ) :
    Function.Injective (fun i : Level r => residue (r+1) (4^i.val)) := by
  intro i j he
  have hc : 4^i.val ≡ 4^j.val [MOD 3^(r+1)] := congrArg Fin.val he
  suffices ∀ i j : Level r, i.val ≤ j.val →
      4^i.val ≡ 4^j.val [MOD 3^(r+1)] → i = j by
    rcases le_total i.val j.val with hij | hji
    · exact this i j hij hc
    · exact (this j i hji hc.symm).symm
  intro i j hij h
  have hd := h.dvd'
  have hpow : 4^j.val = 4^i.val * 4^(j.val-i.val) := by
    rw [← pow_add, Nat.add_sub_of_le hij]
  have hdiff : 4^j.val-4^i.val = 4^i.val*(4^(j.val-i.val)-1) := by
    rw [hpow, Nat.mul_sub_left_distrib, Nat.mul_one]
  rw [hdiff] at hd
  have hcop : Nat.Coprime (3^(r+1)) (4^i.val) :=
    ((by norm_num : Nat.Coprime 3 4).pow_left _).pow_right _
  have ht := (four_pow_dvd r (j.val-i.val)).mp (hcop.dvd_of_dvd_mul_left hd)
  have hz : j.val-i.val = 0 := Nat.eq_zero_of_dvd_of_lt ht (by have := j.isLt; omega)
  apply Fin.ext
  omega

private theorem four_mod_three (r i : ℕ) : (4^i % 3^(r+1)) % 3 = 1 := by
  rw [Nat.mod_mod_of_dvd _ (dvd_pow_self 3 (by omega : r+1 ≠ 0))]
  norm_num [Nat.pow_mod]

private theorem exists_four_pow (r : ℕ) (a : Level (r+1)) (ha : a.val % 3 = 1) :
    ∃ i : ℕ, i < 3^r ∧ residue (r+1) (4^i) = a := by
  let f : Level r → Level r := fun i =>
    ⟨(4^i.val % 3^(r+1))/3, by
      have h := Nat.mod_lt (4^i.val) (by positivity : 0 < 3^(r+1))
      rw [pow_succ] at h
      omega⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply four_pow_injective r
    apply Fin.ext
    have he := congrArg Fin.val hij
    change (4^i.val % 3^(r+1))/3 = (4^j.val % 3^(r+1))/3 at he
    have hi := four_mod_three r i.val
    have hj := four_mod_three r j.val
    change 4^i.val % 3^(r+1) = 4^j.val % 3^(r+1)
    omega
  let b : Level r := ⟨a.val/3, by have := a.isLt; simp only [pow_succ] at this; omega⟩
  obtain ⟨i, hi⟩ := hf.bijective_of_finite.surjective b
  refine ⟨i.val, i.isLt, Fin.ext ?_⟩
  have he := congrArg Fin.val hi
  change (4^i.val % 3^(r+1))/3 = a.val/3 at he
  have hm := four_mod_three r i.val
  change 4^i.val % 3^(r+1) = a.val
  omega

private theorem exists_two_pow (r : ℕ) (a : Level (r+1)) (ha : a.val % 3 ≠ 0) :
    ∃ k : ℕ, k < 2*3^r ∧ residue (r+1) (2^k) = a := by
  by_cases ha1 : a.val % 3 = 1
  · obtain ⟨i, hlt, hi⟩ := exists_four_pow r a ha1
    refine ⟨2*i, by omega, ?_⟩
    simpa [pow_mul] using hi
  have ha2 : a.val % 3 = 2 := by omega
  let b := (doubleEquiv (r+1)).symm a
  have hb : (2*b.val) % 3^(r+1) = a.val := by
    have he := congrArg Fin.val ((doubleEquiv (r+1)).apply_symm_apply a)
    rw [doubleEquiv_val] at he
    exact he
  have hb1 : b.val % 3 = 1 := by
    have he := congrArg (fun n : ℕ => n % 3) hb
    rw [Nat.mod_mod_of_dvd _ (dvd_pow_self 3 (by omega : r+1 ≠ 0)), ha2,
      Nat.mul_mod] at he
    omega
  obtain ⟨i, hlt, hi⟩ := exists_four_pow r b hb1
  refine ⟨2*i+1, by omega, Fin.ext ?_⟩
  have he := congrArg Fin.val hi
  change 4^i % 3^(r+1) = b.val at he
  change 2^(2*i+1) % 3^(r+1) = a.val
  rw [pow_succ, pow_mul]
  norm_num
  simpa [Nat.mul_mod, he, Nat.mul_comm] using hb

/-- Multiplying any ternary unit by the first `2*3^r` powers of two
reaches every unit modulo `3^(r+1)`. The bounded exponent is retained
for quantitative transport through actual inverse branches. -/
theorem exists_bounded_power_mul (r a b : ℕ) (ha : a % 3 ≠ 0) (hb : b % 3 ≠ 0) :
    ∃ k : ℕ, k < 2*3^r ∧ 2^k*a ≡ b [MOD 3^(r+1)] := by
  have hcop : Nat.Coprime (3^(r+1)) a :=
    (Nat.prime_three.coprime_iff_not_dvd.mpr (by simpa [Nat.dvd_iff_mod_eq_zero] using ha)).pow_left _
  obtain ⟨c, hc⟩ := (PreimageBalance.affine_bijective (by positivity) a 0 hcop).surjective
    (residue (r+1) b)
  have he : (a*c.val) % 3^(r+1) = b % 3^(r+1) := by
    simpa only [PreimageBalance.affine, Nat.add_zero, residue] using congrArg Fin.val hc
  have hu : c.val % 3 ≠ 0 := by
    intro hz
    have ht := congrArg (fun n : ℕ => n % 3) he
    simp only [Nat.mod_mod_of_dvd _ (dvd_pow_self 3 (by omega : r+1 ≠ 0))] at ht
    rw [Nat.mul_mod, hz] at ht
    exact hb (by simpa using ht.symm)
  obtain ⟨k, hlt, hk⟩ := exists_two_pow r c hu
  refine ⟨k, hlt, ?_⟩
  have hp := congrArg Fin.val hk
  change 2^k % 3^(r+1) = c.val at hp
  change (2^k*a) % 3^(r+1) = b % 3^(r+1)
  rw [Nat.mul_mod, hp]
  simpa [Nat.mul_mod, Nat.mul_comm] using he

private theorem exists_shift (plus : Bool) (r : ℕ) (a : Level (r+1))
    (ha : a.val % 3 ≠ 0) :
    ∃ k : ℕ, 2^k*a.val ≡ (spike plus (r+1)).val [MOD 3^(r+1)] := by
  obtain ⟨k, _, hk⟩ := exists_bounded_power_mul r a.val (spike plus (r+1)).val
    ha (spike_unit plus (by omega : 1 ≤ r+1))
  exact ⟨k, hk⟩

private theorem shifted_spike_congr (plus : Bool) (r k d : ℕ) (hrd : r ≤ d)
    (a : Level (r+1))
    (ha : 2^k*a.val ≡ (spike plus (r+1)).val [MOD 3^(r+1)]) :
    (parent plus (1+d) k (spike plus (1+d))).val ≡ a.val [MOD 3^(r+1)] := by
  let b := parent plus (1+d) k (spike plus (1+d))
  have hp := (parent_iff plus (1+d) k b (spike plus (1+d))).mp rfl
  have hz := (parent_iff plus (1+d) 0 (spike plus (1+d+1))
    (spike plus (1+d))).mp (parent_spike plus (by omega))
  have h2 : 2*(2^k*b.val) ≡ 2*(spike plus (1+d+1)).val [MOD 3^(1+d+1)] := by
    simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hp.trans hz.symm
  have hc := h2.cancel_left_of_coprime ((by norm_num : Nat.Coprime 3 2).pow_left _)
  have hl := hc.of_dvd (Nat.pow_dvd_pow 3 (by omega : r+1 ≤ 1+d+1))
  have hs : (spike plus (1+d+1)).val ≡ (spike plus (r+1)).val [MOD 3^(r+1)] := by
    have he := congrArg Fin.val (project_spike plus (by omega : 1 ≤ r+1) (d+1-r))
    change (spike plus (1+d+1)).val % 3^(r+1) = (spike plus (r+1)).val % 3^(r+1)
    rw [Nat.mod_eq_of_lt (spike plus (r+1)).isLt]
    change (spike plus (r+1+(d+1-r))).val % 3^(r+1) = (spike plus (r+1)).val at he
    have hn : r+1+(d+1-r) = 1+d+1 := by omega
    rw [hn] at he
    exact he
  exact ((hl.trans hs).trans ha.symm).cancel_left_of_coprime
    (((by norm_num : Nat.Coprime 3 2).pow_left _).pow_right _)

/-- A one-halving peak survives transport through any fixed exponent branch.
The coefficient is evaluated at a depth-dependent residue, not a fixed integer. -/
theorem shifted_spike_lower (plus : Bool) (k d : ℕ) :
    (3/(2:ℝ)^(k+1))*(3/2:ℝ)^d ≤
      iterate plus 1 unitWeight (d+1) (parent plus (1+d) k (spike plus (1+d))) := by
  have hu : ∀ b, 0 ≤ unitWeight b := by
    intro b; unfold unitWeight; split_ifs <;> norm_num
  have hs := iterate_spike plus (by omega : 1 ≤ 1) hu d
  have hw : unitWeight (spike plus 1) = 1 := by
    simp [unitWeight, spike_unit plus (by omega : 1 ≤ 1)]
  rw [hw, mul_one] at hs
  have hi := iterate_nonneg plus 1 hu d
  have ht := (row_summable plus (1+d) hi (parent plus (1+d) k (spike plus (1+d)))).le_tsum k
    (fun i _ => row_nonneg plus (1+d) i hi _)
  rw [row_at_parent] at ht
  exact (mul_le_mul_of_nonneg_left hs (by positivity)).trans ht

/-- In every fixed ternary unit class, actual unit coefficients exceed any
bound at arbitrarily large depths and positive odd targets above any height.
The target can depend on the depth; no fixed-integer divergence follows. -/
theorem unit_unbounded (plus : Bool) (r : ℕ) (a : Level (r+1))
    (ha : a.val % 3 ≠ 0) (H : ℝ) (D B : ℕ) :
    ∃ d m : ℕ, D ≤ d ∧ B ≤ m ∧ 1 ≤ m ∧ Odd m ∧
      residue (r+1) m = a ∧ H < FibreHeightBudget.kernel plus d m := by
  obtain ⟨k, hk⟩ := exists_shift plus r a ha
  let w : ℝ := 3/(2:ℝ)^(k+1)
  have hw : 0 < w := by dsimp [w]; positivity
  have hg := tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 3/2)
  have he : ∀ᶠ d : ℕ in Filter.atTop, H/w < (3/2:ℝ)^d :=
    hg.eventually (Filter.eventually_gt_atTop (H/w))
  obtain ⟨d, hd, hgt⟩ := ((Filter.eventually_ge_atTop (max r D)).and he).exists
  have hr : r ≤ d := (le_max_left _ _).trans hd
  let b := parent plus (1+d) k (spike plus (1+d))
  let m := FibreDeficit.progression (1+d) b B 0
  have hm := FibreDeficit.progression_residue (1+d) b B 0
  have hma : residue (r+1) m = a := by
    have hc : m ≡ b.val [MOD 3^(1+d+1)] := by
      change m % 3^(1+d+1) = b.val % 3^(1+d+1)
      rw [Nat.mod_eq_of_lt b.isLt]
      exact congrArg Fin.val hm
    have ht := (hc.of_dvd (Nat.pow_dvd_pow 3 (by omega : r+1 ≤ 1+d+1))).trans
      (shifted_spike_congr plus r k d hr a hk)
    exact Fin.ext (by simpa only [residue, Nat.ModEq, Nat.mod_eq_of_lt a.isLt] using ht)
  refine ⟨d+1, m, by omega, FibreDeficit.progression_large _ _ _ _,
    FibreDeficit.progression_pos _ _ _ _, FibreDeficit.progression_odd _ _ _ _, hma, ?_⟩
  have hl := shifted_spike_lower plus k d
  have hh : H < w*(3/2:ℝ)^d := (div_lt_iff₀ hw).mp hgt |>.trans_eq (mul_comm _ _)
  apply hh.trans_le
  change w*(3/2:ℝ)^d ≤ iterate plus 1 unitWeight (d+1) (residue (1+d+1) m)
  rw [hm]
  exact hl

/-- The complete all-source coefficient is also unbounded on every fixed
unit neighborhood across arbitrarily large depths and positive odd heights.
This follows from the checked relative comparison with unit coefficients. -/
theorem coarse_unbounded (plus : Bool) (r : ℕ) (a : Level (r+1))
    (ha : a.val % 3 ≠ 0) (H : ℝ) (D B : ℕ) :
    ∃ d m : ℕ, D ≤ d ∧ B ≤ m ∧ 1 ≤ m ∧ Odd m ∧
      residue (r+1) m = a ∧ H < FibreUnitComparison.coarse plus d m := by
  obtain ⟨d,m,hd,hB,hm,ho,hr,hK⟩ := unit_unbounded plus r a ha ((20/21:ℝ)*H) (max 1 D) B
  refine ⟨d,m,(le_max_right _ _).trans hd,hB,hm,ho,hr,?_⟩
  have ht := (FibreUnitComparison.kernel_bounds plus ((le_max_left _ _).trans hd) m).2
  linarith

end Problems.Collatz.FibreLocalBounds

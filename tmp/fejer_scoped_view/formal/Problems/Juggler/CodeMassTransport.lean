import Problems.Juggler.FateSeed
import Problems.Juggler.CollatzPadic
import Problems.Juggler.Preimages
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.ENNReal.Real

/-!
# Exact even-fibre mass with signed coded source cutoffs

The parity-paired logarithmic weight conserves the mass of every actual
even Juggler fibre. All cutoffs below refer to source integers.
-/

noncomputable section

namespace Problems.Juggler.CodeMassTransport

open Finset
open scoped Classical

def paired (n : ℕ) : ℕ := n + n % 2

def weight (n : ℕ) : ℝ :=
  Real.log ((paired n : ℝ) + 1) - Real.log ((paired n : ℝ) - 1)

theorem paired_ge_two {n : ℕ} (hn : 1 ≤ n) : 2 ≤ paired n := by
  unfold paired
  omega

theorem weight_log_ratio {n : ℕ} (hn : 1 ≤ n) :
    weight n = Real.log (((paired n : ℝ) + 1) / ((paired n : ℝ) - 1)) := by
  have he : (2 : ℝ) ≤ paired n := by exact_mod_cast paired_ge_two hn
  exact (Real.log_div (by linarith) (by linarith)).symm

theorem weight_pos {n : ℕ} (hn : 1 ≤ n) : 0 < weight n := by
  have he : (2 : ℝ) ≤ paired n := by exact_mod_cast paired_ge_two hn
  exact sub_pos.mpr (Real.log_lt_log (by linarith) (by linarith))

theorem weight_nonneg (n : ℕ) : 0 ≤ weight n := by
  rcases n with _ | n
  · norm_num [weight, paired]
  · exact (weight_pos (by omega)).le

theorem weight_even {n : ℕ} (hn : n % 2 = 0) :
    weight n = Real.log ((n : ℝ) + 1) - Real.log ((n : ℝ) - 1) := by
  simp [weight, paired, hn]

theorem evenBlock_progression (m : ℕ) :
    evenBlock m = (range (m + 1 - m % 2)).image
      (fun j => m * m + m % 2 + 2 * j) := by
  have hr : m % 2 ≤ 1 := by omega
  have hsq : m * m % 2 = m % 2 := by
    rw [Nat.mul_mod]
    rcases Nat.mod_two_eq_zero_or_one m with h | h <;> simp [h]
  have htop : (m + 1) * (m + 1) = m * m + 2 * m + 1 := by ring
  ext n
  simp only [evenBlock, mem_filter, mem_Ico, mem_image, mem_range]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, he⟩
    rw [htop] at hhi
    refine ⟨(n - (m * m + m % 2)) / 2, ?_, ?_⟩ <;> omega
  · rintro ⟨j, hj, rfl⟩
    constructor
    · rw [htop]
      constructor <;> omega
    · omega

theorem even_progression_sum {a : ℕ} (ha : a % 2 = 0) (L : ℕ) :
    ∑ j ∈ range L, weight (a + 2 * j) =
      Real.log ((a : ℝ) + 2 * L - 1) - Real.log ((a : ℝ) - 1) := by
  have hw (j : ℕ) : weight (a + 2 * j) =
      Real.log ((a : ℝ) + 2 * (j + 1) - 1) -
        Real.log ((a : ℝ) + 2 * j - 1) := by
    rw [weight_even (by omega)]
    push_cast
    congr 2
    ring
  simp_rw [hw]
  simpa using sum_range_sub (fun j : ℕ => Real.log ((a : ℝ) + 2 * j - 1)) L

theorem evenBlock_mass {m : ℕ} (hm : 1 ≤ m) :
    ∑ n ∈ evenBlock m, weight n = weight m := by
  rw [evenBlock_progression, sum_image]
  · have heven : (m * m + m % 2) % 2 = 0 := by
      rw [Nat.add_mod, Nat.mul_mod]
      rcases Nat.mod_two_eq_zero_or_one m with h | h <;> simp [h]
    rw [even_progression_sum heven]
    rcases Nat.mod_two_eq_zero_or_one m with he | ho
    · have hm2 : 2 ≤ m := by omega
      have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm2
      have hp : (0 : ℝ) < m - 1 := by linarith
      have hp' : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      simp only [he, Nat.add_zero, Nat.sub_zero, Nat.cast_mul, Nat.cast_add,
        Nat.cast_one, weight, paired]
      have h1 : (m : ℝ) * m + 2 * (m + 1) - 1 = (m + 1) * (m + 1) := by ring
      have h2 : (m : ℝ) * m - 1 = (m - 1) * (m + 1) := by ring
      rw [h1, h2, Real.log_mul hp'.ne' hp'.ne', Real.log_mul hp.ne' hp'.ne']
      ring
    · have hp : (0 : ℝ) < m := by exact_mod_cast hm
      have hp' : (0 : ℝ) < (m : ℝ) + 2 := by positivity
      simp only [ho, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
        weight, paired]
      have h1 : (m : ℝ) * m + 1 + 2 * m - 1 = m * (m + 2) := by ring
      have h2 : (m : ℝ) * m + 1 - 1 = m * m := by ring
      rw [h1, h2, Real.log_mul hp.ne' hp'.ne', Real.log_mul hp.ne' hp.ne']
      ring_nf
  · intro i _ j _ hij
    dsimp at hij
    omega

theorem mem_evenBlock_iff (m n : ℕ) :
    n ∈ evenBlock m ↔ n % 2 = 0 ∧ floorPower n = m := by
  simp only [evenBlock, mem_filter, mem_Ico]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, he⟩
    exact ⟨he, floorPower_even_block he hlo hhi⟩
  · rintro ⟨he, hJ⟩
    rw [floorPower_even_eq he] at hJ
    exact ⟨Nat.eq_sqrt.mp hJ.symm, he⟩

theorem evenBlock_positive {m n : ℕ} (hm : 1 ≤ m) (hn : n ∈ evenBlock m) :
    1 ≤ n := by
  have hlo := (mem_Ico.mp (mem_filter.mp hn).1).1
  nlinarith

theorem blockTree_mass {m : ℕ} (hm : 1 ≤ m) (d : ℕ) :
    ∑ n ∈ blockTree m d, weight n = weight m := by
  induction d with
  | zero => simp [blockTree_zero]
  | succ d ih =>
    rw [blockTree_succ, sum_biUnion (evenBlock_pairwiseDisjoint _)]
    have he : ∀ n ∈ blockTree m d, ∑ k ∈ evenBlock n, weight k = weight n := by
      intro n hn
      apply evenBlock_mass
      exact (Nat.one_le_pow _ _ hm).trans (blockTree_bounds m d n hn).1
    simp_rw [sum_congr rfl he]
    exact ih

def evenSources (X : ℕ) : Finset ℕ := (Icc 1 X).filter (fun n => n % 2 = 0)

def partialMass (X m : ℕ) : ℝ :=
  ∑ n ∈ (evenBlock m).filter (fun n => n ≤ X), weight n

def mass (A : ℕ → Prop) (X : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 X, if A n then weight n else 0

theorem partialMass_nonneg (X m : ℕ) : 0 ≤ partialMass X m :=
  sum_nonneg fun n _ => weight_nonneg n

theorem partialMass_le {m : ℕ} (hm : 1 ≤ m) (X : ℕ) :
    partialMass X m ≤ weight m := by
  rw [← evenBlock_mass hm]
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    (fun n _ _ => weight_nonneg n)

theorem partialMass_complete {m X : ℕ} (hm : 1 ≤ m) (hM : m < Nat.sqrt X) :
    partialMass X m = weight m := by
  unfold partialMass
  rw [filter_eq_self.mpr, evenBlock_mass hm]
  intro n hn
  have hhi := (mem_Ico.mp (mem_filter.mp hn).1).2
  have hs := Nat.sqrt_le X
  have hsq : (m + 1) * (m + 1) ≤ Nat.sqrt X * Nat.sqrt X :=
    Nat.mul_le_mul hM hM
  omega

theorem source_fibre {m : ℕ} (hm : 1 ≤ m) (X : ℕ) :
    (evenSources X).filter (fun n => floorPower n = m) =
      (evenBlock m).filter (fun n => n ≤ X) := by
  ext n
  simp only [evenSources, mem_filter, mem_Icc, mem_evenBlock_iff]
  constructor
  · tauto
  · intro h
    have hn := evenBlock_positive hm ((mem_evenBlock_iff m n).mpr h.1)
    tauto

theorem even_weighted_reindex (X : ℕ) (g : ℕ → ℝ) :
    ∑ n ∈ evenSources X, weight n * g (floorPower n) =
      ∑ m ∈ Icc 1 (Nat.sqrt X), partialMass X m * g m := by
  have hmaps : ∀ n ∈ evenSources X, floorPower n ∈ Icc 1 (Nat.sqrt X) := by
    intro n hn
    obtain ⟨hI, he⟩ := mem_filter.mp hn
    obtain ⟨hlo, hhi⟩ := mem_Icc.mp hI
    exact mem_Icc.mpr ⟨floorPower_pos hlo, by
      rw [floorPower_even_eq he]
      exact Nat.sqrt_le_sqrt hhi⟩
  rw [← sum_fiberwise_of_maps_to hmaps]
  apply sum_congr rfl
  intro m hm
  rw [source_fibre (mem_Icc.mp hm).1 X, partialMass, sum_mul]
  apply sum_congr rfl
  intro n hn
  rw [((mem_evenBlock_iff m n).mp (mem_filter.mp hn).1).2]

theorem even_pullback_cutoff (A : ℕ → Prop) {X : ℕ} (hX : 1 ≤ X) :
    ∑ n ∈ evenSources X, (if A (floorPower n) then weight n else 0) =
      mass A (Nat.sqrt X - 1) +
        if A (Nat.sqrt X) then partialMass X (Nat.sqrt X) else 0 := by
  have hM : 1 ≤ Nat.sqrt X := Nat.le_sqrt.mpr (by simpa using hX)
  have hr := even_weighted_reindex X (fun m => if A m then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero] at hr
  rw [hr]
  let f (m : ℕ) : ℝ := if A m then partialMass X m else 0
  have hsplit := sum_Icc_succ_top (a := 1) (b := Nat.sqrt X - 1) (by omega) f
  have hsucc : Nat.sqrt X - 1 + 1 = Nat.sqrt X := by omega
  rw [hsucc] at hsplit
  rw [show (∑ m ∈ Icc 1 (Nat.sqrt X), if A m then partialMass X m else 0) =
      (∑ m ∈ Icc 1 (Nat.sqrt X - 1), if A m then partialMass X m else 0) +
        (if A (Nat.sqrt X) then partialMass X (Nat.sqrt X) else 0) from hsplit]
  congr 1
  apply sum_congr rfl
  intro m hm
  rw [partialMass_complete (mem_Icc.mp hm).1 (by have := (mem_Icc.mp hm).2; omega)]

theorem fate_even_cutoff (A : ℕ → Prop)
    (hA : ∀ n, A n ↔ A (floorPower n)) {X : ℕ} (hX : 1 ≤ X) :
    ∑ n ∈ evenSources X, (if A n then weight n else 0) =
      mass A (Nat.sqrt X - 1) +
        if A (Nat.sqrt X) then partialMass X (Nat.sqrt X) else 0 := by
  calc
    _ = ∑ n ∈ evenSources X, (if A (floorPower n) then weight n else 0) := by
      apply sum_congr rfl
      intro n _
      rw [hA n]
    _ = _ := even_pullback_cutoff A hX

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def doubled (B : ℤ_[2] → Prop) (x : ℤ_[2]) : Prop :=
  ∃ q, B q ∧ x = 2 * q

def codedMass (H : ℕ → ℤ_[2]) (B : ℤ_[2] → Prop) (X : ℕ) : ℝ :=
  mass (fun n => B (H n)) X

theorem doubled_iff (H : ℕ → ℤ_[2])
    (hpar : ∀ n, PadicInt.toZModPow 1 (H n) = 0 ↔ n % 2 = 0)
    (hstep : ∀ n, n % 2 = 0 → H n = 2 * H (floorPower n)) (B : ℤ_[2] → Prop)
    (n : ℕ) : doubled B (H n) ↔ n % 2 = 0 ∧ B (H (floorPower n)) := by
  constructor
  · rintro ⟨q, hB, heq⟩
    have he : n % 2 = 0 := (hpar n).mp (by
      rw [heq, map_mul, map_ofNat]
      have hz : (2 : ZMod (2 ^ 1)) = 0 := by decide
      rw [hz, zero_mul])
    have hq : H (floorPower n) = q :=
      mul_left_cancel₀ (by norm_num : (2 : ℤ_[2]) ≠ 0) ((hstep n he).symm.trans heq)
    exact ⟨he, hq.symm ▸ hB⟩
  · rintro ⟨he, hB⟩
    exact ⟨H (floorPower n), hB, hstep n he⟩

theorem coded_even_cutoff (H : ℕ → ℤ_[2])
    (hpar : ∀ n, PadicInt.toZModPow 1 (H n) = 0 ↔ n % 2 = 0)
    (hstep : ∀ n, n % 2 = 0 → H n = 2 * H (floorPower n))
    (B : ℤ_[2] → Prop) {X : ℕ} (hX : 1 ≤ X) :
    codedMass H (doubled B) X = codedMass H B (Nat.sqrt X - 1) +
      if B (H (Nat.sqrt X)) then partialMass X (Nat.sqrt X) else 0 := by
  have he : codedMass H (doubled B) X =
      ∑ n ∈ evenSources X, if B (H (floorPower n)) then weight n else 0 := by
    unfold codedMass mass evenSources
    rw [sum_filter]
    apply sum_congr rfl
    intro n _
    dsimp only
    by_cases hn : n % 2 = 0 <;> simp [doubled_iff H hpar hstep, hn]
  rw [he]
  exact even_pullback_cutoff (fun n => B (H n)) hX

theorem minus_code_cutoff (B : ℤ_[2] → Prop) {X : ℕ} (hX : 1 ≤ X) :
    codedMass CollatzPadic.code (doubled B) X =
      codedMass CollatzPadic.code B (Nat.sqrt X - 1) +
      if B (CollatzPadic.code (Nat.sqrt X)) then partialMass X (Nat.sqrt X) else 0 := by
  apply coded_even_cutoff CollatzPadic.code CollatzPadic.code_parity _ B hX
  intro n hn
  simpa [hn] using (CollatzPadic.code_step n).symm

theorem plus_code_cutoff (B : ℤ_[2] → Prop) {X : ℕ} (hX : 1 ≤ X) :
    codedMass CollatzPadic.plusCode (doubled B) X =
      codedMass CollatzPadic.plusCode B (Nat.sqrt X - 1) +
      if B (CollatzPadic.plusCode (Nat.sqrt X)) then partialMass X (Nat.sqrt X) else 0 := by
  apply coded_even_cutoff CollatzPadic.plusCode CollatzPadic.plusCode_parity _ B hX
  intro n hn
  simpa [hn] using (CollatzPadic.plusCode_step n).symm

theorem mass_last (A : ℕ → Prop) {M : ℕ} (hM : 1 ≤ M) :
    mass A M = mass A (M - 1) + if A M then weight M else 0 := by
  have hs := sum_Icc_succ_top (a := 1) (b := M - 1) (by omega)
    (fun n => if A n then weight n else 0)
  simpa only [mass, show M - 1 + 1 = M from by omega] using hs

theorem coded_cutoff_bounds (H : ℕ → ℤ_[2])
    (hpar : ∀ n, PadicInt.toZModPow 1 (H n) = 0 ↔ n % 2 = 0)
    (hstep : ∀ n, n % 2 = 0 → H n = 2 * H (floorPower n))
    (B : ℤ_[2] → Prop) {X : ℕ} (hX : 1 ≤ X) :
    codedMass H B (Nat.sqrt X - 1) ≤ codedMass H (doubled B) X ∧
      codedMass H (doubled B) X ≤ codedMass H B (Nat.sqrt X) := by
  have hM : 1 ≤ Nat.sqrt X := Nat.le_sqrt.mpr (by simpa using hX)
  rw [coded_even_cutoff H hpar hstep B hX]
  have hs := mass_last (fun n => B (H n)) hM
  change codedMass H B (Nat.sqrt X) = codedMass H B (Nat.sqrt X - 1) +
    (if B (H (Nat.sqrt X)) then weight (Nat.sqrt X) else 0) at hs
  rw [hs]
  by_cases hB : B (H (Nat.sqrt X))
  · simp only [if_pos hB]
    exact ⟨le_add_of_nonneg_right (partialMass_nonneg _ _),
      add_le_add le_rfl (partialMass_le hM X)⟩
  · simp [hB]

/-- Nonnegative infinite coded mass, defined as the supremum of source cutoffs. -/
def codedTotal (H : ℕ → ℤ_[2]) (B : ℤ_[2] → Prop) : ENNReal :=
  ⨆ X : ℕ, ENNReal.ofReal (codedMass H B X)

theorem codedTotal_doubled (H : ℕ → ℤ_[2])
    (hpar : ∀ n, PadicInt.toZModPow 1 (H n) = 0 ↔ n % 2 = 0)
    (hstep : ∀ n, n % 2 = 0 → H n = 2 * H (floorPower n)) (B : ℤ_[2] → Prop) :
    codedTotal H (doubled B) = codedTotal H B := by
  apply le_antisymm
  · apply iSup_le
    intro X
    rcases X with _ | X
    · simp [codedMass, mass]
    · exact (ENNReal.ofReal_le_ofReal (coded_cutoff_bounds H hpar hstep B (by omega)).2).trans
        (le_iSup (fun N => ENNReal.ofReal (codedMass H B N)) (Nat.sqrt (X + 1)))
  · apply iSup_le
    intro M
    have hX : 1 ≤ (M + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have hb := (coded_cutoff_bounds H hpar hstep B hX).1
    have hs := Nat.sqrt_eq' (M + 1)
    rw [hs, Nat.add_sub_cancel] at hb
    exact (ENNReal.ofReal_le_ofReal hb).trans
      (le_iSup (fun X => ENNReal.ofReal (codedMass H (doubled B) X)) ((M + 1) ^ 2))

theorem minus_code_total (B : ℤ_[2] → Prop) :
    codedTotal CollatzPadic.code (doubled B) = codedTotal CollatzPadic.code B := by
  apply codedTotal_doubled CollatzPadic.code CollatzPadic.code_parity _ B
  intro n hn
  simpa [hn] using (CollatzPadic.code_step n).symm

theorem plus_code_total (B : ℤ_[2] → Prop) :
    codedTotal CollatzPadic.plusCode (doubled B) = codedTotal CollatzPadic.plusCode B := by
  apply codedTotal_doubled CollatzPadic.plusCode CollatzPadic.plusCode_parity _ B
  intro n hn
  simpa [hn] using (CollatzPadic.plusCode_step n).symm

/-- The code forgets whether a physical target has an odd predecessor. -/
theorem code_collision_odd_preimages :
    CollatzPadic.code 16 = CollatzPadic.code 18 ∧
      (∀ n, n % 2 = 1 → floorPower n ≠ 16) ∧ floorPower 7 = 18 := by
  have h16 : floorPower 16 = 4 := by decide +kernel
  have h18 : floorPower 18 = 4 := by decide +kernel
  refine ⟨?_, ?_, by decide +kernel⟩
  · have h1 := CollatzPadic.code_step 16
    have h2 := CollatzPadic.code_step 18
    norm_num [h16, h18] at h1 h2
    exact h1.symm.trans h2
  · intro n hn heq
    have hc := (floorPower_odd_eq_iff_cube_interval hn).mp heq
    rcases le_or_gt n 6 with hsmall | hlarge
    · have hb := Nat.pow_le_pow_left hsmall 3
      norm_num at hc hb
      omega
    · have hb := Nat.pow_le_pow_left (show 7 ≤ n by omega) 3
      norm_num at hc hb
      omega

end Problems.Juggler.CodeMassTransport

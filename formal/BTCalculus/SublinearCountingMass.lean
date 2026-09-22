import Mathlib.Analysis.PSeries
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Algebra.Order.Floor.Semiring

/-! # Sublinear counting growth with finite reciprocal mass

For every exponent strictly between zero and one, the floored power
sequence realizes the elementary counterexample used in Paper E.
-/

noncomputable section
attribute [local instance] Classical.propDecidable

namespace BTCalculus.SublinearCountingMass

open Finset

def sequence (κ : ℝ) (n : ℕ) : ℕ := ⌊((n : ℝ)+1)^κ⁻¹⌋₊

def support (κ : ℝ) : Set ℕ := Set.range (sequence κ)

def counting (κ X : ℝ) : ℕ := ((Icc 1 ⌊X⌋₊).filter (fun n => n ∈ support κ)).card

theorem sequence_pos {κ : ℝ} (hκ : 0 < κ) (n : ℕ) : 1 ≤ sequence κ n := by
  apply Nat.le_floor
  norm_num only [Nat.cast_one]
  exact Real.one_le_rpow (by linarith [Nat.cast_nonneg (α := ℝ) n]) (inv_nonneg.mpr hκ.le)

theorem sequence_strictMono {κ : ℝ} (hκ : 0 < κ) (hk : κ < 1) :
    StrictMono (sequence κ) := by
  have hp : 1 < κ⁻¹ := (one_lt_inv₀ hκ).2 hk
  apply strictMono_nat_of_lt_succ
  intro n
  have h := Real.add_rpow_le_rpow_add (by positivity : (0 : ℝ) ≤ (n : ℝ)+1)
    (by norm_num : (0 : ℝ) ≤ 1) hp.le
  simp only [Real.one_rpow] at h
  have hf := Nat.floor_mono h
  rw [Nat.floor_add_one (by positivity)] at hf
  simpa only [sequence, Nat.cast_add, Nat.cast_one] using Nat.lt_of_succ_le hf

theorem sequence_le_cutoff {κ X : ℝ} (hκ : 0 < κ) (hX : 0 ≤ X)
    {n : ℕ} (hn : n < ⌊X^κ⌋₊) : sequence κ n ≤ ⌊X⌋₊ := by
  have hn' : (n : ℝ)+1 ≤ X^κ := by
    have hcast : (n : ℝ)+1 ≤ (⌊X^κ⌋₊ : ℝ) := by exact_mod_cast hn
    exact hcast.trans (Nat.floor_le (by positivity))
  have hp := Real.rpow_le_rpow (by positivity) hn' (inv_nonneg.mpr hκ.le)
  rw [← Real.rpow_mul hX, mul_inv_cancel₀ hκ.ne', Real.rpow_one] at hp
  exact Nat.floor_mono hp

/-- Every real cutoff has at least the displayed sublinear number of distinct positive terms. -/
theorem counting_lower_bound {κ X : ℝ} (hκ : 0 < κ) (hk : κ < 1) (hX : 0 ≤ X) :
    ⌊X^κ⌋₊ ≤ counting κ X := by
  have hinj := (sequence_strictMono hκ hk).injective
  have hsub : (range ⌊X^κ⌋₊).image (sequence κ) ⊆
      (Icc 1 ⌊X⌋₊).filter (fun n => n ∈ support κ) := by
    intro m hm
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hm
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨sequence_pos hκ n,
      sequence_le_cutoff hκ hX (mem_range.mp hn)⟩, ⟨n, rfl⟩⟩
  have h := card_le_card hsub
  simpa only [card_image_of_injective _ hinj, card_range, counting] using h

theorem reciprocal_sequence_bound {κ : ℝ} (hκ : 0 < κ) (n : ℕ) :
    1/(sequence κ n : ℝ) ≤ 2/((n : ℝ)+1)^κ⁻¹ := by
  have hs : (1 : ℝ) ≤ sequence κ n := by exact_mod_cast sequence_pos hκ n
  have hp : (0 : ℝ) < ((n : ℝ)+1)^κ⁻¹ := by positivity
  have hf := Nat.lt_floor_add_one (((n : ℝ)+1)^κ⁻¹)
  change ((n : ℝ)+1)^κ⁻¹ < (sequence κ n : ℝ)+1 at hf
  apply (div_le_div_iff₀ (by linarith : (0 : ℝ) < sequence κ n) hp).2
  nlinarith

/-- The reciprocal series converges, although the counting function has power growth. -/
theorem summable_reciprocal_sequence {κ : ℝ} (hκ : 0 < κ) (hk : κ < 1) :
    Summable (fun n => 1/(sequence κ n : ℝ)) := by
  have hp : 1 < κ⁻¹ := (one_lt_inv₀ hκ).2 hk
  have hs := (Real.summable_one_div_nat_add_rpow 1 κ⁻¹).2 hp
  have he : (fun n : ℕ => 1/|(n : ℝ)+1|^κ⁻¹) =
      (fun n : ℕ => 1/((n : ℝ)+1)^κ⁻¹) := by
    funext n
    rw [abs_of_pos (by positivity)]
  rw [he] at hs
  apply Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => reciprocal_sequence_bound hκ n)
  simpa only [mul_one_div] using hs.mul_left 2

theorem support_infinite {κ : ℝ} (hκ : 0 < κ) (hk : κ < 1) : (support κ).Infinite :=
  Set.infinite_range_of_injective (sequence_strictMono hκ hk).injective

theorem summable_reciprocal_support {κ : ℝ} (hκ : 0 < κ) (hk : κ < 1) :
    Summable (fun n : support κ => 1/(n.val : ℝ)) := by
  let e : ℕ ≃ support κ := Equiv.ofInjective (sequence κ) (sequence_strictMono hκ hk).injective
  exact e.summable_iff.mp (summable_reciprocal_sequence hκ hk)

/-- A positive infinite set can have any prescribed sublinear power lower count and finite mass. -/
theorem sublinear_counting_finite_mass {κ : ℝ} (hκ : 0 < κ) (hk : κ < 1) :
    (support κ).Infinite ∧ (∀ n ∈ support κ, 0 < n) ∧
      (∀ X : ℝ, 0 ≤ X → ⌊X^κ⌋₊ ≤ counting κ X) ∧
      Summable (fun n : support κ => 1/(n.val : ℝ)) := by
  refine ⟨support_infinite hκ hk, ?_, fun _ hX => counting_lower_bound hκ hk hX,
    summable_reciprocal_support hκ hk⟩
  rintro n ⟨i, rfl⟩
  exact sequence_pos hκ i

end BTCalculus.SublinearCountingMass

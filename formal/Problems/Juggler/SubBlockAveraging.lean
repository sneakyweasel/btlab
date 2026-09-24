import Mathlib

/-!
# Sub-block averaging for count-poor fibres

The combinatorial core of Lemma E9 (`docs/problems/juggler_depth_five_production.md`,
Result 23). Cut a fibre into full blocks of size `L` with deviations `dev i`,
`|dev i| ≤ L`, plus partial pieces. If the fibre's total deviation is at least
`η H`, where `H` bounds the total block size, then a positive proportion of the
blocks are bad: those with `|dev i| ≥ (η/2) L` have total size at least
`(3/10) η H`. This is what lets the depth-five poor tails use differenced sums only
at shifts below a small power of `P`. Nothing here concerns the Juggler map.
-/

namespace Problems.Juggler.SubBlockAveraging

open Finset

/-- Blocks whose deviation is at least `(η/2) L` carry total size at least
`(3/10) η H`, once the block deviations sum in absolute value to `(4/5) η H`. -/
theorem bad_blocks_mass {ι : Type*} (s : Finset ι) (dev : ι → ℝ) {L η H : ℝ}
    (hL : 0 ≤ L) (hη : 0 ≤ η) (hdev : ∀ i ∈ s, |dev i| ≤ L)
    (hH : (s.card : ℝ) * L ≤ H) (hsum : 4 / 5 * η * H ≤ ∑ i ∈ s, |dev i|) :
    3 / 10 * η * H ≤ ((s.filter fun i => η / 2 * L ≤ |dev i|).card : ℝ) * L := by
  classical
  set b := s.filter fun i => η / 2 * L ≤ |dev i|
  set g := s.filter fun i => ¬ η / 2 * L ≤ |dev i|
  have hsplit := sum_filter_add_sum_filter_not s (fun i => η / 2 * L ≤ |dev i|)
    (fun i => |dev i|)
  have hb : ∑ i ∈ b, |dev i| ≤ (b.card : ℝ) * L := by
    have := sum_le_card_nsmul b (fun i => |dev i|) L
      (fun i hi => hdev i (mem_filter.mp hi).1)
    simpa [nsmul_eq_mul] using this
  have hg : ∑ i ∈ g, |dev i| ≤ (g.card : ℝ) * (η / 2 * L) := by
    have := sum_le_card_nsmul g (fun i => |dev i|) (η / 2 * L)
      (fun i hi => le_of_lt (not_le.mp (mem_filter.mp hi).2))
    simpa [nsmul_eq_mul] using this
  have hgcard : (g.card : ℝ) ≤ s.card := by
    exact_mod_cast card_filter_le s _
  have hgH : (g.card : ℝ) * (η / 2 * L) ≤ η / 2 * H := by
    have h1 : (g.card : ℝ) * L ≤ H :=
      (mul_le_mul_of_nonneg_right hgcard hL).trans hH
    nlinarith
  have hbg : ∑ i ∈ s, |dev i| = ∑ i ∈ b, |dev i| + ∑ i ∈ g, |dev i| := hsplit.symm
  linarith

/-- A fibre with total deviation at least `η H`, split into full blocks and a
remainder of absolute deviation at most `η H / 5`, contains bad blocks of total size
at least `(3/10) η H`. -/
theorem poor_fibre_bad_blocks {ι : Type*} (s : Finset ι) (dev : ι → ℝ) {L η H p : ℝ}
    (hL : 0 ≤ L) (hη : 0 ≤ η) (hdev : ∀ i ∈ s, |dev i| ≤ L)
    (hH : (s.card : ℝ) * L ≤ H) (hp : |p| ≤ η * H / 5)
    (hpoor : η * H ≤ |∑ i ∈ s, dev i + p|) :
    3 / 10 * η * H ≤ ((s.filter fun i => η / 2 * L ≤ |dev i|).card : ℝ) * L := by
  apply bad_blocks_mass s dev hL hη hdev hH
  have h1 := abs_add_le (∑ i ∈ s, dev i) p
  have h2 := abs_sum_le_sum_abs (fun i => dev i) s
  linarith

end Problems.Juggler.SubBlockAveraging

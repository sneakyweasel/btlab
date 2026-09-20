import Problems.Juggler.FateFiberLock
import Problems.Juggler.FateResonanceCount

namespace Problems.Juggler

open Finset
open scoped Classical

namespace FiberParity

/-!
# The poor-fiber tail

`docs/theory/juggler_oe_poor_fiber_tail_note.md`, Theorem 4: for fixed `η₀` the fibers
whose parity share misses `1/2` by `η₀` or more are `O(u^{2/3})` on a dyadic block, so
their `1/m`-weighted mass beyond `U` is `O(U^{-1/3})` and the poor set has finite total
logarithmic mass.

The composition is the note's. `fiber_lock` (Lemma 2) says a poor fiber resonates at some
`q ≤ 3.77/η₀` with width `32/(η₀ H_m)`; `resonance_count_le'` (Lemma 3) counts the
resonant `m` on `(u, 2u]`. The only work between them is uniformity: Lemma 2's width
depends on `H_m`, which varies over the block, so it is replaced by the width at the
block's smallest fiber through `resonant_mono`, and `H_m ≥ (2/3)u^{1/3} - 1` supplies
that (`oeFiber_card_ge`).

`Poor` is stated on `(oeFiber m).card` rather than on `Hlen m hne`, so that it is a
predicate on `m` alone with no nonemptiness proof inside it; `Hlen_eq` identifies the two
wherever Lemma 2 is applied.

Not a halt theorem, and not a statement about any individual fiber: it is a bound on how
many can be unbalanced, which is what the averaging question needed.
-/

/-! ### The fiber is nonempty at the scales in play -/

/-- For `m ≥ 10^6` the `OE` fiber is nonempty: `oeFiber_card_ge` gives at least
`(2/3) m^{1/3} - 1 ≥ 65` members. -/
theorem oeFiber_nonempty {m : ℕ} (hm : 10 ^ 6 ≤ m) : (oeFiber m).Nonempty := by
  have hm1 : 1 ≤ m := by omega
  have hcard := oeFiber_card_ge hm1
  have he := eps_le hm
  have hep := eps_pos hm1
  have hmul := eps_mul_cbrt hm1
  have h100 : (100 : ℝ) ≤ (m : ℝ) ^ ((1 : ℝ) / 3) := by nlinarith [hmul, he, hep]
  have hpos : (0 : ℝ) < ((oeFiber m).card : ℝ) := by linarith
  have : 0 < (oeFiber m).card := by exact_mod_cast hpos
  exact Finset.card_pos.mp this

/-! ### Poor fibers -/

/-- A fiber is `η₀`-poor when its parity share misses `1/2` by at least `η₀`. Written
un-divided, so that no positivity side condition on `H_m` is needed. -/
def Poor (η₀ : ℝ) (m : ℕ) : Prop :=
  η₀ * ((oeFiber m).card : ℝ) ≤
    |(evenImageCount m : ℝ) - ((oeFiber m).card : ℝ) / 2|

/-- Resonance only widens. -/
theorem resonant_mono {Q : ℕ} {δ δ' : ℝ} {m : ℕ} (h : Resonant Q δ m) (hδ : δ ≤ δ') :
    Resonant Q δ' m := by
  obtain ⟨q, hq1, hqQ, P, hP⟩ := h
  exact ⟨q, hq1, hqQ, P, le_trans hP hδ⟩

/-! ### Lemma 2, as an inclusion of the poor set in a resonant set -/

/-- **A poor fiber is resonant.** `fiber_lock` in the shape the count consumes: the
denominator bound becomes `q ≤ ⌊3.77/η₀⌋₊` and the width is the one at this fiber. -/
theorem poor_resonant {m : ℕ} (hm : 10 ^ 6 ≤ m) {η₀ : ℝ} (hη0 : 0 < η₀) (hη1 : η₀ ≤ 1 / 2)
    (hH : 1280 / η₀ ^ 2 ≤ ((oeFiber m).card : ℝ)) (hp : Poor η₀ m) :
    Resonant ⌊3.77 / η₀⌋₊ (32 / (η₀ * ((oeFiber m).card : ℝ))) m := by
  have hne := oeFiber_nonempty hm
  have hHeq : (Hlen m hne : ℝ) = ((oeFiber m).card : ℝ) := by
    rw [Hlen_eq hne]
  have hH' : 1280 / η₀ ^ 2 ≤ (Hlen m hne : ℝ) := by rw [hHeq]; exact hH
  have hp' : η₀ * (Hlen m hne : ℝ) ≤
      |(evenImageCount m : ℝ) - (Hlen m hne : ℝ) / 2| := by rw [hHeq]; exact hp
  obtain ⟨q, hq1, hqle, P, hP⟩ := fiber_lock hm hne hη0 hη1 hH' hp'
  refine ⟨q, hq1, Nat.le_floor hqle, P, ?_⟩
  rw [← hHeq]
  exact hP


/-! ### Theorem 4: the block count -/

/-- **Theorem 4 (poor-fiber tail), one dyadic block.** For `u ≥ 10^6` and `η₀ ∈ (0, 1/2]`,
if the block's smallest fiber already satisfies Lemma 2's hypothesis
(`1280/η₀² ≤ (2/3)u^{1/3} - 1`) and the resulting width is below `1/2`, then the `η₀`-poor
`m ∈ (u, 2u]` are counted by Lemma 3 at the uniform width.

The two lemmas meet here and nowhere else: `poor_resonant` turns poorness into resonance at
this fiber's width, `resonant_mono` widens it to the block's, and `resonance_count_le'`
counts. The note's `420 u^{2/3}/η₀²` is this bound with the arithmetic done; it is left
symbolic so that the constant is the reader's to check against the note rather than
Lean's to assert. -/
theorem poor_count_le {u : ℕ} (hu : 10 ^ 6 ≤ u) {η₀ : ℝ} (hη0 : 0 < η₀) (hη1 : η₀ ≤ 1 / 2)
    (hB : 1280 / η₀ ^ 2 ≤ 2 / 3 * (u : ℝ) ^ ((1 : ℝ) / 3) - 1)
    (hδ2 : 32 / (η₀ * (2 / 3 * (u : ℝ) ^ ((1 : ℝ) / 3) - 1)) < 1 / 2) :
    (#{m ∈ Finset.Ioc u (2 * u) | Poor η₀ m} : ℝ) ≤
      (0.882 * (u : ℝ) ^ ((2 : ℝ) / 3) + 2) *
        (2 * (⌊3.77 / η₀⌋₊ : ℝ) *
              (32 / (η₀ * (2 / 3 * (u : ℝ) ^ ((1 : ℝ) / 3) - 1))) *
              ((2 * u : ℕ) : ℝ) ^ ((1 : ℝ) / 3)
          + (⌊3.77 / η₀⌋₊ : ℝ) * ((⌊3.77 / η₀⌋₊ : ℝ) + 1)) := by
  set B : ℝ := 2 / 3 * (u : ℝ) ^ ((1 : ℝ) / 3) - 1 with hBdef
  set Q : ℕ := ⌊3.77 / η₀⌋₊ with hQdef
  set δ : ℝ := 32 / (η₀ * B) with hδdef
  have hBpos : 0 < B := by
    have h : (0 : ℝ) < 1280 / η₀ ^ 2 := by positivity
    linarith
  have hδ0 : 0 ≤ δ := by rw [hδdef]; positivity
  have hsub : {m ∈ Finset.Ioc u (2 * u) | Poor η₀ m} ⊆
      {m ∈ Finset.Ioc u (2 * u) | Resonant Q δ m} := by
    intro m hm
    rw [Finset.mem_filter, Finset.mem_Ioc] at hm
    rw [Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨hm.1, ?_⟩
    have hmu : u < m := hm.1.1
    have hm6 : 10 ^ 6 ≤ m := by omega
    have hcard : B ≤ ((oeFiber m).card : ℝ) := by
      have h := oeFiber_card_ge (m := m) (by omega)
      have hmono : (u : ℝ) ^ ((1 : ℝ) / 3) ≤ (m : ℝ) ^ ((1 : ℝ) / 3) :=
        Real.rpow_le_rpow (by positivity) (by exact_mod_cast hmu.le) (by norm_num)
      rw [hBdef]
      linarith
    have hcpos : (0 : ℝ) < ((oeFiber m).card : ℝ) := lt_of_lt_of_le hBpos hcard
    have hres := poor_resonant hm6 hη0 hη1 (le_trans hB hcard) hm.2
    refine resonant_mono hres ?_
    rw [hδdef, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hcard, hη0, hBpos]
  have hcount := resonance_count_le' hu Q hδ0 hδ2
  have hcards : (#{m ∈ Finset.Ioc u (2 * u) | Poor η₀ m} : ℝ) ≤
      (#{m ∈ Finset.Ioc u (2 * u) | Resonant Q δ m} : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  exact le_trans hcards hcount

end FiberParity

end Problems.Juggler

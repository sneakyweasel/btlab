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


/-! ### The block count with the note's constant -/

/-- `B_u = (2/3) u^{1/3} - 1 ≥ 0.6566 u^{1/3}` for `u ≥ 10^6`: the `-1` costs at most a
hundredth of the main term once `u^{1/3} ≥ 100`. -/
theorem B_ge {u : ℕ} (hu : 10 ^ 6 ≤ u) :
    0.6566 * (u : ℝ) ^ ((1 : ℝ) / 3) ≤ 2 / 3 * (u : ℝ) ^ ((1 : ℝ) / 3) - 1 := by
  have hu1 : 1 ≤ u := by omega
  have he := eps_le hu
  have hep := eps_pos hu1
  have hmul := eps_mul_cbrt hu1
  have h100 : (100 : ℝ) ≤ (u : ℝ) ^ ((1 : ℝ) / 3) := by nlinarith [hmul, he, hep]
  linarith

/-- `(2u)^{1/3} ≤ 1.26 u^{1/3}`. -/
theorem two_mul_cbrt_le {u : ℕ} (hu : 1 ≤ u) :
    ((2 * u : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤ 1.26 * (u : ℝ) ^ ((1 : ℝ) / 3) := by
  have hu0 : (0 : ℝ) ≤ (u : ℝ) := by positivity
  have hcast : ((2 * u : ℕ) : ℝ) = 2 * (u : ℝ) := by push_cast; ring
  rw [hcast, Real.mul_rpow (by norm_num) hu0]
  have h := two_rpow_third_le
  have hp : (0 : ℝ) ≤ (u : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hu0 _
  nlinarith

/-- **Theorem 4, the block count with an explicit constant.** `430 u^{2/3}/η₀²`.

The note claims `420`. That figure assumed the second term of Lemma 3 was `Q(Q+1)/2`,
the Gauss sum; `resonance_count_le'` delivers `Q(Q+1)`, because `arc_count_le` counts a
half-open arc while `‖q A_m‖ ≤ δ` is closed, so each of the `Q` arcs is widened by one
point. Carried through, `2·3.77·61.5 + 18 = 481.71` against `0.8825 u^{2/3}` gives
`425.11`, so `420` is false and `430` is the honest constant. Nothing downstream moves:
the note already records that only the positivity of the exponent matters, never the
size of the constant. -/
theorem poor_count_le' {u : ℕ} (hu : 10 ^ 6 ≤ u) {η₀ : ℝ} (hη0 : 0 < η₀) (hη1 : η₀ ≤ 1 / 2)
    (hB : 1280 / η₀ ^ 2 ≤ 2 / 3 * (u : ℝ) ^ ((1 : ℝ) / 3) - 1)
    (hδ2 : 32 / (η₀ * (2 / 3 * (u : ℝ) ^ ((1 : ℝ) / 3) - 1)) < 1 / 2) :
    (#{m ∈ Finset.Ioc u (2 * u) | Poor η₀ m} : ℝ) ≤ 430 * (u : ℝ) ^ ((2 : ℝ) / 3) / η₀ ^ 2 := by
  have hu1 : 1 ≤ u := by omega
  have hmain := poor_count_le hu hη0 hη1 hB hδ2
  set c : ℝ := (u : ℝ) ^ ((1 : ℝ) / 3) with hcdef
  have hc0 : 0 < c := Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < u)) _
  set B : ℝ := 2 / 3 * c - 1 with hBdef
  have hBge : 0.6566 * c ≤ B := B_ge hu
  have hBpos : 0 < B := by nlinarith [hc0, hBge]
  set Q : ℝ := (⌊3.77 / η₀⌋₊ : ℝ) with hQdef
  have hQle : Q ≤ 3.77 / η₀ := Nat.floor_le (by positivity)
  have hQ0 : 0 ≤ Q := by positivity
  have hinv : 0 < 1 / η₀ := by positivity
  -- the width of one arc, uniformly on the block
  have hstep : (32 : ℝ) / (η₀ * B) * ((2 * u : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤ 61.5 / η₀ := by
    have h2u := two_mul_cbrt_le hu1
    have hcbrt0 : (0 : ℝ) ≤ ((2 * u : ℕ) : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_nonneg (by positivity) _
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hη0]
    nlinarith [h2u, hBge, hc0, hη0, hBpos, hcbrt0,
      mul_le_mul_of_nonneg_left h2u (le_of_lt hη0),
      mul_le_mul_of_nonneg_left hBge (le_of_lt hη0)]
  -- the two terms
  have hwidth : 2 * Q * (32 / (η₀ * B)) * ((2 * u : ℕ) : ℝ) ^ ((1 : ℝ) / 3)
      ≤ 463.71 * (1 / η₀) ^ 2 := by
    have hcnn : (0 : ℝ) ≤ (32 : ℝ) / (η₀ * B) * ((2 * u : ℕ) : ℝ) ^ ((1 : ℝ) / 3) :=
      mul_nonneg (div_nonneg (by norm_num) (le_of_lt (mul_pos hη0 hBpos)))
        (Real.rpow_nonneg (by positivity) _)
    have h1 : Q * ((32 : ℝ) / (η₀ * B) * ((2 * u : ℕ) : ℝ) ^ ((1 : ℝ) / 3))
        ≤ (3.77 / η₀) * (61.5 / η₀) :=
      mul_le_mul hQle hstep hcnn (by positivity)
    have h2 : (3.77 : ℝ) / η₀ * (61.5 / η₀) = 231.855 * (1 / η₀) ^ 2 := by
      field_simp
      ring
    rw [h2] at h1
    nlinarith [h1]
  have harc : Q * (Q + 1) ≤ 18 * (1 / η₀) ^ 2 := by
    have h1 : Q ≤ 3.77 * (1 / η₀) := by
      rw [show (3.77 : ℝ) * (1 / η₀) = 3.77 / η₀ by ring]; exact hQle
    have h2 : (1 : ℝ) ≤ 1 / η₀ := by rw [le_div_iff₀ hη0]; linarith
    nlinarith [h1, h2, hQ0]
  -- the window factor
  have hu23 : (0 : ℝ) ≤ (u : ℝ) ^ ((2 : ℝ) / 3) := Real.rpow_nonneg (by positivity) _
  have hwin : 0.882 * (u : ℝ) ^ ((2 : ℝ) / 3) + 2 ≤ 0.8825 * (u : ℝ) ^ ((2 : ℝ) / 3) := by
    linarith [rpow_two_thirds_ge hu]
  have hsum0 : (0 : ℝ) ≤ 2 * Q * (32 / (η₀ * B)) * ((2 * u : ℕ) : ℝ) ^ ((1 : ℝ) / 3)
      + Q * (Q + 1) := by positivity
  have hinv2 : (1 / η₀) ^ 2 = 1 / η₀ ^ 2 := by rw [div_pow]; norm_num
  calc (#{m ∈ Finset.Ioc u (2 * u) | Poor η₀ m} : ℝ)
      ≤ (0.882 * (u : ℝ) ^ ((2 : ℝ) / 3) + 2) *
          (2 * Q * (32 / (η₀ * B)) * ((2 * u : ℕ) : ℝ) ^ ((1 : ℝ) / 3) + Q * (Q + 1)) := hmain
    _ ≤ (0.8825 * (u : ℝ) ^ ((2 : ℝ) / 3)) * (481.71 * (1 / η₀) ^ 2) := by
        apply mul_le_mul hwin (by linarith [hwidth, harc]) hsum0 (by positivity)
    _ ≤ 430 * (u : ℝ) ^ ((2 : ℝ) / 3) / η₀ ^ 2 := by
        have hrw : (0.8825 * (u : ℝ) ^ ((2 : ℝ) / 3)) * (481.71 * (1 / η₀) ^ 2)
            = (0.8825 * 481.71 * (u : ℝ) ^ ((2 : ℝ) / 3)) / η₀ ^ 2 := by
          field_simp
        rw [hrw, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hu23, sq_nonneg η₀]

end FiberParity

end Problems.Juggler

/-
# Paper B, Theorems 5.2-5.4: the certificate count assembly

`docs/theory/juggler_parity_discrepancy_note.md`, Section 5.  `PaperBCertificates`
proved the combinatorial half (Lemma 5.1: the minimal certificates through length five
are `E, OE, OOEE, OOOEE, OOEOE`) and recorded the printed density as the rational
identity `1/2 + 1/4 + 1/16 + 1/32 + 1/32 = 7/8`.  That identity is attached to nothing:
it is `norm_num` on five literals, and `DepthFourFive.cor64_density` proves the same
five literals a second time.  Neither says the five cylinders are disjoint, neither says
they exhaust the certified words, and neither mentions a Juggler start.

This file supplies the assembly those numbers were supposed to summarise, and states it
over real starts rather than formal measures.  `RateFreeDensity.lean` already carries the
counting layer -- `allWords`, `classCount w N` (the starts in `{1,…,N}` whose length-`|w|`
itinerary is `w`), `neverNegWords` and `itinerary_take`, all in `Problems.Juggler` itself
-- so nothing here re-invents it.

Four sections.

1. **The certified words at a fixed depth.**  `certifiedWords d` is the complement of
   `RateFreeDensity.neverNegWords d`: the length-`d` words with a contracting prefix.
   Its cardinality is `13` at `d = 4`, `28` at `d = 5`, `56` at `d = 6` and `115` at
   `d = 7`, all by `decide +kernel`.  These are the numerators the paper prints as
   `13/16`, `7/8`, `7/8` -- the last of which the paper does not print, because depth six
   adds nothing.
2. **The partition.**  At depth five the five certificates' cylinders are pairwise
   disjoint and their union is exactly `certifiedWords 5`, with block sizes
   `16, 8, 2, 1, 1`.  This is the content the rational identity stood in for:
   `16 + 8 + 2 + 1 + 1 = 28` and `28 / 32 = 7/8`.
3. **The count over real starts.**  Because a start is certified at depth five exactly
   when its length-five itinerary lies in one of the five cylinders, and a cylinder is a
   condition on a prefix, the certified count is the sum of five `classCount`s.  That
   equality is Theorem 5.4's assembly; the five summands are what Theorem 3.1 and
   Corollaries 4.6, 4.10 and 4.12 estimate, and this file proves none of them.
4. **The error bookkeeping.**  The triangle inequality behind "add Theorem 5.3 and
   Corollary 4.12, the former error is smaller", and the exponent ordering
   `5/6 < 23/24 < 47/48 < 127/128 < 1` that licenses the absorption.

**Lemma 5.1 extends past the printed length five, and the extension is decidable.**
Depth six contributes no new minimal certificate at all -- which is why the density is
still `7/8` there -- and depth seven contributes exactly three, `OOEOOEE`, `OOOEOEE`,
`OOOOEEE`, taking the combinatorial certificate density to `115/128`.  Section 5 stops at
five because that is where the analysis stops, not where the combinatorics stops: each
new word needs its own mixed-mode estimate, and this file supplies none.

**What is not here.**  No exponential sum, no discrepancy estimate, no equidistribution
input.  Every analytic count is a hypothesis, exactly as in `PaperBAssembly`.  Nothing
here bounds `#(C_5 ∩ [1,N])` on its own, and nothing here is a termination statement.
-/

import Mathlib.Tactic
import Problems.Juggler.PaperBCertificates
import Problems.Juggler.RateFreeDensity

namespace Problems.Juggler

open Finset PaperBCertificates

/-! ## 1. The certified words at a fixed depth -/

/-- The length-`d` words carrying a descent certificate: those with a contracting
prefix. The complement of `RateFreeDensity.neverNegWords d` inside `allWords d`. -/
def certifiedWords (d : ℕ) : Finset (List Branch) :=
  (allWords d).filter (fun w => ¬ prefixNoncontracting w)

/-- `#C_d` as a count of words. -/
def certifiedWordCount (d : ℕ) : ℕ := (certifiedWords d).card

/-- The certified words of length `d` are words of length `d`. -/
theorem certifiedWords_subset (d : ℕ) : certifiedWords d ⊆ allWords d :=
  filter_subset _ _

/-- Certified and never-negative words partition `allWords d`. -/
theorem certifiedWords_compl (d : ℕ) :
    certifiedWords d = allWords d \ neverNegWords d := by
  classical
  ext w
  simp only [certifiedWords, neverNegWords]
  constructor
  · intro hw
    have hw' := mem_filter.mp hw
    refine mem_sdiff.mpr ⟨hw'.1, fun hmem => hw'.2 (mem_filter.mp hmem).2⟩
  · intro hw
    have hw' := mem_sdiff.mp hw
    exact mem_filter.mpr ⟨hw'.1, fun hp => hw'.2 (mem_filter.mpr ⟨hw'.1, hp⟩)⟩

/-- `allWords d` has `2 ^ d` elements, in `ℕ`.  `FateEnergyAtoms.card_allWords` states
this over `ℝ`, but that module sits in the fate layer; Paper B should not import it for a
counting fact. -/
theorem card_allWords_nat : ∀ d : ℕ, (allWords d).card = 2 ^ d
  | 0 => rfl
  | d + 1 => by
      classical
      rw [allWords_succ, card_biUnion (fun x _ y _ hne => extend_fiber_disjoint hne)]
      have hpair : ∀ w : List Branch,
          ({w ++ [.even], w ++ [.odd]} : Finset (List Branch)).card = 2 := by
        intro w
        rw [card_insert_of_notMem (by
          simp only [mem_singleton]
          intro h
          exact Branch.noConfusion (append_singleton_inj h).2), card_singleton]
      simp only [hpair, sum_const, smul_eq_mul]
      rw [card_allWords_nat d, pow_succ]

/-- `#C_d + N_d = 2^d`: every word is certified or never-negative, never both. -/
theorem certifiedWordCount_add_neverNegCount (d : ℕ) :
    certifiedWordCount d + neverNegCount d = 2 ^ d := by
  classical
  rw [certifiedWordCount, certifiedWords_compl, neverNegCount,
    card_sdiff_add_card_eq_card (neverNegWords_subset d), card_allWords_nat d]

/-! ## 2. The counts the paper prints

`13/16` is Theorem 5.2, `7/8` is Theorem 5.4, and the depth-six value is the one the
paper has no reason to print: depth six adds no certificate, so the density does not move.
-/

/-- `#C_4 = 13`: thirteen of the `16` words of length four have a contracting prefix. -/
theorem certifiedWordCount_four : certifiedWordCount 4 = 13 := by decide +kernel

/-- `#C_5 = 28`: twenty-eight of the `32` words of length five have a contracting prefix. -/
theorem certifiedWordCount_five : certifiedWordCount 5 = 28 := by decide +kernel

/-- `#C_6 = 56`: fifty-six of the `64` words of length six have a contracting prefix. -/
theorem certifiedWordCount_six : certifiedWordCount 6 = 56 := by decide +kernel

/-- **Theorem 5.2's density, as a count.** -/
theorem four_step_density : (certifiedWordCount 4 : ℚ) / 2 ^ 4 = 13 / 16 := by
  rw [certifiedWordCount_four]; norm_num

/-- **Theorem 5.4's density, as a count.**  This is what
`PaperBCertificates.certificate_measures_sum` and `DepthFourFive.cor64_density` assert
as an identity between five rational literals: here the `7/8` is the number of certified
words over the number of words. -/
theorem five_step_density : (certifiedWordCount 5 : ℚ) / 2 ^ 5 = 7 / 8 := by
  rw [certifiedWordCount_five]; norm_num

/-- **Depth six adds nothing.**  The density is still `7/8`, so Section 5 stopping at five
costs no certificate. -/
theorem six_step_density : (certifiedWordCount 6 : ℚ) / 2 ^ 6 = 7 / 8 := by
  rw [certifiedWordCount_six]; norm_num

/-! ## 3. The partition behind the `7/8` -/

/-- The length-`d` words extending `c`: the cylinder of `c` cut to depth `d`.
A set of **words**, unlike `FateChernoff.cylinder`, which is the set of odd starts in
`(y, 2y]` realizing a given word. -/
def wordCylinder (c : List Branch) (d : ℕ) : Finset (List Branch) :=
  (allWords d).filter (fun w => c <+: w)

/-- The depth-five cylinder of `E` holds `16` words. -/
theorem wordCylinder_card_E : (wordCylinder certE 5).card = 16 := by decide +kernel
/-- The depth-five cylinder of `OE` holds `8` words. -/
theorem wordCylinder_card_OE : (wordCylinder certOE 5).card = 8 := by decide +kernel
/-- The depth-five cylinder of `OOEE` holds `2` words. -/
theorem wordCylinder_card_OOEE : (wordCylinder certOOEE 5).card = 2 := by decide +kernel
/-- The depth-five cylinder of `OOOEE` holds `1` word. -/
theorem wordCylinder_card_OOOEE : (wordCylinder certOOOEE 5).card = 1 := by decide +kernel
/-- The depth-five cylinder of `OOEOE` holds `1` word. -/
theorem wordCylinder_card_OOEOE : (wordCylinder certOOEOE 5).card = 1 := by decide +kernel

/-- **The five cylinders cover the certified words at depth five.** -/
theorem five_cylinders_cover :
    wordCylinder certE 5 ∪ wordCylinder certOE 5 ∪ wordCylinder certOOEE 5
        ∪ wordCylinder certOOOEE 5 ∪ wordCylinder certOOEOE 5
      = certifiedWords 5 := by
  decide +kernel

/-- **And they are disjoint**, because their sizes add to the size of the union.
`16 + 8 + 2 + 1 + 1 = 28`, which is the main-term arithmetic Theorem 5.4 prints as
`1/2 + 1/4 + 1/16 + 1/32 + 1/32`. -/
theorem five_cylinders_card_sum :
    (wordCylinder certE 5).card + (wordCylinder certOE 5).card + (wordCylinder certOOEE 5).card
      + (wordCylinder certOOOEE 5).card + (wordCylinder certOOEOE 5).card
      = certifiedWordCount 5 := by
  decide +kernel

/-- The printed measures are the cylinder counts. -/
theorem printed_measures_are_counts :
    ((wordCylinder certE 5).card : ℚ) / 32 = 1 / 2 ∧
    ((wordCylinder certOE 5).card : ℚ) / 32 = 1 / 4 ∧
    ((wordCylinder certOOEE 5).card : ℚ) / 32 = 1 / 16 ∧
    ((wordCylinder certOOOEE 5).card : ℚ) / 32 = 1 / 32 ∧
    ((wordCylinder certOOEOE 5).card : ℚ) / 32 = 1 / 32 := by
  rw [wordCylinder_card_E, wordCylinder_card_OE, wordCylinder_card_OOEE, wordCylinder_card_OOOEE,
    wordCylinder_card_OOEOE]
  norm_num

/-! ## 4. The count over real starts

Sections 1-3 are about words. This section is about starts: the certified count of
`{1,…,N}` is a sum of five `classCount`s, one per printed prefix class. The bridge is
`itinerary_take` -- a start's depth-five itinerary extends `c` exactly when its
depth-`|c|` itinerary *is* `c` -- so a cylinder condition at depth five is the prefix
condition the manuscript's estimates are stated for.
-/

/-- Starts in `{1,…,N}` carrying a descent certificate by depth `d`. -/
def certifiedCount (d N : ℕ) : ℕ :=
  ((Icc 1 N).filter (fun n => ¬ prefixNoncontracting (itinerary n d))).card

/-- Every start in `{1,…,N}` is either certified by depth `d` or not:
`certifiedCount d N + uncertifiedCount d N = N`. -/
theorem certifiedCount_add_uncertifiedCount (d N : ℕ) :
    certifiedCount d N + uncertifiedCount d N = N := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s := Icc 1 N)
    (p := fun n => prefixNoncontracting (itinerary n d))
  have hIcc : (Icc 1 N).card = N := by rw [Nat.card_Icc]; omega
  rw [hIcc] at h
  rw [certifiedCount, uncertifiedCount, add_comm]
  omega

/-- A word lies in the depth-`d` cylinder of `c` exactly when it has length `d` and
extends `c`. -/
theorem mem_wordCylinder_iff {c w : List Branch} {d : ℕ} :
    w ∈ wordCylinder c d ↔ w.length = d ∧ c <+: w := by
  simp [wordCylinder, mem_filter, mem_allWords]

/-- A start's depth-`d` itinerary extends `c` exactly when its depth-`|c|` itinerary
is `c`. -/
theorem prefix_itinerary_iff {c : List Branch} {d n : ℕ} (hcd : c.length ≤ d) :
    c <+: itinerary n d ↔ itinerary n c.length = c := by
  rw [List.prefix_iff_eq_take, itinerary_take n d c.length hcd]
  exact eq_comm

/-- **Summing depth-`d` class counts over a cylinder gives the prefix class count.**
This is the step that lets Theorem 5.4's five summands be the quantities Theorem 3.1
and Corollaries 4.6, 4.10 and 4.12 estimate. -/
theorem sum_classCount_cylinder {c : List Branch} {d N : ℕ} (hcd : c.length ≤ d) :
    ∑ w ∈ wordCylinder c d, classCount w N = classCount c N := by
  classical
  have hdisj : ∀ x ∈ wordCylinder c d, ∀ y ∈ wordCylinder c d, x ≠ y →
      Disjoint ((Icc 1 N).filter (fun n => itinerary n d = x))
        ((Icc 1 N).filter (fun n => itinerary n d = y)) :=
    fun _ _ _ _ hne => classCount_fiber_disjoint hne
  have hunion :
      (Icc 1 N).filter (fun n => itinerary n c.length = c) =
        (wordCylinder c d).biUnion fun w => (Icc 1 N).filter (fun n => itinerary n d = w) := by
    ext n
    simp only [mem_biUnion, mem_filter, mem_Icc]
    constructor
    · intro ⟨hn, hc⟩
      refine ⟨itinerary n d, ?_, hn, rfl⟩
      exact mem_wordCylinder_iff.mpr ⟨itinerary_length n d, (prefix_itinerary_iff hcd).mpr hc⟩
    · intro ⟨w, hw, hn, heq⟩
      refine ⟨hn, ?_⟩
      have hpre : c <+: itinerary n d := heq ▸ (mem_wordCylinder_iff.mp hw).2
      exact (prefix_itinerary_iff hcd).mp hpre
  calc ∑ w ∈ wordCylinder c d, classCount w N
      = ∑ w ∈ wordCylinder c d, ((Icc 1 N).filter (fun n => itinerary n d = w)).card := by
        refine Finset.sum_congr rfl (fun w hw => ?_)
        exact classCount_eq (mem_allWords.mpr (mem_wordCylinder_iff.mp hw).1)
    _ = ((wordCylinder c d).biUnion fun w =>
          (Icc 1 N).filter (fun n => itinerary n d = w)).card := by
        rw [card_biUnion hdisj]
    _ = ((Icc 1 N).filter (fun n => itinerary n c.length = c)).card := by rw [← hunion]
    _ = classCount c N := rfl

/-- **Theorem 5.4's assembly over real starts.**  The certified count at depth five is
the sum of the five printed prefix-class counts.  Combined with Theorem 3.1 and
Corollaries 4.6, 4.10 and 4.12 -- none of them proved anywhere in this repository -- this
is the equality the paper's `7N/8 + O_ε(N^(127/128+ε))` rests on. -/
theorem certifiedCount_five_eq (N : ℕ) :
    certifiedCount 5 N = classCount certE N + classCount certOE N + classCount certOOEE N
      + classCount certOOOEE N + classCount certOOEOE N := by
  classical
  have hsum : ∀ w : List Branch, w.length ≤ 5 →
      ∑ v ∈ wordCylinder w 5, classCount v N = classCount w N :=
    fun w hw => sum_classCount_cylinder hw
  have hcert : certifiedCount 5 N = ∑ w ∈ certifiedWords 5, classCount w N := by
    have hdisj : ∀ x ∈ certifiedWords 5, ∀ y ∈ certifiedWords 5, x ≠ y →
        Disjoint ((Icc 1 N).filter (fun n => itinerary n 5 = x))
          ((Icc 1 N).filter (fun n => itinerary n 5 = y)) :=
      fun _ _ _ _ hne => classCount_fiber_disjoint hne
    have hunion :
        (Icc 1 N).filter (fun n => ¬ prefixNoncontracting (itinerary n 5)) =
          (certifiedWords 5).biUnion fun w =>
            (Icc 1 N).filter (fun n => itinerary n 5 = w) := by
      ext n
      simp only [mem_biUnion, mem_filter, mem_Icc]
      constructor
      · intro ⟨hn, hp⟩
        exact ⟨itinerary n 5, mem_filter.mpr ⟨itinerary_mem_allWords n 5, hp⟩, hn, rfl⟩
      · intro ⟨w, hw, hn, heq⟩
        exact ⟨hn, heq ▸ (mem_filter.mp hw).2⟩
    calc certifiedCount 5 N
        = ((certifiedWords 5).biUnion fun w =>
            (Icc 1 N).filter (fun n => itinerary n 5 = w)).card := by
          rw [certifiedCount, hunion]
      _ = ∑ w ∈ certifiedWords 5, ((Icc 1 N).filter (fun n => itinerary n 5 = w)).card :=
          card_biUnion hdisj
      _ = ∑ w ∈ certifiedWords 5, classCount w N := by
          refine Finset.sum_congr rfl (fun w hw => ?_)
          exact (classCount_eq (certifiedWords_subset 5 hw)).symm
  rw [hcert, ← five_cylinders_cover]
  rw [sum_union, sum_union, sum_union, sum_union] <;>
    first
      | (rw [hsum certE (by decide), hsum certOE (by decide), hsum certOOEE (by decide),
            hsum certOOOEE (by decide), hsum certOOEOE (by decide)])
      | (rw [disjoint_left]; decide +kernel)

/-! ## 5. Lemma 5.1 past length five

Depth six adds no minimal certificate, depth seven adds exactly three. Neither fact is
in the manuscript; both are decidable, and neither supplies the mixed-mode estimate each
new word would need.
-/

/-- `OOEOOEE`, one of the three minimal certificates of length seven. -/
def certOOEOOEE : List Branch := [.odd, .odd, .even, .odd, .odd, .even, .even]
/-- `OOOEOEE`, one of the three minimal certificates of length seven. -/
def certOOOEOEE : List Branch := [.odd, .odd, .odd, .even, .odd, .even, .even]
/-- `OOOOEEE`, one of the three minimal certificates of length seven. -/
def certOOOOEEE : List Branch := [.odd, .odd, .odd, .odd, .even, .even, .even]

/-- **Depth six contributes nothing.** -/
theorem no_minimal_certificate_six :
    (allWords 6).filter IsMinimalCertificate = ∅ := by decide +kernel

/-- **Depth seven contributes exactly three.** -/
theorem minimal_certificates_seven :
    (allWords 7).filter IsMinimalCertificate
      = {certOOEOOEE, certOOOEOEE, certOOOOEEE} := by decide +kernel

/-- `#C_7 = 115`: of the `128` words of length seven, `115` have a contracting prefix. -/
theorem certifiedWordCount_seven : certifiedWordCount 7 = 115 := by decide +kernel

/-- The next rung of the table: `115/128`, not `7/8`. -/
theorem seven_step_density : (certifiedWordCount 7 : ℚ) / 2 ^ 7 = 115 / 128 := by
  rw [certifiedWordCount_seven]; norm_num

/-- The gain over Theorem 5.4 is exactly the three new cylinders. -/
theorem seven_step_gain : (115 : ℚ) / 128 - 7 / 8 = 3 * (1 / 128) := by norm_num

/-! ## 6. The error bookkeeping -/

/-- The printed error exponents of Theorems 3.1, 5.2, 5.3 and 5.4, in increasing order.
This is what licenses "absorbing the smaller four-step error". -/
theorem error_exponents_ordered :
    (5 : ℝ) / 6 < 23 / 24 ∧ (23 : ℝ) / 24 < 47 / 48 ∧ (47 : ℝ) / 48 < 127 / 128
      ∧ (127 : ℝ) / 128 < 1 := by
  norm_num

/-- **Absorption.**  At `N ≥ 1` the smaller exponent is dominated. -/
theorem error_absorb {N e f : ℝ} (hN : 1 ≤ N) (hef : e ≤ f) : N ^ e ≤ N ^ f :=
  Real.rpow_le_rpow_of_exponent_le hN hef

/-- **The count assembly, with the analysis as hypotheses.**  Five class counts, each
within its own error of its printed main term, add to `7N/8` within the sum of the
errors.  Every hypothesis here is an analytic estimate this repository does not prove. -/
theorem five_step_error_assembly
    {N cE cOE cOOEE cOOOEE cOOEOE errE errOE errOOEE errOOOEE errOOEOE B : ℝ}
    (hE : |cE - N / 2| ≤ errE) (hOE : |cOE - N / 4| ≤ errOE)
    (hOOEE : |cOOEE - N / 16| ≤ errOOEE) (hOOOEE : |cOOOEE - N / 32| ≤ errOOOEE)
    (hOOEOE : |cOOEOE - N / 32| ≤ errOOEOE)
    (hB : errE + errOE + errOOEE + errOOOEE + errOOEOE ≤ B) :
    |cE + cOE + cOOEE + cOOOEE + cOOEOE - 7 * N / 8| ≤ B := by
  rw [abs_le] at hE hOE hOOEE hOOOEE hOOEOE ⊢
  constructor <;> linarith [hE.1, hE.2, hOE.1, hOE.2, hOOEE.1, hOOEE.2,
    hOOOEE.1, hOOOEE.2, hOOEOE.1, hOOEOE.2]

end Problems.Juggler

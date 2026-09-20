/-
# Paper B: the survivors and the minimal certificates are one recursion

`PaperBFiveStepDensity` counts the words of length `d` carrying a descent certificate;
`RateFreeDensity` counts the survivors `N_d`, the words carrying none;
`PaperBCertificateLengths` says which lengths carry a *minimal* certificate at all. This
file is the identity tying the three together, and it is a one-step decomposition rather
than anything asymptotic.

Extend a word `w` of length `d` by one letter. If `w` already failed -- some prefix of it
contracted -- then `w ++ [b]` fails too, and contributes nowhere. If `w` survived, then
`w ++ [b]` either contracts for the first time, which is exactly what it means to be a
*minimal* certificate of length `d + 1`, or it does not, and it is a survivor of length
`d + 1`. Every survivor of length `d` yields two extensions, and each lands in exactly one
of the two classes:

  `neverNegCount (d+1) + minimalCertCount (d+1) = 2 * neverNegCount d`

which is `N_{d+1} = 2 N_d - M_{d+1}` (`neverNegCount_add_minimalCertCount`). Taking
complements inside `2 ^ d` turns it into the statement about density:

  `certifiedWordCount (d+1) = 2 * certifiedWordCount d + minimalCertCount (d+1)`

so the certificate density gains **exactly** the cylinder measure of the new minimal
certificates at each step (`density_succ`), and gains nothing when there are none
(`density_succ_of_no_new_cert`). `PaperBFiveStepDensity.five_cylinders_card_sum` is the
case `d = 5` of the first, read across the five words at once.

**The plateaus, proved rather than listed.** `PaperBCertificateLengths` shows a minimal
certificate of length `L` exists only when a power of three lies in `[2 ^ (L-1), 2 ^ L)`.
Combining: when no power of three lies there, `minimalCertCount L = 0` and the density
does not move (`density_flat_of_window_empty`). That is why `7/8` holds at both `d = 5`
and `d = 6`, and `237/256` at both `d = 8` and `d = 9` -- not a coincidence of small
numbers but the rotation `beta = log 2 / log 3` missing an integer, and nothing in the
proof mentions a real number.

**What is not here.** The size of `minimalCertCount d` when it is not zero. Measured it
is `1, 1, 0, 1, 2, 0, 3, 7, 0, 12, 0, 30, 85, 0, 173, 476` for `d = 1 … 16`, and the
survival ratio `M_d / (2 N_{d-1})` oscillates -- `0.500, 0.250, 0.333, 0.188, 0.269,
0.158, 0.117, 0.188, …` -- without converging, which is the almost-periodicity
`J-paper-b-meander-prefactor-is-almost-periodic` measures from the other side. This file
gives that ratio an exact combinatorial meaning; it does not evaluate it.
-/

import Mathlib.Tactic
import Problems.Juggler.PaperBFiveStepDensity
import Problems.Juggler.PaperBCertificateLengths

namespace Problems.Juggler

open Finset PaperBCertificates

/-! ## 1. The minimal certificates of a fixed length, as a `Finset` -/

/-- The minimal certificates of length `d`. -/
def minimalCertWords (d : ℕ) : Finset (List Branch) :=
  (allWords d).filter IsMinimalCertificate

/-- `M_d`, the number of minimal certificates of length `d`. -/
def minimalCertCount (d : ℕ) : ℕ := (minimalCertWords d).card

/-! ## 2. One extension step, classified

`prefixNoncontracting` quantifies over `k ≤ length`, so it already says the word itself
does not contract; `IsMinimalCertificate` quantifies over `0 < k < length`. On a word of
the form `w ++ [b]` both reduce to a condition on `w` together with the fate of the whole.
-/

theorem take_concat_of_le {w : List Branch} {b : Branch} {k : ℕ} (hk : k ≤ w.length) :
    (w ++ [b]).take k = w.take k := List.take_append_of_le_length hk

/-- A one-letter extension survives exactly when its base survives and it does not
contract. -/
theorem prefixNoncontracting_concat {w : List Branch} {b : Branch} :
    prefixNoncontracting (w ++ [b]) ↔
      prefixNoncontracting w ∧ ¬ exponentGap (w ++ [b]) := by
  constructor
  · intro h
    refine ⟨fun k hk => ?_, ?_⟩
    · have := h k (by simp; omega)
      rwa [take_concat_of_le hk] at this
    · have := h (w ++ [b]).length le_rfl
      rwa [List.take_length] at this
  · rintro ⟨hw, hgap⟩ k hk
    simp only [List.length_append, List.length_singleton] at hk
    rcases Nat.lt_or_ge k (w.length + 1) with hlt | hge
    · have hkw : k ≤ w.length := by omega
      rw [take_concat_of_le hkw]
      exact hw k hkw
    · have : k = w.length + 1 := by omega
      subst this
      have hlen : (w ++ [b]).length = w.length + 1 := by simp
      rw [show (w ++ [b]).take (w.length + 1) = w ++ [b] by
        rw [← hlen, List.take_length]]
      exact hgap

/-- A one-letter extension is a *minimal* certificate exactly when its base survives and
it does contract. -/
theorem isMinimalCertificate_concat {w : List Branch} {b : Branch} :
    IsMinimalCertificate (w ++ [b]) ↔
      prefixNoncontracting w ∧ exponentGap (w ++ [b]) := by
  constructor
  · rintro ⟨-, hgap, hmin⟩
    refine ⟨fun k hk => ?_, hgap⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp [exponentGap]
    · have hklt : k < (w ++ [b]).length := by simp; omega
      have := hmin k hk0 hklt
      rwa [take_concat_of_le hk] at this
  · rintro ⟨hw, hgap⟩
    refine ⟨by simp, hgap, fun k hk0 hklt => ?_⟩
    simp only [List.length_append, List.length_singleton] at hklt
    have hkw : k ≤ w.length := by omega
    rw [take_concat_of_le hkw]
    exact hw k hkw

/-! ## 3. The recursion -/

theorem survivors_disjoint_certs (d : ℕ) :
    Disjoint (neverNegWords (d + 1)) (minimalCertWords (d + 1)) := by
  classical
  rw [disjoint_left]
  intro v hv hc
  have h1 : prefixNoncontracting v := (mem_filter.mp hv).2
  have h2 : IsMinimalCertificate v := (mem_filter.mp hc).2
  exact (h1 v.length le_rfl) (by simpa using h2.2.1)

/-- **The extensions of the survivors are exactly the survivors and the new minimal
certificates.** -/
theorem extensions_eq_survivors_union_certs (d : ℕ) :
    (neverNegWords d).biUnion (fun w => {w ++ [Branch.even], w ++ [Branch.odd]})
      = neverNegWords (d + 1) ∪ minimalCertWords (d + 1) := by
  classical
  ext v
  simp only [mem_biUnion, mem_union, mem_insert, mem_singleton, neverNegWords,
    minimalCertWords, mem_filter]
  constructor
  · rintro ⟨w, hw, hv⟩
    have hwlen : w.length = d := mem_allWords.mp hw.1
    have hvmem : v ∈ allWords (d + 1) := by
      rcases hv with rfl | rfl <;>
        exact mem_allWords.mpr (by simp [hwlen])
    by_cases hgap : exponentGap v
    · refine Or.inr ⟨hvmem, ?_⟩
      rcases hv with rfl | rfl <;>
        exact isMinimalCertificate_concat.mpr ⟨hw.2, hgap⟩
    · refine Or.inl ⟨hvmem, ?_⟩
      rcases hv with rfl | rfl <;>
        exact prefixNoncontracting_concat.mpr ⟨hw.2, hgap⟩
  · intro h
    have hvmem : v ∈ allWords (d + 1) := by
      rcases h with ⟨hm, -⟩ | ⟨hm, -⟩ <;> exact hm
    have hvlen : v.length = d + 1 := mem_allWords.mp hvmem
    obtain ⟨w, b, rfl⟩ : ∃ w b, v = w ++ [b] := by
      rcases List.eq_nil_or_concat v with rfl | ⟨u, b, rfl⟩
      · simp at hvlen
      · exact ⟨u, b, by simp⟩
    have hwlen : w.length = d := by
      simpa using hvlen
    have hwsurv : prefixNoncontracting w := by
      rcases h with ⟨-, hs⟩ | ⟨-, hc⟩
      · exact (prefixNoncontracting_concat.mp hs).1
      · exact (isMinimalCertificate_concat.mp hc).1
    refine ⟨w, ⟨mem_allWords.mpr hwlen, hwsurv⟩, ?_⟩
    cases b
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- **`N_{d+1} + M_{d+1} = 2 N_d`.**  Each survivor of length `d` has two extensions, and
each extension either survives or contracts for the first time. -/
theorem neverNegCount_add_minimalCertCount (d : ℕ) :
    neverNegCount (d + 1) + minimalCertCount (d + 1) = 2 * neverNegCount d := by
  classical
  have hpair : ∀ w : List Branch,
      ({w ++ [Branch.even], w ++ [Branch.odd]} : Finset (List Branch)).card = 2 := by
    intro w
    rw [card_insert_of_notMem (by
      simp only [mem_singleton]
      intro h
      exact Branch.noConfusion (append_singleton_inj h).2), card_singleton]
  have hbi : ((neverNegWords d).biUnion
      (fun w => {w ++ [Branch.even], w ++ [Branch.odd]})).card = 2 * neverNegCount d := by
    rw [card_biUnion (fun x _ y _ hne => extend_fiber_disjoint hne)]
    simp only [hpair, sum_const, smul_eq_mul, neverNegCount]
    ring
  rw [← hbi, extensions_eq_survivors_union_certs d,
    card_union_of_disjoint (survivors_disjoint_certs d), neverNegCount, minimalCertCount]

/-! ## 3b. The same recursion in the barrier's own words

`J-count-recursion-is-the-boundary-mass` states `N_(d+1) = 2 N_d - b_d M_d`, with `M_d`
the survivors sitting exactly ON the barrier and `b_d` the Sturmian rise, and proves its
three branch cases in `PaperBBarrierStep` on real-valued `⌈t * beta⌉`. That row records
the cardinality bookkeeping joining those branches as *not* formalised.

This is that bookkeeping, and it needs no real number. The bridge is that a survivor's
**odd** extension can never contract: surviving gives `2 ^ d ≤ 3 ^ o`, so
`3 ^ (o+1) ≥ 3 * 2 ^ d > 2 ^ (d+1)`. Hence every minimal certificate of length `d + 1`
is an `E`-extension, and the ones that contract are exactly the survivors whose
`E`-extension does -- which is `b_d M_d` counted without mentioning `b_d`.
-/

/-- **A survivor's odd extension never contracts.**  One more odd letter multiplies the
odd side by three while the even side only doubles. -/
theorem not_exponentGap_concat_odd {w : List Branch} (hw : prefixNoncontracting w) :
    ¬ exponentGap (w ++ [Branch.odd]) := by
  have hsurv : ¬ exponentGap w := by
    have := hw w.length le_rfl
    rwa [List.take_length] at this
  rw [exponentGap, Nat.not_lt] at hsurv
  rw [exponentGap, oddCount_append, List.length_append]
  have hoc : oddCount [Branch.odd] = 1 := rfl
  have hln : ([Branch.odd] : List Branch).length = 1 := rfl
  rw [hoc, hln, Nat.not_lt]
  have h3 : (3 : ℕ) ^ (oddCount w + 1) = 3 * 3 ^ oddCount w := by ring
  have h2 : (2 : ℕ) ^ (w.length + 1) = 2 * 2 ^ w.length := by ring
  have hmul : 3 * 2 ^ w.length ≤ 3 * 3 ^ oddCount w := Nat.mul_le_mul_left 3 hsurv
  have hpos : 0 < 2 ^ w.length := Nat.two_pow_pos _
  omega

/-- The survivors of length `d` whose `E`-extension contracts: those sitting on the
barrier at a step where it rises.  This is `b_d M_d` of the boundary-mass row. -/
def onBarrierWords (d : ℕ) : Finset (List Branch) :=
  (neverNegWords d).filter (fun w => exponentGap (w ++ [Branch.even]))

def onBarrierCount (d : ℕ) : ℕ := (onBarrierWords d).card

/-- **The minimal certificates of length `d+1` are exactly the `E`-extensions of the
on-barrier survivors of length `d`.** -/
theorem minimalCertWords_succ (d : ℕ) :
    minimalCertWords (d + 1) = (onBarrierWords d).image (fun w => w ++ [Branch.even]) := by
  classical
  ext v
  simp only [minimalCertWords, onBarrierWords, neverNegWords, mem_filter, mem_image]
  constructor
  · rintro ⟨hv, hcert⟩
    have hvlen : v.length = d + 1 := mem_allWords.mp hv
    obtain ⟨w, b, rfl⟩ : ∃ w b, v = w ++ [b] := by
      rcases List.eq_nil_or_concat v with rfl | ⟨u, b, rfl⟩
      · simp at hvlen
      · exact ⟨u, b, by simp⟩
    obtain ⟨hsurv, hgap⟩ := isMinimalCertificate_concat.mp hcert
    have hb : b = Branch.even := by
      cases b with
      | even => rfl
      | odd => exact absurd hgap (not_exponentGap_concat_odd hsurv)
    subst hb
    have hwlen : w.length = d := by simpa using hvlen
    exact ⟨w, ⟨⟨mem_allWords.mpr hwlen, hsurv⟩, hgap⟩, rfl⟩
  · rintro ⟨w, ⟨⟨hwmem, hsurv⟩, hgap⟩, rfl⟩
    have hwlen : w.length = d := mem_allWords.mp hwmem
    exact ⟨mem_allWords.mpr (by simp [hwlen]), isMinimalCertificate_concat.mpr ⟨hsurv, hgap⟩⟩

/-- Hence the counts agree, which is the cardinality step the boundary-mass row leaves
unformalised. -/
theorem minimalCertCount_succ (d : ℕ) :
    minimalCertCount (d + 1) = onBarrierCount d := by
  classical
  rw [minimalCertCount, minimalCertWords_succ d, onBarrierCount,
    card_image_of_injective _ (fun x y h => by simpa using (append_singleton_inj h).1)]

/-- **`N_(d+1) = 2 N_d - b_d M_d`, in the shape the boundary-mass row states it.**

The recursion doubles exactly when `onBarrierCount d = 0`, and those lengths have a closed
form: `M_d = 0` iff `d` lies in OEIS A054414, `1 + floor (n / (1 - log 2 / log 3))`, apart
from `d = 1`, where `E` contracts at once; `M_d /= 0` iff `d` lies in A020914,
`floor (n * log 2 3) + 1`, the laboratory's own distinguished length. The two partition the
positive integers, so the plateaus of `density_flat_of_window_empty` below are a Beatty
complement rather than a list. Checked to `d = 200` in
`research.juggler_sequence.oeis_neighbourhood`; A054414 is the only one of the four
sequences around this recursion that the laboratory had not already named. -/
theorem neverNegCount_succ_sub_onBarrier (d : ℕ) :
    neverNegCount (d + 1) + onBarrierCount d = 2 * neverNegCount d := by
  rw [← minimalCertCount_succ d]
  exact neverNegCount_add_minimalCertCount d

/-! ## 4. What it says about the density -/

/-- **The certified count doubles and gains the new minimal certificates.** -/
theorem certifiedWordCount_succ (d : ℕ) :
    certifiedWordCount (d + 1) = 2 * certifiedWordCount d + minimalCertCount (d + 1) := by
  have h1 := certifiedWordCount_add_neverNegCount d
  have h2 := certifiedWordCount_add_neverNegCount (d + 1)
  have h3 := neverNegCount_add_minimalCertCount d
  have hpow : (2 : ℕ) ^ (d + 1) = 2 * 2 ^ d := by ring
  omega

/-- **The density gains exactly the cylinder measure of the new minimal certificates.**
`PaperBFiveStepDensity.five_cylinders_card_sum` is this at `d = 4 → 5`, read across the
five words at once. -/
theorem density_succ (d : ℕ) :
    (certifiedWordCount (d + 1) : ℚ) / 2 ^ (d + 1)
      = (certifiedWordCount d : ℚ) / 2 ^ d + (minimalCertCount (d + 1) : ℚ) / 2 ^ (d + 1) := by
  rw [certifiedWordCount_succ d]
  push_cast
  rw [pow_succ]
  field_simp

/-- No new minimal certificate means no movement in the density. -/
theorem density_succ_of_no_new_cert {d : ℕ} (h : minimalCertCount (d + 1) = 0) :
    (certifiedWordCount (d + 1) : ℚ) / 2 ^ (d + 1) = (certifiedWordCount d : ℚ) / 2 ^ d := by
  rw [density_succ d, h]
  simp

/-! ## 5. The plateau law -/

/-- An empty odd-count window leaves no minimal certificate of that length. -/
theorem minimalCertCount_eq_zero_of_window_empty {L : ℕ}
    (h : ∀ o, ¬ CertWindow L o) : minimalCertCount L = 0 := by
  classical
  rw [minimalCertCount, card_eq_zero, minimalCertWords, filter_eq_empty_iff]
  intro w hw hcert
  have hlen : w.length = L := mem_allWords.mp hw
  exact h (oddCount w) (hlen ▸ minimalCert_window hcert)

/-- **The plateau law.**  When no power of three lies in `[2 ^ d, 2 ^ (d+1))`, the
certificate density at depth `d + 1` equals the density at depth `d`.  With
`beta = log 2 / log 3` that is the rotation missing an integer; the proof mentions no
real number. -/
theorem density_flat_of_window_empty {d : ℕ}
    (h : ∀ o, ¬ CertWindow (d + 1) o) :
    (certifiedWordCount (d + 1) : ℚ) / 2 ^ (d + 1) = (certifiedWordCount d : ℚ) / 2 ^ d :=
  density_succ_of_no_new_cert (minimalCertCount_eq_zero_of_window_empty h)

/-- The plateaus the enumeration found, now as consequences rather than observations:
`7/8` at both `d = 5` and `d = 6`, `237/256` at both `d = 8` and `d = 9`.

These three are the first plateau lengths after `d = 3`: the full list is OEIS A054414
without its initial `1`, so the next are `14, 17, 19, 22, 25, 28, 30`. -/
theorem density_flat_five_to_six :
    (certifiedWordCount 6 : ℚ) / 2 ^ 6 = (certifiedWordCount 5 : ℚ) / 2 ^ 5 :=
  density_flat_of_window_empty (d := 5) window_empty_six

theorem density_flat_eight_to_nine :
    (certifiedWordCount 9 : ℚ) / 2 ^ 9 = (certifiedWordCount 8 : ℚ) / 2 ^ 8 :=
  density_flat_of_window_empty (d := 8) window_empty_nine

theorem density_flat_ten_to_eleven :
    (certifiedWordCount 11 : ℚ) / 2 ^ 11 = (certifiedWordCount 10 : ℚ) / 2 ^ 10 :=
  density_flat_of_window_empty (d := 10) window_empty_eleven

/-! ## 6. The telescoped form: a survivor count is a weighted tail of certificate counts

The one-step identity above says where each survivor's two extensions go. Summing it from
depth `d` up to depth `K` says what a survivor count *is*: the certificates still to come,
plus whatever has not decided yet.

This is the identity behind the statement that Paper B's prefactor is the two-adic tail of
A100982. Divided through by `2 ^ K` the theorem reads

  `N_d / 2 ^ d = Σ_{j = d+1}^{K} M_j / 2 ^ j + N_K / 2 ^ K`,

and letting `K` run off leaves the survivor density as the tail mass of the minimal
certificates. Everything here stays in `ℕ`, so no division, no limit and no real number
enters; the analytic reading is a remark about the statement, not part of it.
-/

/-- **The telescoping identity.** For `d ≤ K`,
`2 ^ (K - d) · N_d = Σ_{j = d+1}^{K} 2 ^ (K - j) · M_j + N_K`.

It is `neverNegCount_add_minimalCertCount` summed and nothing else. -/
theorem neverNegCount_telescope {d K : ℕ} (h : d ≤ K) :
    2 ^ (K - d) * neverNegCount d
      = (∑ j ∈ Finset.Ico (d + 1) (K + 1), 2 ^ (K - j) * minimalCertCount j)
        + neverNegCount K := by
  induction K, h using Nat.le_induction with
  | base => simp
  | succ K hK ih =>
      have hdouble : ∀ j ∈ Finset.Ico (d + 1) (K + 1),
          2 ^ (K + 1 - j) * minimalCertCount j = 2 * (2 ^ (K - j) * minimalCertCount j) := by
        intro j hj
        have hjK : j ≤ K := by
          have := (Finset.mem_Ico.mp hj).2
          omega
        rw [show K + 1 - j = (K - j) + 1 by omega, pow_succ]
        ring
      have hpow : 2 ^ (K + 1 - d) = 2 * 2 ^ (K - d) := by
        rw [show K + 1 - d = (K - d) + 1 by omega, pow_succ]
        ring
      have hrec := neverNegCount_add_minimalCertCount K
      rw [Finset.sum_Ico_succ_top (by omega : d + 1 ≤ K + 1), Finset.sum_congr rfl hdouble,
        ← Finset.mul_sum, Nat.sub_self, pow_zero, one_mul, hpow, mul_assoc, ih]
      omega

/-- The same identity with the certificate tail on the left, which is how Section 6 of the
manuscript uses it: the mass of certificates appearing strictly after depth `d` and no later
than `K` is exactly what separates the two survivor counts. -/
theorem minimalCert_tail_eq {d K : ℕ} (h : d ≤ K) :
    (∑ j ∈ Finset.Ico (d + 1) (K + 1), 2 ^ (K - j) * minimalCertCount j)
      = 2 ^ (K - d) * neverNegCount d - neverNegCount K := by
  rw [neverNegCount_telescope h]
  omega

/-! ## 7. A free length is a full cylinder extension, and what that buys

`density_flat_of_window_empty` reads the empty window through the *counts*. The counts are
not where the content is. When no power of three lies in the window, nothing contracts, so
every survivor keeps both of its extensions and the survivor set at the next length is the
previous one times the full alphabet:

  `neverNegWords (d+1) = neverNegWords d · {E, O}`

That is `neverNegWords_succ_of_window_empty`, and it is `extensions_eq_survivors_union_certs`
with the certificate side removed.

The reason to state it at the level of sets rather than counts is
`sum_neverNegWords_succ_of_window_empty`: at a free length **every** additive functional of
the survivor set factorises over the two extensions. Three summands were recorded separately
as three findings:

* `f = 1` gives the doubling of the counts, hence the density plateaus;
* a character gives the vanishing Fourier coordinate under the good-set Wiener-norm plateau;
* `f w = a ^ oddCount w` gives the tilted count, which multiplies by exactly `1 + a`.

**Two corrections to an earlier version of this paragraph, which had the third one wrong.**
The amplitude law of the jump spectrum is *not* the weight summand. Its weight
`(2 θ) ^ (n - 1)` depends on the length and not on the word, so as a functional on the
survivor set it is `f = 1` up to a constant, and the amplitude law is the density plateau
counted a second time -- which is why the ledger already tags that row `REPARAMETERIZATION`.
The genuine weight summand is the tilted count, the object Paper C's Chernoff and ladder
arguments run on.

And the factorisation is *sufficient, not necessary*, for a plateau. At `d = 5` the length is
not free (`N₅ = 4` against `2 N₄ = 6`) yet the good-set Wiener norm is unchanged. A measured
plateau is evidence of a free length, not proof of one.

**Its relation to `PaperBJumpTransposition.total_stepFlat_eq_two_mul`, which is not
duplication.** That file proves a doubling too, and the two look alike enough that this file
claimed they were one theorem before anyone checked. They are incomparable. This one is
general in the *functional* -- any additive commutative monoid, any `f` -- and specific to the
survivor word set, with freeness as an explicit hypothesis. That one is the counting
functional alone, but carried on an abstract graded `Profile` with no word set in sight, and
its hypothesis `v H = 0` is a truncation width rather than freeness: freeness is not a
hypothesis there at all, it is carried by which operator is applied, `stepFlat` against
`stepRise`. Neither implies the other. They coincide at `f = 1` against the survivor height
profile, where both read `N_{d+1} = 2 N_d`, and the transposition results need the abstract
carrier because a transposition rearranges the barrier word and there is no single `d` whose
word set one could sum over.
-/

/-- **A free length is a full cylinder extension.** When no power of three lies in the window
at `d + 1`, the survivors of length `d + 1` are exactly the survivors of length `d` with
either letter appended. -/
theorem neverNegWords_succ_of_window_empty {d : ℕ} (h : minimalCertWords (d + 1) = ∅) :
    (neverNegWords d).biUnion (fun w => {w ++ [Branch.even], w ++ [Branch.odd]})
      = neverNegWords (d + 1) := by
  rw [extensions_eq_survivors_union_certs, h, union_empty]

/-- The hypothesis in the form the window theorem supplies it. -/
theorem minimalCertWords_eq_empty_of_window_empty {d : ℕ}
    (h : ∀ o, ¬ CertWindow (d + 1) o) : minimalCertWords (d + 1) = ∅ :=
  card_eq_zero.mp (minimalCertCount_eq_zero_of_window_empty h)

/-- **At a free length every additive functional of the survivor set factorises.** For any
`f` into an additive commutative monoid,
`∑_{v ∈ S_{d+1}} f v = ∑_{w ∈ S_d} (f (w ++ [E]) + f (w ++ [O]))`.

This is the single statement behind the separately recorded plateaus: the summand `1` gives
`N_{d+1} = 2 N_d`, a character gives the vanishing Fourier coordinate, a weight gives the
amplitude law. -/
theorem sum_neverNegWords_succ_of_window_empty {M : Type*} [AddCommMonoid M] {d : ℕ}
    (h : minimalCertWords (d + 1) = ∅) (f : List Branch → M) :
    ∑ v ∈ neverNegWords (d + 1), f v
      = ∑ w ∈ neverNegWords d, (f (w ++ [Branch.even]) + f (w ++ [Branch.odd])) := by
  classical
  have hne : ∀ w : List Branch, w ++ [Branch.even] ≠ w ++ [Branch.odd] := by
    intro w hw
    exact Branch.noConfusion (append_singleton_inj hw).2
  have hdisj : Set.PairwiseDisjoint (↑(neverNegWords d) : Set (List Branch))
      (fun w => ({w ++ [Branch.even], w ++ [Branch.odd]} : Finset (List Branch))) := by
    intro a _ b _ hab
    simp only [Function.onFun, disjoint_left, mem_insert, mem_singleton]
    rintro x (rfl | rfl) (hx | hx) <;>
      exact hab (append_singleton_inj hx).1
  rw [← neverNegWords_succ_of_window_empty h, sum_biUnion hdisj]
  exact sum_congr rfl fun w _ => sum_pair (hne w)

/-- The counting corollary, to show the factorisation really does contain the doubling. -/
theorem neverNegCount_succ_of_window_empty {d : ℕ} (h : minimalCertWords (d + 1) = ∅) :
    neverNegCount (d + 1) = 2 * neverNegCount d := by
  have h0 : minimalCertCount (d + 1) = 0 := by rw [minimalCertCount, h, card_empty]
  have hrec := neverNegCount_add_minimalCertCount d
  omega

end Problems.Juggler

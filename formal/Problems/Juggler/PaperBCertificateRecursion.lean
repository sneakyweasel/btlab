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
`7/8` at both `d = 5` and `d = 6`, `237/256` at both `d = 8` and `d = 9`. -/
theorem density_flat_five_to_six :
    (certifiedWordCount 6 : ℚ) / 2 ^ 6 = (certifiedWordCount 5 : ℚ) / 2 ^ 5 :=
  density_flat_of_window_empty (d := 5) window_empty_six

theorem density_flat_eight_to_nine :
    (certifiedWordCount 9 : ℚ) / 2 ^ 9 = (certifiedWordCount 8 : ℚ) / 2 ^ 8 :=
  density_flat_of_window_empty (d := 8) window_empty_nine

theorem density_flat_ten_to_eleven :
    (certifiedWordCount 11 : ℚ) / 2 ^ 11 = (certifiedWordCount 10 : ℚ) / 2 ^ 10 :=
  density_flat_of_window_empty (d := 10) window_empty_eleven

end Problems.Juggler

/-
# Paper B, Lemma 5.1 over starts: the five prefix classes of `C_5`

`docs/theory/juggler_parity_discrepancy_note.md`, Section 2 and Lemma 5.1. A word `w` is
*contracting* when `3^{o(w)} < 2^{|w|}` (`exponentGap`), and

  `C_d = {n ≥ 2 : some contracting prefix of length at most d is realized at n}`

is the power-envelope certificate class (`CertifiedAt d n`). `PaperBCertificates.lemma51`
classifies the minimal contracting words of length at most five as words. This module
states what Lemma 5.1 is used for, over Juggler starts:

* `minimal_certificates_five_iff`: the minimal contracting words of length at most five are
  exactly the five words (from `lemma51`);
* `exists_minimal_prefix`: every contracting word has a minimal contracting prefix;
* `fiveCertificates_prefix_free`: no one of `E, OE, OOEE, OOEOE, OOOEE` is a proper prefix of
  another, so their prefix classes are pairwise disjoint (`prefix_classes_disjoint`);
* `certifiedAt_five_iff`, `certifiedAt_five_unique`: `n ∈ C_5` exactly when `n ≥ 2` realizes
  one of the five words, and then exactly one;
* `certifiedAt_descends`: a start in `C_d` descends within `d` steps (Section 2's envelope,
  `power_bound_contracts`).

`C_d` is defined by the certificate, not by descent: a start that descends within `d` steps
without realizing a contracting prefix is not in `C_d`.
-/

import Problems.Juggler.PaperBCertificates
import Problems.Juggler.Envelope
import Problems.Juggler.RateFreeDensity

namespace Problems.Juggler

namespace PaperBMinimalPrefixes

open PaperBCertificates

/-- The power-envelope certificate class `C_d`: starts `n ≥ 2` realizing a contracting word of
length at most `d`. -/
def CertifiedAt (d n : ℕ) : Prop :=
  2 ≤ n ∧ ∃ w : List Branch, w.length ≤ d ∧ exponentGap w ∧ follows n w

/-- The five words of Lemma 5.1, in the manuscript's order. -/
def fiveCertificates : List (List Branch) := [certE, certOE, certOOEE, certOOOEE, certOOEOE]

/-- The empty word does not contract. -/
theorem not_exponentGap_nil : ¬ exponentGap [] := by
  simp [exponentGap, oddCount]

/-- **Minimal prefixes exist.** Every contracting word has a prefix of positive length that is a
minimal certificate: the shortest contracting prefix. -/
theorem exists_minimal_prefix {w : List Branch} (hw : exponentGap w) :
    ∃ k, 0 < k ∧ k ≤ w.length ∧ IsMinimalCertificate (w.take k) := by
  classical
  have hex : ∃ k, exponentGap (w.take k) := ⟨w.length, by rwa [List.take_length]⟩
  set k := Nat.find hex with hk
  have hspec : exponentGap (w.take k) := Nat.find_spec hex
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, List.take_zero] at hspec
      exact (not_exponentGap_nil hspec).elim
    · exact h
  have hklen : k ≤ w.length := Nat.find_min' hex (by rwa [List.take_length])
  refine ⟨k, hk0, hklen, ?_, hspec, ?_⟩
  · intro h
    have := congrArg List.length h
    rw [List.length_take, List.length_nil] at this
    omega
  · intro j hj0 hjk
    rw [List.length_take] at hjk
    rw [List.take_take]
    have hjk' : j < k := lt_of_lt_of_le hjk (min_le_left _ _)
    rw [min_eq_left hjk'.le]
    exact Nat.find_min hex hjk'

/-- Each of the five words is a minimal certificate of length at most five. -/
theorem fiveCertificates_minimal :
    ∀ c ∈ fiveCertificates, IsMinimalCertificate c ∧ c.length ≤ 5 := by
  decide

/-- **Lemma 5.1.** The minimal contracting words of length at most five are exactly
`E, OE, OOEE, OOOEE, OOEOE`. -/
theorem minimal_certificates_five_iff (w : List Branch) :
    IsMinimalCertificate w ∧ w.length ≤ 5 ↔ w ∈ fiveCertificates := by
  constructor
  · rintro ⟨hmin, hlen⟩
    rcases lemma51 hmin hlen with h | h | h | h | h <;> rw [h] <;> simp [fiveCertificates]
  · exact fiveCertificates_minimal w

/-- **The five words are prefix-free**: none is a prefix of a different one. -/
theorem fiveCertificates_prefix_free :
    ∀ c ∈ fiveCertificates, ∀ c' ∈ fiveCertificates, c <+: c' → c = c' := by
  decide

/-- **Lemma 5.1 as prefixes.** A contracting word of length at most five has exactly one of the
five words as a prefix. -/
theorem minimal_prefix_mem {w : List Branch} (hw : exponentGap w) (hlen : w.length ≤ 5) :
    ∃ c ∈ fiveCertificates, c <+: w := by
  obtain ⟨k, _, hkw, hmin⟩ := exists_minimal_prefix hw
  have hlen' : (w.take k).length ≤ 5 := by
    rw [List.length_take]
    omega
  refine ⟨w.take k, ?_, List.take_prefix k w⟩
  rcases lemma51 hmin hlen' with h | h | h | h | h <;> rw [h] <;> simp [fiveCertificates]

/-- Two realized words are comparable under the prefix order. -/
theorem prefix_or_prefix_of_follows {n : ℕ} {u v : List Branch}
    (hu : follows n u) (hv : follows n v) : u <+: v ∨ v <+: u := by
  rw [follows_iff_itinerary] at hu hv
  rcases le_total u.length v.length with h | h
  · left
    have e := itinerary_take n v.length u.length h
    rw [hv, hu] at e
    rw [← e]
    exact List.take_prefix _ _
  · right
    have e := itinerary_take n u.length v.length h
    rw [hu, hv] at e
    rw [← e]
    exact List.take_prefix _ _

/-- **The prefix classes are disjoint**: no start realizes two of the five words. -/
theorem prefix_classes_disjoint {n : ℕ} {c c' : List Branch}
    (hc : c ∈ fiveCertificates) (hc' : c' ∈ fiveCertificates)
    (h : follows n c) (h' : follows n c') : c = c' := by
  rcases prefix_or_prefix_of_follows h h' with hp | hp
  · exact fiveCertificates_prefix_free c hc c' hc' hp
  · exact (fiveCertificates_prefix_free c' hc' c hc hp).symm

/-- **The union is `C_5`.** A start lies in `C_5` exactly when it is at least `2` and realizes
one of the five words of Lemma 5.1. -/
theorem certifiedAt_five_iff (n : ℕ) :
    CertifiedAt 5 n ↔ 2 ≤ n ∧ ∃ c ∈ fiveCertificates, follows n c := by
  constructor
  · rintro ⟨hn, w, hlen, hgap, hf⟩
    obtain ⟨c, hc, hcw⟩ := minimal_prefix_mem hgap hlen
    refine ⟨hn, c, hc, ?_⟩
    rw [List.prefix_iff_eq_take] at hcw
    rw [hcw]
    exact follows_take w _ hf
  · rintro ⟨hn, c, hc, hf⟩
    obtain ⟨hmin, hlen⟩ := fiveCertificates_minimal c hc
    exact ⟨hn, c, hlen, hmin.2.1, hf⟩

/-- **Lemma 5.1, as used in Section 5.** `C_5` is the disjoint union of the five prefix
classes: every start in `C_5` realizes exactly one of `E, OE, OOEE, OOOEE, OOEOE`. -/
theorem certifiedAt_five_unique {n : ℕ} (h : CertifiedAt 5 n) :
    ∃! c, c ∈ fiveCertificates ∧ follows n c := by
  obtain ⟨_, c, hc, hf⟩ := (certifiedAt_five_iff n).1 h
  exact ⟨c, ⟨hc, hf⟩, fun c' ⟨hc', hf'⟩ => prefix_classes_disjoint hc' hc hf' hf⟩

/-- **A certificate certifies descent.** A start in `C_d` descends within `d` steps. -/
theorem certifiedAt_descends {d n : ℕ} (h : CertifiedAt d n) :
    ∃ k, 0 < k ∧ k ≤ d ∧ floorPower^[k] n < n := by
  obtain ⟨hn, w, hlen, hgap, hf⟩ := h
  refine ⟨w.length, ?_, hlen, power_bound_contracts hn hf hgap⟩
  rcases Nat.eq_zero_or_pos w.length with h0 | h0
  · rw [List.length_eq_zero_iff] at h0
    subst h0
    exact (not_exponentGap_nil hgap).elim
  · exact h0

end PaperBMinimalPrefixes

end Problems.Juggler

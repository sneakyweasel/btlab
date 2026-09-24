/-
# Paper B, Lemma 5.1: minimal certificates through length five

The combinatorial half of Theorems 5.2--5.4. A word is an
`IsMinimalCertificate` when it has an exponent gap
(`3^(oddCount) < 2^(length)`) and no proper nonempty prefix does.
Lemma 5.1 of `docs/theory/juggler_parity_discrepancy_note.md` asserts that
the only such words of length at most five are

  `E`, `OE`, `OOEE`, `OOOEE`, `OOEOE`.

Their formal cylinder measures sum to `7/8`, which is the main-term
arithmetic behind Theorem 5.4. Nothing here bounds an exponential sum,
counts starts, or claims a density for the Juggler map: the analytic
inputs that turn these five words into `7N/8 + O(...)` stay written.
-/

import Mathlib.Tactic
import Problems.Juggler.ItineraryStats

namespace Problems.Juggler

namespace PaperBCertificates

/-- A nonempty word that contracts, with no proper nonempty contracting prefix.
This is the exact reading of Paper B Lemma 5.1's "contracting words ... with no
proper contracting prefix". -/
def IsMinimalCertificate (w : List Branch) : Prop :=
  w ≠ [] ∧ exponentGap w ∧
    ∀ k, 0 < k → k < w.length → ¬exponentGap (w.take k)

instance : DecidablePred exponentGap :=
  fun w => inferInstanceAs (Decidable (3 ^ oddCount w < 2 ^ w.length))

instance (w : List Branch) : Decidable (IsMinimalCertificate w) :=
  decidable_of_iff
    (w ≠ [] ∧ exponentGap w ∧
      ∀ k : Fin w.length, 0 < k.val → ¬exponentGap (w.take k.val))
    ⟨fun ⟨hne, hg, h⟩ => ⟨hne, hg, fun k hk0 hkl => h ⟨k, hkl⟩ hk0⟩,
     fun ⟨hne, hg, h⟩ => ⟨hne, hg, fun ⟨k, hkl⟩ hk0 => h k hk0 hkl⟩⟩

/-- The five words of Lemma 5.1. -/
def certE : List Branch := [.even]
/-- `OE`, the length-two minimal certificate of Lemma 5.1. -/
def certOE : List Branch := [.odd, .even]
/-- `OOEE`, the length-four minimal certificate of Lemma 5.1. -/
def certOOEE : List Branch := [.odd, .odd, .even, .even]
/-- `OOOEE`, one of the two length-five minimal certificates of Lemma 5.1. -/
def certOOOEE : List Branch := [.odd, .odd, .odd, .even, .even]
/-- `OOEOE`, the other length-five minimal certificate of Lemma 5.1. -/
def certOOEOE : List Branch := [.odd, .odd, .even, .odd, .even]

/-- `E` is a minimal certificate: `3 ^ 0 < 2 ^ 1`, and it has no proper nonempty prefix. -/
theorem certE_is : IsMinimalCertificate certE := by decide
/-- `OE` is a minimal certificate: `3 < 2 ^ 2`, and its prefix `O` does not contract. -/
theorem certOE_is : IsMinimalCertificate certOE := by decide
/-- `OOEE` is a minimal certificate: `3 ^ 2 < 2 ^ 4`, and no proper nonempty prefix
contracts. -/
theorem certOOEE_is : IsMinimalCertificate certOOEE := by decide
/-- `OOOEE` is a minimal certificate: `3 ^ 3 < 2 ^ 5`, and no proper nonempty prefix
contracts. -/
theorem certOOOEE_is : IsMinimalCertificate certOOOEE := by decide
/-- `OOEOE` is a minimal certificate: `3 ^ 3 < 2 ^ 5`, and no proper nonempty prefix
contracts. -/
theorem certOOEOE_is : IsMinimalCertificate certOOEOE := by decide

/-- Formal cylinder measures of the five certificates sum to `7/8`. -/
theorem certificate_measures_sum :
    (1 : ℚ) / 2 + 1 / 4 + 1 / 16 + 1 / 32 + 1 / 32 = 7 / 8 := by
  norm_num

/-- `1/2 + 1/4 + 1/16 = 13/16`: the cylinder measures of `E`, `OE`, `OOEE`, the minimal
certificates of length at most four. -/
theorem four_step_measures_sum :
    (1 : ℚ) / 2 + 1 / 4 + 1 / 16 = 13 / 16 := by
  norm_num

/-- `13/16 + 1/32 = 27/32`: the length-at-most-four total plus one length-five cylinder. -/
theorem twenty_seven_thirty_two_sum :
    (13 : ℚ) / 16 + 1 / 32 = 27 / 32 := by
  norm_num

/-- An `E`-rooted word of length ≥ 2 is never minimal: its first letter already contracts. -/
theorem not_minimal_of_even_head {t : List Branch}
    (hw : IsMinimalCertificate (Branch.even :: t)) (ht : t ≠ []) : False := by
  have hlen : 1 < (Branch.even :: t).length := by
    cases t with
    | nil => exact (ht rfl).elim
    | cons _ _ => simp
  have h := hw.2.2 1 (by decide) hlen
  simp [exponentGap, oddCount] at h

/-- An `OE`-rooted word of length ≥ 3 is never minimal. -/
theorem not_minimal_of_OE_prefix {t : List Branch}
    (hw : IsMinimalCertificate (Branch.odd :: Branch.even :: t))
    (ht : t ≠ []) : False := by
  have hlen : 2 < (Branch.odd :: Branch.even :: t).length := by
    cases t with
    | nil => exact (ht rfl).elim
    | cons _ _ => simp
  have h := hw.2.2 2 (by decide) hlen
  simp [exponentGap, oddCount] at h

/-- Length one: only `E` contracts. -/
theorem length_one {w : List Branch}
    (hw : IsMinimalCertificate w) (hlen : w.length = 1) : w = certE := by
  match w, hlen with
  | [.even], _ => rfl
  | [.odd], _ =>
      have hg : exponentGap [.odd] := hw.2.1
      simp [exponentGap, oddCount] at hg

/-- Length two: only `OE`. -/
theorem length_two {w : List Branch}
    (hw : IsMinimalCertificate w) (hlen : w.length = 2) : w = certOE := by
  match w, hlen with
  | [.even, b], _ =>
      exact (not_minimal_of_even_head (t := [b]) hw (List.cons_ne_nil _ _)).elim
  | [.odd, .even], _ => rfl
  | [.odd, .odd], _ =>
      have hg : exponentGap [.odd, .odd] := hw.2.1
      simp [exponentGap, oddCount] at hg

/-- At length three no new certificate appears: `3^2 > 2^3`. -/
theorem length_three {w : List Branch}
    (hw : IsMinimalCertificate w) (hlen : w.length = 3) : False := by
  match w, hlen with
  | [.even, b, c], _ =>
      exact not_minimal_of_even_head (t := [b, c]) hw (List.cons_ne_nil _ _)
  | [.odd, .even, c], _ =>
      exact not_minimal_of_OE_prefix (t := [c]) hw (List.cons_ne_nil _ _)
  | [.odd, .odd, c], _ =>
      -- prefix `OO`; two odds already refuse contraction at length 3
      have hg : exponentGap [.odd, .odd, c] := hw.2.1
      have ho : 2 ≤ oddCount [.odd, .odd, c] := by cases c <;> simp [oddCount]
      have hpow : (3 : ℕ) ^ 2 ≤ 3 ^ oddCount [.odd, .odd, c] :=
        Nat.pow_le_pow_right (by decide : 0 < 3) ho
      have : (3 : ℕ) ^ 2 < 2 ^ 3 :=
        lt_of_le_of_lt hpow (by simpa [exponentGap] using hg)
      exact (by decide : ¬ (9 : ℕ) < 8) this

/-- Length four: only `OOEE`. -/
theorem length_four {w : List Branch}
    (hw : IsMinimalCertificate w) (hlen : w.length = 4) : w = certOOEE := by
  match w, hlen with
  | [.even, b, c, d], _ =>
      exact (not_minimal_of_even_head (t := [b, c, d]) hw (List.cons_ne_nil _ _)).elim
  | [.odd, .even, c, d], _ =>
      exact (not_minimal_of_OE_prefix (t := [c, d]) hw (List.cons_ne_nil _ _)).elim
  | [.odd, .odd, .odd, d], _ =>
      have hg : exponentGap [.odd, .odd, .odd, d] := hw.2.1
      have ho : 3 ≤ oddCount [.odd, .odd, .odd, d] := by cases d <;> simp [oddCount]
      have hpow : (3 : ℕ) ^ 3 ≤ 3 ^ oddCount [.odd, .odd, .odd, d] :=
        Nat.pow_le_pow_right (by decide) ho
      have hlt : (3 : ℕ) ^ 3 < 2 ^ 4 :=
        lt_of_le_of_lt hpow (by simpa [exponentGap] using hg)
      exact (False.elim ((by decide : ¬ (27 : ℕ) < 16) hlt))
  | [.odd, .odd, .even, .even], _ => rfl
  | [.odd, .odd, .even, .odd], _ =>
      have hg : exponentGap [.odd, .odd, .even, .odd] := hw.2.1
      simp [exponentGap, oddCount] at hg

/-- Length five: `OOOEE` and `OOEOE`. -/
theorem length_five {w : List Branch}
    (hw : IsMinimalCertificate w) (hlen : w.length = 5) :
    w = certOOOEE ∨ w = certOOEOE := by
  match w, hlen with
  | [.even, b, c, d, e], _ =>
      exact (not_minimal_of_even_head (t := [b, c, d, e]) hw (List.cons_ne_nil _ _)).elim
  | [.odd, .even, c, d, e], _ =>
      exact (not_minimal_of_OE_prefix (t := [c, d, e]) hw (List.cons_ne_nil _ _)).elim
  | [.odd, .odd, .even, .even, e], _ =>
      -- prefix `OOEE` already contracts
      have h := hw.2.2 4 (by decide) (by simp)
      simp [exponentGap, oddCount] at h
  | [.odd, .odd, .even, .odd, .even], _ => exact Or.inr rfl
  | [.odd, .odd, .even, .odd, .odd], _ =>
      have hg : exponentGap [.odd, .odd, .even, .odd, .odd] := hw.2.1
      simp [exponentGap, oddCount] at hg
  | [.odd, .odd, .odd, .odd, e], _ =>
      have hg : exponentGap [.odd, .odd, .odd, .odd, e] := hw.2.1
      have ho : 4 ≤ oddCount [.odd, .odd, .odd, .odd, e] := by cases e <;> simp [oddCount]
      have hpow : (3 : ℕ) ^ 4 ≤ 3 ^ oddCount [.odd, .odd, .odd, .odd, e] :=
        Nat.pow_le_pow_right (by decide) ho
      have hlt : (3 : ℕ) ^ 4 < 2 ^ 5 :=
        lt_of_le_of_lt hpow (by simpa [exponentGap] using hg)
      exact (False.elim ((by decide : ¬ (81 : ℕ) < 32) hlt))
  | [.odd, .odd, .odd, .even, .even], _ => exact Or.inl rfl
  | [.odd, .odd, .odd, .even, .odd], _ =>
      have hg : exponentGap [.odd, .odd, .odd, .even, .odd] := hw.2.1
      simp [exponentGap, oddCount] at hg

/-- **Lemma 5.1.** The minimal certificates of length at most five are exactly
`E`, `OE`, `OOEE`, `OOOEE`, and `OOEOE`. -/
theorem lemma51 {w : List Branch}
    (hw : IsMinimalCertificate w) (hlen : w.length ≤ 5) :
    w = certE ∨ w = certOE ∨ w = certOOEE ∨ w = certOOOEE ∨ w = certOOEOE := by
  match h : w.length with
  | 0 =>
      exact False.elim (hw.1 (List.length_eq_zero_iff.mp h))
  | 1 =>
      exact Or.inl (length_one hw h)
  | 2 =>
      exact Or.inr (Or.inl (length_two hw h))
  | 3 =>
      exact (length_three hw h).elim
  | 4 =>
      exact Or.inr (Or.inr (Or.inl (length_four hw h)))
  | 5 =>
      rcases length_five hw h with h' | h'
      · exact Or.inr (Or.inr (Or.inr (Or.inl h')))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h')))
  | n + 6 =>
      omega

/-- The five named words are indeed the complete list through length five. -/
theorem lemma51_complete :
    (∀ w, IsMinimalCertificate w → w.length ≤ 5 →
      w = certE ∨ w = certOE ∨ w = certOOEE ∨ w = certOOOEE ∨ w = certOOEOE) ∧
    IsMinimalCertificate certE ∧ IsMinimalCertificate certOE ∧
    IsMinimalCertificate certOOEE ∧ IsMinimalCertificate certOOOEE ∧
    IsMinimalCertificate certOOEOE ∧
    (1 : ℚ) / 2 + 1 / 4 + 1 / 16 + 1 / 32 + 1 / 32 = 7 / 8 :=
  ⟨fun _ hw hlen => lemma51 hw hlen,
    certE_is, certOE_is, certOOEE_is, certOOOEE_is, certOOEOE_is,
    certificate_measures_sum⟩

end PaperBCertificates

end Problems.Juggler

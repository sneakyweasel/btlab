/-
# Paper B, Lemma 5.1 for every length: which `L` carry a minimal certificate

`docs/theory/juggler_parity_discrepancy_note.md`, Lemma 5.1 lists the minimal
power-envelope certificates of length at most five: `E, OE, OOEE, OOOEE, OOEOE`. It
says nothing about longer words, and the enumeration behind `PaperBFiveStepDensity`
shows the list is not uniform in `L`: lengths `3, 6, 9, 11, 14` carry no minimal
certificate at all, which is why the certificate density is flat at `7/8` across
`d = 5, 6` and at `237/256` across `d = 8, 9`.

The pattern is exact, and it is arithmetic rather than combinatorial. A minimal
certificate of length `L` contracts, so `3 ^ oddCount w < 2 ^ L`; and no proper prefix
contracts, so in particular the prefix of length `L - 1` does not, which reads
`2 ^ (L - 1) ≤ 3 ^ oddCount w`. The odd count is therefore pinned inside a window

  `2 ^ (L - 1) ≤ 3 ^ o < 2 ^ L`

that holds at most one power of three, since consecutive powers of two differ by a
factor `2` and `3 > 2`. So:

* the odd count is **forced** by the length, not chosen (`minimalCert_window`,
  `certWindow_unique`);
* the last letter is **always** `E` (`minimalCert_concat_even`) -- an odd last letter
  would need `3 ^ (o + 1) < 2 ^ L` while `3 ^ o ≥ 2 ^ (L - 1)`, i.e. `3 < 2`;
* and when the window does hold a power of three, `O^o E^(L-o)` realises it
  (`blockWord_isMinimalCertificate`), so the condition is not merely necessary.

Hence `minimalCert_exists_iff`: a minimal certificate of length `L` exists exactly when
some power of three lies in `[2 ^ (L - 1), 2 ^ L)`. Writing `beta = log 2 / log 3`, that
is the statement that the half-open interval `[(L-1) * beta, L * beta)` contains an
integer, so the carrying lengths are the jump points of `⌊L * beta⌋` and the empty ones
are the complement of a Beatty sequence. **No real number appears below.** The rotation
is the reading; the obligation is `Nat` arithmetic, which is why this is provable here
while Sections 2 to 4 of the manuscript are not.

The same `beta` is already `PaperBSurvivorDecay`'s endpoint tilt and
`PaperBSturmianBarrier`'s slope. This is its third appearance, and the first where it
governs the *lengths* rather than the counts.

**What is not here.** No exponential sum, no density for the Juggler map, and no claim
about how many minimal certificates a carrying length has -- only that it has at least
one and that all of them share an odd count. The count itself is a constrained-walk
problem against the same line of slope `beta`, left open.
-/

import Mathlib.Tactic
import Problems.Juggler.PaperBCertificates

namespace Problems.Juggler

open PaperBCertificates

/-! ## 1. The window a length forces on the odd count -/

/-- The odd-count window of a length: `2 ^ (L - 1) ≤ 3 ^ o < 2 ^ L`. A minimal
certificate of length `L` must have `o` odd letters for an `o` in this window, and the
window holds at most one such `o`. -/
def CertWindow (L o : ℕ) : Prop := 2 ^ (L - 1) ≤ 3 ^ o ∧ 3 ^ o < 2 ^ L

instance (L o : ℕ) : Decidable (CertWindow L o) := inferInstanceAs (Decidable (_ ∧ _))

/-- **The window holds at most one power of three.** Consecutive powers of two differ by
a factor of two and `3 > 2`, so two distinct powers of three cannot both land in
`[2 ^ (L - 1), 2 ^ L)`. -/
theorem certWindow_unique {L o o' : ℕ} (h : CertWindow L o) (h' : CertWindow L o') :
    o = o' := by
  by_contra hne
  rcases Nat.lt_or_ge o o' with hlt | hge
  · -- `3 ^ o' ≥ 3 ^ (o + 1) = 3 * 3 ^ o ≥ 3 * 2 ^ (L - 1) > 2 * 2 ^ (L - 1) ≥ 2 ^ L`
    have h1 : 3 ^ (o + 1) ≤ 3 ^ o' := Nat.pow_le_pow_right (by decide) hlt
    have h2 : 3 * 2 ^ (L - 1) ≤ 3 * 3 ^ o := Nat.mul_le_mul_left 3 h.1
    have h3 : 2 ^ L ≤ 2 * 2 ^ (L - 1) := by
      rcases Nat.eq_zero_or_pos L with rfl | hL
      · simp
      · rw [← pow_succ']
        exact Nat.pow_le_pow_right (by decide) (by omega)
    have : 2 ^ L ≤ 3 ^ o' := by
      calc 2 ^ L ≤ 2 * 2 ^ (L - 1) := h3
        _ ≤ 3 * 2 ^ (L - 1) := by omega
        _ ≤ 3 * 3 ^ o := h2
        _ = 3 ^ (o + 1) := by ring
        _ ≤ 3 ^ o' := h1
    exact absurd h'.2 (Nat.not_lt.mpr this)
  · have hlt' : o' < o := by omega
    have h1 : 3 ^ (o' + 1) ≤ 3 ^ o := Nat.pow_le_pow_right (by decide) hlt'
    have h2 : 3 * 2 ^ (L - 1) ≤ 3 * 3 ^ o' := Nat.mul_le_mul_left 3 h'.1
    have h3 : 2 ^ L ≤ 2 * 2 ^ (L - 1) := by
      rcases Nat.eq_zero_or_pos L with rfl | hL
      · simp
      · rw [← pow_succ']
        exact Nat.pow_le_pow_right (by decide) (by omega)
    have : 2 ^ L ≤ 3 ^ o := by
      calc 2 ^ L ≤ 2 * 2 ^ (L - 1) := h3
        _ ≤ 3 * 2 ^ (L - 1) := by omega
        _ ≤ 3 * 3 ^ o' := h2
        _ = 3 ^ (o' + 1) := by ring
        _ ≤ 3 ^ o := h1
    exact absurd h.2 (Nat.not_lt.mpr this)

/-- The window bounds the odd count by the length: `3 ^ o < 2 ^ L` forces `o ≤ L`
because `2 ^ o ≤ 3 ^ o`. -/
theorem certWindow_le {L o : ℕ} (h : CertWindow L o) : o ≤ L := by
  by_contra hlt
  have h1 : (2 : ℕ) ^ L ≤ 2 ^ o := Nat.pow_le_pow_right (by decide) (by omega)
  have h2 : (2 : ℕ) ^ o ≤ 3 ^ o := Nat.pow_le_pow_left (by decide) o
  exact absurd h.2 (Nat.not_lt.mpr (le_trans h1 h2))

/-! ## 2. What a minimal certificate must look like -/

/-- The length-`(L-1)` prefix of a minimal certificate does not contract. For `L = 1`
this is vacuous and the bound `2 ^ 0 ≤ 3 ^ 0` holds outright. -/
theorem minimalCert_prefix_not_gap {w : List Branch} (hw : IsMinimalCertificate w)
    (hlen : 1 < w.length) : ¬ exponentGap (w.take (w.length - 1)) :=
  hw.2.2 (w.length - 1) (by omega) (by omega)

/-- **A minimal certificate ends in `E`.** An odd last letter would need
`3 * 3 ^ o < 2 ^ L` while the prefix gives `3 ^ o ≥ 2 ^ (L - 1)`, i.e. `3 < 2`. -/
theorem minimalCert_concat_even {u : List Branch} {b : Branch}
    (hw : IsMinimalCertificate (u ++ [b])) : b = Branch.even := by
  cases b with
  | even => rfl
  | odd =>
      exfalso
      have hgap : exponentGap (u ++ [Branch.odd]) := hw.2.1
      rw [exponentGap, oddCount_append, List.length_append] at hgap
      have hoc : oddCount [Branch.odd] = 1 := rfl
      have hln : ([Branch.odd] : List Branch).length = 1 := rfl
      rw [hoc, hln] at hgap
      -- `3 ^ (oddCount u + 1) < 2 ^ (u.length + 1)`
      have h3 : (3 : ℕ) ^ (oddCount u + 1) = 3 * 3 ^ oddCount u := by ring
      have h2 : (2 : ℕ) ^ (u.length + 1) = 2 * 2 ^ u.length := by ring
      rw [h3, h2] at hgap
      rcases Nat.eq_zero_or_pos u.length with hu | hu
      · have hnil : u = [] := List.length_eq_zero_iff.mp hu
        subst hnil
        simp [oddCount] at hgap
      · have hpre : ¬ exponentGap u := by
          have := hw.2.2 u.length hu (by simp)
          simpa [List.take_left'] using this
        rw [exponentGap, Nat.not_lt] at hpre
        have hmul : 3 * 2 ^ u.length ≤ 3 * 3 ^ oddCount u := Nat.mul_le_mul_left 3 hpre
        have hpos : 0 < 2 ^ u.length := Nat.two_pow_pos _
        omega

/-- **The odd count of a minimal certificate is inside the window of its length.** -/
theorem minimalCert_window {w : List Branch} (hw : IsMinimalCertificate w) :
    CertWindow w.length (oddCount w) := by
  refine ⟨?_, hw.2.1⟩
  rcases Nat.lt_or_ge w.length 2 with hlen | hlen
  · have h0 : w.length - 1 = 0 := by omega
    rw [h0, pow_zero]
    exact Nat.one_le_pow _ _ (by decide)
  · have hne : w ≠ [] := hw.1
    have hsplit : w.dropLast ++ [w.getLast hne] = w := List.dropLast_append_getLast hne
    have hlast : w.getLast hne = Branch.even :=
      minimalCert_concat_even (by rw [hsplit]; exact hw)
    have hdl : w.dropLast.length = w.length - 1 := List.length_dropLast
    have hodd : oddCount w.dropLast = oddCount w := by
      conv_rhs => rw [← hsplit]
      rw [oddCount_append, hlast]
      simp [oddCount]
    have hpre : ¬ exponentGap w.dropLast := by
      have hd : w.dropLast = w.take (w.length - 1) := List.dropLast_eq_take
      rw [hd]
      exact hw.2.2 (w.length - 1) (by omega) (by omega)
    rw [exponentGap, Nat.not_lt, hdl, hodd] at hpre
    exact hpre

/-! ## 3. The window is realised, so the condition is exact -/

/-- `O^o E^(L-o)`: all the odd letters first. -/
def blockWord (L o : ℕ) : List Branch :=
  List.replicate o Branch.odd ++ List.replicate (L - o) Branch.even

@[simp] theorem blockWord_length {L o : ℕ} (h : o ≤ L) : (blockWord L o).length = L := by
  simp [blockWord]; omega

@[simp] theorem blockWord_oddCount {L o : ℕ} : oddCount (blockWord L o) = o := by
  simp [blockWord, oddCount_append, oddCount_replicate_odd, oddCount_replicate_even]

/-- **The window is attained.**  When some power of three lies in `[2 ^ (L-1), 2 ^ L)`,
the word `O^o E^(L-o)` is a minimal certificate: every proper prefix either is all odd
(where `3 ^ k > 2 ^ k`) or is `O^o E^j` with `j < L - o`, where the window's lower bound
`2 ^ (L-1) ≤ 3 ^ o` is exactly what stops it contracting early. -/
theorem blockWord_isMinimalCertificate {L o : ℕ} (hL : 0 < L) (ho : o ≤ L)
    (hwin : CertWindow L o) : IsMinimalCertificate (blockWord L o) := by
  have hlen : (blockWord L o).length = L := blockWord_length ho
  refine ⟨?_, ?_, ?_⟩
  · intro hnil
    have := congrArg List.length hnil
    rw [hlen] at this
    simp at this
    omega
  · rw [exponentGap, hlen, blockWord_oddCount]
    exact hwin.2
  · intro k hk0 hkl
    rw [hlen] at hkl
    rw [exponentGap]
    rcases Nat.lt_or_ge k o with hko | hko
    · -- all-odd prefix: `3 ^ k > 2 ^ k`, so no contraction
      have htake : (blockWord L o).take k = List.replicate k Branch.odd := by
        rw [blockWord, List.take_append, List.take_replicate, List.length_replicate]
        rw [show min k o = k from Nat.min_eq_left (le_of_lt hko),
          show k - o = 0 from by omega]
        simp
      rw [htake]
      simp only [oddCount_replicate_odd, List.length_replicate]
      exact Nat.not_lt.mpr (Nat.pow_le_pow_left (by decide) k)
    · -- prefix `O^o E^(k-o)` with `k < L`: the lower bound blocks it
      have htake : (blockWord L o).take k
          = List.replicate o Branch.odd ++ List.replicate (k - o) Branch.even := by
        rw [blockWord, List.take_append, List.take_replicate, List.take_replicate,
          List.length_replicate]
        rw [show min k o = o from Nat.min_eq_right hko,
          show min (k - o) (L - o) = k - o from Nat.min_eq_left (by omega)]
      rw [htake]
      simp only [oddCount_append, oddCount_replicate_odd, oddCount_replicate_even,
        List.length_append, List.length_replicate, Nat.add_zero]
      have hk : o + (k - o) = k := by omega
      rw [hk]
      -- `2 ^ k ≤ 2 ^ (L - 1) ≤ 3 ^ o`
      have h1 : (2 : ℕ) ^ k ≤ 2 ^ (L - 1) := Nat.pow_le_pow_right (by decide) (by omega)
      exact Nat.not_lt.mpr (le_trans h1 hwin.1)

/-- **Lemma 5.1 for every length.**  A minimal certificate of length `L ≥ 1` exists
exactly when some power of three lies in `[2 ^ (L - 1), 2 ^ L)`.  The manuscript's list
is the case `L ≤ 5`. -/
theorem minimalCert_exists_iff {L : ℕ} (hL : 0 < L) :
    (∃ w : List Branch, IsMinimalCertificate w ∧ w.length = L) ↔ ∃ o, CertWindow L o := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨oddCount w, minimalCert_window hw⟩
  · rintro ⟨o, hwin⟩
    have ho : o ≤ L := certWindow_le hwin
    exact ⟨blockWord L o, blockWord_isMinimalCertificate hL ho hwin,
      blockWord_length ho⟩

/-- The contrapositive, which is the form the plateaus use: no power of three in the
window means no minimal certificate of that length at all. -/
theorem no_minimalCert_of_window_empty {L : ℕ} (_hL : 0 < L) (h : ∀ o, ¬ CertWindow L o)
    {w : List Branch} (hw : IsMinimalCertificate w) : w.length ≠ L := by
  intro hlen
  exact h (oddCount w) (hlen ▸ minimalCert_window hw)

/-! ## 4. The empty lengths, checked -/

/-- `3, 6, 9, 11, 14` carry no minimal certificate: no power of three lies in their
windows.  These are exactly the lengths where the certificate density does not move. -/
theorem window_empty_three : ∀ o, ¬ CertWindow 3 o := by
  intro o hw
  have hle : o ≤ 3 := certWindow_le hw
  obtain ⟨hlo, hhi⟩ := hw
  interval_cases o <;> omega

theorem window_empty_six : ∀ o, ¬ CertWindow 6 o := by
  intro o hw
  have hle : o ≤ 6 := certWindow_le hw
  obtain ⟨hlo, hhi⟩ := hw
  interval_cases o <;> omega

theorem window_empty_nine : ∀ o, ¬ CertWindow 9 o := by
  intro o hw
  have hle : o ≤ 9 := certWindow_le hw
  obtain ⟨hlo, hhi⟩ := hw
  interval_cases o <;> omega

theorem window_empty_eleven : ∀ o, ¬ CertWindow 11 o := by
  intro o hw
  have hle : o ≤ 11 := certWindow_le hw
  obtain ⟨hlo, hhi⟩ := hw
  interval_cases o <;> omega

theorem window_empty_fourteen : ∀ o, ¬ CertWindow 14 o := by
  intro o hw
  have hle : o ≤ 14 := certWindow_le hw
  obtain ⟨hlo, hhi⟩ := hw
  interval_cases o <;> omega

/-- The first five carrying lengths give the manuscript's list back: `L = 1, 2, 4, 5`
have windows, `L = 3` does not. -/
theorem window_one : CertWindow 1 0 := by constructor <;> norm_num
theorem window_two : CertWindow 2 1 := by constructor <;> norm_num
theorem window_four : CertWindow 4 2 := by constructor <;> norm_num
theorem window_five : CertWindow 5 3 := by constructor <;> norm_num
theorem window_seven : CertWindow 7 4 := by constructor <;> norm_num

/-- The odd counts the manuscript's five certificates carry are the windows' values:
`E` has none, `OE` one, `OOEE` two, and both `OOOEE` and `OOEOE` three. -/
theorem lemma51_odd_counts_are_the_windows :
    oddCount certE = 0 ∧ oddCount certOE = 1 ∧ oddCount certOOEE = 2 ∧
      oddCount certOOOEE = 3 ∧ oddCount certOOEOE = 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

end Problems.Juggler

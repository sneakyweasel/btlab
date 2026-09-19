/-
# The empty-window theorem at every level

`PaperBCertificateLengths` proves that a minimal certificate of length `L` exists only when a
power of three lies in `[2 ^ (L - 1), 2 ^ L)`. That is Paper B's statement, and Paper B works
at level zero: a word is a certificate when its walk drops below its starting point at all.

Paper C works at every level `Λ > 0`: the object there is the set of words whose walk first
reaches `-Λ`. The two papers are tied by a four-row dictionary -- conditions, counts,
exponents, measures -- and every row of it has only ever been driven from Paper C down to
Paper B, where the transfer is recorded as valid and empty.

**The empty-window argument never used the level.** A word whose walk first reaches the
barrier at its last step must end in `E`: an odd last letter would need `3 ^ (o + 1) c < 2 ^
(L)` while the length-`(L-1)` prefix gives `3 ^ o c ≥ 2 ^ (L - 1)`, i.e. `3 < 2`, which is
`minimalCert_concat_even` verbatim with the barrier moved. So the odd count is pinned in a
**shifted** window, and when no power of three lies in the shifted window, no word of that
length can first reach the barrier there.

This file carries the level as a positive real scale `c`, where `c = 2 ^ Λ`. That choice keeps
every level in range rather than only the integer ones: `Λ = 1.2486`, the level Paper C's
spectrum work actually runs at, is `c = 2 ^ 1.2486` and is covered. Level zero is `c = 1`, and
`exponentGapAt_one_iff` identifies this file's predicate with `exponentGap` there, so Paper B's
statements are the `c = 1` case of these rather than a separate development.

The hypothesis throughout is `1 ≤ c`, which says the barrier is at or below the start
(`Λ ≥ 0`). It is used, and an adversarial pass corrected an earlier account of where.
`minimalCertAt_concat_even` needs only `2 / 3 ≤ c`, and does fail below that, where `[O]`
becomes a certificate in its own right. The lemma that needs the full `1 ≤ c` is
`minimalCertAt_window`, in its length-one branch, and the binding word is `[E]`: at `c = 3/4`
the word `[E]` is a minimal certificate while its window demands `1 ≤ 3 / 4`. A reader who
weakens the hypothesis to `2 / 3` breaks the file.

**The barrier here is strict, and Paper C's is not.** This file lifts Paper B's pair of
inequalities unchanged, so `exponentGapAt` passes the barrier strictly. The laboratory's Paper
C code reaches it non-strictly (`FateChernoff.lean`'s `LBad`, and the walk in
`collision_large_sieve`). The two coincide exactly when `3 ^ o * c` is never a power of two,
which holds at **every non-integer level**, 1.2486 included, and fails at every integer level
at `o = 0`. There they disagree at exactly two lengths, `⌊Λ⌋` and `⌊Λ⌋ + 1`: at `Λ = 3` this
file makes `EEEE` the length-four certificate and has none at length three, while Paper C's
convention has `EEE` at length three and none at length four. Level zero is the case Paper B
was entitled to ignore, because `3 ^ o = 2 ^ t` forces `o = t = 0`; that entitlement does not
survive the move to `Λ > 0` and is not inherited here.

**What is not here.** Two things. The cylinder identity at level `c` -- that the alive set is a
full cylinder extension when the shifted window is empty -- follows from these the same way
`neverNegWords_succ_of_window_empty` (`PaperBCertificateRecursion`) follows from Paper B's, but
needs the `Finset` machinery of `RateFreeDensity` re-indexed by `c`, and is not attempted. And
only the **necessary** direction is proved: Paper B has the biconditional
(`minimalCert_exists_iff`, via `blockWord_isMinimalCertificate`), and the realisation half at
level `c` is not here.

The enumeration behind the claim is in
`tests/research/juggler_sequence/test_empty_window_levels.py`, brute force over all `2 ^ d`
words to `d = 15`. It runs Paper C's non-strict convention, so it corroborates this file at its
levels `0.5` and `1.2486` and **not** at its level `3.0`, where it is checking the mirror
statement.
-/

import Mathlib.Tactic
import Problems.Juggler.PaperBCertificateLengths

namespace Problems.Juggler

open PaperBCertificates

/-! ## 1. The level-carrying predicates -/

/-- **The walk has fallen past the barrier**, where the level `Λ` enters as `c = 2 ^ Λ`.
At `c = 1` this is `exponentGap`. -/
def exponentGapAt (c : ℝ) (w : List Branch) : Prop :=
  (3 : ℝ) ^ oddCount w * c < 2 ^ w.length

/-- **A minimal certificate at level `c`**: the walk passes the barrier at the last step and
at no earlier one. -/
def IsMinimalCertificateAt (c : ℝ) (w : List Branch) : Prop :=
  w ≠ [] ∧ exponentGapAt c w ∧ ∀ k, 0 < k → k < w.length → ¬ exponentGapAt c (w.take k)

/-- **The shifted window.** At level `c` the odd count of a length-`L` minimal certificate is
pinned to an `o` with `2 ^ (L - 1) ≤ 3 ^ o c < 2 ^ L`. -/
def CertWindowAt (c : ℝ) (L o : ℕ) : Prop :=
  (2 : ℝ) ^ (L - 1) ≤ 3 ^ o * c ∧ (3 : ℝ) ^ o * c < 2 ^ L

/-! ## 2. Level zero is Paper B -/

theorem exponentGapAt_one_iff (w : List Branch) :
    exponentGapAt 1 w ↔ exponentGap w := by
  unfold exponentGapAt exponentGap
  constructor
  · intro h
    have hc : ((3 ^ oddCount w : ℕ) : ℝ) < ((2 ^ w.length : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hc
  · intro h
    have hc : ((3 ^ oddCount w : ℕ) : ℝ) < ((2 ^ w.length : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    linarith

theorem certWindowAt_one_iff (L o : ℕ) : CertWindowAt 1 L o ↔ CertWindow L o := by
  unfold CertWindowAt CertWindow
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · have hc : ((2 ^ (L - 1) : ℕ) : ℝ) ≤ ((3 ^ o : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast hc
    · have hc : ((3 ^ o : ℕ) : ℝ) < ((2 ^ L : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast hc
  · rintro ⟨h1, h2⟩
    have c1 : ((2 ^ (L - 1) : ℕ) : ℝ) ≤ ((3 ^ o : ℕ) : ℝ) := by exact_mod_cast h1
    have c2 : ((3 ^ o : ℕ) : ℝ) < ((2 ^ L : ℕ) : ℝ) := by exact_mod_cast h2
    push_cast at c1 c2
    constructor <;> linarith

/-- **A whole-number level is only a shift of the length.** At `c = 2`, that is `Λ = 1`, the
window at length `L` is Paper B's window at length `L - 1`.

This is worth stating because it says where the new content is and where it is not. It is
proved here at `c = 2` only; the same re-indexing holds at `c = 2 ^ k` by the same argument.
So a whole-number level proves nothing Paper B did not already have, and the content of this
file is at the *fractional* levels -- which is also the only place its strict barrier agrees
with Paper C's non-strict one. `certWindowAt_twelve_empty_at_paperC_level` is the worked
instance at such a level. -/
theorem certWindowAt_two_iff {L : ℕ} (hL : 2 ≤ L) (o : ℕ) :
    CertWindowAt 2 L o ↔ CertWindow (L - 1) o := by
  have hA : (2 : ℝ) ^ (L - 1) = 2 * 2 ^ (L - 2) := by
    conv_lhs => rw [show L - 1 = (L - 2) + 1 by omega]
    rw [pow_succ]; ring
  have hB : (2 : ℝ) ^ L = 2 * 2 ^ (L - 1) := by
    conv_lhs => rw [show L = (L - 1) + 1 by omega]
    rw [pow_succ]; ring
  have hsub : (L - 1) - 1 = L - 2 := by omega
  unfold CertWindowAt CertWindow
  rw [hsub]
  constructor
  · rintro ⟨h1, h2⟩
    rw [hA] at h1
    rw [hB] at h2
    constructor
    · have hc : ((2 ^ (L - 2) : ℕ) : ℝ) ≤ ((3 ^ o : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast hc
    · have hc : ((3 ^ o : ℕ) : ℝ) < ((2 ^ (L - 1) : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast hc
  · rintro ⟨h1, h2⟩
    have c1 : ((2 ^ (L - 2) : ℕ) : ℝ) ≤ ((3 ^ o : ℕ) : ℝ) := by exact_mod_cast h1
    have c2 : ((3 ^ o : ℕ) : ℝ) < ((2 ^ (L - 1) : ℕ) : ℝ) := by exact_mod_cast h2
    push_cast at c1 c2
    rw [hA, hB]
    constructor <;> linarith

/-! ## 3. The window still holds at most one power of three -/

theorem two_pow_le_two_mul (L : ℕ) : (2 : ℝ) ^ L ≤ 2 * 2 ^ (L - 1) := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · norm_num
  · rw [← pow_succ']
    exact pow_le_pow_right₀ (by norm_num) (by omega)

/-- **At most one power of three lands in the shifted window**, for the same reason as at
level zero: consecutive powers of two differ by `2` and `3 > 2`, and scaling both sides by `c`
does not change that. -/
theorem certWindowAt_unique {c : ℝ} (hc : 0 < c) {L o o' : ℕ}
    (h : CertWindowAt c L o) (h' : CertWindowAt c L o') : o = o' := by
  have key : ∀ a b : ℕ, a < b → CertWindowAt c L a → CertWindowAt c L b → False := by
    intro a b hab ha hb
    have hpos : (0 : ℝ) < 2 ^ (L - 1) := by positivity
    have hstep : (3 : ℝ) ^ (a + 1) ≤ 3 ^ b := pow_le_pow_right₀ (by norm_num) (by omega)
    have hmul : (3 : ℝ) ^ (a + 1) * c ≤ 3 ^ b * c := by nlinarith [hc.le]
    have hlow : 3 * ((2 : ℝ) ^ (L - 1)) ≤ (3 : ℝ) ^ (a + 1) * c := by
      have : (3 : ℝ) ^ (a + 1) * c = 3 * (3 ^ a * c) := by ring
      rw [this]
      nlinarith [ha.1]
    have htop := two_pow_le_two_mul L
    nlinarith [hb.2]
  rcases lt_trichotomy o o' with hlt | heq | hgt
  · exact absurd (key o o' hlt h h') not_false
  · exact heq
  · exact absurd (key o' o hgt h' h) not_false

/-! ## 4. A minimal certificate still ends in `E` -/

/-- **The last letter is `E` at every level.** The proof is Paper B's with the barrier moved:
an odd last letter forces `3 < 2`. -/
theorem minimalCertAt_concat_even {c : ℝ} (hc : 1 ≤ c) {u : List Branch} {b : Branch}
    (hw : IsMinimalCertificateAt c (u ++ [b])) : b = Branch.even := by
  cases b with
  | even => rfl
  | odd =>
      exfalso
      have hgap : exponentGapAt c (u ++ [Branch.odd]) := hw.2.1
      unfold exponentGapAt at hgap
      rw [oddCount_append, List.length_append] at hgap
      have hoc : oddCount [Branch.odd] = 1 := rfl
      have hln : ([Branch.odd] : List Branch).length = 1 := rfl
      rw [hoc, hln] at hgap
      have h3 : (3 : ℝ) ^ (oddCount u + 1) = 3 * 3 ^ oddCount u := by ring
      have h2 : (2 : ℝ) ^ (u.length + 1) = 2 * 2 ^ u.length := by ring
      rw [h3, h2] at hgap
      rcases Nat.eq_zero_or_pos u.length with hu | hu
      · have hnil : u = [] := List.length_eq_zero_iff.mp hu
        subst hnil
        simp only [oddCount, List.length_nil, pow_zero] at hgap
        linarith
      · have hpre : ¬ exponentGapAt c u := by
          have := hw.2.2 u.length hu (by simp)
          simpa [List.take_left'] using this
        unfold exponentGapAt at hpre
        rw [not_lt] at hpre
        have hpos : (0 : ℝ) < 2 ^ u.length := by positivity
        nlinarith

/-! ## 5. The odd count is pinned, and the empty window forbids the length -/

/-- **The odd count of a level-`c` minimal certificate lies in the shifted window.** -/
theorem minimalCertAt_window {c : ℝ} (hc : 1 ≤ c) {w : List Branch}
    (hw : IsMinimalCertificateAt c w) : CertWindowAt c w.length (oddCount w) := by
  refine ⟨?_, hw.2.1⟩
  rcases Nat.lt_or_ge w.length 2 with hlen | hlen
  · have h0 : w.length - 1 = 0 := by omega
    rw [h0, pow_zero]
    have : (1 : ℝ) ≤ 3 ^ oddCount w := one_le_pow₀ (by norm_num)
    nlinarith
  · have hne : w ≠ [] := hw.1
    have hsplit : w.dropLast ++ [w.getLast hne] = w := List.dropLast_append_getLast hne
    have hlast : w.getLast hne = Branch.even :=
      minimalCertAt_concat_even hc (by rw [hsplit]; exact hw)
    have hdl : w.dropLast.length = w.length - 1 := List.length_dropLast
    have hodd : oddCount w.dropLast = oddCount w := by
      conv_rhs => rw [← hsplit]
      rw [oddCount_append, hlast]
      simp [oddCount]
    have hpre : ¬ exponentGapAt c w.dropLast := by
      have hd : w.dropLast = w.take (w.length - 1) := List.dropLast_eq_take
      rw [hd]
      exact hw.2.2 (w.length - 1) (by omega) (by omega)
    unfold exponentGapAt at hpre
    rw [not_lt, hdl, hodd] at hpre
    exact hpre

/-- **The empty-window theorem, at every level.** When no power of three lies in the shifted
window at `L`, no word of length `L` is a minimal certificate at level `c`.

At `c = 1` this is `no_minimalCert_of_window_empty`, now derived rather than asserted
(`no_minimalCert_of_window_empty_of_level`). For `c > 1` it is the word-level input to the
level-`Λ` cylinder identity, and it is the statement Paper C's bad sets satisfy **at every
non-integer level**; at integer levels the two conventions part, as the module docstring
records. -/
theorem no_minimalCertAt_of_window_empty {c : ℝ} (hc : 1 ≤ c) {L : ℕ}
    (h : ∀ o, ¬ CertWindowAt c L o) :
    ∀ w : List Branch, w.length = L → ¬ IsMinimalCertificateAt c w := by
  intro w hlen hw
  exact h (oddCount w) (hlen ▸ minimalCertAt_window hc hw)

/-- The contrapositive: a length that carries a level-`c` certificate has a power of three in
its shifted window. -/
theorem certWindowAt_of_minimalCertAt {c : ℝ} (hc : 1 ≤ c) {L : ℕ}
    (h : ∃ w : List Branch, IsMinimalCertificateAt c w ∧ w.length = L) :
    ∃ o, CertWindowAt c L o := by
  obtain ⟨w, hw, hlen⟩ := h
  exact ⟨oddCount w, hlen ▸ minimalCertAt_window hc hw⟩

/-! ## 6. Paper B is the `c = 1` case, derived rather than asserted -/

/-- The certificate predicates agree at level zero, not merely the gap predicates. -/
theorem isMinimalCertificateAt_one_iff (w : List Branch) :
    IsMinimalCertificateAt 1 w ↔ IsMinimalCertificate w := by
  simp [IsMinimalCertificateAt, IsMinimalCertificate, exponentGapAt_one_iff]

/-- **Paper B's empty-window theorem, obtained from the level-carrying one at `c = 1`.**
The module docstring claims Paper B's statements are the `c = 1` case of these; this is that
claim discharged rather than asserted. -/
theorem no_minimalCert_of_window_empty_of_level {L : ℕ} (h : ∀ o, ¬ CertWindow L o) :
    ∀ w : List Branch, w.length = L → ¬ IsMinimalCertificate w := by
  intro w hlen hw
  refine no_minimalCertAt_of_window_empty (c := 1) le_rfl (fun o ho => h o ?_) w hlen ?_
  · exact (certWindowAt_one_iff L o).mp ho
  · exact (isMinimalCertificateAt_one_iff w).mpr hw

/-! ## 7. A worked instance at a fractional level

Everything above is universally quantified over `c`, and the two instances the file gives are
`c = 1` and `c = 2` -- exactly the levels it declares contentless. This section supplies one
instance at a level that is neither, so that "the content is at the fractional levels" is a
fact about a theorem rather than a remark about a quantifier. -/

/-- The odd count of a window is bounded by the length, at any level at or below the start. -/
theorem certWindowAt_le {c : ℝ} (hc : 1 ≤ c) {L o : ℕ} (h : CertWindowAt c L o) : o ≤ L := by
  by_contra hle
  have hlt : L < o := Nat.lt_of_not_le hle
  have h3pos : (0 : ℝ) < 3 ^ o := by positivity
  have h23 : (2 : ℝ) ^ o ≤ 3 ^ o := pow_le_pow_left₀ (by norm_num) (by norm_num) o
  have hLo : (2 : ℝ) ^ L < 2 ^ o := by
    exact pow_lt_pow_right₀ (by norm_num) hlt
  have hge : (3 : ℝ) ^ o * 1 ≤ 3 ^ o * c := by nlinarith
  rw [mul_one] at hge
  linarith [h.2]

/-- **Length twelve is free at Paper C's level.** For every scale `c` between `2.37` and
`2.38` -- that is, every level `Λ` between `log₂ 2.37 = 1.2450` and `log₂ 2.38 = 1.2511`, a
range containing the `1.2486` the spectrum work runs at -- no power of three lies in the window
at `L = 12`, so no word of length twelve first passes the barrier there.

The two neighbouring powers of three miss from opposite sides: `3 ^ 6 c ≤ 1735` is below
`2 ^ 11 = 2048`, and `3 ^ 7 c ≥ 5183` is above `2 ^ 12 = 4096`. -/
theorem certWindowAt_twelve_empty_at_paperC_level {c : ℝ}
    (hlo : 2.37 ≤ c) (hhi : c ≤ 2.38) (o : ℕ) : ¬ CertWindowAt c 12 o := by
  intro h
  have ho : o ≤ 12 := certWindowAt_le (by linarith) h
  obtain ⟨h1, h2⟩ := h
  norm_num at h1 h2
  interval_cases o <;> norm_num at h1 h2 <;> linarith

/-- The consequence, at that level: no word of length twelve is a minimal certificate. -/
theorem no_minimalCertAt_twelve_at_paperC_level {c : ℝ}
    (hlo : 2.37 ≤ c) (hhi : c ≤ 2.38) :
    ∀ w : List Branch, w.length = 12 → ¬ IsMinimalCertificateAt c w :=
  no_minimalCertAt_of_window_empty (by linarith) (certWindowAt_twelve_empty_at_paperC_level hlo hhi)

end Problems.Juggler

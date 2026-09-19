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
`collision_large_sieve`). Section 11 settles exactly when that matters:
`exponentGapAt_agrees_iff` says the two agree on every word precisely when `c` avoids the
lattice of values `2 ^ t / 3 ^ o`, equivalently when `Λ` is not of the form `t - o log₂ 3`.

**An earlier version of this paragraph got that set wrong**, and the error is left on the
record because it is the kind prose invites and a theorem forbids. It said the two agree at
*every non-integer level*. They do not. Taking `o = 0` gives the integer levels, which is what
I had noticed; taking `o ≥ 1` gives irrational ones, and those are non-integer too. At
`Λ = 2 - log₂ 3 = 0.415`, so `c = 4/3`, the two certificate sets differ at seven of the first
ten lengths.

What is true, and is the real reason `0.5` and `1.2486` are safe, is that a **rational**
non-integer level always avoids the lattice: `3 ^ a = 2 ^ b` forces `a = b = 0`, so
`3 ^ o · 2 ^ (p/q) = 2 ^ t` raised to the `q`-th power gives `3 ^ (oq) = 2 ^ (tq - p)` and
hence `o = 0`, making `Λ` an integer. The safety of Paper C's level comes from its being
rational, not from its being non-integer, and those are different reasons that happen to
coincide there.

**Which lengths move, stated in the right variable.** On the lattice point `3 ^ o c = 2 ^ t`
the *certificate sets* differ at many lengths, but the *free* lengths -- the ones this file's
theorems are about -- differ at exactly two, `t` and `t + 1`. An earlier version said
`⌊Λ⌋` and `⌊Λ⌋ + 1`, which is the `o = 0` case generalised to the wrong variable. Measured:
`c = 8`, which is `o = 0, t = 3`, moves the free lengths 3 and 4; `c = 4/3`, which is
`o = 1, t = 2`, moves 2 and 3. At `Λ = 3` concretely, this file makes `EEEE` the length-four
certificate and has none at length three, while Paper C's convention has `EEE` at length three
and none at length four.

Level zero is the case Paper B was entitled to ignore, because `3 ^ o = 2 ^ t` forces
`o = t = 0`; that entitlement does not survive the move to `Λ > 0` and is not inherited here.

**The cylinder identity is here**, in Section 8: at a free length the alive set at level `c`
is the previous one times the full alphabet (`aliveWordsAt_succ_of_window_empty`), so every
additive functional of it factorises (`sum_aliveWordsAt_succ_of_window_empty`). That is the
statement the downstream observations actually use -- a frozen statistic at a given depth is
that theorem at `f` equal to the statistic -- and until it was proved, reading a frozen
Wiener norm as a free length rested on enumeration alone.

**The realisation half is here too**, in Section 9, so the length statement is a
biconditional at every level (`minimalCertAt_exists_iff`) exactly as Paper B's is, and a free
length is characterised rather than merely recognised: `aliveWordsAt_succ_iff_window_empty`
says the cylinder identity holds *if and only if* the shifted window is empty. A frozen
statistic is therefore an exact diagnostic of a free length and not a one-way hint.

**What is still not here.** Three things, none of them the mathematics. There are no
`decide`-backed concrete instances, because the predicate is real-valued and a real comparison
does not reduce; the level-zero file keeps those and this one substitutes the interval
argument of `certWindowAt_twelve_empty_at_paperC_level`. There is no bridge to Paper C's own
`LBad`, which would have to carry the strict/non-strict difference explicitly. And the
carrying lengths are not identified in closed form: at level `Λ` they are the inhomogeneous
Beatty sequence `⌊o log₂ 3 + Λ⌋ + 1`, the level-zero case of which *is* recorded in closed form
as `minimalCert_exists_iff_natLog`, and the shifted case would need `Real.logb` rather than
`Nat.log`.

The enumeration behind the claim is in
`tests/research/juggler_sequence/test_empty_window_levels.py`, brute force over all `2 ^ d`
words to `d = 15`. It runs Paper C's non-strict convention, so it corroborates this file at its
levels `0.5` and `1.2486` and **not** at its level `3.0`, where it is checking the mirror
statement.
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Problems.Juggler.PaperBCertificateLengths
import Problems.Juggler.RateFreeDensity

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
`2 ^ 11 = 2048`, and `3 ^ 7 c ≥ 5183` is above `2 ^ 12 = 4096`.

The bracket is about the window, not about the convention. It contains the lattice point
`c = 64/27 = 2.3704`, where `3 ^ 3 c = 2 ^ 6` and the two barriers part. That costs this
theorem nothing, since it is stated in the strict convention throughout, but the bracket
should not be read as a range on which the conventions agree. -/
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

/-! ## 8. The cylinder identity at level `c`

The sections above are about *lengths*: which of them can carry a word that first passes the
barrier. What every consumer downstream actually uses is the statement about *sets* -- that at
a free length nothing is lost, so the alive set is the previous one times the full alphabet and
every additive functional of it factorises. At level zero that is
`neverNegWords_succ_of_window_empty` and `sum_neverNegWords_succ_of_window_empty`
(`PaperBCertificateRecursion`). This section is the same at level `c`.

It is what licenses reading a frozen statistic as a free length. The laboratory's caution on
`J-bad-set-spectrum-cannot-win` -- that two of its four quoted Wiener points are exact copies
of the depth below -- rested on enumeration alone until now; the mechanism is here.

The predicates are real-valued, so the `Finset`s are classical rather than decidable. Paper C's
own `LBad` already lives under `open scoped Classical`, so this costs nothing that layer was
not already paying; what it does cost is the `decide`-backed concrete instances, which is why
the level-zero file keeps them and this one has none. -/

/-- The word has not passed the barrier at any prefix: alive at level `c`. -/
def prefixNoncontractingAt (c : ℝ) (w : List Branch) : Prop :=
  ∀ k, k ≤ w.length → ¬ exponentGapAt c (w.take k)

/-- The empty word never passes a barrier at or below the start. This is the one place the
structural argument needs `1 ≤ c`, and it is why the level-`c` recursion has the hypothesis. -/
theorem not_exponentGapAt_nil {c : ℝ} (hc : 1 ≤ c) : ¬ exponentGapAt c [] := by
  unfold exponentGapAt
  simp only [oddCount, List.length_nil, pow_zero, one_mul]
  exact not_lt.mpr hc

theorem takeAt_concat_of_le {w : List Branch} {b : Branch} {k : ℕ} (hk : k ≤ w.length) :
    (w ++ [b]).take k = w.take k := List.take_append_of_le_length hk

/-- A one-letter extension is alive exactly when its base is alive and it does not pass. -/
theorem prefixNoncontractingAt_concat {c : ℝ} {w : List Branch} {b : Branch} :
    prefixNoncontractingAt c (w ++ [b]) ↔
      prefixNoncontractingAt c w ∧ ¬ exponentGapAt c (w ++ [b]) := by
  constructor
  · intro h
    refine ⟨fun k hk => ?_, ?_⟩
    · have := h k (by simp; omega)
      rwa [takeAt_concat_of_le hk] at this
    · have := h (w ++ [b]).length le_rfl
      rwa [List.take_length] at this
  · rintro ⟨hw, hgap⟩ k hk
    simp only [List.length_append, List.length_singleton] at hk
    rcases Nat.lt_or_ge k (w.length + 1) with hlt | hge
    · have hkw : k ≤ w.length := by omega
      rw [takeAt_concat_of_le hkw]
      exact hw k hkw
    · have hkeq : k = w.length + 1 := by omega
      subst hkeq
      have hlen : (w ++ [b]).length = w.length + 1 := by simp
      rw [show (w ++ [b]).take (w.length + 1) = w ++ [b] by rw [← hlen, List.take_length]]
      exact hgap

/-- A one-letter extension first passes exactly when its base is alive and it does pass. -/
theorem isMinimalCertificateAt_concat {c : ℝ} (hc : 1 ≤ c) {w : List Branch} {b : Branch} :
    IsMinimalCertificateAt c (w ++ [b]) ↔
      prefixNoncontractingAt c w ∧ exponentGapAt c (w ++ [b]) := by
  constructor
  · rintro ⟨-, hgap, hmin⟩
    refine ⟨fun k hk => ?_, hgap⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simpa using not_exponentGapAt_nil (c := c) hc
    · have hklt : k < (w ++ [b]).length := by simp; omega
      have := hmin k hk0 hklt
      rwa [takeAt_concat_of_le hk] at this
  · rintro ⟨hw, hgap⟩
    refine ⟨by simp, hgap, fun k hk0 hklt => ?_⟩
    simp only [List.length_append, List.length_singleton] at hklt
    have hkw : k ≤ w.length := by omega
    rw [takeAt_concat_of_le hkw]
    exact hw k hkw

open scoped Classical in
/-- The words of length `d` still alive at level `c`. -/
noncomputable def aliveWordsAt (c : ℝ) (d : ℕ) : Finset (List Branch) :=
  (allWords d).filter (prefixNoncontractingAt c)

open scoped Classical in
/-- The words of length `d` that first pass the barrier at level `c` exactly at their end. -/
noncomputable def minimalCertWordsAt (c : ℝ) (d : ℕ) : Finset (List Branch) :=
  (allWords d).filter (IsMinimalCertificateAt c)

/-- **The extensions of the alive words are the alive words and the new first-passages.** -/
theorem extensionsAt_eq_alive_union_certs {c : ℝ} (hc : 1 ≤ c) (d : ℕ) :
    (aliveWordsAt c d).biUnion (fun w => {w ++ [Branch.even], w ++ [Branch.odd]})
      = aliveWordsAt c (d + 1) ∪ minimalCertWordsAt c (d + 1) := by
  classical
  ext v
  simp only [Finset.mem_biUnion, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
    aliveWordsAt, minimalCertWordsAt, Finset.mem_filter]
  constructor
  · rintro ⟨w, hw, hv⟩
    have hwlen : w.length = d := mem_allWords.mp hw.1
    have hvmem : v ∈ allWords (d + 1) := by
      rcases hv with rfl | rfl <;> exact mem_allWords.mpr (by simp [hwlen])
    by_cases hgap : exponentGapAt c v
    · refine Or.inr ⟨hvmem, ?_⟩
      rcases hv with rfl | rfl <;>
        exact (isMinimalCertificateAt_concat hc).mpr ⟨hw.2, hgap⟩
    · refine Or.inl ⟨hvmem, ?_⟩
      rcases hv with rfl | rfl <;>
        exact prefixNoncontractingAt_concat.mpr ⟨hw.2, hgap⟩
  · intro h
    have hvmem : v ∈ allWords (d + 1) := by
      rcases h with ⟨hm, -⟩ | ⟨hm, -⟩ <;> exact hm
    have hvlen : v.length = d + 1 := mem_allWords.mp hvmem
    obtain ⟨w, b, rfl⟩ : ∃ w b, v = w ++ [b] := by
      rcases List.eq_nil_or_concat v with rfl | ⟨u, b, rfl⟩
      · simp at hvlen
      · exact ⟨u, b, by simp⟩
    have hwlen : w.length = d := by simpa using hvlen
    have hwalive : prefixNoncontractingAt c w := by
      rcases h with ⟨-, hs⟩ | ⟨-, hcert⟩
      · exact (prefixNoncontractingAt_concat.mp hs).1
      · exact ((isMinimalCertificateAt_concat hc).mp hcert).1
    refine ⟨w, ⟨mem_allWords.mpr hwlen, hwalive⟩, ?_⟩
    cases b
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- An empty shifted window empties the first-passage set at that length. -/
theorem minimalCertWordsAt_eq_empty_of_window_empty {c : ℝ} (hc : 1 ≤ c) {d : ℕ}
    (h : ∀ o, ¬ CertWindowAt c (d + 1) o) : minimalCertWordsAt c (d + 1) = ∅ := by
  classical
  rw [minimalCertWordsAt, Finset.filter_eq_empty_iff]
  intro w hw
  exact no_minimalCertAt_of_window_empty hc h w (mem_allWords.mp hw)

/-- **A free length is a full cylinder extension, at level `c`.** -/
theorem aliveWordsAt_succ_of_window_empty {c : ℝ} (hc : 1 ≤ c) {d : ℕ}
    (h : ∀ o, ¬ CertWindowAt c (d + 1) o) :
    (aliveWordsAt c d).biUnion (fun w => {w ++ [Branch.even], w ++ [Branch.odd]})
      = aliveWordsAt c (d + 1) := by
  rw [extensionsAt_eq_alive_union_certs hc,
    minimalCertWordsAt_eq_empty_of_window_empty hc h, Finset.union_empty]

/-- **At a free length every additive functional of the alive set factorises, at level `c`.**
This is the statement the frozen-statistic observations rest on: the summand `1` gives the
doubling of the counts, a character gives the vanishing Fourier coordinate, and the weight
`a ^ oddCount` gives the tilted count multiplying by `1 + a`. -/
theorem sum_aliveWordsAt_succ_of_window_empty {M : Type*} [AddCommMonoid M] {c : ℝ}
    (hc : 1 ≤ c) {d : ℕ} (h : ∀ o, ¬ CertWindowAt c (d + 1) o) (f : List Branch → M) :
    ∑ v ∈ aliveWordsAt c (d + 1), f v
      = ∑ w ∈ aliveWordsAt c d, (f (w ++ [Branch.even]) + f (w ++ [Branch.odd])) := by
  classical
  have hne : ∀ w : List Branch, w ++ [Branch.even] ≠ w ++ [Branch.odd] := by
    intro w hw
    exact Branch.noConfusion (append_singleton_inj hw).2
  have hdisj : Set.PairwiseDisjoint (↑(aliveWordsAt c d) : Set (List Branch))
      (fun w => ({w ++ [Branch.even], w ++ [Branch.odd]} : Finset (List Branch))) := by
    intro a _ b _ hab
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton]
    rintro x (rfl | rfl) (hx | hx) <;>
      exact hab (append_singleton_inj hx).1
  rw [← aliveWordsAt_succ_of_window_empty hc h, Finset.sum_biUnion hdisj]
  exact Finset.sum_congr rfl fun w _ => Finset.sum_pair (hne w)

/-! ## 9. The realisation half, and the biconditional

Everything above says a length carries nothing. Paper B says more: its window condition is
an *iff*, because when the window does hold a power of three the word `O^o E^(L-o)` realises
it. That argument survives the level shift too, and with it the whole statement becomes a
biconditional and the cylinder identity becomes an exact characterisation of a free length
rather than a sufficient condition for one. -/

/-- **The shifted window is attained.** When a power of three lies in the shifted window,
`O^o E^(L-o)` first passes the barrier at level `c` exactly at its end.

The two prefix branches are Paper B's, and each keeps working for its own reason: an all-odd
prefix has `3 ^ k c ≥ 3 ^ k ≥ 2 ^ k`, which is where `1 ≤ c` is used, and a prefix `O^o E^j`
with `j < L - o` is blocked by the window's lower bound, which already carries the `c`. -/
theorem blockWordAt_isMinimalCertificateAt {c : ℝ} (hc : 1 ≤ c) {L o : ℕ} (hL : 0 < L)
    (ho : o ≤ L) (hwin : CertWindowAt c L o) : IsMinimalCertificateAt c (blockWord L o) := by
  have hlen : (blockWord L o).length = L := blockWord_length ho
  refine ⟨?_, ?_, ?_⟩
  · intro hnil
    have hz := congrArg List.length hnil
    rw [hlen] at hz
    simp at hz
    omega
  · unfold exponentGapAt
    rw [hlen, blockWord_oddCount]
    exact hwin.2
  · intro k hk0 hkl
    rw [hlen] at hkl
    unfold exponentGapAt
    rcases Nat.lt_or_ge k o with hko | hko
    · have htake : (blockWord L o).take k = List.replicate k Branch.odd := by
        rw [blockWord, List.take_append, List.take_replicate, List.length_replicate]
        rw [show min k o = k from Nat.min_eq_left (le_of_lt hko),
          show k - o = 0 from by omega]
        simp
      rw [htake]
      simp only [oddCount_replicate_odd, List.length_replicate]
      have h3pos : (0 : ℝ) < 3 ^ k := by positivity
      have h23 : (2 : ℝ) ^ k ≤ 3 ^ k := pow_le_pow_left₀ (by norm_num) (by norm_num) k
      have hge : (3 : ℝ) ^ k * 1 ≤ 3 ^ k * c := by nlinarith
      rw [mul_one] at hge
      exact not_lt.mpr (by linarith)
    · have htake : (blockWord L o).take k
          = List.replicate o Branch.odd ++ List.replicate (k - o) Branch.even := by
        rw [blockWord, List.take_append, List.take_replicate, List.take_replicate,
          List.length_replicate]
        rw [show min k o = o from Nat.min_eq_right hko,
          show min (k - o) (L - o) = k - o from Nat.min_eq_left (by omega)]
      rw [htake]
      simp only [oddCount_append, oddCount_replicate_odd, oddCount_replicate_even,
        List.length_append, List.length_replicate, Nat.add_zero]
      rw [show o + (k - o) = k by omega]
      have h1 : (2 : ℝ) ^ k ≤ 2 ^ (L - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      exact not_lt.mpr (le_trans h1 hwin.1)

/-- **The level-`c` empty-window theorem, as a biconditional.** A word of length `L ≥ 1` first
passes the barrier at level `c` exactly when a power of three lies in the shifted window. This
is Paper B's `minimalCert_exists_iff` at every level. -/
theorem minimalCertAt_exists_iff {c : ℝ} (hc : 1 ≤ c) {L : ℕ} (hL : 0 < L) :
    (∃ w : List Branch, IsMinimalCertificateAt c w ∧ w.length = L) ↔ ∃ o, CertWindowAt c L o := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨oddCount w, minimalCertAt_window hc hw⟩
  · rintro ⟨o, hwin⟩
    have ho : o ≤ L := certWindowAt_le hc hwin
    exact ⟨blockWord L o, blockWordAt_isMinimalCertificateAt hc hL ho hwin, blockWord_length ho⟩

/-- Alive and first-passing are exclusive: a first passage passes at its own length. -/
theorem aliveAt_disjoint_certsAt {c : ℝ} (d : ℕ) :
    Disjoint (aliveWordsAt c (d + 1)) (minimalCertWordsAt c (d + 1)) := by
  classical
  rw [Finset.disjoint_left]
  intro v hv hcert
  have h1 : prefixNoncontractingAt c v := (Finset.mem_filter.mp hv).2
  have h2 : IsMinimalCertificateAt c v := (Finset.mem_filter.mp hcert).2
  exact (h1 v.length le_rfl) (by simpa using h2.2.1)

/-- **A length is free exactly when it is a full cylinder extension**, at every level. The
forward direction is Section 8; the converse is the realisation half, and together they make a
frozen statistic an exact diagnostic rather than a one-way hint. -/
theorem aliveWordsAt_succ_iff_window_empty {c : ℝ} (hc : 1 ≤ c) {d : ℕ} :
    ((aliveWordsAt c d).biUnion (fun w => {w ++ [Branch.even], w ++ [Branch.odd]})
        = aliveWordsAt c (d + 1))
      ↔ ∀ o, ¬ CertWindowAt c (d + 1) o := by
  classical
  constructor
  · intro hcyl o hwin
    have hne : minimalCertWordsAt c (d + 1) ≠ ∅ := by
      obtain ⟨w, hw, hlen⟩ :=
        (minimalCertAt_exists_iff hc (L := d + 1) (Nat.succ_pos d)).mpr ⟨o, hwin⟩
      intro hempty
      have : w ∈ minimalCertWordsAt c (d + 1) :=
        Finset.mem_filter.mpr ⟨mem_allWords.mpr hlen, hw⟩
      rw [hempty] at this
      exact absurd this (Finset.notMem_empty w)
    apply hne
    have hsub : minimalCertWordsAt c (d + 1) ⊆ aliveWordsAt c (d + 1) := by
      intro v hv
      have : v ∈ aliveWordsAt c (d + 1) ∪ minimalCertWordsAt c (d + 1) :=
        Finset.mem_union_right _ hv
      rw [← extensionsAt_eq_alive_union_certs hc, hcyl] at this
      exact this
    exact Finset.eq_empty_of_forall_notMem fun v hv =>
      (Finset.disjoint_left.mp (aliveAt_disjoint_certsAt (c := c) d) (hsub hv)) hv
  · exact aliveWordsAt_succ_of_window_empty hc

/-- The counting corollary: a free length doubles the alive count at every level. -/
theorem card_aliveWordsAt_succ_of_window_empty {c : ℝ} (hc : 1 ≤ c) {d : ℕ}
    (h : ∀ o, ¬ CertWindowAt c (d + 1) o) :
    (aliveWordsAt c (d + 1)).card = 2 * (aliveWordsAt c d).card := by
  classical
  have hne : ∀ w : List Branch, w ++ [Branch.even] ≠ w ++ [Branch.odd] := by
    intro w hw
    exact Branch.noConfusion (append_singleton_inj hw).2
  have hdisj : ∀ a ∈ aliveWordsAt c d, ∀ b ∈ aliveWordsAt c d, a ≠ b →
      Disjoint ({a ++ [Branch.even], a ++ [Branch.odd]} : Finset (List Branch))
        ({b ++ [Branch.even], b ++ [Branch.odd]} : Finset (List Branch)) := by
    intro a _ b _ hab
    simp only [Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton]
    rintro x (rfl | rfl) (hx | hx) <;> exact hab (append_singleton_inj hx).1
  have hpair : ∀ w ∈ aliveWordsAt c d,
      ({w ++ [Branch.even], w ++ [Branch.odd]} : Finset (List Branch)).card = 2 := by
    intro w _
    rw [Finset.card_insert_of_notMem (by simp [hne w]), Finset.card_singleton]
  rw [← aliveWordsAt_succ_of_window_empty hc h, Finset.card_biUnion hdisj,
    Finset.sum_congr rfl hpair, Finset.sum_const, smul_eq_mul, mul_comm]

/-! ## 10. The carrying lengths at level `Λ`, in closed form

At level zero `minimalCert_exists_iff_natLog` names the carrying lengths as
`Nat.log 2 (3 ^ o) + 1`, which is A020914 and needs no real number. At level `Λ` that closed
form has to move into the reals, and what it becomes is an **inhomogeneous** Beatty sequence:
the same slope `log₂ 3`, with intercept `Λ`.

So the level moves the intercept and nothing else. In particular it moves *which* lengths are
free without moving how many: the free density is `1 - 1/log₂ 3` at every level, because that
depends on the slope alone. -/

/-- `3 ^ o` is `2` to the power `o log₂ 3`. -/
theorem three_pow_eq_rpow (o : ℕ) :
    (3 : ℝ) ^ o = (2 : ℝ) ^ ((o : ℝ) * Real.logb 2 3) := by
  rw [mul_comm, Real.rpow_mul (by norm_num),
    Real.rpow_logb (by norm_num) (by norm_num) (by norm_num), Real.rpow_natCast]

/-- `3 ^ o · 2 ^ Λ` is `2` to the power `o log₂ 3 + Λ`. -/
theorem three_pow_mul_rpow (Λ : ℝ) (o : ℕ) :
    (3 : ℝ) ^ o * (2 : ℝ) ^ Λ = (2 : ℝ) ^ ((o : ℝ) * Real.logb 2 3 + Λ) := by
  rw [Real.rpow_add (by norm_num), ← three_pow_eq_rpow]

/-- **The shifted window is an inhomogeneous Beatty condition.** At level `Λ ≥ 0` the length
`L ≥ 1` carries the odd count `o` exactly when `⌊o log₂ 3 + Λ⌋ = L - 1`.

At `Λ = 0` this is `certWindow_iff_natLog`, since `Nat.log 2 (3 ^ o) = ⌊o log₂ 3⌋`. -/
theorem certWindowAt_iff_floor {Λ : ℝ} {L o : ℕ} (hL : 1 ≤ L) :
    CertWindowAt ((2 : ℝ) ^ Λ) L o ↔ ⌊(o : ℝ) * Real.logb 2 3 + Λ⌋ = (L : ℤ) - 1 := by
  have hkey := three_pow_mul_rpow Λ o
  have hLcast : ((L - 1 : ℕ) : ℝ) = (L : ℝ) - 1 := by
    have : (1 : ℕ) ≤ L := hL
    push_cast [Nat.cast_sub this]
    ring
  constructor
  · rintro ⟨h1, h2⟩
    rw [hkey] at h1 h2
    rw [← Real.rpow_natCast (2 : ℝ) (L - 1)] at h1
    rw [← Real.rpow_natCast (2 : ℝ) L] at h2
    rw [Real.rpow_le_rpow_left_iff (by norm_num)] at h1
    rw [Real.rpow_lt_rpow_left_iff (by norm_num)] at h2
    rw [hLcast] at h1
    rw [Int.floor_eq_iff]
    constructor
    · push_cast
      linarith
    · push_cast
      linarith
  · intro h
    rw [Int.floor_eq_iff] at h
    obtain ⟨h1, h2⟩ := h
    push_cast at h1 h2
    refine ⟨?_, ?_⟩
    · rw [hkey, ← Real.rpow_natCast (2 : ℝ) (L - 1),
        Real.rpow_le_rpow_left_iff (by norm_num), hLcast]
      linarith
    · rw [hkey, ← Real.rpow_natCast (2 : ℝ) L, Real.rpow_lt_rpow_left_iff (by norm_num)]
      linarith

/-! ## 11. Exactly when the two barrier conventions agree

This file passes the barrier strictly, following Paper B. Paper C's code reaches it
non-strictly. The difference is invisible except where `3 ^ o c` lands exactly on a power of
two, and this section says that and nothing more, because a prose version of it was wrong. -/

/-- Paper C's convention: the barrier is reached, not passed. -/
def exponentGapAtLE (c : ℝ) (w : List Branch) : Prop :=
  (3 : ℝ) ^ oddCount w * c ≤ 2 ^ w.length

/-- Off the lattice, the two conventions are the same predicate. -/
theorem exponentGapAt_iff_le_of_offLattice {c : ℝ}
    (h : ∀ o t : ℕ, (3 : ℝ) ^ o * c ≠ 2 ^ t) (w : List Branch) :
    exponentGapAt c w ↔ exponentGapAtLE c w := by
  constructor
  · exact le_of_lt
  · intro hle
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    · exact absurd heq (h (oddCount w) w.length)

/-- On the lattice they are not: the block word of the witnessing pair separates them. -/
theorem exists_disagreement_of_onLattice {c : ℝ} (hc : 1 ≤ c) {o t : ℕ}
    (h : (3 : ℝ) ^ o * c = 2 ^ t) :
    ∃ w : List Branch, exponentGapAtLE c w ∧ ¬ exponentGapAt c w := by
  have h3pos : (0 : ℝ) < 3 ^ o := by positivity
  have h23 : (2 : ℝ) ^ o ≤ 3 ^ o := pow_le_pow_left₀ (by norm_num) (by norm_num) o
  have hge : (3 : ℝ) ^ o * 1 ≤ 3 ^ o * c := by nlinarith
  rw [mul_one] at hge
  have hle : (2 : ℝ) ^ o ≤ 2 ^ t := by rw [← h]; linarith
  have hot : o ≤ t := by
    by_contra hcon
    have hlt : t < o := Nat.lt_of_not_le hcon
    have : (2 : ℝ) ^ t < 2 ^ o := pow_lt_pow_right₀ (by norm_num) hlt
    linarith
  refine ⟨blockWord t o, ?_, ?_⟩
  · unfold exponentGapAtLE
    rw [blockWord_length hot, blockWord_oddCount, h]
  · unfold exponentGapAt
    rw [blockWord_length hot, blockWord_oddCount, h]
    exact lt_irrefl _

/-- **The two conventions agree on every word exactly off the lattice.** -/
theorem exponentGapAt_agrees_iff {c : ℝ} (hc : 1 ≤ c) :
    (∀ w : List Branch, exponentGapAt c w ↔ exponentGapAtLE c w)
      ↔ ∀ o t : ℕ, (3 : ℝ) ^ o * c ≠ 2 ^ t := by
  constructor
  · intro hall o t heq
    obtain ⟨w, hle, hnot⟩ := exists_disagreement_of_onLattice hc heq
    exact hnot ((hall w).mpr hle)
  · intro h
    exact exponentGapAt_iff_le_of_offLattice h

/-- **Every whole-number level is on the lattice**, at `o = 0`. This is the half the earlier
prose had right, and it is the only half it had right. -/
theorem integer_level_onLattice (k : ℕ) :
    ¬ ∀ w : List Branch, exponentGapAt ((2 : ℝ) ^ k) w ↔ exponentGapAtLE ((2 : ℝ) ^ k) w := by
  intro hall
  have hc : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  exact (exponentGapAt_agrees_iff hc).mp hall 0 k (by norm_num)

end Problems.Juggler

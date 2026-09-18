# Paper B: which lengths carry a minimal certificate (Lean)

## Problem

Paper B's Lemma 5.1 lists the minimal power-envelope certificates of length at
most five. Determine, for every length, whether one exists and what it must look
like.

## Exact statement

Write `oddCount w` for the number of odd letters of a parity word and call `w` a
minimal certificate when `3 ^ oddCount w < 2 ^ |w|` and no proper nonempty prefix
satisfies the same. Define the window `CertWindow L o` as
`2 ^ (L - 1) <= 3 ^ o < 2 ^ L`. Then for `L >= 1`:

1. `certWindow_unique`: at most one `o` satisfies `CertWindow L o`.
2. `minimalCert_concat_even`: a minimal certificate's last letter is `E`.
3. `minimalCert_window`: a minimal certificate of length `L` has
   `CertWindow L (oddCount w)`, so its odd count is forced by its length.
4. `blockWord_isMinimalCertificate`: if `CertWindow L o` holds then
   `O^o E^(L-o)` is a minimal certificate of length `L`.
5. `minimalCert_exists_iff`: a minimal certificate of length `L` exists if and
   only if some power of three lies in `[2 ^ (L - 1), 2 ^ L)`.

Equivalently, with `beta = log 2 / log 3`, a certificate exists at `L` exactly
when `[(L-1) * beta, L * beta)` contains an integer, so the carrying lengths are
the jump points of `floor(L * beta)` and the empty lengths are the complement of
a Beatty sequence. No real number occurs in any statement or proof.

## Current literature

`extended`. Lemma 5.1 of
[juggler_parity_discrepancy_note.md](../theory/juggler_parity_discrepancy_note.md)
is the case `L <= 5` of (5), and the manuscript says nothing about longer words,
about the forced odd count, or about the last letter. The three-distance and
Beatty facts behind the reading are classical; nothing here claims them as new,
and none of them is used in a proof. No literature-wide priority claim.

## Branch budget

- **Target:** for which `L` does a minimal certificate exist, how many odd
  letters must it have, and does that explain the density plateaus?
- **Novelty hypothesis:** Lemma 5.1 generalised from a finite list to a
  structure theorem for every length, in `Nat` arithmetic.
- **Falsifier:** a minimal certificate whose odd count falls outside the window,
  two of one length with different odd counts, or one not ending in `E`.
- **Already killed by?:** none. [negative_knowledge.md](../negative_knowledge.md)
  kills the Paper A x B merge, local attacks, Baker/SdW, kernel localize and
  harvest counting; this is a finite-word structure theorem and none of the three
  tests (cycle, termination, local) applies to it.
- **Existing machinery:** `ItineraryStats` (`oddCount`, `exponentGap`),
  `PaperBCertificates` (`IsMinimalCertificate`), `PaperBFiveStepDensity`
  (the enumeration that exposed the plateaus).
- **Maximum Phase-0 scope:** one Lean module, registration, dossier, ledger row.
  No analysis, no exponential sum, no real-valued `beta`.
- **Promotion criterion:** existence, forcing, last letter and the explicit
  witness proved for general `L`, not by `decide` per length.
- **Stop criterion:** if the converse needs a nonconstructive witness, `PARK`
  with the forward direction only.

## Balanced-ternary formulation

Not used; the objects are parity words and powers of two and three.

## Why BT may be relevant

Not claimed.

## Candidate operations / invariants

The window `2 ^ (L-1) <= 3 ^ o < 2 ^ L`; minimality under proper prefixes; the
block word `O^o E^(L-o)`.

## Experiments

Exhaustive enumeration over all `2^L` words for `L = 1..16` agrees with the
window criterion at every length, with no exception. The empty lengths are
`3, 6, 9, 11, 14` -- not the multiples of three, which was the first guess and is
wrong at `L = 11`. The odd counts observed at the carrying lengths are
`0,1,2,3,4,5,6,7,8,9,10`, a single value at each, matching `ceil((L-1) * beta)`.
The minimal-certificate counts are `1,1,1,2,3,7,12,30,85,173,476`; that sequence
is recorded as an observation and is not claimed new or characterised.

## Conjectures

None. The counting question -- how many minimal certificates a carrying length
has -- is left open below rather than conjectured.

## Counterexamples

None. The falsifier did not fire at any length up to 16, and (1)-(5) are proved
for general `L`.

## Formalization

`formal/Problems/Juggler/PaperBCertificateLengths.lean`, imported by the umbrella
`Problems.Juggler`, registered in `AUXILIARY_MODULES`. Deliberately outside the
Paper B barrel, like `PaperBCertificates` which it imports: that module depends on
the itinerary stack shared with Paper A.

Twenty-one declarations, no `sorry`, no `decide` in the general theorems. The
per-length facts `window_empty_three`, `window_empty_six`, `window_empty_nine`,
`window_empty_eleven` and `window_empty_fourteen` are the plateau lengths, each
closed by `interval_cases` on the bound `certWindow_le` supplies.

## Results

`J-paper-b-certificate-length-window` — `EXACT — LEAN VERIFIED`.

The plateaus in the certificate density are explained rather than observed: the
density is flat from `d-1` to `d` exactly when no power of three lies in
`[2 ^ (d-1), 2 ^ d)`, which is why `7/8` holds at both `d = 5` and `d = 6` and
`237/256` at both `d = 8` and `d = 9`.

## Open questions

How many minimal certificates a carrying length has. The count is the number of
words of length `L` with `ceil((L-1) * beta)` odd letters that stay non-contracting
until the final `E` -- a walk constrained below a line of irrational slope, which
is the same object as the survivor count `N_d` of `PaperBSurvivorDecay` read from
the other side. That connection is the reason this branch may be worth more than
its own statement: `PaperBSurvivorAsymptotic` states the meander local limit
theorem as a hypothesis with no route to it, and this gives a second reading of
the same constrained walk.

Whether the count sequence `1,1,1,2,3,7,12,30,85,173,476` is known.

## Decision

`PROMOTE` — all five statements are proved for general `L` and the falsifier did
not fire. Nothing analytic was proved and the manuscript's status is unchanged:
this characterises the certificates, not their density for the Juggler map. Best
next question: is the minimal-certificate count at length `L` the same
constrained-walk quantity as `N_d`, and does a bijection between them give the
meander shape that `PaperBSurvivorAsymptotic` has to assume?

## Publication assessment

Status: `THEOREM`. Generalises a printed lemma of Paper B and explains a pattern
the manuscript does not mention, but proves no estimate and does not move any
density.

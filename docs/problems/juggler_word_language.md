# Juggler word language

Status: **EXPLORATORY**

Standalone arithmetic layer on the rewritten Juggler formalization. It
is **not** a Research Engine control-layer experiment and not a claim
that every positive integer reaches 1.

## Problem

Do the existential \(O/E\) languages of realized Juggler words carry
arrangement constraints beyond the already-known persistent-expanding
block grammar \(O^a E^b\)?

## Exact statement

Keep the quantifiers existential.

\[
\mathcal L=\{w\in\{O,E\}^*:\exists n,\ \operatorname{follows}(n,w)\},
\]

\[
\mathcal L_\uparrow=\{w:\exists n,\ \operatorname{follows}(n,w)\land T_w(n)>n\},
\]

and two PE languages: single residual blocks that some \(n\) realises
as `PersistentExpandingResidual`, and concatenations of such blocks
(PE-run words). Syntactic `expandingItinerary` (\(2^{|w|}<3^{\#O(w)}\)) is
a different predicate.

After subtracting the known grammar

\[
O^a E^b,\qquad a\ge 2,\quad b\ge 1,\quad b\le\texttt{maxExpandingEvens}(a),
\]

do \(\operatorname{Fact}_r\), \(\operatorname{Pref}_r\), or
\(\operatorname{Suff}_r\) of the realised PE-run language miss a
grammar-legal word that survives larger numeric windows? Isolated-odd
factors such as \(EOE\) are that grammar, not a new law.

This says nothing about totality.

## Current literature

- `follows` / `image` —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.Itinerary`.
- Expanding residual block \(a\ge 2\), \(b<a\) —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.Scale` and
  `ExpansionBlocks`.
- Expanding-word grammar is persistence —
  **CLOSE** as `EXPANDING_GRAMMAR_IS_PERSISTENCE`.
- Every mixed prefix-NC itinerary of length \(\le 8\) is realized —
  **CLOSE** as `PREFIX_NC_ARITHMETIC_COMPLEX`.
- Residual-state finite quotients need the integer itself —
  **CLOSE** as `RESIDUAL_STATE_NEEDS_X`.
- Odd-to-even two-step contraction —
  **EXACT — LEAN VERIFIED** as `floorPower_odd_even_two_step_lt`.

Project relationship: **extended**.

## Branch budget

```text
Mathematical target     After subtracting the known PE block grammar,
                        do L, L_up, or PE-run words have extra
                        forbidden factors or prefix/suffix constraints
                        that survive larger windows?
Novelty hypothesis      Arithmetic realization forbids some
                        grammar-legal arrangements, not just letter
                        counts or 3^{#O}>2^{|w|}
Falsifier               Fact_r(realized PE runs)=Fact_r(block grammar);
                        L_r={O,E}^r; every missing factor appears later;
                        any MN compression is the landing integer
Existing machinery      follows/image, oddEvenBlock, expandingItinerary,
                        PersistentExpandingResidual, PersistentExpansionChain,
                        walk_pe_run, expanding_grammar type graph,
                        prefix-NC realizability ≤8, residual-state CLOSE
Maximum Phase-0 scope   Language defs; cheap Fact/Pref/Suff census;
                        grammar-vs-realized comparison; one Lean
                        constraint if it survives; no automaton,
                        no cycles, no extremal theory, no halt
Promotion criterion     A surviving arrangement constraint that is not
                        a≥2 / b<a / 3^{#O}>2^k / T_w(n)>n
Stop criterion          Falsifiers A–F; machinery gravity
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- `jugglerLanguage` / `jugglerLanguage_factor` —
  **EXACT — LEAN VERIFIED**, and a **REPARAMETERIZATION** of
  `follows` / `image`
- `expandingLanguage` is existential, not `expandingItinerary` —
  **EXACT — LEAN VERIFIED**
- `expandingLanguage_not_factor_closed` (`OOE` at 5, not `OE`) —
  **EXACT — LEAN VERIFIED**, using
  `floorPower_odd_even_two_step_lt`
- A grammar-legal PE factor is permanently forbidden —
  **REFUTED** on growing windows (Falsifier C)
- \(\mathcal L_r=\{O,E\}^r\) fails independently of the search window —
  **REFUTED** for \(r\le 6\) (Falsifier A for \(\mathcal L\))
- Prefix Myhill–Nerode compresses beyond the landing integer —
  **REFUTED** on the scanned PE runs (Falsifier D)
- Finite PE automaton — not added
- Infinite PE orbit — not claimed

## Experiments

Cheap language census, not a new raw search.

- Forward \(\mathcal L\) through length 8 at \(n\le 2000\) misses many
  even-prefix words. Those are window artefacts: `EEOE` is realised at
  \(2500\); every length-\(\le 5\) word is realised by \(n\le 10000\);
  the three length-\(6\) leftovers are realised at \(18226\), \(33933\),
  and by even pullback at \(131044\).
- PE-run factors at \(n\le 400\) miss several grammar-legal words,
  including `OEEO` and `EEEEEE`. At \(n\le 2000\) the missing set
  shrinks; at \(n\le 8000\) only `EEEEEE` and `OEEEEO` remain. Both
  appear on already-known longer runs: `OEEEEO` at \(9157\)
  (`OOOOOOOOEEEE` then `OOE`), `EEEEEE` at \(14237\) (the length-\(7\)
  run whose third block is `OOOOOOOOOOOEEEEEE`).
- Realised PE-run factors stay inside the grammatical factor language.
  Isolated-odd `EOE` never occurs.
- Prefix Myhill–Nerode on PE-run words is coarser than the landing
  integer: the empty prefix, `OOE`, and `OOOE` each admit more than
  one next block. Distinct landings share future classes.
- Terminal PE suffixes occupy the same short block types
  (`OOE`, `OOOE`, …) for both `leave_odd_odd` and `descent`.

Tests: `tests/research/juggler_sequence/test_itinerary_language.py`.
Do not default-test \(n\le 20000\).

## Conjectures

None opened in `conjectures/`.

## Counterexamples

- “Some length-\(\le 5\) word is unrealisable.” False:
  \(\mathcal L_r=\{O,E\}^r\) for \(r\le 5\) once \(n\le 10000\).
- “`EEOE` is a forbidden factor of \(\mathcal L\).” False: \(n=2500\).
- “`EEEEEE` is a permanent PE-run forbidden factor.” False: the
  \(14237\) run contains `OOOOOOOOOOOEEEEEE`.
- “`OEEEEO` never occurs because a \(b=4\) block cannot continue.”
  False: \(9157\xrightarrow{\mathrm{OOOOOOOOEEEE}}{}\xrightarrow{\mathrm{OOE}}\).
- “PE-run prefixes determine the next block.” False: `OOE` continues
  as `OOE`, `OOOOE`, `OOOOEE`, or ends.

## Formalization

`formal/Problems/Juggler/ItineraryLanguage.lean`, after `OddLandingSets`.
No `sorry`. No automaton. No forbidden-factor theorem. No ledger
row: the Lean lemmas package `follows` / `image` and the existing
odd-to-even contraction.

## Results

- \(\mathcal L\) is factor-closed. \(\mathcal L_\uparrow\) is not:
  `OOE` is expanding-existential and `OE` is not.
- On the scanned windows, realised PE-run factors fill the known
  block-grammar factor language as \(n\) grows. No extra arrangement
  law survives.
- Short missing words in \(\mathcal L\) are even-prefix scale, not
  a forbidden-factor theorem. Do not infer \(\mathcal L=\{O,E\}^*\).
- The symbolic prefix quotient is strictly coarser than the landing
  integer. That is Case B of the language-versus-residual comparison,
  already predicted by `RESIDUAL_STATE_NEEDS_X`.

## Open questions

The leftover is still whether an odd-to-odd residual chain can
continue indefinitely. Do not reopen factor languages, Myhill–Nerode
automata, or extremal word arrangements.

## Decision

**CLOSE** the itinerary-language attack as
`JUGGLER_LANGUAGE_IS_KNOWN_GRAMMAR`. After the known \(O^a E^b\)
grammar is subtracted, every candidate forbidden factor is a search
window. \(\mathcal L\) fills at short length. Prefix futures do not
compress beyond the landing integer. The only exact language lemmas
are factor-closure of \(\mathcal L\) and the already-known `OE`
contraction. Do not claim termination. Do not `PROMOTE` a linguistic
rewrite of \(a\ge 2\) or \(3^{\#O}>2^{|w|}\). Parked later phases
(extremal words, cyclic words, automata) stay parked.

Best next question: is there any arithmetic, other than the integer
\(y\) itself, that decides whether a persistent residual landing
stays odd-to-odd?

## Publication assessment

Status: `EXPLORATORY`. A negative language census and two packaging
lemmas, not a paper candidate and not a Juggler totality result.

# Juggler Amplify versus surplus on the thirty length-11 leftovers

Status: **ARCHIVED**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1. It is not a length-11 census, not a
leftover cell, and not the \(O^7\mathrm{EEEE}\) +1-chain.

## Problem

The thirty first-expanding four-even short-gap leftovers have length
11 and leak under \(Z_4\). First-defect Amplify lower-bounds the
global defect \(\Delta\) by lifting the first remainder and dropping
later floors. Does that bound beat the formal surplus
\(G=n^{3^7}-n^{2^{11}}\) below the leftover-cell cutoff?

## Exact statement

For a realized itinerary \(w\),

\[
\Delta_w(n)\ge\operatorname{Amplify}(n,w),\qquad
G_w(n)=n^{3^{\#O}}-n^{2^{|w|}}.
\]

\(\operatorname{Amplify}>G\) forces \(T_w(n)<n\), so \(w\) is not a
cycle itinerary. Phase 0 asks whether a uniform first-defect \(F\le
\operatorname{Amplify}\) exceeds \(G\) on the thirty words
\(O^{a_0}EO^{a_1}EO^{a_2}EO^{a_3}E\) at the first expanding \(a_0\)
(seven odds, length 11), at an \(N_0\) below the leftover-cell fire.

This is not a `CycleItinerary` theorem. It is not a length-8, length-9,
or length-11 census and not a halt theorem. There is no
`no_cycle_itinerary_amplify_surplus` and no
`no_cycle_itinerary_length_eleven`.

## Current literature

- `amplifyDefect` / `firstDefect` / odd cubic lift —
  **EXACT — LEAN VERIFIED**. Those bounds do not claim
  \(\Delta>G\).
- Compensated contraction \(\Delta>G\Rightarrow T_w<n\) —
  **EXACT — LEAN VERIFIED**. First-defect-only compensation
  on `EOO` is **REFUTED**.
- Four-even short-first-gap \(Z_4\) —
  **PARK**. Fires at \(a_0+1\); leaks at length 11.
- Tighter last-cluster pullback —
  **REFUTED** / **CLOSE**.
- \(O^7\mathrm{EEEE}\) +1-chain —
  **EXACT — LEAN VERIFIED** (`no_cycle_itinerary_oooooooeeee`).
  A different comparison: image versus \((n+1)^{16}\), not
  Amplify versus \(G\).

Project relationship: **extended**, then **refuted**.

## Branch budget

```text
Mathematical target     Does Amplify beat G=n^{2187}-n^{2048}
                        on the 30 length-11 leftovers below
                        the leftover-cell cutoff?
Novelty hypothesis      First-defect cubic lift eats the
                        n^{139} surplus earlier than Z=(n+1)^{16}
Falsifier               Best uniform F is n^{2184} rho against
                        G~n^{2187}, or F>G is T_w<n rewritten
Existing machinery      amplifyDefect; formal surplus;
                        30-word list; compensated contraction
Maximum Phase-0 scope   Exponent census plus log F vs log G;
                        no Lean, no length-11 assembler
Promotion criterion     A uniform F fires below leftover N0
                        on a named itinerary, and is not T<n
Stop criterion          F is the trailing-evens cell; Amplify
                        never beats G past the seven-odd cutoff
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- every length-11 short-gap word has seven odds, so
  \(G\sim n^{2187}\) —
  **EXACT — HUMAN PROOF**
- after a first-letter insertion, each later odd multiplies
  \(D\) by \(3x^{2^{k+1}}\); an even letter halves \(x\) and
  increments \(k\), so \(2^{k+1}x\) is invariant —
  **EXACT — HUMAN PROOF**
- linear Amplify exponent is 2184 for \(\rho=1\) and 2185.5
  for \(\rho\asymp n^{3/2}\), on all thirty words —
  **COMPUTATIONALLY VERIFIED**
- later first-defect index only loses lifts —
  **COMPUTATIONALLY VERIFIED**
- \(\rho=1\) Amplify misses \(G\) at every \(n\ge 12\) —
  **COMPUTATIONALLY VERIFIED**
- optimistic max-\(\rho\) Amplify (tight scales) beats \(G\)
  at \(n=12\) and already misses at the seven-odd cutoff
  \(256\) —
  **COMPUTATIONALLY VERIFIED**
- realized followers with \(n\le 400\) have Amplify \(<G\) —
  **COMPUTATIONALLY VERIFIED**
- Amplify excludes a length-11 leftover — **REFUTED**
- no cycle of length eleven — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.amplify_surplus`
- Records: [juggler_amplify_surplus.md](../research/juggler_amplify_surplus.md),
  [juggler_amplify_surplus.json](../research/juggler_amplify_surplus.json)
- Tests: `tests/research/juggler_sequence/test_amplify_surplus.py`
- No new Lean. No length-11 census. Paper A is unchanged.

## Conjectures

None opened.

## Counterexamples

The hypothesis that first-defect Amplify beats \(G\) below the
leftover-cell cutoff is **REFUTED**. The linear term is
\(n^{2184}\rho\) against \(n^{2187}\). Even letters do not close
that \(n^3\) gap. Optimistic max-\(\rho\) Amplify already loses
at \(n=256\), which is the first \(n\) that can follow seven
odds.

The stronger claims that remain false or unproved:

- “later remainders dropped from Amplify are a small error” —
  they are the \(n^3\) that leftover cells and the +1-chain
  keep.
- “interleaved evens strengthen Amplify” — the product
  \(2^{k+1}x\) is invariant.
- “no cycle of length eleven” — not claimed.

## Formalization

None new. `amplifyDefect` and
`power_bound_compensated_contracts` already exist.
`SmallCycleCensus.lean` still assembles only through length
seven. No `no_cycle_itinerary_amplify_surplus`. No
`no_cycle_itinerary_length_eleven`. No `sorry`. No halt theorem.
Paper A is unchanged.

## Results

Classification **AMPLIFY_SURPLUS_REFUTED**.

First-defect Amplify is the wrong side of an \(n^3\) gap. The
first odd *inserts* \(\rho\) and does not lift an existing
defect; the six later odds produce exponent 2184. Surplus is
\(3^7=2187\). The cubic \(D^2,D^3\) terms stay behind the
scale \(x^{2^k}\) by that same \(n^3\). Leftover cells and the
\(O^7\mathrm{EEEE}\) +1-chain succeed at large \(n\) because
they bound the *image*, not the first remainder.

## Open questions

Stop on Amplify versus surplus. Do not write a thirty-word
Amplify assembler. The +1-chain that killed \(O^7\mathrm{EEEE}\)
is a different method; do not automatically scan the other
twenty-nine with leftover cells.

## Decision

**CLOSE**. First-defect Amplify cannot beat the formal surplus
on any of the thirty length-11 leftovers past the seven-odd
cutoff. The method is \(T_w<n\) with the later remainders
dropped, and those remainders are the gap. It is not a
length-11 census and not a halt theorem.

Best next question: an itinerary-equation or inverse-cell argument
for a named leftover other than \(O^7\mathrm{EEEE}\), not
another defect-versus-surplus bound.

## Publication assessment

Status: `ARCHIVED`.

A negative method gate: Amplify does not repair the length-11
leak. Not a paper theorem and not a Juggler totality result.

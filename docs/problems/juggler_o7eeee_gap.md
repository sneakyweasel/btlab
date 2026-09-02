# Juggler \(O^7\mathrm{EEEE}\) +1-chain gap

Status: **THEOREM**

Standalone application phase on the sharp four-even leftover
\(O^7\mathrm{EEEE}\). It is **not** a Research Engine control-layer
experiment, not a length-11 census, not a \(Z_5\) family, and not a
claim that every positive integer reaches 1.

## Problem

Does every seven-odd image sit at or above \((n+1)^{16}\), so that
the EEEE inverse cell is empty by a proof rather than a scan to
\(N_0=828\,484\,409\)?

## Exact statement

If \(n\ge 2\) follows \(O^7\), then

\[
T^7(n)\ge(n+1)^{16}.
\]

In particular \(T^7(n)\notin[n^{16},(n+1)^{16})\), so
\(O^7\mathrm{EEEE}\) is not a cycle itinerary. Lean theorems
`o7_image_ge_succ_pow16` and `no_cycle_itinerary_oooooooeeee`
live in `O7EEEEGap.lean`. They are not Paper A theorems.

## Current literature

- Inverse-cell window empty on \(3\le n<N_0\) —
  **COMPUTATIONALLY VERIFIED**
  ([juggler_o7eeee_window](juggler_o7eeee_window.md)).
- Leftover prefix-cell with the \(4\)-fudge, first fire at
  \(N_0=828\,484\,409\) —
  **EXACT — LEAN VERIFIED**.
- No seven-odd run on \(2\le n<256\) —
  **EXACT — LEAN VERIFIED** (`no_follows_seven_odds_of_lt256`).
- Tight last-cluster pullback; rotation / internal-E on the
  thirty leftovers —
  **REFUTED** / **CLOSE**.
- Leftover-cell lag —
  **CLOSE**.

Project relationship: **extended**. The window gap is now an exact
\(+1\)-chain, not another \(Z\).

## Branch budget

```text
Mathematical target     Prove T^7(n) >= (n+1)^16 on O^7 starts
Novelty hypothesis      the leftover 4-fudge is the slack;
                        the exact +1 cell fires at 256
Falsifier               an O^7 image below (n+1)^16, or the
                        +1-chain still needs n ~ 10^8
Existing machinery      (T+1)^2 > x^3; x_k >= n on odd runs;
                        no_follows_seven_odds_of_lt256;
                        leftover_prefix_preimage at N0=828484409
Maximum Phase-0 scope   one-word +1-chain; no Lean, no Z5,
                        no thirty-itinerary census
Promotion criterion     a proof covering every O^7 start
Stop criterion          the bound still needs a huge pin;
                        a 30-word scan; Z5; halt claim
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- no seven-odd run below \(256\) —
  **EXACT — LEAN VERIFIED**
- \(n^{6177}<(n+1)^{3990}(T^7(n)+1)^{128}\) on an \(O^7\) run —
  **EXACT — LEAN VERIFIED**
- \(n^{6177}>(n+1)^{6038}\) for every \(n\ge 256\) —
  **EXACT — LEAN VERIFIED**
- \(T^7(n)\ge(n+1)^{16}\) on every \(O^7\) start —
  **EXACT — LEAN VERIFIED** (`o7_image_ge_succ_pow16`)
- \(O^7\mathrm{EEEE}\) is not a cycle itinerary —
  **EXACT — LEAN VERIFIED** (`no_cycle_itinerary_oooooooeeee`)
- no cycle of length 11 — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.o7eeee_gap`
- Records: [juggler_o7eeee_gap.md](../research/juggler_o7eeee_gap.md),
  [juggler_o7eeee_gap.json](../research/juggler_o7eeee_gap.json)
- Tests: `tests/research/juggler_sequence/test_o7eeee_gap.py`
- The Research Engine control layer is not modified.
- Finite checks: \(257^{256}<3\cdot256^{256}\), \(3^{24}<2^{40}\),
  pin \(n<10^4\).
- Lean: `Problems/Juggler/O7EEEEGap.lean`. Not imported by Paper A.

## Conjectures

None opened.

## Counterexamples

None to the gap. The stronger claims that fail:

- “the leftover \(4\)-fudge is necessary for this itinerary” — the
  exact successor cell fires at the existing seven-odd cutoff.
- “this is a length-11 census” — one word.
- “this is a Paper A theorem” — `JugglerPaper` does not import
  `O7EEEEGap.lean`.

## Formalization

`formal/Problems/Juggler/O7EEEEGap.lean`. Theorems
`o7_image_ge_succ_pow16` and `no_cycle_itinerary_oooooooeeee`.
Existing `no_follows_seven_odds_of_lt256` and
`cycle_trailing_evens_lt` are reused. No `sorry`. Paper A is
unchanged.

## Results

Classification **O7EEEE_GAP_PROVED**.

On an \(O^7\) run the exact cells \(x_k^3<(x_{k+1}+1)^2\) and the
comparisons \(x_k\ge n\) compose to
\(n^{6177}<(n+1)^{3990}(T^7(n)+1)^{128}\). For \(n\ge 256\) one
has \(n^{6177}>(n+1)^{6038}\) because \(257^{256}<3\cdot256^{256}\)
and \(256^{139}>2^{40}>3^{24}>(257/256)^{6038}\). Lean excludes
seven-odd runs below \(256\). Therefore
\(T^7(n)\ge(n+1)^{16}\) on every \(O^7\) start, and
\(O^7\mathrm{EEEE}\) is not a cycle itinerary.

The leftover envelope \(2^{4118}(n+1)^{2048}<n^{2187}\) is a
strictly weaker comparison. It is not used.

## Open questions

Do not scan the other twenty-nine leftovers automatically. Do not
write \(Z_5\). The same \(+1\)-chain is not automatically a method
for the other leftovers.

## Decision

**PROMOTE** the Lean \(+1\)-chain. The leftover \(4\)-fudge was the
obstruction to a small threshold, not a missing inverse-cell
phenomenon. This is not a halt result and not an exclusion of the
other twenty-nine words.

Best next question: stop. Do not open the other twenty-nine
leftovers from this theorem.

## Publication assessment

Status: `THEOREM`. A one-word exact exclusion by an elementary
\(+1\)-chain, not a paper candidate and not a Juggler totality
result.

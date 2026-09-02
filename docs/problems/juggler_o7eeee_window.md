# Juggler \(O^7\mathrm{EEEE}\) inverse-cell window

Status: **EXPLORATORY**

Standalone application phase on the sharp four-even leftover
\(O^7\mathrm{EEEE}\). It is **not** a Research Engine control-layer
experiment, not a length-11 census, not a \(Z_5\) family, and not a
claim that every positive integer reaches 1.

## Problem

Is \(T_{O^7\mathrm{EEEE}}(n)=n\) possible on the leftover-cell
window, or is the EEEE inverse cell empty of seven-odd images?

## Exact statement

Write \(w=O^7\mathrm{EEEE}\). A realization with \(T_w(n)=n\) is
exactly

\[
T^7(n)\in\bigl[n^{16},(n+1)^{16}\bigr)
\]

together with an even \(T^7(n)\) and four even square-roots back
to \(n\). The leftover prefix-cell

\[
n^{3^7}>2^{\mathrm{denomBits}(7)}(n+1)^{2^{11}}
\]

holds for every \(n\ge N_0=828\,484\,409\) and forbids a cycle
there. Phase 0 asks whether any odd \(n\) with \(3\le n<N_0\)
lands in that inverse cell.

This is one word. It is not a length-11 census and not a halt
theorem. The later satellite `O7EEEEGap.lean` has
`no_cycle_itinerary_oooooooeeee`.

## Current literature

- Leftover prefix-cell; trailing-evens \(r=4\) —
  **EXACT — LEAN VERIFIED**.
- \(N_0(7,4)=828\,484\,409\) —
  **COMPUTATIONALLY VERIFIED**
  ([juggler_leftover_cell_lag](juggler_leftover_cell_lag.md)).
- Four-even short-gap \(Z_4\) leaks at length 11 —
  **PARK**.
- Tight last-cluster pullback on this itinerary —
  **REFUTED** / **CLOSE**.
- Rotation / internal-E on the thirty leftovers —
  **REFUTED** / **CLOSE**.
- Even-count \(\le 3\) —
  **EXACT — LEAN VERIFIED**. Period \(\ge 11\).

Project relationship: **extended**. The envelope leftover is now
an exact inverse-cell search, not another \(Z\).

## Branch budget

```text
Mathematical target     Is T_{O^7 EEEE}(n)=n empty on the
                        leftover-cell window n<N0?
Novelty hypothesis      the EEEE inverse cell is empty of
                        O^7 images below N0
Falsifier               a hit, or T^7 enters the cell
Existing machinery      leftover_prefix_preimage; trailing evens
                        r=4; odd_preimage_unique; N0=828484409
Maximum Phase-0 scope   exact window scan of one word; no Lean,
                        no thirty-itinerary census, no Z5
Promotion criterion     Empty window, or a cycle
Stop criterion          A hit without a theorem; a 30-word
                        scan; Z5; halt claim
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- leftover cell fires at \(n\ge 828\,484\,409\) and not at
  \(N_0-1\) —
  **COMPUTATIONALLY VERIFIED**
- no \(O^7\mathrm{EEEE}\) return on \(3\le n<N_0\) —
  **COMPUTATIONALLY VERIFIED**
- \(T^7(n)\) never entered \([n^{16},(n+1)^{16})\)
  (\(6\,473\,954\) \(O^7\) starts; \(3\,234\,088\) even images,
  all above the cell) —
  **COMPUTATIONALLY VERIFIED**
- closest ratio \(T^7(n)/(n+1)^{16}=445.01\) at \(n=289\) —
  **COMPUTATIONALLY VERIFIED**
- `no_cycle_itinerary_oooooooeeee` — later Lean, see
  [juggler_o7eeee_gap](juggler_o7eeee_gap.md)
- no cycle of length 11 — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.o7eeee_window`
- Records: [juggler_o7eeee_window.md](../research/juggler_o7eeee_window.md),
  [juggler_o7eeee_window.json](../research/juggler_o7eeee_window.json)
- Tests: `tests/research/juggler_sequence/test_o7eeee_window.py`
- The Research Engine control layer is not modified.
- Exact integer scan. No Lean. No Paper A theorem.

## Conjectures

None opened.

## Counterexamples

None to emptiness. The stronger claims that fail:

- “the leftover cell is sharp in the window” — every even
  seven-odd image overshoots \((n+1)^{16}\) by at least \(445\).
- “a hit exists below \(N_0\)” — the window is empty.
- “this is a length-11 census” — one word.

## Formalization

The later laboratory satellite `O7EEEEGap.lean` now has
`no_cycle_itinerary_oooooooeeee`. This window page remains a
computational scan. Paper A is unchanged.

## Results

Classification **O7EEEE_WINDOW_EMPTY**.

There is no cycle itinerary \(O^7\mathrm{EEEE}\) on
\(3\le n<828\,484\,409\). Combined with the leftover cell, there
is no such cycle itinerary for any \(n\ge 3\). The seven-odd image
never meets the EEEE inverse cell. This is a one-word
computational exclusion, not a Lean theorem and not a
length-11 census.

## Open questions

Answered in [juggler_o7eeee_gap.md](juggler_o7eeee_gap.md):
every \(O^7\) image satisfies \(T^7(n)\ge(n+1)^{16}\). Do not
scan the other twenty-nine leftovers automatically.

## Decision

**PROMOTE** the empty inverse-cell window. The leftover envelope
is not sharp: the actual obstruction is a factor-\(445\) miss,
not the \(N_0\sim 8\cdot 10^8\) cell. This is not a halt result
and not an exclusion of the other twenty-nine words.

Best next question: answered in
[juggler_o7eeee_gap.md](juggler_o7eeee_gap.md).

## Publication assessment

Status: `EXPLORATORY`. A one-word empty-window verification, not
a paper candidate and not a Juggler totality result.

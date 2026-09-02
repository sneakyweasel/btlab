# Juggler leftover-cell lag

Status: **EXPLORATORY**

Standalone diagnostic on the trailing-evens leftover family
\(O^a E^e\). It is **not** a Research Engine control-layer
experiment, not a \(Z_5\) family, not a length census, and not a
claim that every positive integer reaches 1.

## Problem

Does the leftover-cell lag of \(O^{a_*(e)}E^e\) stay \(1\) as
\(e\) grows, or does it grow? If it grows, leftover-cell induction
is permanently parked for \(e\ge 4\). If it stays \(1\), each
\(e\) still leaves a finite first-layer list: an honest census,
not a unifying method.

## Exact statement

Write \(a_*(e)\) for the least \(a\) with \(2^{a+e}<3^a\). The
leftover prefix-cell for the trailing-evens word \(O^a E^e\) is

\[
n^{3^a}>2^{\mathrm{denomBits}(a)}(n+1)^{2^{a+e}}.
\]

\(N_0(e,a)\) is the first \(n\ge 2\) at which the cell holds.
Lag is the least \(k\ge 0\) with \(N_0(e,a_*(e)+k)\le 800\).

At \(e=4\), \(a_*=7\) and the cell misses the window
(\(N_0\sim 8\cdot 10^8\)); it fires at \(a_*+1\) with
\(N_0=37\). Phase 0 asks whether that lag stays in \(\{0,1\}\)
through \(e\le 16\), or reaches \(2\).

Do not open an \(e=5\) leftover-cell family. Do not prove a lag
theorem for all \(e\). Do not prove totality.

## Current literature

- Leftover prefix-cell schema —
  **EXACT — LEAN VERIFIED**.
- Uniform two-even tails (Theorem 3.12) fire at \(a_*(2)=4\)
  with \(N_0=205\) —
  **EXACT — LEAN VERIFIED**.
- Bunched \(O^6\mathrm{EEE}\) fires at first expanding \(a\) —
  **EXACT — LEAN VERIFIED**.
- Four-even short-gap \(Z_4\) misses the first expanding layer
  and fires at \(a_0+1\) with \(N_0\le 180\) —
  **COMPUTATIONALLY VERIFIED** / **PARK**.
- Tight \(Z_4\) pullback on \(O^7\mathrm{EEEE}\) —
  **REFUTED**.

Project relationship: **extended**. One family, one number
(does the lag grow?). Not a new cell.

## Branch budget

```text
Mathematical target     Does leftover-cell lag of O^{a_*(e)} E^e
                        stay 1 as e grows, or grow?
Novelty hypothesis      lag grows, so leftover induction is
                        permanently parked for e≥4
Falsifier               lag stays 0 or 1 through e≤16
Existing machinery      leftover_prefix_preimage; denomBits;
                        Z=(n+1)^{2^e}; e=4 lag 1
Maximum Phase-0 scope   N0 at a_*, a_*+1, a_*+2 for e=2..16;
                        no Lean, no Z5, no thirty shapes
Promotion criterion     A named lag law, or a proof lag ≤ 1
                        for all e
Stop criterion          Lag computed. Do not write Z5.
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- \(a_*(2),\ldots,a_*(6)=(4,6,7,9,11)\) —
  **EXACT — HUMAN PROOF**
- lag \(\in\{0,1\}\) for \(2\le e\le 16\); max lag \(1\) —
  **COMPUTATIONALLY VERIFIED**
- \(N_0(e,a_*(e)+1)\le 59\) on that range —
  **COMPUTATIONALLY VERIFIED**
- \(e=4\): \(N_0(7,4)=828\,484\,409\), \(N_0(8,4)=37\) —
  **COMPUTATIONALLY VERIFIED**
- lag grows with \(e\) —
  **REFUTED** through \(e=16\)
- leftover induction kills every \(e\) automatically —
  **REFUTED** (lag \(1\) still leaks a first-layer list)
- lag \(\le 1\) for all \(e\) — not claimed
- no five-even leftover — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.leftover_cell_lag`
- Records: [juggler_leftover_cell_lag.md](../research/juggler_leftover_cell_lag.md),
  [juggler_leftover_cell_lag.json](../research/juggler_leftover_cell_lag.json)
- Tests: `tests/research/juggler_sequence/test_leftover_cell_lag.py`
- The Research Engine control layer is not modified.
- No Lean. No \(Z_5\). No Paper A theorem.

## Conjectures

None opened.

## Counterexamples

- “lag grows with \(e\)” — lags on \(e=2..16\) are
  \(0,0,1,1,0,1,1,0,0,1,1,0,1,1,0\). Max is \(1\).
- “\(a_*+1\) eventually needs a huge \(N_0\)” — max
  \(N_0(a_*+1)\) on the range is \(59\) (at \(e=7\)).
- “leftover induction is a step on \(e\)” — when lag is
  \(1\), the first expanding itinerary still leaks, as at
  \(O^7\mathrm{EEEE}\).

## Formalization

None. Existing `leftover_prefix_preimage` and `denomBits` are
unchanged. No `sorry`. No `no_cycle_itinerary_five_even`. No
`leftover_cell_lag_inductive`. Paper A is unchanged.

## Results

Classification **LEFTOVER_CELL_LAG_STAYS_ONE**.

The leftover-cell lag of \(O^{a_*(e)}E^e\) stays in
\(\{0,1\}\) through \(e=16\). It does not grow. Leftover-cell
induction is therefore a per-\(e\) census: each lag-\(1\) even
count still has a finite first-layer list. That is not a
unifying method and not a reason to write \(Z_5\).

## Open questions

Answered in [juggler_o7eeee_window.md](juggler_o7eeee_window.md):
the \(O^7\mathrm{EEEE}\) inverse-cell window is empty. Do not
write \(Z_5\).

## Decision

**CLOSE**. The growth hypothesis is false on the Phase-0 range.
Leftover induction does not become a theorem by raising \(e\).
This is not a halt result and not a five-even cell.

Best next question: answered in
[juggler_o7eeee_window.md](juggler_o7eeee_window.md).

## Publication assessment

Status: `EXPLORATORY`. A one-family lag table, not a paper
candidate and not a Juggler totality result.

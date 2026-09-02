# Juggler repeated OE scale budget

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1.

## Problem

How many consecutive `OE` blocks can a hypothetical minimal
non-terminating orbit sustain before the repeated \(3/4\)-contraction
forces a state below \(n_*\)?

## Exact statement

Do not assume that every long trajectory contains many `OE` blocks.
If a later state \(x\) on a `MinimalNonTerm` orbit realizes
\((\texttt{OE})^r\), prove

\[
T^{2r}(x)^{4^r}\le x^{3^r}
\]

and, since the image stays \(\ge n_*\),

\[
n_*^{4^r}\le x^{3^r}.
\]

The start itself cannot realize \((\texttt{OE})^r\) for \(r\ge 1\),
because its first image is odd. Do not prove an `OE` frequency
theorem. Do not prove totality.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Finite-itinerary envelope \(T_w(n)^{2^k}\le n^{3^o}\) —
  **EXACT — LEAN VERIFIED**.
- Even-run scale barrier \(m\ge n_*^{2^r}\) —
  **EXACT — LEAN VERIFIED**.
- First image of a minimal start is odd —
  **EXACT — LEAN VERIFIED**.

Project relationship: **extended**. The itinerary envelope is specialized
to repeated `OE` and combined with minimality. Totality remains
unclaimed.

## Branch budget

```text
Mathematical target     r consecutive OE blocks require n^{4^r} <= x^{3^r}
Novelty hypothesis      Repeated OE is a finite scale budget
Falsifier               Envelope fail, or stay-ge-n run with x^{3^r} < n^{4^r}
Existing machinery      power_bound_word, MinimalNonTerm, even_run_scale_barrier
Maximum Phase-0 scope   OE/(OE)^r envelope; barrier; start-forbidden (OE)^r
Promotion criterion     Proved repeated-OE scale barrier
Stop criterion          Halt; log energy; frequency theorem; FloorPower rewrite; grammar engine
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- `oe_block_scale` / `oe_block_contracts` —
  **EXACT — LEAN VERIFIED**
- `repeated_oe_scale` —
  **EXACT — LEAN VERIFIED**
- `repeated_oe_scale_barrier` / `oe_requires_scale` —
  **EXACT — LEAN VERIFIED**
- `(OE)^r` cannot start at \(n_*\) —
  **EXACT — LEAN VERIFIED**
- realized consecutive `OE` runs obey the envelope; stay-\(\ge n\)
  runs obey the scale inequality —
  **COMPUTATIONALLY VERIFIED**
- longest stay-\(\ge n\) consecutive run on \(n\le 80\) is \(r=2\)
  at \(x=17537\) on the orbit of \(77\) —
  **OBSERVATION**
- `OE` frequency — not claimed
- global halt — not claimed
- `PowerHeight` / log energy — not added

## Experiments

- Probe: `research.juggler_sequence.repeated_oe`
- Records: [juggler_repeated_oe.md](../research/juggler_repeated_oe.md),
  [juggler_repeated_oe.json](../research/juggler_repeated_oe.json)
- Tests: `tests/research/juggler_sequence/test_repeated_oe.py`
- The Research Engine control layer is not modified.

## Conjectures

None opened.

## Counterexamples

None to the envelope or to the scale barrier on \(n\le 80\). A
consecutive `OE` run of length \(2\) can stay above the start
(\(77\): \(17537\xrightarrow{(OE)^2}243\)). That is allowed
numerically because \(77^{16}\le 17537^9\). It does not refute the
barrier and is not a frequency statement.

## Formalization

`formal/Problems/Engine/RepeatedOE.lean`, above `MinimalNonTerm`.
Added:

- `wordOE` / `repeatedOE`
- `oe_block_scale` / `oe_block_contracts`
- `repeated_oe_scale`
- `repeated_oe_scale_barrier` / `oe_requires_scale`
- `minimal_nonterm_not_repeated_oe`

`FloorPower` and `MinimalNonTerm` are not rewritten. No `sorry`. No
halt theorem. No `PowerHeight`. No infinite-path type.

## Results

Classification **REPEATED_OE_SCALE_GREEN**, with
**OE_RUN_FORBIDDEN_GREEN** at the start only.

A later \((\texttt{OE})^r\) segment on a minimal non-1 orbit requires
\(n_*^{4^r}\le x^{3^r}\). The start cannot carry any such segment.
Odd growth must finance every later `OE` block. That is a scale
budget, not a grammar of all parity itineraries.

## Open questions

Answered in [juggler_odd_run_financing.md](juggler_odd_run_financing.md):
a realized \(O^aE\) on a minimal non-1 orbit requires
\(n_*^{2^{a+1}}\le x^{3^a}\), and more generally
\(O^aE^b\) requires \(n_*^{2^{a+b}}\le x^{3^a}\). At the start the
first even residual cannot occur before `OOE`. Later odd runs may be
shorter if the entry is already large.

## Decision

**PROMOTE** the repeated-`OE` scale barrier. Do not claim that every
orbit contains many `OE` blocks. Do not claim a uniform bound on \(r\)
independent of \(x\). Do not claim termination.

Best next question: answered in
[juggler_odd_run_financing.md](juggler_odd_run_financing.md).

## Publication assessment

Status: `EXPLORATORY`. A conditional block-scale obstruction, not a
paper candidate and not a Juggler totality result.

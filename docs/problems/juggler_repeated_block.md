# Juggler repeated \(O^aE^b\) blocks

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1.

## Problem

Can a fixed block \(B=O^aE^b\) repeat indefinitely on a hypothetical
minimal non-terminating orbit without violating the scale budget?

## Exact statement

If a later orbit state \(x\) realizes \(B^r=(O^aE^b)^r\), the itinerary
envelope gives

\[
T^{r(a+b)}(x)^{2^{r(a+b)}}\le x^{3^{ar}}.
\]

Minimality keeps the exit \(\ge n\), so

\[
n^{2^{r(a+b)}}\le x^{3^{ar}}.
\]

For nonempty \(B\), \(3^a\neq 2^{a+b}\). The contracting regime
\(3^a<2^{a+b}\) forces \(T_B(x)<x\) for \(x\ge 2\), and such a block
cannot start at \(n_*\). Later contracting copies may stay \(\ge n_*\)
if the entry is already large. The expanding regime \(3^a>2^{a+b}\)
does not force contraction.

Do not claim that every orbit contains many copies of any block. Do
not prove totality.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Finite-itinerary envelope \(T_w(n)^{2^k}\le n^{3^o}\) —
  **EXACT — LEAN VERIFIED**.
- Repeated-`OE` scale \(n^{4^r}\le x^{3^r}\) —
  **EXACT — LEAN VERIFIED**.
- Odd-run financing \(n^{2^{a+b}}\le x^{3^a}\) —
  **EXACT — LEAN VERIFIED**.

Project relationship: **extended**. The two previous scale theorems
are the cases \((a,b,r)=(1,1,r)\) and \(r=1\). Totality remains
unclaimed.

## Branch budget

```text
Mathematical target     (O^a E^b)^r on MinimalNonTerm => n^{2^{r(a+b)}} <= x^{3^{a r}}
Novelty hypothesis      Contracting start is forbidden; expanding repetition may survive
Falsifier               Envelope fail, stay-ge-n scale fail, or start-contracting stay
Existing machinery      power_bound_word, power_bound_contracts, oddEvenBlock, MinimalNonTerm
Maximum Phase-0 scope   Repeated envelope+barrier; start contraction; expanding census
Promotion criterion     Proved repeated scale law and regime split, or useful negative
Stop criterion          Halt; frequency; log energy; periodic-word engine; assume contradiction
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- `repeated_block_power_bound` —
  **EXACT — LEAN VERIFIED**
- `repeated_odd_even_scale_barrier` —
  **EXACT — LEAN VERIFIED**
- \(3^a\neq 2^{a+b}\) for nonempty \(O^aE^b\) —
  **EXACT — LEAN VERIFIED**
- formally contracting \(B\) contracts the entry; cannot start at
  \(n_*\) —
  **EXACT — LEAN VERIFIED**
- later contracting copies may stay \(\ge n\) (`OE` from \(17537\)
  to \(243\ge 77\)) —
  **OBSERVATION**
- expanding \((OOE)^2\) from \(69\) stays at \(212>69\) —
  **OBSERVATION** / **REPEATED_EXPANSION_SURVIVES**
- closest expanding pair is \(O^2E\) (\(9>8\)); exact equality is
  impossible —
  **OBSERVATION**
- repetition as a global obstruction — not claimed
- block frequency — not claimed
- global halt — not claimed
- `PowerHeight` / log energy / lower envelope — not added

## Experiments

- Probe: `research.juggler_sequence.repeated_block`
- Records: [juggler_repeated_block.md](../research/juggler_repeated_block.md),
  [juggler_repeated_block.json](../research/juggler_repeated_block.json)
- Tests: `tests/research/juggler_sequence/test_repeated_block.py`
- The Research Engine control layer is not modified.

## Conjectures

None opened.

## Counterexamples

None to the envelope or to the repeated scale barrier on \(n\le 80\).
No formally contracting block stays at the start.

The stronger claims that fail:

- “a formally contracting block is always a descent below \(n_*\)” —
  false later (`17537\xrightarrow{(OE)^2}243\ge 77`).
- “repeated expansion contradicts the scale budget” — false
  (`69\xrightarrow{(OOE)^2}212`).

Those are **SCALE_FINANCING**-style negatives: keep the exact
inequality.

## Formalization

`formal/Problems/Engine/RepeatedBlock.lean`, above `OddRunFinancing`.
Added:

- `repeatedOddEven`
- `odd_even_exponents_ne` / `contracting_gap_repeat`
- `repeated_block_power_bound`
- `repeated_odd_even_scale_barrier`
- `contracting_odd_even_block_contracts` /
  `contracting_repeated_odd_even_contracts`
- `initial_contracting_block_forbidden` /
  `initial_contracting_repeated_forbidden`

`FloorPower` is not rewritten. No `sorry`. No halt theorem. No
`PowerHeight`. No infinite-path type. No lower-growth programme.

## Results

Classification **REPEATED_BLOCK_SCALE_GREEN**, with
**REPEATED_CONTRACTION_FORBIDDEN** at the start only and
**REPEATED_EXPANSION_SURVIVES**.

Repetition alone is not a global obstruction. Expanding copies can
finance every later even collapse more easily as they grow. Contracting
copies are forbidden at \(n_*\) and allowed later if already financed.

## Open questions

Does some *other* existing certificate (capture, residual progress,
first-even freeze) eventually meet a long expanding repetition, or
can an expanding block family avoid every current certificate
indefinitely? Do not treat this as a frequency theorem, and do not
open a periodic-word engine until that question is sharp.

## Decision

**PROMOTE** the repeated-block scale law and the contracting/expanding
split. Accept the negative: repetition of a fixed \(O^aE^b\) is not
by itself a contradiction with minimality. Do not claim a uniform
bound on \(r\). Do not claim termination.

Best next question: can a long expanding repetition avoid every
current certificate, or does some already-proved certificate
eventually apply?

## Publication assessment

Status: `EXPLORATORY`. A conditional repeated-block scale theorem plus
a useful negative, not a paper candidate and not a Juggler totality
result.

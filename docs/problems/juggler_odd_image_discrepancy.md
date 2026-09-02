# Juggler odd-image discrepancy

Status: **EXPLORATORY**

Follow-up of the parked image-parity census. It is **not** a Research
Engine experiment, not a frequency theorem, and not a claim that
every positive integer reaches 1.

## Problem

Can the odd-start sign sequence \(s(n)=(-1)^{\lfloor n^{3/2}\rfloor}\)
be given an explicit sublinear discrepancy bound on intervals, and
does that cancellation survive on sets produced by \(J\)?

## Exact statement

Write \(S_O(N)=\sum s(n)\) over odd \(n\le N\). Phase 0 asks for
an explicit \(F(N)=o(N)\) with \(|S_O(N)|\le F(N)\), obtained from
the cell multiplicities \(c_m\) or from the exact fractional-part
form of \(s\). After an interval bound exists, the same sum is
evaluated on \(J([1,N])\), \(J^{2}([1,N])\), and selected Atlas
words. Totality is unclaimed.

## Current literature

- Parent census [juggler_parity_discrepancy.md](juggler_parity_discrepancy.md)
  **PARK** / `IMAGE_PARITY_CENSUS`. \(D_O=-S_O/2\).
- `odd_preimage_unique` / `odd_preimage_iff` —
  **EXACT — LEAN VERIFIED**.
- `floorPower_odd_macro_direction` —
  **EXACT — LEAN VERIFIED**.
- Even-cell \(|D_E|\le\lfloor\sqrt N\rfloor+1\) —
  **EXACT — HUMAN PROOF**; not the target.
- 2-adic bridge, landing-θ, PE / residual / LD model —
  **CLOSE**. Do not reopen.
- Prasad–Prasad 2025 (`prasad-prasad-2025-juggler-like`) —
  motivation only.
- Van der Corput / Erdős–Turán —
  **KNOWN** analytic tools, applied here to `n^{3/2}/2` mod 1.

Project relationship: **extended** from the parked census.
Totality remains unclaimed.

## Branch budget

```text
Mathematical target     Prove |S_O(N)| <= F(N) with F=o(N) for
                        s(n)=(-1)^{floor(n^{3/2})} on odd n;
                        then test S_O on J([1,N]) and J^2([1,N]).
Novelty hypothesis      Cell pairing cancellation, or an explicit
                        fractional-part discrepancy rate
Falsifier               Pairing is linear variation only; no honest
                        F; images concentrate one sign
Existing machinery      odd_preimage_unique; parity_discrepancy D_O;
                        floor_power; follows_itinerary / image_after
Maximum Phase-0 scope   Exact S_O; c_m prefix; pairing/runs;
                        one analytic rate; image/word tests on
                        the existing grids; no CUDA; no Lean ANT
Promotion criterion     Explicit F=o(N) with a proof, and a
                        transfer statement on J-images
Stop criterion          Pairing useless and rate only KNOWN
                        method with no transfer; machinery gravity;
                        halt claim; promoting N^{1/3}
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required. The 2-adic / BT bridge is closed.

## Candidate operations / invariants

- \(S_O=-2D_O\) —
  **EXACT — HUMAN PROOF**
- \(c_m\in\{0,1\}\) —
  **EXACT — LEAN VERIFIED**
- Adjacent pairing bound —
  **REFUTED** as a sublinear estimate
- \(|S_O(N)|\ll N^{5/6}\) —
  **EXACT — HUMAN PROOF**
- Observed \(N^{1/3}\) —
  **OBSERVATION**, not promoted
- Interval bound on \(J([1,N])\) without transfer —
  not claimed
- `parity_frequency_theorem` —
  stays false
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.odd_image_discrepancy`
- Records: [juggler_odd_image_discrepancy.md](../research/juggler_odd_image_discrepancy.md),
  [juggler_odd_image_discrepancy.json](../research/juggler_odd_image_discrepancy.json)
- Dataset: `data/research/juggler/parity_discrepancy_next/`
- Tests: `tests/research/juggler_sequence/test_odd_image_discrepancy.py`

No GPU. No new Lean file.

## Conjectures

None opened. The \(N^{1/3}\) envelope is not entered as a
conjecture.

## Counterexamples

- Adjacent cell pairing as a sublinear variation bound: variation
  over `#odds` is `1.0`
  on `n<=1000000`.
- “`N^{1/3}` is proved”: descriptive slope
  `0.34595847` on `[1000, 1000000]`.

## Formalization

None added. The cell uniqueness lemma already exists. Analytic
number theory is not Lean-packaged. No `sorry`.

## Results

Classification **ODD_IMAGE_DISCREPANCY_GREEN**.

S_O(N) = -2 D_O(N) and the cell rewrite S_O = sum_m (-1)^m c_m with c_m in {0,1} are exact. Adjacent pairing has linear variation and is not a cancellation theorem. The fractional-part identity plus van der Corput / Erdős–Turán give the explicit interval bound |S_O(N)| << N^{5/6}. The observed N^{1/3} envelope is not promoted. One-step Juggler images stay small relative to |A_odd|; that is a census, not a transfer theorem.

On `n<=1000000`: `S_O=146`,
`max|S_O|=256` at `n=985351`.
`c_m<=1` on the prefix: `True`.

## Open questions

Sharpen \(N^{5/6}\) toward the census envelope, or prove a
transfer estimate for \(S_O(J([1,N]))\). Do not iterate by
numerics. Do not claim termination.

## Decision

**PARK**. S_O(N) = -2 D_O(N) and the cell rewrite S_O = sum_m (-1)^m c_m with c_m in {0,1} are exact. Adjacent pairing has linear variation and is not a cancellation theorem. The fractional-part identity plus van der Corput / Erdős–Turán give the explicit interval bound |S_O(N)| << N^{5/6}. The observed N^{1/3} envelope is not promoted. One-step Juggler images stay small relative to |A_odd|; that is a census, not a transfer theorem. Do not claim
termination. Do not flip `parity_frequency_theorem`.

Best next question: prove a transfer bound for \(S_O\) on
\(J([1,N])\), or replace \(N^{5/6}\) by an effective
\(N^{1/2+\varepsilon}\) estimate without a Weyl engine.

## Publication assessment

Status: `EXPLORATORY`. An exact cell rewrite plus a classical
discrepancy rate on one sequence, not a paper candidate and not a
Juggler totality result.

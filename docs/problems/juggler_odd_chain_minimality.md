# Juggler long odd-chain minimality

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a
cube-crossing reopen, not an integer-power hierarchy, not a
\(\mathrm{mod}\,2^k\) census, not generic predecessor enumeration,
not \(Z_5\), not a length-11 assembly, not a four-even cell, not
p-adic machinery, not Paper A, and not a claim that every positive
integer reaches 1.

The local cube-boundary program closed. The residual is a
`MinimalNonTerm` orbit that stays `AboveAnchor` through a run of
odd steps. This phase asks whether the *entire* odd chain encodes
a smaller bad witness or a good-set contradiction.

## Problem

Can an arbitrarily long odd chain exist on a minimal nonterminating
orbit without forcing a smaller bad state or a good-set closure
contradiction?

## Exact statement

Let \(x_0,\ldots,x_{r-1}\) be odd with \(x_{i+1}=T(x_i)\) and
\(x_0\ge n\). On `MinimalNonTerm` every \(x_i\) is at least \(n\),
and `floorPower_odd_gt` gives \(n\le x_0<x_1<\cdots\) for
\(x_0\ge 3\). Phase 0 asks whether the coupled system

\[
x_i^3=x_{i+1}^2+\delta_i,\qquad 0\le\delta_i<2x_{i+1}+1
\]

produces a state \(m<x_0\) whose orbit shadows or rejoins the
chain, or a controlled inverse interval inside \([1,n-1]\), beyond
`odd_preimage_unique` and `EnvelopeState` applied one step at a time.

The named orbits are \(37,69,89,365,501,1517,6187\). Long initial
runs \(37,241,329\) and the \(L\)-landing \(33391\to 67709\) are
length controls. This is not a halt theorem and not a universal
odd-run bound.

## Current literature

- Odd growth \(T(x)>x\) for odd \(x\ge 3\) —
  **EXACT — LEAN VERIFIED** (`floorPower_odd_gt`)
- Unique odd preimage —
  **EXACT — LEAN VERIFIED** (`odd_preimage_unique`)
- Isolated odd prefix envelope \(T^a(x)^{2^a}\le x^{3^a}\) —
  **EXACT — LEAN VERIFIED** (`odd_run_power_bound`)
- Iterated odd-landing sets \(\mathcal P_r\) —
  **CLOSE** (`juggler_odd_landing_sets.md`)
- \(L\)-envelope odd-run cap —
  **REFUTED** (`J-cyclemin-l-odd-run-envelope-caps`)
- Short `Pred_{E,OE,OOE,OOOE}` closure —
  **REFUTED** (`J-minimal-anchor-closure`)
- Cube-boundary crossing arithmetic —
  **CLOSE** (`juggler_cube_crossing.md`)
- Source-relative odd reset —
  **REFUTED** (`J-source-relative-odd-reset`)
- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**.
  Totality is not claimed

Project relationship: **extended**, then **reparameterized**. The
designated chain-level question after the crossing CLOSE.

## Branch budget

```text
Mathematical target     long odd chain => smaller bad state or
                        good-set contradiction
Novelty hypothesis      the coupled near-power system compresses
                        or deepens inverse closure with r
Falsifier A             unrestricted defect structure
Falsifier B             no whole-chain relation beyond
                        EnvelopeState per step
Falsifier C             compression yields only larger states
Falsifier D             good-set closure depth does not grow
                        with r
Falsifier E             a broad family of long finite chains
Existing machinery      floorPower_odd_gt; odd_preimage_unique;
                        odd_run_power_bound; EnvelopeState;
                        pred_odd; leftover / 37 / L laboratories
Maximum Phase-0 scope   named odd runs; long starts 37/241/329;
                        L-lab 33391; no Lean; no inverse census
Promotion criterion     a chain-level Diophantine obstruction,
                        a smaller bad witness, or a bound on
                        odd-chain length under MinimalNonTerm
Stop criterion          step-wise envelope rewrite; generic
                        inverse; residue census; universal
                        odd-run bound; cube-crossing reopen
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- \(x_{i+1}>x_i\) — **EXACT — LEAN VERIFIED**
  (`floorPower_odd_gt`)
- unique odd preimage of \(x_{i+1}\) is \(x_i\) —
  **EXACT — LEAN VERIFIED** (`odd_preimage_unique`)
- \(\delta_i\equiv x_i-1\pmod 8\) —
  **REPARAMETERIZATION** of generic odd-odd
- constant shift \(x_i\mapsto x_i-2\) couples the chain —
  **REFUTED**
- odd predecessor of a later run start lies below \(n\) —
  **REFUTED** on the named set (empty or off-orbit, never
  \(<n\))
- \(D_r=\sum\delta_i/x_i^3\) is a new chain budget —
  **REPARAMETERIZATION** of the local floor identities
- `OddChain` Lean primitive — not introduced
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.odd_chain_minimality`
- Records: [juggler_odd_chain_minimality.md](../research/juggler_odd_chain_minimality.md),
  [juggler_odd_chain_minimality.json](../research/juggler_odd_chain_minimality.json)
- Tests: `tests/research/juggler_sequence/test_odd_chain_minimality.py`

No CLI. No Lean. No generic inverse search. No odd-run length
census.

## Conjectures

None opened.

## Counterexamples

“A long odd chain compresses to \(m<x_0\) that rejoins the
chain” is false. By `odd_preimage_unique` the only odd preimage of
\(x_{i+1}\) is \(x_i\). Walking backward recovers the chain and
then an empty odd cell at the run start.

“The first leftover overshoot has a new smaller odd predecessor”
is false. The first step of each leftover run starts at \(n\) and
its unique odd preimage is \(n\). Later leftover run starts have
empty odd cells.

“A constant shift couples the chain” is false on every named
run.

“\(3375\to 9317\to 2233\) is an odd chain” is false. Those are
cube-crossing returns, not consecutive odd iterates. The odd
runs on \(37\) are \(37\) (length \(4\)), \(9317\) (length \(3\)),
and \(2233\) (length \(2\)).

Long finite chains exist with the same structure: \(329\) has
an initial odd run of length \(8\); \(33391\) follows \(L\) to
\(67709\) and then an odd run of length \(5\).

## Formalization

None added. Existing `Dynamics`, `Cells`, and `Scale` already
contain monotonicity, uniqueness, and the odd-run envelope.
No `OddChain.lean`. No `OddChainCompression.lean`. Paper A is
unchanged. No `sorry`.

## Results

Classification **ODD_CHAIN_MINIMALITY_CLOSED**.

Every named AboveAnchor odd run is strictly increasing, has
generic \(\delta\equiv x-1\pmod 8\) on odd-odd steps, and has
unique step-wise odd inverses equal to the chain itself. The
odd predecessor of a run start is empty on every named run,
including later leftover landings. A shift by \(2\) never
preserves the chain. The first leftover step is the known
unique-preimage identity \(T(n)=x_1\).

Whole-chain composition of the floor identities is
`odd_run_power_bound` / `EnvelopeState`. Cumulative defect
\(D_r\) is the same local identities under a sum. Good-set
closure depth does not grow with run length: it is \(0\) at
the start of a later run and \(1\) at the first leftover
step.

This is Falsifier A, B, C, D, and E. Not a finite odd-run
theorem.

## Open questions

None from whole-chain Diophantine compression. Do not introduce
`OddChain`. Do not prove a universal maximum odd-run length.
Do not reopen cube-crossing, short `Pred_*`, or \(\mathcal P_r\).
The leftover hole is still an odd cube escape whose even lift
is known and whose odd lift is a generic high odd step.

## Decision

**CLOSE**. An arbitrarily long odd chain, as a finite object,
does not manufacture a smaller bad state. Its inverse is
itself; its growth and envelope are already Lean; its defects
are generic odd-odd. Minimality alone does not contradict the
chain, and the chain does not contradict minimality. A branch
of that kind is a close.

Best next question: none from odd-chain compression. The
residual is not an odd-chain Diophantine problem.

## Publication assessment

Status: `EXPLORATORY`.

A negative whole-chain fragment. Not a paper candidate and not
a Juggler totality result.

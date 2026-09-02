# Juggler first-return excursion frontier

Status: **EXPLORATORY**

Standalone arithmetic layer on complete first-return-below trajectories.
It is **not** a Research Engine control-layer experiment, not a
reopening of PE-factor, residual-future, sum-rho, realization-set,
landing-image, or finite-itinerary \(N_w\)-boundary branches, and not a
claim that every positive integer reaches 1.

## Problem

Does the conjunction “every proper prefix stays at or above \(n\), and
the complete word returns strictly below \(n\)” force a structural
relation among the first-return itinerary, peak, defects, and return margin
that is not already in the finite-itinerary envelope?

## Exact statement

For \(n>1\), when the minimum exists,

\[
\tau_<(n)=\min\{t\ge 1:T^t(n)<n\}.
\]

The first-return word is the itinerary of length \(\tau_<\). Phase 0
asks whether the observed returns on \(2\le n\le 4000\) obey a
non-tautological law of type H1–H5. A horizon miss is not a bound on
\(\tau_<\). This is not a termination theorem.

## Current literature

- \(T(n)\ge n\) for odd \(n\) —
  **EXACT — LEAN VERIFIED** (`floorPower_odd_ge`).
- \(3^o<2^k\Rightarrow T_w(n)<n\) for \(n\ge 2\) —
  **EXACT — LEAN VERIFIED** (`power_bound_contracts`).
- First-return census \(2\le n\le 2000\): every completed return word
  has \(2^k>3^o\) —
  **COMPUTATIONALLY VERIFIED**, parked as
  `EXCURSION_ENVELOPE_GREEN` in [juggler_excursions.md](juggler_excursions.md).
- PE / residual-future / sum-rho / realization-set / landing-image /
  \(N_w\)-boundary — **CLOSE**. Do not reopen.

Project relationship: **extended**. Totality remains unclaimed.

## Branch budget

```text
Mathematical target     Does first-return maximality force a new
                        relation among itinerary, peak, defects, margin?
Novelty hypothesis      H1–H5: margin/peak/profile/final-step/class
Falsifier               every useful statement is T<n, 2^k>3^o,
                        or floorPower_odd_ge
Existing machinery      _walk_returns, floorPower_odd_ge,
                        power_bound_contracts
Maximum Phase-0 scope   n=2..4000 exact CPU returns; extremal
                        profiles only; no GPU; no H6 induction
Promotion criterion     a law that uses prefix>=n AND final<n
                        and is not an existing lemma
Stop criterion          EXCURSION_COMPLEX; closed-branch reopen;
                        halt claim; another scalar energy
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- \(M\ge F(k,o)\) stronger than \(M\ge 1\) —
  **REFUTED** at \(n=3\), word `OOOEE`, \(M=1\)
- Peak bound stronger than the envelope —
  **REFUTED**; \(n=2183\) has a \(19694\)-bit peak
- New \(G_j\) law —
  **REPARAMETERIZATION** of the parked first formally
  contracting prefix
- Final letter \(E\) and \(n\le y<n^2\) —
  **REPARAMETERIZATION** of `floorPower_odd_ge` plus `isqrt`
- Pareto extremals form one class —
  **REFUTED**; ten undominated records; min-\(M\), min-\(M/n\),
  max-\(\tau\), and max-peak are four different words
- Same first-return word determines \(M\) —
  **REFUTED**; `OOEE` has \(M\) from \(3\) to \(3878\)
- Same run signature determines \(M\) —
  **REFUTED**; signature \((4,3,2)\) has \(M\) from \(21\) to \(3615\)

## Experiments

- Probe: `research.juggler_sequence.first_return_excursions`
- Diagnostic: \(2\le n\le 4000\) (3999 starts, all returned)
- Bit-cap promotions: \(n=2183,3431\) at \(25000\) bits
- Reuses: `research.juggler_sequence.excursions._walk_returns`
- Records: [juggler_first_return_excursions.md](../research/juggler_first_return_excursions.md)
- Tests: `tests/research/juggler_sequence/test_first_return_excursions.py`

No GPU. No H6. No new census.

## Conjectures

None opened.

## Counterexamples

- H1: `OOOEE` at \(3\) has \(M=1<k,o,|G|\).
- H2: even starts have peak \(n\); \(n=2183\) has peak \(19694\) bits.
- H5: min \(M\) is \(E\) at \(2\); min \(M/n\) is a length-\(46\) word
  at \(425\); max \(\tau=77\) at \(3889\); max peak at \(2183\).
- Same word: `OOEE` from \(255\) odd starts, \(M\in[3,3878]\).
- Same \((k,o)=(15,9)\): \(M\) from \(29\) to \(3691\).
- Same run signature \((4,3,2)\): \(M\) from \(21\) to \(3615\).
- Absolute min-\(M\) at \(n=2\) is not on the \((M/n,\mathrm{peak},\tau)\) Pareto front.

## Formalization

None added. `floorPower_odd_ge` and `power_bound_contracts` already
exist. No `sorry`. H6 was not attempted.

## Results

Phase 0 is recorded in
[juggler_first_return_excursions.md](../research/juggler_first_return_excursions.md).
Classification **EXCURSION_COMPLEX**.

All \(3999\) starts in \(2..4000\) returned (two after a bit-cap
raise). Every return is maximal. Every return word ends with \(E\).
Every proper prefix is formally noncontracting and the complete word
is formally contracting. Those facts are already Lean or the parked
envelope census. H1–H3 and H5 fail. Margin remains state-dependent
even for a fixed first-return itinerary, a fixed \((k,o)\), or a fixed run
signature. The exact Pareto front on \(\min M/n\), \(\max\) peak bits,
\(\max\tau\) has ten records and no common word class.

## Open questions

None from this branch. Do not infer that \(\tau_<\) is finite for
all \(n\).

## Decision

**CLOSE**. First-return maximality does not add an exact relation
beyond \(T^{\tau}(n)<n\), `power_bound_contracts`, and
`floorPower_odd_ge`. Do not invent another scalar. Do not attempt
H6. Do not claim termination.

Best next question: none from this branch.

## Publication assessment

Status: `EXPLORATORY`. Not a paper candidate and not a Juggler
totality result.

# Juggler first positive-drift crossing and endpoint arithmetic

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1.

## Problem

If an actual Juggler orbit postpones the first positive-drift crossing
for a long time, what arithmetic structure is forced on the endpoint
\(x_k=T^k(n)\)?

## Exact statement

For the actual orbit of \(n\ge 2\) write \(o_k\) for the number of
odd states among \(n,T(n),\ldots,T^{k-1}(n)\) and

\[
G_k=2^k-3^{o_k}.
\]

When the minimum exists,

\[
\tau_+(n)=\min\{k\ge 1:G_k>0\}.
\]

A prefix of length \(k\) is prefix-NC when \(G_j\le 0\) for all
\(j\le k\). Phase 0 asks whether the endpoint \(x_k=T^k(n)\) of a
realized prefix-NC prefix belongs to a strictly smaller arithmetic
class as \(k\) grows, or whether the first crossing
\(G_{\tau-1}\le 0\to G_\tau>0\) has a structural description that is
not the \(G\)-recurrence itself.

Do not claim \(\tau_+(n)<\infty\). Do not assume an asymptotic
frequency bound. Finite horizons are not a bound \(L\).

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Finite-itinerary envelope, equality rigidity, first-defect, and
  compensated contraction — **EXACT — LEAN VERIFIED**.
- \(G_k>0\Longrightarrow T^k(n)<n\) — **EXACT — LEAN VERIFIED**
  (`power_bound_contracts`).
- Prefix-NC language — **OBSERVATION**, parked.
- Prefix-NC arithmetic admissibility — closed as
  `PREFIX_NC_ARITHMETIC_COMPLEX`.
- Escape-state margin — closed as `ESCAPE_STATE_COMPLEX`.
- Corridor — closed as `CORRIDOR_REPACKAGING`.
- Odd-odd residual scalars — closed as `ODD_ODD_RESIDUAL_COMPLEX`.
- Cycle Diophantine peak identities — closed as
  `DIOPHANTIC_REPACKAGING`.
- Odd-fourth-power — parked.

Project relationship: **extended**. The leftover after the closed
word-level and corridor branches is the actual parity count of an
orbit and the arithmetic of its endpoint. Totality remains unclaimed.

## Branch budget

```text
Mathematical target     If an actual orbit stays prefix-NC through k,
                        what new arithmetic is forced on x_k?
Novelty hypothesis      long NC survival forces an endpoint
                        filtration not implied by G or T>=n
Falsifier               every endpoint predicate is G-recurrence or T>=n
Existing machinery      power_bound_*, exponent_gap, first-defect,
                        square_depth, floor_power
Maximum Phase-0 scope   one probe; actual orbits until first G>0; no Lean
Promotion criterion     a new endpoint restriction or filtration
Stop criterion          DRIFT_ENDPOINT_COMPLEX; machinery gravity;
                        ResidualStep / prefix-NC / corridor reopen
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- First crossing is an even letter, with
  \(2^{\tau-1}\le 3^o<2^\tau\) — **EXACT — HUMAN PROOF** as a
  one-line \(G\)-recurrence; **COMPUTATIONALLY VERIFIED** on the
  window; a **REPARAMETERIZATION** of \(G\), not a Juggler endpoint
  law. Odd append: \(G'=2G-3^o\le -3^o<0\) whenever \(G\le 0\).
- Even starts have \(\tau_+=1\) — **EXACT — HUMAN PROOF**;
  **COMPUTATIONALLY VERIFIED**
- \(G_k=0\) never occurs — **KNOWN** (\(2^a=3^b\) has no positive
  solutions)
- Mixed prefix-NC endpoint parity, square status, \(v_2\), \(v_3\),
  residue, or \(\gcd(x_k,n)>1\) — **REFUTED** as uniform laws
- Mixed prefix-NC \(\Rightarrow T^k(n)\ge n\) on the window —
  **OBSERVATION**, the excursion identity \(\tau_+=\tau_<\) rewritten;
  not a new progress measure
- Global halt or \(\tau_+<\infty\) — not claimed

## Experiments

- Probe: `research.juggler_sequence.drift_crossing`
- Records: [juggler_drift_crossing.md](../research/juggler_drift_crossing.md),
  [juggler_drift_crossing.json](../research/juggler_drift_crossing.json)
- Dataset: `data/research/juggler/drift_crossing/`
- Tests: `tests/research/juggler_sequence/test_drift_crossing.py`
- The Research Engine control layer is not modified.
- `ResidualStep` is not extended. Prefix-NC word admissibility,
  the corridor, escape-state, and odd-fourth-power are not reopened.
- No Lean file.

## Conjectures

None opened.

## Counterexamples

- “Long prefix-NC survival forces \(x_k\) even / odd / square /
  \(v_2\ge 1\) / \(v_3\ge 1\) / \(\gcd>1\) / a fixed residue”:
  mixed-NC hits on \(n=2..2000\) are split on every such predicate.
- “\(\gcd(x_k,n)\) grows with \(k\)”: 2304 mixed-NC prefixes have
  \(\gcd=1\), including the longest survivor \(n=193\) at \(k=69\).
- “Crossing predecessor is a square”: 31 yes, 1968 no.
- “A start reaches 1 while still prefix-NC”: none in the window.
- “\(2^k=3^o\) occurs”: none.

## Formalization

None added. Envelope, equality, and compensated contraction already
live in `formal/Problems/Engine/FloorPower.lean`. No
`DriftCrossing.lean`. The even-letter crossing identity is a
\(G\)-recurrence and is not packaged. No `sorry`. No ledger row.

## Results

Classification **DRIFT_ENDPOINT_COMPLEX**, with secondary
**DRIFT_FIRST_CROSSING_GREEN** recorded only as the elementary
crossing description.

On \(2\le n\le 2000\), all 1999 starts cross before the horizon.
Identity failures 0. Absorbed-at-1 still NC: 0. \(G=0\) hits: 0.
Even starts all have \(\tau_+=1\) (1000 of them). Every realized
crossing is an even letter whose predecessor is even and lies in
the window \(2^{\tau-1}\le 3^o<2^\tau\), and \(T^\tau(n)<n\).

4812 prefix-NC prefixes; 2797 mixed. Mixed endpoints: even 1428,
odd 1369; square 8; \(\gcd>1\) 493; \(\gcd=1\) 2304. The only
universal mixed-NC predicate is \(T^k(n)\ge n\), already the
non-contraction side of the escape-state identity and the window
form of \(\tau_+=\tau_<\). Closest NC gap is \(G=-1\)
(\(3-2\) and \(9-8\)). Longest crossing is \(n=193\),
\(\tau_+=70\), last NC state \(6498\), \(\gcd=1\), not a square.
Peak bits 900. No endpoint filtration survives.

No Lean file. No halt theorem.

## Open questions

The missing theorem is unchanged: does every \(n\ge 2\) realize a
finite prefix with \(3^o<2^k\)? If yes, `FiniteProgress` follows
from `power_bound_contracts`. An infinite prefix-NC itinerary would
be a non-terminator. Do not reopen endpoint-metric censuses,
prefix-NC word admissibility, the corridor, ResidualStep,
escape-state margins, or odd-fourth-power.

## Decision

**CLOSE** the drift-crossing branch as `DRIFT_ENDPOINT_COMPLEX`.
The only exact crossing law is the \(G\)-recurrence: a first
positive \(G\) must be an even letter. Mixed prefix-NC endpoints
do not collapse to a smaller arithmetic class. That is not an
obstruction to arbitrarily long prefix-NC orbits. Do not add Lean.
Do not claim \(\tau_+<\infty\). Do not claim termination.

Best next question: a genuine existence argument that every
\(n\ge 2\) eventually takes an even step in the window
\(2^{k-1}\le 3^{o_{k-1}}<2^k\), not another endpoint laboratory.

## Publication assessment

Status: `EXPLORATORY`. A negative endpoint-filtration result, not a
paper candidate and not a Juggler totality result.

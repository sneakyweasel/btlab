# Juggler infinite AboveAnchor parity balance

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a new cell,
not a CycleMin leftover census, not an invented word automaton, not
Paper A, and not a claim that every positive integer reaches 1.

Local attacks on single-step cells, two-sided corridors, scalar
descent, episode rank, odd-chain compression, cube-boundary defects,
and odd/even reset identities are already `CLOSE` or `PARK`. This
phase asks whether the *already-proved shared* `AboveAnchor`
restrictions force an asymptotic opposite to the exact envelope
budget.

## Problem

Does an infinite `AboveAnchor` trajectory require so many even
letters that the exact word envelope becomes contracting?

## Exact statement

For a realized finite prefix \(w\) write \(\ell=|w|\) and
\(o=\operatorname{oddCount}(w)\). The existing envelope is

\[
T_w(n)^{2^\ell}\le n^{3^o}.
\]

`AboveAnchor` on that prefix is \(n\le T_w(n)\). For \(n\ge 2\)
this forces the integer inequality

\[
2^\ell\le 3^o.
\]

That lower constraint is already Lean as
`aboveAnchor_not_envelope_drop`. Phase 0 asks whether the shared
`AboveAnchor` language — not `CycleMin` closure, not a new
automaton — also forces the opposite inequality on every
sufficiently long surviving prefix:

\[
2^\ell>3^o.
\]

Equivalently: is there \(\rho<\log 2/\log 3\) and a constant \(C\)
such that every long shared-admissible word satisfies
\(o\le\rho\ell+C\)? Do not treat the decimal \(0.6309\) as a
theorem. Do not infer a contradiction from numerical parity
statistics.

This is not a halt theorem.

## Current literature

- Finite-itinerary envelope \(T_w(n)^{2^\ell}\le n^{3^o}\) —
  **EXACT — LEAN VERIFIED** (`J-power-envelope-contraction`)
- `AboveAnchor` plus \(3^o<2^\ell\) forbids the prefix —
  **EXACT — LEAN VERIFIED** (`aboveAnchor_not_envelope_drop`)
- Isolated prefix \(O^a E(\mathtt{OE})^r\) survival
  \(2^{a+2r+1}\le 3^{a+r}\) —
  **EXACT — LEAN VERIFIED** (`J-cyclemin-first-oo-r-bound`)
- Initial `OE` cannot stay `AboveAnchor` —
  **EXACT — LEAN VERIFIED** (`aboveAnchor_not_odd_even`)
- Prefix growth / retention as an independent budget —
  **REPARAMETERIZATION** (`J-prefix-retention-budget`)
- Later odd-run pairs form a grammar —
  **REFUTED** (`J-odd-run-itinerary-grammar`)
- Expanding residual block \(a\ge 2\), \(b<a\) —
  **EXACT — LEAN VERIFIED** (`J-expansion-block-grammar`)
- Consecutive PE run length bounded —
  **REFUTED** (certified length \(3\) at \(365\); computed \(L=7\))
- Cycle leftover cells / even-count \(\le 3\) —
  cycle-only; not in the shared language
- Every start reaches 1 — not claimed

Project relationship: **extended**, then **refuted** as an
independent density-gap attack. The designated global question
after the local-program close.

## Branch budget

```text
Mathematical target     Do already-proved shared AboveAnchor
                        restrictions force 2^{|w|} > 3^{oddCount(w)}
                        on long surviving prefixes?
Novelty hypothesis      isolated-OE / first-OO / even-reset lemmas
                        compose into o <= ρ|w|+C with ρ < log2/log3
Falsifier A             shared language admits 2^{|w|} <= 3^{oddCount(w)}
                        at density >= 2/3 (O*, O^{N-1}E, (OOE)*)
Falsifier C             a nonnegative shared cycle mean (OOE: 9>8)
Existing machinery      aboveAnchor_not_envelope_drop;
                        isolatedOddSurvival_bound;
                        odd-run itinerary REFUTED; PE grammar;
                        leftovers 365, 501, 1517, 6187
Maximum Phase-0 scope   integer word optimizer on shared constraints;
                        leftover prefix table; no Lean; no automaton
Promotion criterion     a shared finite-prefix opposite inequality
Stop criterion          ρ_max >= log2/log3; nonnegative cycle mean;
                        local constraints do not compose; invented
                        automaton; CycleMin silently included
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Survival \(2^{|w|}\le 3^{\operatorname{oddCount}(w)}\) on every
  `AboveAnchor` prefix — **KNOWN**
  (`aboveAnchor_not_envelope_drop`)
- Isolated \(2^{a+2r+1}\le 3^{a+r}\) — **REPARAMETERIZATION** of
  the same prefix envelope on \(O^a E(\mathtt{OE})^r\)
- Initial `OE` — **REPARAMETERIZATION** of the prefix envelope
  (\(4>3\))
- Shared \(\rho_{\max}\) — **COMPUTATIONALLY VERIFIED** as \(1\)
  via \(O^*\) through length \(18\); mixed \(\rho_{\max}=(N-1)/N\)
  via \(O^{N-1}E\) for \(N\ge 3\)
- Concatenable `OOE` cycle \(9>8\) —
  **EXACT — LEAN VERIFIED** as a PE block, and
  **COMPUTATIONALLY VERIFIED** as a positive envelope weight
- Independent structural upper bound \(o\le\rho\ell+C\) with
  \(\rho<\log 2/\log 3\) — **REFUTED**
  (`J-shared-parity-balance-gap`)
- Universal odd density — not claimed
- Global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.parity_balance`
- Records: [juggler_parity_balance.md](../research/juggler_parity_balance.md),
  [juggler_parity_balance.json](../research/juggler_parity_balance.json)
- Tests: `tests/research/juggler_sequence/test_parity_balance.py`

No CLI. No Lean. No weighted automaton. Cycle-only words are
audited and excluded from \(\rho_{\max}\).

## Conjectures

None opened.

## Counterexamples

The preferred density-gap hypothesis is false by the shared
language, not by a special start.

- “shared exclusions force \(2^{|w|}>3^{\operatorname{oddCount}(w)}\)”
  — false. Every prefix-surviving word is shared-admissible.
  \(O^N\) has \(2^N\le 3^N\). For \(N\ge 3\), \(O^{N-1}E\) has
  \(2^N\le 3^{N-1}\). The block `OOE` has \(8\le 9\).
- “isolated-`OE` is an independent upper bound on odd density” —
  false. Its exponents are exactly the prefix envelope on that
  shape. The bound *forbids low-odd isolated prefixes*, so it
  raises density rather than capping it.
- “the shared transition graph has negative cycle mean” — false.
  `O` has \(3>2\). `OOE` has \(9>8\).
- “only a `CycleMin` theorem supplies the density restriction” —
  the shared language already has no useful upper bound. Cycle
  leftover cells were not used.

## Formalization

None added. Existing `Envelope`, `FirstInternalOO`, and
`MinimumRelative` already contain the identities. No
`ParityBalance.lean`. No `sorry`. Paper A is unchanged.

## Results

Classification **PARITY_BALANCE_CLOSED**.

Every finite `AboveAnchor` prefix satisfies \(2^{|w|}\le
3^{\operatorname{oddCount}(w)}\). That is the first global
parity-balance constraint, and it is already
`aboveAnchor_not_envelope_drop`.

The shared forbidden language, after removing CycleMin-only and
termination-only wrappers, is the same constraint: an itinerary is
shared-admissible iff every prefix is noncontracting. Isolated
`O^a E(\mathtt{OE})^r` and initial `OE` are instances, not extra
letter-transition rules. They do not define a finite automaton
beyond the envelope itself.

On that language the optimizer through length \(18\) returns

\[
\rho_{\max}=1
\]

by \(O^*\), and mixed \(\rho_{\max}=(N-1)/N\) by \(O^{N-1}E\)
for \(N\ge 3\). The concatenable block `OOE` has odd density
\(2/3>\log 2/\log 3\) and exact weight \(9/8>1\). Leftover
controls \(365,501,1517,6187\) stay on the surviving side of
\(2^k\le 3^O\) until a formally contracting extra even letter.

This is Falsifier A and Falsifier C. Existing local obstructions
do not force too many even steps. Parity balance cannot close
termination from the current shared library.

## Open questions

None from shared parity balance. Do not build a weighted
transition graph. Do not reopen isolated-`OE` as a global
density theorem. Do not include CycleMin leftover cells in the
survival language. The leftover residual is still the integer
landing of an expanding block.

## Decision

**CLOSE**. The survival inequality is `KNOWN`. Isolated-`OE` and
initial `OE` are `REPARAMETERIZATION`s of that inequality on
named shapes. The hoped-for opposite inequality is `REFUTED`:
the shared language contains \(O^*\), \(O^{N-1}E\), and
\((\mathtt{OOE})^*\). A branch of that kind is a close.

Best next question: none from existing shared exclusions. The
highest-density surviving language is the already-named
noncontracting envelope language, not a new residual.

## Publication assessment

Status: `EXPLORATORY`.

A negative global-density fragment. Not a paper candidate and
not a Juggler totality result.

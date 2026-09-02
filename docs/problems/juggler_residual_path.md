# Juggler residual-path regimes

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1.

## Problem

Can a hypothetical minimal non-terminating residual path be split into
a bounded regime, which reduces to a cycle candidate, and an unbounded
regime, which still only carries the existing per-step scale budget?

## Exact statement

A residual step is the existing finite relation `ResidualStep`. This
phase does not add an infinite-path type.

If `floorPower^[i] n = floorPower^[j] n` and `i ≤ j`, then

\[
T^{j-i}(T^i(n))=T^i(n).
\]

A finite residual prefix valued in \([L,M]\) and longer than \(M-L+1\)
cannot be nodup. That is the finite form of “bounded ⇒ repeat”.

If a realized itinerary returns to `x ≥ 2`, the envelope gives
\(2^r\le 3^o\). Equality is impossible for \(r\ge 1\), because \(2^r\)
is even and \(3^o\) is odd. Contracting words cannot return.
Therefore every nonempty cycle itinerary satisfies

\[
2^r<3^o.
\]

A residual return `O^a E^b` with \(b\ge 1\) is such a cycle, so
\(2^{a+b}<3^a\) and therefore \(a\ge 2\). Residual period-1 with
\(a\le 1\) is impossible.

On `MinimalNonTerm n`, every residual-chain state stays \(\ge n\).

Do not prove that cycles are impossible. Do not prove that the
unbounded branch is impossible. Do not prove totality.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed. No nontrivial cycle is recorded there.
- Finite-itinerary envelope \(T_w(x)^{2^k}\le x^{3^o}\) —
  **EXACT — LEAN VERIFIED**.
- Contracting words give `Descent` —
  **EXACT — LEAN VERIFIED**.
- Residual-step certificate propagation —
  **EXACT — LEAN VERIFIED**.

Project relationship: **extended**. The bounded residual regime is
reduced to a cycle with a strict exponent gap. Totality remains
unclaimed.

## Branch budget

```text
Mathematical target     bounded residual prefix ⇒ cycle; cycle envelope 2^r < 3^o
Novelty hypothesis      residual return needs a ≥ 2; equality 2^r = 3^o is impossible
Falsifier               a residual return with a ≤ 1; or a contracting cycle itinerary
Existing machinery      ResidualStep, power_bound_word, power_bound_contracts
Maximum Phase-0 scope   orbit repeat; cycle envelope; residual-return a≥2; small cycle scan
Promotion criterion     exact bounded⇒cycle reduction, or a meaningful excluded cycle class
Stop criterion          halt; cycle engine; infinite-path type; claim all cycles impossible
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- orbit repeat is a finite cycle —
  **EXACT — LEAN VERIFIED**
- bounded prefix longer than the window is not nodup —
  **EXACT — LEAN VERIFIED**
- cycle envelope \(2^r\le 3^o\), and \(2^r\neq 3^o\) for \(r\ge 1\) —
  **EXACT — LEAN VERIFIED**
- contracting itineraries cannot close a cycle —
  **EXACT — LEAN VERIFIED**
- residual return needs \(a\ge 2\) and \(2^{a+b}<3^a\) —
  **EXACT — LEAN VERIFIED**
- no fixed point except \(1\), and no return-to-self before \(1\), in
  \(2\le n\le 400\) —
  **OBSERVATION**
- no residual period-1 among odd-odd starts in \(2\le n\le 200\) —
  **OBSERVATION**
- all cycles are impossible — not claimed
- unbounded residual paths are impossible — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.residual_path`
- Records: [juggler_residual_path.md](../research/juggler_residual_path.md),
  [juggler_residual_path.json](../research/juggler_residual_path.json)
- Tests: `tests/research/juggler_sequence/test_residual_path.py`
- The Research Engine control layer is not modified.

## Conjectures

None opened.

## Counterexamples

None to the cycle envelope or to `a≥2` for residual returns. The
stronger claims that fail:

- “the residual relation is a new dynamical obstruction by itself” —
  unbounded constraints remain the existing per-step financing
  \(n^{2^{a+b}}\le x^{3^a}\).
- “every stay residual is a cycle candidate” — ordinary hard paths
  overshoot then descend; none return in the scanned window.
- “two residual steps always return below \(n\)” — already refuted
  by \(37\) and \(77\).

## Formalization

`formal/Problems/Engine/ResidualPath.lean`, above `ResidualChain` and
`RepeatedBlock`. Added:

- `ResidualDescent` / `ResidualReturn` / `ResidualOvershoot`
- `two_pow_ne_three_pow` / `cycle_envelope` / `cycle_strict_envelope`
- `cycle_not_contracting` / `trajectory_repeat_cycle`
- `residual_return_cycle` / `residual_return_envelope` /
  `residual_return_a_ge_two`
- `minimal_residual_chain_ge` / `bounded_prefix_not_nodup`

`FloorPower`, `Progress`, and `MinimalNonTerm` are not rewritten. No
`sorry`. No halt theorem. No `no_juggler_cycle`. No `CycleSearch`.
No infinite-path type. No `PowerHeight`.

## Results

Classification **BOUNDED_RESIDUAL_CYCLE_GREEN**, with secondary
**CYCLE_OBSTRUCTION_GREEN** for contracting itineraries, exponent equality,
and residual returns with \(a\le 1\).

A bounded residual prefix reduces to a cycle candidate. Expanding
cycles with \(a\ge 2\) are not excluded. The unbounded branch is
untouched beyond the existing scale budget.

## Open questions

Answered in [juggler_cycle_word.md](juggler_cycle_word.md): cycle
return is not envelope equality. Lower growth gives
\(n^{3^o-2^k}\le D_w\). Contracting words, `O`, `OO`, and `EOO` are
excluded.

## Decision

**PROMOTE** the bounded-path reduction and the strict cycle envelope.
Do not claim that cycles are impossible. Do not close the unbounded
branch. Do not claim termination.

Best next question: answered in
[juggler_cycle_word.md](juggler_cycle_word.md).

## Publication assessment

Status: `EXPLORATORY`. A case split for later attacks, not a paper
candidate and not a Juggler totality result.

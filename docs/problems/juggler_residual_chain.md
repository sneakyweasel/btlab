# Juggler residual-chain certificate propagation

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1.

## Problem

After an odd-to-odd start takes one `O^a E^b` residual step to a later
state \(y\), which already-proved certificates propagate back to the
start, and when is \(y\) simply another odd-to-odd frontier state?

## Exact statement

A residual step `ResidualStep x y` is a realized itinerary `O^a E^b` with
\(b\ge 1\) and image \(y\). It is a finite relation, not an infinite
transition system.

If `ResidualStep x y` and `ReachesOne y`, then `ReachesOne x`.

If `ResidualStep x y` and `Capture y v`, then `FiniteProgress x`.

If `ResidualStep x y` and `ReturnBelow x y`, then `FiniteProgress x`.

If a later word realizes `Descent y v` with image still \(\ge x\), the
concatenated word is not `Descent` at \(x\). In particular

\[
\mathrm{FiniteProgress}(y)
\nRightarrow
\mathrm{FiniteProgress}(x).
\]

`PersistentOddResidual x y` means the residual is another odd-to-odd
state with \(y>x\). The same frontier analysis applies to \(y\). This
is recursion, not progress.

If `MinimalNonTerm n` and `ResidualStep n y`, then \(n\le y\), and if
\(y\) is even then \(n^2\le y\).

Do not prove that every residual chain reaches 1 or drops below the
start. Do not prove a uniform horizon. Do not prove totality.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Backward closure of `ReachesOne` along a realized image —
  **EXACT — LEAN VERIFIED**.
- `ReturnBelow` plus a prefix is `FiniteProgress` —
  **EXACT — LEAN VERIFIED**.
- Post-overshoot leftover; two excursions do not always return —
  **COMPUTATIONALLY VERIFIED**.

Project relationship: **extended**. Residual composition is named, and
the stay-odd class is split. Totality remains unclaimed.

## Branch budget

```text
Mathematical target     which residual certificates propagate, and which leftover is recursive
Novelty hypothesis      Descent at y with image ≥ n is not progress at n; persistent odd-odd is a subclass
Falsifier               FiniteProgress(y) ⇒ FiniteProgress(n); or every stay residual is odd-odd
Existing machinery      reachesOne_of_image, capture_of_suffix, ReturnBelow, oddEvenBlock
Maximum Phase-0 scope   ResidualStep; compose/non-compose; PersistentOddResidual; hard-chain census
Promotion criterion     exact compose/non-compose split, or a strictly smaller leftover than stay-odd
Stop criterion          halt; cycle engine; uniform horizon; FiniteProgress(y)⇒FiniteProgress(n)
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- `ResidualStep` / `ResidualChain` compose `ReachesOne` —
  **EXACT — LEAN VERIFIED**
- residual `Capture` and `ReturnBelow` are `FiniteProgress` at the
  source —
  **EXACT — LEAN VERIFIED**
- residual `Descent` that stays \(\ge x\) is not `Descent` at \(x\) —
  **EXACT — LEAN VERIFIED**
- `PersistentOddResidual` stays on the odd-odd frontier —
  **EXACT — LEAN VERIFIED**
- CE residual scale: odd exit \(\ge n\), even exit \(\ge n^2\) —
  **EXACT — LEAN VERIFIED**
- in \(2\le n\le 80\), first residuals: 5 capture, 8 return below,
  3 automatic-`FiniteProgress` stay (\(9,49,77\)), 2 persistent
  odd-odd (\(37,69\)) —
  **OBSERVATION**
- `FiniteProgress(y)\Rightarrow\mathrm{FiniteProgress}(n)` —
  **REFUTED** as a general law
- every residual chain closes — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.residual_chain`
- Records: [juggler_residual_chain.md](../research/juggler_residual_chain.md),
  [juggler_residual_chain.json](../research/juggler_residual_chain.json)
- Tests: `tests/research/juggler_sequence/test_residual_chain.py`
- The Research Engine control layer is not modified.

## Conjectures

None opened.

## Counterexamples

None to the composition rules. The stronger claims that fail:

- “`FiniteProgress` at the residual is `FiniteProgress` at the start” —
  \(9\to 11\), \(49\to 79\), and \(77\to 1523\) have automatic
  `FiniteProgress` while remaining above the start; \(37\to 9317\to 2233\)
  is `Descent` at \(9317\) with \(2233>37\).
- “every stay residual is another odd-odd problem” — \(11\), \(79\),
  and \(1523\) are odd-to-even.
- “two residual steps always return below \(n\)” — already refuted
  by \(37\) and \(77\).

## Formalization

`formal/Problems/Engine/ResidualChain.lean`, above `OddOddFrontier`.
Added:

- `ResidualStep` / `PersistentOddResidual` / `ResidualChain`
- `reachesOne_of_residualStep` / `reachesOne_of_residualChain`
- `finiteProgress_of_residual_capture` /
  `finiteProgress_of_residual_returnBelow`
- `residual_descent_not_below`
- `persistent_residual_preserves_frontier`
- `minimal_residual_scale`

`FloorPower`, `Progress`, and `MinimalNonTerm` are not rewritten. No
`sorry`. No halt theorem. No
`finiteProgress_of_residual_finiteProgress`. No cycle engine. No
`PowerHeight`. No coinductive infinite path.

## Results

Classification **RESIDUAL_CHAIN_GREEN**.

A residual step is a composable finite relation. Certificates that
cross \(1\) or the original start propagate. Local descent at a larger
residual does not. The recursive leftover is persistent odd-odd, a
proper subclass of stay-odd.

## Open questions

Answered in [juggler_residual_path.md](juggler_residual_path.md): a
bounded residual prefix with a repeat is a cycle; every nonempty
cycle itinerary has \(2^r<3^o\); residual returns need \(a\ge 2\).

## Decision

**PROMOTE** the residual relation and the compose/non-compose split.
Do not claim that residual chains terminate. Do not claim that
`FiniteProgress` propagates. Do not claim totality.

Best next question: answered in
[juggler_residual_path.md](juggler_residual_path.md).

## Publication assessment

Status: `EXPLORATORY`. An organizing composition lemma, not a paper
candidate and not a Juggler totality result.

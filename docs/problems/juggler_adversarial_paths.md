# Juggler adversarial parity-path optimization

Status: **EXPLORATORY**

Standalone search for the hardest *realizable* finite O/E paths.
It is **not** a Research Engine control-layer experiment, not a new
scalar Lyapunov function, and not a reopening of PE-factor,
residual-future, sum-rho, realization-set, landing-image, \(N_w\),
first-return, or information-complexity branches.

## Problem

Among actually realized finite itineraries, which paths are maximally
difficult to force below their start, and do those extremal paths
share an exact structure?

## Exact statement

For each tested \(n>1\), walk the exact map until the first observed
strict return \(T^{\tau}(n)<n\), or the configured horizon. Objectives
are separate exact orderings: peak ratio \(P/n\), return weakness
\(T^{\tau}(n)/n\), duration \(\tau\), and prefix endpoint \(T^k(n)/n\).
Comparisons use cross-multiplication, or bit-length only when an
integer exceeds the storage cap.

This is an optimization over realized paths. It is not a termination
theorem and not a claim that \(\tau\) is finite.

## Current literature

- First-return maximality — **CLOSE** as `EXCURSION_COMPLEX`.
  The lex records reappear here and are not a new discovery.
- Finite-itinerary envelope — **EXACT — LEAN VERIFIED**
  (`power_bound_contracts`). Every observed return is the first
  formally contracting prefix.
- Odd steps cannot descend — **EXACT — LEAN VERIFIED**
  (`floorPower_odd_ge`).
- PE / residual-future / sum-rho / realization / landing-image /
  \(N_w\) / information-complexity — **CLOSE**.

Project relationship: **extended**.

## Branch budget

```text
Mathematical target     Do the hardest realized paths share a shape,
                        peak law, certificate-survival law, or
                        hardening swap?
Novelty hypothesis      record paths have a recurring arrangement or
                        a local word operation that increases hardness
Falsifier               records are the known first-return extremals;
                        same (k,o) splits; swaps do not harden;
                        certificates fire exactly at first G_j>0
Existing machinery      _walk_returns, exponent_gap,
                        first_defect_sufficient, follows_itinerary
Maximum Phase-0 scope   n=2..4000; prefix records k<=20; observed
                        (k,o) shape tables; local swaps of extremals;
                        no GPU; no Lean; no new scalar
Promotion criterion     a surviving arrangement, swap, or survival law
Stop criterion          EXTREMAL_COMPLEX; restatement of first-return
                        or the envelope; closed-branch reopen
```

## Balanced-ternary formulation

None required.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Recurring record shape —
  **REFUTED**; lex winners are `E`, `OOOEE`, the length-46 word at
  \(425\), \(2183\), and \(3889\)
- Arrangement law at fixed \((k,o)\) —
  **REFUTED**; all \(5\) multi-word groups with \(k\le 12\) split
- Peak always at an O-to-E cut as an extremal law —
  **REPARAMETERIZATION** of odd growth plus even contraction
  (true for all \(1999\) long odd returns)
- First-defect postponement —
  **REFUTED**; defect \(0\) is generic
- Certificate survival beyond the envelope —
  **REPARAMETERIZATION**; first \(G_j>0\) equals \(\tau\) on all
  \(3999\) returns
- Hardening adjacent swap —
  **REFUTED**; \(1\) of \(38\) window trials
- Return-margin law stronger than \(M\ge 1\) —
  **REFUTED**; `OOOEE` at \(3\)

## Experiments

- Probe: `research.juggler_sequence.adversarial_paths`
- Records: [juggler_adversarial_paths.md](../research/juggler_adversarial_paths.md)
- Dataset: `data/research/juggler/adversarial_paths/`
- Tests: `tests/research/juggler_sequence/test_adversarial_paths.py`

No GPU. No Lean. No Phase 1.

## Conjectures

None opened.

## Counterexamples

- Recurring shape: five distinct lex-record words.
- Fixed \((5,3)\): `OOOEE` has min \(M=1\), `OOEOE` has min \(M=3\).
- Hardening swap: \(37\) of \(38\) adjacent rearrangements are either
  unrealized in the window or not harder.
- Prefix \(P_k^*\) for \(k\le 10\) is a long initial odd run of a large
  odd start, not a new envelope.

## Formalization

None added. No `sorry`.

## Results

Phase 0 is recorded in
[juggler_adversarial_paths.md](../research/juggler_adversarial_paths.md).
Classification **EXTREMAL_COMPLEX**.

The hardest observed paths on \(2\le n\le 4000\) are the already-known
first-return records. Word shape at fixed \((k,o)\) changes the
observed min-margin, but there is no reproducible clustering law.
Certificate survival is the parked first formally contracting prefix.
Short-horizon endpoint records are long odd prefixes of large odds.
Extremality is state-determined.

## Open questions

None from this branch. Do not infer that \(\tau\) is finite for all
\(n\). Do not launch a GPU record search without a surviving law.

## Decision

**CLOSE**. Adversarial optimization recovered the known first-return
boundary and no new exact structure. Do not invent a difficulty
scalar. Do not reopen closed compression branches.

Best next question: none from this branch.

## Publication assessment

Status: `EXPLORATORY`. Not a paper candidate and not a Juggler
totality result.

# Juggler information complexity

Status: **EXPLORATORY**

Standalone measurement of *finite dynamical information complexity*.
It is **not** a Research Engine control-layer experiment, not a
reopening of PE-factor, residual-future, sum-rho, realization-set,
landing-image, \(N_w\)-boundary, or first-return branches, and not a
claim of formal independence or of Juggler totality.

## Problem

Does a longer finite Juggler future require more exact arithmetic
information about the starting state, on a *fixed* sample?

## Exact statement

Fix a sample \(Y\) and a horizon \(H\). The Phase-0 observable is

\[
F_H(x)=\text{the }O/E\text{ itinerary of }x,T(x),\dots,T^{H-1}(x).
\]

Experimental equivalence: \(x\sim_H y\) iff \(F_H(x)=F_H(y)\). This is
**not** Myhill–Nerode equivalence and not an automaton.

\[
Q_H=\#\{F_H(x):x\in Y\},\qquad
I_H=\lceil\log_2 Q_H\rceil,
\]

and \(k^*_2(H;Y)\) is the least \(k\) such that \(x\mapsto x\bmod 2^k\)
separates all distinct \(F_H\)-classes on \(Y\), or
`INSUFFICIENT_PRECISION_WITHIN_K_MAX`.

A result about \(Q_H\) or \(k^*\) is not a proof-complexity theorem and
not an independence result.

## Current literature

- Residual future-quotient — **CLOSE** as `FUTURE_QUOTIENT_REPACK`.
  Listed projections of \(y\) fail at \(H=1\); \(k^*=9\) is stable on
  \(n\le 80\) residual *labels*. Do not reopen that sufficiency question.
- ResidualStep \(\sim_H\) — **CLOSE** as `RESIDUAL_MN_REPACK`.
- PE / sum-rho / realization-set / landing-image / \(N_w\) / first-return
  — **CLOSE**.

Project relationship: **extended**. The leftover was whether *word*
futures have a genuine precision hierarchy on fixed samples.

## Branch budget

```text
Mathematical target     On fixed Y, do D_H and k*(H) grow with H<=6
                        for F_H = next H parities?
Novelty hypothesis      longer word futures require strictly more
                        arithmetic precision, surviving |Y| control
Falsifier               Q_H is the 2^H itinerary bound; k* saturates
                        by H=2 at a sample-diameter pair
Existing machinery      floor_power, itinerary, word_of,
                        collect_landings, atlas PE starts, v2, encode
Maximum Phase-0 scope   H<=6; samples A/B/C/D; word then L2/L3;
                        precision + separators + families; no GPU;
                        no Lean pilot; no residual Future_H labels
Promotion criterion     k*(H) or D_H grows with H on more than one
                        fixed sample, with witnesses
Stop criterion          growth is 2^H counting or an H=2 plateau;
                        residual-quotient reopen; independence claim
```

## Balanced-ternary formulation

Low \(k\) balanced-ternary digits were tested. MSD prefixes failed to
separate word classes for \(H\ge 2\). LSD digits track a \(3\)-adic
modulus and did not produce a horizon hierarchy.

## Why BT may be relevant

A trit prefix is a candidate distinguishing predicate, not a claim that
BT solves Juggler.

## Candidate operations / invariants

- \(Q_H\) grows with \(H\) as a new arithmetic law —
  **REFUTED**; \(Q_H\le 2^H\)
- \(I_H\) is a Kolmogorov-style complexity —
  **REPARAMETERIZATION** of \(\lceil\log_2 Q_H\rceil\)
- \(k^*_2(H)\) grows with \(H\) on a fixed sample —
  **REFUTED** on A, B, D; sample C is \(0,22,26,26,26,26\)
- nested \(k^*_2(2)\) is independent of \(|Y|\) —
  **REFUTED**; \(5,7,9,10,12\) on \(|Y|=30,100,500,1000,3999\)
- greedy query count grows with \(H\) —
  **REFUTED**; one residue test of width \(k^*(2)\)
- Level-3 state futures refine with \(H\) —
  **REFUTED**; \(Q_{\mathrm{state}}\) is the image size of \(T\)

## Experiments

- Probe: `research.juggler_sequence.information_complexity`
- Records: [juggler_information_complexity.md](../research/juggler_information_complexity.md)
- Dataset: `data/research/juggler/information_complexity/`
- Tests: `tests/research/juggler_sequence/test_information_complexity.py`

No GPU. No Lean pilot. No Phase 1 \(H\le 12\).

## Conjectures

None opened.

## Counterexamples

- “\(k^*_2\) grows with \(H\) on \(2..4000\)”: sequence \(1,12,12,12,12,12\),
  witness \((4,2052)\) at \(H=2\).
- “\(k^*_2\) grows with \(H\) on residual landings \(n\le 80\)”:
  sequence \(0,9,9,9,9,9\), witness \((243,1523)\).
- “\(k^*_2(2)\) is a property of the map, not of \(|Y|\)”: nested
  consecutive samples give \(5,7,9,10\).
- “the documented \(2^{16}\) pair is an \(H\)-hierarchy”: \(33\) and
  \(573141612728625270488952931933108109345\) split at \(H=2\)
  (`OO` vs `OE`) and then stay the \(k^*=17\) witness.

## Formalization

None added. No `sorry`. No proof-complexity pilot.

## Results

Phase 0 is recorded in
[juggler_information_complexity.md](../research/juggler_information_complexity.md).
Classification **INFO_COMPLEXITY_COUNTEREXAMPLE**.

On every fixed sample, word-class growth is the binary itinerary bound.
Two-adic precision demand jumps when the second letter appears and then
plateaus. The plateau value scales with the sample diameter, not with
further horizon. The O/E word forgets almost every start: on
\(2\le n\le 4000\), \(C_6=49/3999\). Coarse residues of the window
unique-identify starts by \(H=3\); exact \(T(x)\) already determines
the later state tuple.

## Open questions

None from this branch. Do not infer an unbounded information law or a
formal-independence statement.

## Decision

**CLOSE**. Longer finite itinerary futures do not require progressively
finer arithmetic information once \(H\ge 2\) is allowed on a fixed
sample. The collapse mechanism is the \(2^H\) itinerary bound plus a
sample-diameter 2-adic pair. Do not invent another complexity measure.
Do not run a proof-complexity pilot. Do not claim independence.

Best next question: none from this branch.

## Publication assessment

Status: `EXPLORATORY`. Not a paper candidate, not an independence
result, and not a Juggler totality result.

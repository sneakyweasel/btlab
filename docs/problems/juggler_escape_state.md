# Juggler escape-state margin

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1.

## Problem

On prefixes that avoid both exponent contraction and defect-driven
contraction, does

\[
M=\bigl(n^{3^o}-n^{2^k}\bigr)-\Delta_w(n)
\]

or a small tuple built from \(M\), \(G\), and the first defect, admit
a forward progress law?

## Exact statement

Write \(\Delta_w(n)=n^{3^o}-T_w(n)^{2^k}\) and
\(G(w)=2^k-3^o\). When \(G(w)\le 0\) and the powers are defined,

\[
M=T_w(n)^{2^k}-n^{2^k}.
\]

Hence \(M\ge 0\) if and only if \(T_w(n)\ge n\), and \(M=0\) if and
only if \(T_w(n)=n\). An *escape prefix* is a mixed prefix-NC word
with \(T_w(n)\ge n\). The Phase-0 question is whether \(M\), the
first-defect budget \(W=\mathrm{formal\_gap}-\delta_{\mathrm{first}}\),
or the overshoot \(T_w(n)-n\) is strictly more constrained along a
longer escape prefix.

This says nothing about totality. Indefinite escape is
non-termination. A search-horizon escape prefix is not a bound
\(L\).

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Finite-itinerary envelope and formal contraction —
  **EXACT — LEAN VERIFIED**.
- Compensated contraction \(\Delta>\mathrm{formal\_gap}\Rightarrow T<n\)
  — **EXACT — LEAN VERIFIED**.
- Prefix-NC language — **OBSERVATION**, parked.
- Prefix-NC arithmetic admissibility —
  closed as `PREFIX_NC_ARITHMETIC_COMPLEX`.
- Odd-odd residual scalars —
  closed as `ODD_ODD_RESIDUAL_COMPLEX`.

Project relationship: **extended**. The leftover after both local
contraction mechanisms is tested as an escape-state progress
measure. Totality remains unclaimed.

## Branch budget

```text
Mathematical target     Does M or a small tuple progress on escape prefixes?
Novelty hypothesis      escape now implies a strictly tighter escape later
Falsifier               M is T^{2^k}-n^{2^k}; sign is image>=n; overshoot grows
Existing machinery      formal_gap, tiny_deficit, compensated contraction,
                        prefix_noncontracting, first defect
Maximum Phase-0 scope   identity; HARD_STARTS; n<=200 k<=8; no automaton
Promotion criterion     a progress law not equivalent to image>=n
Stop criterion          ESCAPE_STATE_COMPLEX; ResidualStep; itinerary census;
                        inferred L; halt
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- \(M=\mathrm{formal\_gap}-\Delta=T^{2^k}-n^{2^k}\) on \(G\le 0\) —
  **COMPUTATIONALLY VERIFIED**, and a **REPARAMETERIZATION** of
  \(T\ge n\)
- \(M\ge 0\) iff the prefix does not contract —
  **COMPUTATIONALLY VERIFIED** (sign of \(T^{2^k}-n^{2^k}\))
- \(M=0\) iff \(T_w(n)=n\) — **COMPUTATIONALLY VERIFIED**; no
  \(n\ge 2\) return in the window
- \(M\) or \(W\) decreases along escape — **REFUTED** as a uniform
  law: defined consecutive pairs are scarce, and overshoot
  \(T-n\) grows on \(9\), \(37\), \(173\)
- future escape is a property of the current integer plus history
  — the future orbit is determined by the current integer alone
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.escape_state`
- Records: [juggler_escape_state.md](../research/juggler_escape_state.md),
  [juggler_escape_state.json](../research/juggler_escape_state.json)
- Dataset: `data/research/juggler/escape_state/`
- Tests: `tests/research/juggler_sequence/test_escape_state.py`
- The Research Engine control layer is not modified.
- `ResidualStep` is not extended. No adversarial engine.

## Conjectures

None opened.

## Counterexamples

- “\(M\) is a new progress measure”: on \(G\le 0\) it is
  \(T^{2^k}-n^{2^k}\).
- “escape overshoot shrinks”: \(9\) goes \(11\to 36\) after
  `OOE`/`OOEO`; \(37\) goes \(9317\to 24906114455136\) along
  `OOOOE`\(\ldots\)`OOOOEOOO`.
- \(M=0\) as a second envelope boundary with new rigidity: it is
  ordinary return \(T_w(n)=n\). None for \(n\ge 2\) in
  \(n\le 200\), \(k\le 8\).

## Formalization

None added. Compensated contraction and the envelope already live
in `formal/Problems/Engine/FloorPower.lean`. No
`EscapeState.lean`. `ResidualChain.lean` is not rewritten. No
`sorry`. No ledger row.

## Results

Classification **ESCAPE_STATE_COMPLEX**, with secondary
**ESCAPE_COUNTEREXAMPLE** for overshoot decrease.

On the escape set, \(M\) is actual non-contraction. The first-defect
budget does not supply a cheaper law. The future of an integer is
deterministic, so a history certificate does not create a new
state space. Indefinite escape is the global problem rewritten.
No Lean file.

## Open questions

Do not reopen ResidualStep, prefix-NC word exclusion, peak
identities, or a cell-tree engine. A well-founded measure for
non-termination remains the global problem and is not started
here.

## Decision

**CLOSE** the escape-state branch as `ESCAPE_STATE_COMPLEX`.
Record the identity \(M=T^{2^k}-n^{2^k}\) on \(G\le 0\) and the
overshoot counterexamples. Do not add Lean. Do not infer a bound
from the window. Do not claim termination.

Best next question: not another local rewrite of \(T\ge n\). The
global well-founded measure, if it exists, is not this margin.

## Publication assessment

Status: `EXPLORATORY`. A negative progress-measure result, not a
paper candidate and not a Juggler totality result.

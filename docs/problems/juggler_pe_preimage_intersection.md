# Juggler PE-envelope versus odd-cell intersection

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a
`PredClosure` reopen, not Paper A, not a retest of the parked
empty-odd-preimage forward laws, and not a claim that every positive
integer reaches 1.

The parked empty-odd-preimage branch already named Type 0/1/2 and
refuted next-parity / square-subinterval / persistence. This phase
asks the remaining history-sensitive question: whether the odd cell
of a PE landing is incompatible with the inherited PE predecessor
envelope.

## Problem

When a surviving PE episode lands on an odd state, does the fact
that its predecessor came from a constrained PE prefix make the
odd square-cell unreachable, even though the same cell can be
reachable from generic integers?

## Exact statement

Let \(y\) be an odd PE landing produced by an exact finite itinerary
\(uE\) from a start \(s\), and let \(z=T_u(s)\). Write

\[
I_y=\bigl[y^{2/3},(y+1)^{2/3}\bigr),
\qquad
J(s)=\{z\}.
\]

Classify the pair \((z,y)\):

- Type I: \(I_y\) contains no odd integer;
- Type II: \(I_y\) contains an odd integer, but that integer is
  not \(z\) and does not lie in the PE envelope;
- Type III: \(z\in I_y\) (history-compatible odd predecessor).

Decide whether leftover `AboveAnchor` PE landings are Type I or
II for a PE-specific reason, or whether Type III occurs.

Do not reopen \(R_{b,c}(n)\). Do not re-test empty \(\Rightarrow\)
next even.

## Current literature

- `odd_preimage_unique` / even and odd floor cells —
  **EXACT — LEAN VERIFIED**
- Type 0 iff \(k^3\ge(y+1)^2\) —
  **EXACT — HUMAN PROOF** (`J-odd-pred-empty-cube`)
- leftover PE landings are Type 0; emptiness has no forward law —
  **REFUTED** as a dynamical lever (`J-empty-odd-pe-forward`)
- escape-episode rank descent —
  **REFUTED** (`J-escape-episode-dichotomy`)
- `PredClosure \leftrightarrow ReachesOne` — closed, not reopened
- Every start reaches 1 — not claimed

Project relationship: **independent** as an envelope-intersection
question. The emptiness criterion is reused, not re-proved.

## Branch budget

```text
Mathematical target     I_y ∩ J(n) empty is a PE-specific
                        Diophantine obstruction
Novelty hypothesis      PE envelope, not generic inversion
Falsifier               scale mismatch; Type II family;
                        leftover Type I is cube-gap sparsity
Existing machinery      odd_preimage_unique; even_preimage_iff;
                        empty_odd_cell Type 0/1/2; PE words
Maximum Phase-0 scope   leftover PE words; 69/89; OOE < 4000;
                        no new Lean; no R_{b,c}
Promotion criterion     parameterized I_y ∩ J(n)=∅ that is
                        not even-versus-odd cells
Stop criterion          generically nonempty I_y; PE history
                        adds no envelope; R_{b,c} reopen;
                        numerical sparsity only; Z5
```

## Balanced-ternary formulation

None required. The comparison is cube-versus-square.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- PE last letter is `E`, so \(z\) is even and
  \(y^2\le z<(y+1)^2\) —
  **EXACT — LEAN VERIFIED** (`even_preimage_iff`)
- \(I_y\) lives at scale \(y^{2/3}\) and never contains \(z\)
  for a PE landing —
  **COMPUTATIONALLY VERIFIED**
- leftover PE odd landings are Type I —
  **COMPUTATIONALLY VERIFIED**
- OOE below \(4000\) has a Type II family (`199`, `483`,
  \(\ldots\)) and no Type III —
  **COMPUTATIONALLY VERIFIED**
- `69` at `117` and `89` at `291` are Type I with an even cube
  in \(I_y\) —
  **COMPUTATIONALLY VERIFIED**
- \(I_y\cap J(n)=\varnothing\) is a new PE obstruction —
  **REFUTED** (scale / parity of even versus odd cells)
- \(n\ge N_0\) implies all PE odd cells empty —
  **REFUTED** (Type II OOE family)
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.pe_preimage_intersection`
- Records: [juggler_pe_preimage_intersection.md](../research/juggler_pe_preimage_intersection.md),
  [juggler_pe_preimage_intersection.json](../research/juggler_pe_preimage_intersection.json)
- Tests: `tests/research/juggler_sequence/test_pe_preimage_intersection.py`
- The Research Engine control layer is not modified.

## Conjectures

None opened.

## Counterexamples

Ordinary terminating orbits, not `MinimalNonTerm` witnesses.

- “PE landing \(y=\lfloor z^{3/2}\rfloor\)” — leftover PE words
  end in `E`, so \(y=\lfloor\sqrt{z}\rfloor\).
- “\(I_y\cap J(n)=\varnothing\) is PE-specific” — \(z\sim y^2\)
  and \(I_y\sim y^{2/3}\) for every even-produced landing.
- “all PE odd cells empty for large \(n\)” — `199` follows
  `OOE` to `385` with odd predecessor `53`.
- “Type III compatible odd predecessor” — none in the leftover
  laboratories or in the OOE window.
- `69\to 117` has even cube `24` in \(I_y\) and still Type I;
  that does not force the later even trap `212`.

## Formalization

No new Lean module. `odd_preimage_unique`, `even_preimage_iff`, and the
cube-interval lemmas stay in `Preimages.lean`. `AboveAnchor` stays in
`MinimumRelative.lean`. Not imported by `Problems.JugglerPaper`.
No `sorry`. No `PECellIntersection` API. No `juggler_reaches_one`.
The Type 0/1/2 criterion stays in `empty_odd_preimage.py`.

## Results

Classification **PE_PREIMAGE_INTERSECTION_PARK**.

A PE landing is an even-produced square-cell image. The odd cell
\(I_y\) is a different interval. Their intersection is empty by
scale and parity, not by a PE envelope. Leftover landings are
Type I because \([y^2,(y+1)^2)\) contains no cube, the ambient
cube-gap fact already recorded as Type 0. A Type II OOE family
shows that a nonempty odd cell can sit under a PE landing without
the occupant being the PE predecessor. Type III does not occur.

The hoped mechanism “odd landing \(\Rightarrow\) empty/history-
incompatible cell \(\Rightarrow\) forced even reset” does not
start: the landing was already produced by an even reset, and an
empty odd cell is a backward statement.

## Open questions

Stop this predecessor/cell line. Do not build a coupled defect
system for \(I_y\). Do not hunt \(N_0\). The leftover corridor
remains an odd-landing PE walk; its arithmetic location in the
square cell of \(y\) is not a new odd-cell obstruction.

## Decision

**PARK**. The PE envelope does not meet the odd cell at the same
scale. Type I on the leftover controls is generic cube-gap
sparsity. Type II exists and is history-incompatible only because
the PE predecessor is even. That is `even_preimage_iff` versus
`odd_preimage_iff`, not a minimum-relative theorem. Falsifiers A, B
(as a category error), C, and D all hold.

Best next question: none from odd-cell intersection. Do not
reopen \(R_{b,c}\) or empty-cell counting.

## Publication assessment

Status: `EXPLORATORY`. A negative envelope-intersection fragment,
not a paper candidate and not a Juggler totality result.

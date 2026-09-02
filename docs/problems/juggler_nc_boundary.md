# Juggler noncontracting realization boundary

Status: **EXPLORATORY**

Standalone arithmetic layer on finite Juggler words. It is **not** a
Research Engine control-layer experiment, not a reopening of PE-factor,
residual-future, sum-rho, realization-set branching, or landing-image
branches, and not a claim that every positive integer reaches 1.

## Problem

For a fixed finite \(O/E\) word \(w\), what is the arithmetic structure
of the starting states that realize \(w\) and fail the finite-itinerary
contraction test?

## Exact statement

\[
R_w=\{n>0:\operatorname{follows}(n,w)\},\qquad
N_w=\{n\in R_w:T_w(n)\ge n\}.
\]

On a bound \(N\), write \(R_w(N)=R_w\cap[1,N]\) and
\(N_w(N)=N_w\cap[1,N]\). Let \(a_w=\min N_w\) when the set is nonempty.
The identity \(n\in N_w\Leftrightarrow T_w(n)\ge n\) is the definition,
not a theorem. When \(3^{\#O(w)}<2^{|w|}\) the existing envelope already
forces \(T_w(n)<n\) for \(n>1\). The Phase-0 question is whether the
boundary of \(N_w\) on formally expanding itineraries admits a description
structurally simpler than evaluating \(T_w\).

Absence under a scan bound is not global emptiness. This says nothing
about totality.

## Current literature

- Weak envelope and \(3^o<2^k\Rightarrow T_w(n)<n\) —
  **EXACT — LEAN VERIFIED** (`power_bound_contracts`).
- \(T_w\) monotone on \(R_w\) —
  **EXACT — LEAN VERIFIED** (`image_monotone_of_follows`).
- Compensated contraction \(\Delta>\) surplus \(\Rightarrow T<n\) —
  **EXACT — LEAN VERIFIED**; algebraically \(T<n\) on expanding
  words. Do not reopen.
- Prefix-noncontracting *words* (\(G_j\le 0\) on every prefix) —
  parked as language combinatorics, not as \(N_w\).
- Realization-set geometry / landing-image —
  **CLOSE** / **PARK**. \(d(w)\) and \(Y_w\) are not this object.
- PE-factor / residual-future / sum-rho —
  **CLOSE**. Do not reopen.

Project relationship: **extended**. Totality remains unclaimed.

## Branch budget

```text
Mathematical target     structural description of N_w / a_w
                        that is not T_w(n) >= n
Novelty hypothesis      threshold, cell, (k,o,run), or prefix
                        inheritance law
Falsifier               inversions; same (k,o) split a_w;
                        every useful statement is T>=n
Existing machinery      follows, image, power_bound_contracts,
                        image_monotone_of_follows, first_nonexact,
                        even_preimage
Maximum Phase-0 scope   n<=4000 k<=20 complete; selected families
                        n<=1e5; no census / GPU / automaton
Promotion criterion     exact inequality or inheritance/cell law
Stop criterion          generic fragmentation; T>=n restatement;
                        closed-branch reopen; halt claim
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- \(N_w=\varnothing\) on formally contracting itineraries (\(n>1\)) —
  **EXACT — LEAN VERIFIED** (`power_bound_contracts`);
  **COMPUTATIONALLY VERIFIED** on \(n\le 4000\), \(k\le 20\)
- \(N_E=\varnothing\), \(N_{O^r}=\) all odds in the window —
  **COMPUTATIONALLY VERIFIED** (calibration)
- \(n\ge a_w\Rightarrow n\in N_w\) on expanding itineraries —
  **REFUTED** by `EOO` at \(10\in N\), \(12\notin N\), same image \(11\)
- \(a_w\) determined by \((k,o)\) —
  **REFUTED**; 58 expanding groups split, ratio \(37\) vs \(3989\)
  at \((13,9)\)
- \(a_w\) determined by \((k,o,\mathrm{runs})\) —
  **REFUTED**; 457 run-signature groups split
- \(N_{wb}\subseteq N_w\) —
  **REFUTED**; `EO` contracts at \(10\), `EOO` does not
- Prefix \(N_w\) implies child \(N_{wb}\) —
  **REFUTED**; `OOOE` at \(3\) is NC, `OOOEE` contracts
- First-defect position restricted on \(N_w\) —
  **REFUTED**; NC samples use positions \(0\) and \(2\), C uses \(0\)

## Experiments

- Probe: `research.juggler_sequence.nc_boundary`
- Diagnostic: \(n\le 4000\), \(k\le 20\) (7519 realized itineraries)
- Selected confirm: \(n\le 10^5\) on the fixed family list
- Records: [juggler_nc_boundary.md](../research/juggler_nc_boundary.md)
- Tests: `tests/research/juggler_sequence/test_nc_boundary.py`

No new census. No GPU. No atlas schema.

## Conjectures

None opened.

## Counterexamples

- Threshold / upper tail: `EOO`, \(n_1=10\), \(T=11\ge 10\);
  \(n_2=12\), \(T=11<12\). The two starts share the first-even cell
  of \(q=3\).
- Same \((k,o)=(13,9)\): `OOOOEOOOEEOOE` has \(a=37\);
  `OOEOOEOOEOOOE` has \(a=3989\).
- Same run signature \((11,8,5,4,2,4)\): `OOOOEOOOEEO` has \(a=37\);
  `OOOEEOOOOEO` has \(a=3753\).
- Late expand: `EO` at \(10\) contracts, `EOO` does not.
- Late contract: `OOOE` at \(3\) is NC, `OOOEE` contracts. Also
  `O` at \(7\) is NC and `OE` contracts.

## Formalization

None added. Existing `power_bound_contracts` and
`image_monotone_of_follows` certify the envelope and monotonicity.
No `sorry`. No automaton.

## Results

Phase 0 is recorded in
[juggler_nc_boundary.md](../research/juggler_nc_boundary.md).
Classification **NC_BOUNDARY_COMPLEX**.

Formally contracting itineraries have empty \(N_w\) for \(n>1\). That is
the existing envelope. On expanding itineraries, \(2583/2584\) nonempty
windows are upper tails; the only inversion is the constant-image
pair on `EOO`. Word shape does not fix \(a_w\). Prefix extension
fails in both directions. First-defect position does not separate
\(C_w\) from \(N_w\). Locating \(a_w\) still requires evaluating
\(T_w\).

## Open questions

None from this branch.

## Decision

**CLOSE**. Every exact positive statement is `power_bound_contracts`
or the definition \(T_w(n)\ge n\). The threshold, \((k,o)\), run,
inheritance, and first-defect candidates all have small
counterexamples. Do not invent another statistic. Do not pursue
termination.

Best next question: none from this branch.

## Publication assessment

Status: `EXPLORATORY`. Not a paper candidate and not a Juggler
totality result.

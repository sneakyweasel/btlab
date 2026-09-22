# Effective OOE modular returns

## Problem

Replace the qualitative OOE modular-return count by an explicit error and
a first-witness bound, retaining the dependence on the modulus M.

## Exact statement

For positive integers M,T, count parameters 0<=t<T with s=1+2Mt>=16,
floor(s^(9/2)) even, and floor(s^(9/4))=1 modulo 2M. Then

abs(A_M(T)-T/(4M)) <= 2^14*M^(1/4)*T^(127/128).

Consequently some t<2^2176*M^160 supplies an actual OOE return with
n=(1+2Mt)^2<2^4354*M^322, all prefix states at least n, endpoint greater
than n, and both endpoints 1 modulo 2M.

The [complete proof](../theory/juggler_effective_modular_return_note.md)
also gives a sharper error with exponent 63/64 and an explicit logarithmic
factor. These are written statements, not newly compiled Lean results.

## Current literature

Classical derivative machinery: literature id
arias-de-reyna-2024-explicit-derivative-estimate, pinned arXiv v1,
Theorem 11 and Table 1 at orders 3 and 5. The cited constants are below 11.
The explicit Fejer smoothing argument is proved in the note.
Boshernitzan's qualitative criterion, id boshernitzan-1994-hardy-fields,
underlies the earlier written recurrence argument but supplies no constants
used in this proof. The new work is a **PROJECT-SPECIFIC** effective
specialization; novelty of the analytic tools is **KNOWN**. External
priority for the specialized statement remains unclaimed.

## Branch budget

- **Target:** an explicit OOE counting error and first-witness bound.
- **Novelty hypothesis:** a quantitative strengthening useful to Paper E.
- **Falsifier:** an uncovered Fourier mode or an uncontrolled M-dependent constant.
- **Already killed by?:** no listed obstruction excludes this one finite
  block; the closed shrinking-target and continuation attacks remain closed.
- **Existing machinery:** exact root cells, the thresholded OOE construction,
  qualitative counting, and explicit classical derivative estimates.
- **Maximum Phase-0 scope:** one fixed word; written proof with all constants.
- **Promotion criterion:** complete explicit bounds, checked arithmetic,
  and a clear mathematical use.
- **Stop criterion:** missing uniform control or a mere restatement.

## Balanced-ternary formulation

Not used. The phases are ordinary real powers and the guards are parity
and residues of their exact integer floors.

## Why BT may be relevant

The laboratory provides exact arithmetic and registration. No representation
advantage or balanced-ternary proof mechanism is asserted.

## Candidate operations / invariants

**EXACT — HUMAN PROOF:** fifth derivatives control modes with a nonzero
9/2-power coefficient; third derivatives control the remaining axis.
Dyadic initial-segment removal is explicit. Finite Fejer smoothing handles
half-open boxes, including the M=1 endpoint and residue-zero boundary.

## Experiments

Runner: python -m research.juggler_sequence.effective_modular_return.
Output: data/research/juggler/effective_modular_return/summary.json.
There are 22 rational arithmetic checks and 32768 actual-prefix checks:
0<=t<4096 for M in {1,2,3,4,8,16,31,64}. The bound is vacuous at this
sample size, so these experiments test floor guards and bookkeeping only.
They neither establish the analytic estimate nor measure a convergence rate.

## Conjectures

No new conjecture. Improving the numerical bound is a separate question.

## Counterexamples

The actual return 9,27,140,11 at M=1 and t=1 is deliberately excluded
from A_M because s=3<16. This tests the precise thresholded family; the
count is not the count of all genuine returns. Its first selected M=1
witness is t=9, with orbit 361,6859,568056,753.

## Formalization

No new Lean module. The existing PaperEModularReturn and PaperECorollaries
prove the exact orbit construction and qualitative counts. The quantitative
mode estimates, Fejer inequality, and explicit assembly in this branch are
written proofs. Finite Python checks do not discharge these Lean gaps.

## Results

The complete uniform counting error and polynomial first-witness bound
are derived in the proof note. The nonzero-high-frequency and pure-low-
frequency cases are both included. The proof tracks all short initial
segments and all half-open boundary values. No asymptotic constant or
unspecified threshold remains in the theorem statement.

## Open questions

Independent review of the analytic specialization and prose-to-formal scope.
Full Lean formalization of this quantitative result remains open. The coarse
bound is not a useful computational limit, despite its polynomial dependence
on M. Extension beyond OOE is outside this branch.

## Decision

**PROMOTE** the written effective OOE theorem. It strengthens the existing
qualitative result with a uniform explicit error and a bounded search domain.
Do not optimize constants or open other words automatically.

Best next question: does an independent proof audit confirm every uniform
constant and boundary condition in the effective counting estimate?

## Publication assessment

Status: **THEOREM**, as an AI-assisted written specialization of a classical
estimate. Candidate supplement to Paper E after review; not incorporated
into the version 0.5.0 manuscript or its 49-declaration Lean audit.
External novelty and independent verification are not claimed. The OOE
word code has denominator 1, so this specialization does not itself provide
effective large-denominator counterfamilies.

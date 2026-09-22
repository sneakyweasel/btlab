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

The existing PaperEModularReturn and PaperECorollaries prove the exact
orbit construction and qualitative counts. The complete finite Fejer
inequality is now proved by `BTCalculus.FejerBox.finite_box_discrepancy`,
with supporting modules FejerKernel, FejerArc, and FourierDiscrepancy.
The [proof map](../theory/finite_fejer_box_note.md) records the constants,
half-open boundaries, saturation, and dependency audit. The quantitative
mode estimates are now also proved in `OOEEffectiveModes`; the explicit
OOE counting and witness assembly remain written proofs.
Finite Python checks do not discharge those Lean gaps.
The [internal proof audit](../theory/juggler_effective_modular_return_audit.md)
maps the five quantitative obligations and the exact declarations that
can be reused. Q3 is closed by the subsequent formalization. The generic
analytic part of Q1 now has explicit kernel-checked third- and
fifth-derivative alternatives in `BTCalculus.HigherDerivative`; the
[proof map](../theory/higher_derivative_finite_note.md) records constants
12 and 7, both signs, cutoffs, and real endpoints with extended support.
The [OOE specialization](../theory/juggler_ooe_effective_modes_note.md)
now proves the actual derivative chains, signs, and comparison with
constant 32, then the all-length normalized constant 128. Q1's application
and Q2 are closed. Q4 and Q5 remain open.

## Results

The complete uniform counting error and polynomial first-witness bound
are derived in the proof note. The nonzero-high-frequency and pure-low-
frequency cases are both included. The proof tracks all short initial
segments and all half-open boundary values. No asymptotic constant or
unspecified threshold remains in the theorem statement.
The fresh internal audit retained every constant and exponent. It expanded
the source hypotheses, pure low-power terms, dyadic endpoint accounting,
and the pointwise smoothing proof for empty or full circular intervals.
The M=1 right endpoint is explicitly excluded. This second derivation is
not independent external review.

## Open questions

Independent external review of the analytic specialization. The internal
audit and its explicit prose-to-formal scope map are complete.
Full Lean formalization of this quantitative result remains open. The coarse
bound is not a useful computational limit, despite its polynomial dependence
on M. Extension beyond OOE is outside this branch.

## Decision

**PROMOTE** the written effective OOE theorem. It strengthens the existing
qualitative result with a uniform explicit error and a bounded search domain.
Do not optimize constants or open other words automatically.

The finite half-open Fejer box estimate (Q3 in the audit) is kernel-checked
with its constants and all boundary cases. The authorized continuation
also proves explicit order-3 and order-5 derivative tests with automatic
cutoffs. The actual OOE phase specialization and quantitative dyadic
assembly now compile, with the exact constants 32 and 128.
**PROMOTE** these formalizations. The next dependency is Q4, the exact
counting and explicit error assembly, followed by bounded witnesses.
External review remains open; modulus optimization is outside this scope.

## Publication assessment

Status: **THEOREM**, as an AI-assisted written specialization of a classical
estimate. Candidate supplement to Paper E after review; not incorporated
into the version 0.5.0 manuscript or its 49-declaration Lean audit.
External novelty and independent verification are not claimed. The OOE
word code has denominator 1, so this specialization does not itself provide
effective large-denominator counterfamilies.

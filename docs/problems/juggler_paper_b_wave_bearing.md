# Paper B: the wave-bearing family

## Problem

Repair the family with nonzero total Y frequency, including the widened
D1 terms and the previously repaired D2 floor factors.

## Exact statement

For every fixed C,M and epsilon>0, the sum (W3) in
[the full statement and proof](../theory/paper_b_wave_bearing_report.md)
is O_(C,M,epsilon)(P^(31/32+epsilon)). Here 1/2<=|t|<=CP^(1/24),
each signed first-difference coefficient satisfies |a_j|r_j<=CP^(1/2),
and there are at most M such terms and M D2 factors. Coefficients are
constant on a coarse partition of local cell count
O_C(1+L P^(-11/24)); phi is C^3 there with |phi'''|<=CP^(-13/12),
and eta has bounded sup norm plus variation per cell. D2 labels stay
fixed on their original gap runs despite further refinement.
All other shifts, domains, and quantifiers are specified in Section 1.

## Current literature

**Extended:** the local D2 and signed zero-offset supplements isolate
other parts of the historical Paper B argument. This result repairs
the wave-bearing family over the widened coefficient range.
Classical van der Corput differencing and second-derivative estimates
are used as in Graham and Kolesnik, Van der Corput's Method of
Exponential Sums (1991), linked in the report.
No literature-wide novelty claim is made, and no new literature id
is assigned to a standard tool. No independent mathematical review.

## Branch budget

This transcribes the triage announced before the proof was written.

- **Target:** bound the family with nonzero total Y frequency.
- **Novelty hypothesis:** linearize each D1 term on its carry branch
  and retain the main differenced wave's curvature.
- **Falsifier:** a floor error or boundary cost exhausts the saving.
- **Already killed by?:** the signed-wave dominance failure in
  [negative knowledge](../negative_knowledge.md) concerns another
  argument; here the total main frequency is bounded away from zero.
- **Existing machinery:** exact carry identities, D2 reduction,
  Fourier interval expansions, and second-derivative bounds.
- **Maximum Phase-0 scope:** prove or block this family over the
  widened coefficient ranges.
- **Promotion criterion:** control both signs, all retained modes,
  and every original, coarse, carry, and coefficient partition cut.
- **Stop criterion:** leave kernel assembly open wherever an
  application has not yet been verified.

## Balanced-ternary formulation

The integer source and its nested floor images can be stored in
canonical balanced ternary. The proof is representation independent:
it uses m=floor(n^(3/2)), Y=m^(3/2), and exact carry differences.

## Why BT may be relevant

Balanced ternary supports exact integer bookkeeping elsewhere in
the laboratory. No analytic saving here is attributed to the radix.

## Candidate operations / invariants

- **EXACT — HUMAN PROOF**, J-paper-b-widened-d1-linearization:
  differentiate the frozen D1 branch in the variable m before replacing
  m by X; its total phase error is O(P^(3/4)).
- **EXACT — HUMAN PROOF**, J-paper-b-wave-bearing-sums:
  apply one A-process with H=P^(1/12), use the nonzero main curvature
  beyond a fixed number of small shifts, and count all partition cuts.
  The ledger tag denotes a written proof, not independent review.

## Experiments

Runner: tools/validate_paper_b_wave_bearing.py, optionally with
--output <json path>. The artifact
[validation record](../theory/paper_b_wave_bearing_validation.json)
contains status, counts, rational exponents, and scope.

Controls: 12 frozen-coefficient and derivative identities, 2916
base-zero telescope cases, 288 commuting-shift cases, 1575 exact
carry and endpoint cases, and 29 exponent controls.
The proof is analytic; these finite checks do not independently
prove cancellation. No unbounded search or floor campaign was run.

## Conjectures

No new conjecture is registered. The complete kernel and OOOEE
mixed-mode transfer remain unproved.

## Counterexamples

No new counterexample. The old signed-wave maximum criterion remains
refuted as recorded in the D2 supplement. The present argument
does not use that criterion. The older loose D1 floor bound is
strengthened, not declared false.

## Formalization

No Lean module exists for this supplement. The written proof and
exact rational controls are the present evidence; independent review
remains outstanding.

## Results

The [report](../theory/paper_b_wave_bearing_report.md) proves:
1. (W5)--(W7), the widened D1 floor replacement and curvature estimates.
2. (W18), every large-shift correlation is
   O(P^(15/16) log^B(P)), including the D2 errors.
3. (W3), the wave-bearing sum is O_epsilon(P^(31/32+epsilon)).

The fixed number of small shifts fits the A-process diagonal.
The original D2 runs are distinguished from additional refinements,
and the carry expansion is charged globally at its endpoints.
No new kernel bound or five-step certificate density follows yet.

## Open questions

The nonzero-offset anchor family with zero total Y frequency remains
to be bounded. Complete kernel assembly and the transfer to every
OOOEE mixed mode then require separate verification.

## Decision

**PROMOTE** the stated wave-bearing theorem and widened D1
linearization. Their explicit errors and boundary costs all fit the
claimed power saving. The best next question is: can the nonzero-offset
anchor family with zero total Y frequency, including its signed
decorations, be bounded uniformly? This branch stops here.

## Publication assessment

Status: **THEOREM** (AI-assisted written proof; independent review
outstanding). Keep as a research supplement pending the remaining
family and assembly audits. The main 27/32 manuscript, metadata,
PDF, and Zenodo deposit package are unchanged.


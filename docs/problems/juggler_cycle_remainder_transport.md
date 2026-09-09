# Finite family-growth chains and exact remainder transport

Status: **PROMOTE** the two scoped results below. Authorized continuation,
9 September 2026. General orbit escape, universal family termination,
uniform word-guard closure and global no-cycle are not proved.

**The infinite family is unbounded as a collection of starting values;
that does not produce one escaping orbit.** Its exact three-step growth
pattern cannot concatenate indefinitely: a finite 2-adic valuation drops
by 2 at each continuing family transition. All six previously selected
members also reach 1 in exact finite computations. Separately, retaining
the actual square remainder repairs the short-block quotient error with
a uniform error below \(5/6\), giving a faithful OOE guard.

## Problem

The user asked whether the infinite OOE family could escape to infinity,
then authorized the next arithmetic question: transport the exact square
remainder instead of discarding it. The
[previous carry gate](juggler_cycle_guard_carries.md) proves the family
and the failure of a bounded additive correction after pure-power
replacement. Its full block proof is not duplicated here.

## Exact statement

For odd \(r\ge3\), define
\[
X(r)=r^8+8,\qquad Z(r)=r^9+9r-1.
\]
The known exact block gives \(J^3(X(r))=Z(r)>X(r)\).
The escape-mechanism question is whether there can be infinitely many
consecutive exact returns \(Z(r_i)=X(r_{i+1})\).
This is narrower than whether some fixed orbit \(J^k(X(r))\) escapes.

The arithmetic question concerns \(x\overset O\longmapsto u
\overset O\longmapsto v\overset E\longmapsto z\), with exact first
square remainder \(R=x^3-u^2\). Does retaining \(R\) repair the suffix
quotient with a uniform correction, and does that yield a uniform
description for arbitrary induced words? Result 2 answers the first
part positively. The second part remains open.

## Current literature

**Internal exact results; external priority not claimed.** The family,
the OE quotient guard and short endpoint identities are established in
the preceding dossiers. The aggregate composition law is already
formalized as `Problems.Juggler.global_defect_append` in
[GlobalDefect.lean](../../formal/Problems/Juggler/GlobalDefect.lean);
it is not a new finding of this gate. No external novelty or literature
survey is claimed.

## Branch budget

The triage was written before implementation.

- **Target:** distinguish parameter growth from escape; test faithful
  exact-remainder transport through the next short return substitution.
- **Novelty hypothesis:** a valuation may obstruct repetition of the
  family, and a first-order remainder correction may bound the nonlinear
  quotient error uniformly.
- **Falsifier:** the family is not invariant; a correction needs fresh
  residue or guard evaluations without a uniform update rule.
- **Already killed by?:** bounded additive pure-power substitution,
  word interpreters, packed guard lists, generic local cells and
  finance-only reformulations.
- **Existing machinery:** the exact OOE family, square cells, the OE
  quotient guard, short endpoint identities and return towers.
- **Maximum Phase-0 scope:** analytic re-entry and remainder checks;
  six existing parameters capped at 500 steps and 16,384 state bits;
  one correction theorem and one composition audit. No cap enlargement,
  new cycle census or descent-floor campaign.
- **Promotion criterion:** a genuine obstruction to the proposed family
  escape mechanism, or a faithful arithmetic repair with precise scope.
- **Stop criterion:** retain scoped results; leave full fate and uniform
  closure open when their required invariants are not proved.

## Balanced-ternary formulation

The states and exact remainders are integers. The family obstruction
uses the usual divisibility valuation \(\nu_2\), independent of how the
integers are written.

## Why BT may be relevant

No representation advantage is used or claimed.

## Candidate operations / invariants

For continuing exact family transitions, \(\nu_2(r-1)\) decreases.
For the quotient repair, the retained data are \(x,z,R\); initialization
and the endpoint certificate are explicit in Result 2. The stored
remainder is an unbounded integer carrying absolute-state information.
A fixed number of temporary registers does not bound the work needed
to evaluate a growing word.

## Experiments

The [exact verifier](../../src/research/juggler_sequence/cycle_remainder_transport.py)
and [tests](../../tests/research/juggler_sequence/test_cycle_remainder_transport.py)
replay [summary.json](../../data/research/juggler/cycle_remainder_transport/summary.json):

    python -m research.juggler_sequence.cycle_remainder_transport

All trajectory steps and comparisons use integers. Orbit states are
stored losslessly in hexadecimal. The six parameters are reused from
the previous counterfamily controls. Every trace finished below the
fixed caps of 500 steps and 16,384 state bits; no cap was enlarged.

| Parameter \(r\) | Steps from \(X(r)\) to 1 | Decimal digits at the maximum |
|---|---:|---:|
| 3 | 28 | 111 |
| 5 | 13 | 13 |
| 11 | 64 | 129 |
| 101 | 24 | 41 |
| \(10^6+1\) | 60 | 468 |
| \(10^{20}+1\) | 54 | 1,480 |

These are exact results for six specified starts, not a theorem for all
parameters. The first starts at 6569. The last starts at a 161-digit
integer and still reaches 1 after a 1,480-digit excursion. A cap hit,
had one occurred, would have meant unresolved computation, not escape.

The repair controls use sources \(3\le x\le128\) plus the six family
starts, for 132 instances. Another 65 short-word controls compare the
validated OOEOE procedure with literal prescribed traces. These finite
checks support implementation consistency; the quantified results
have the written proofs below.

## Conjectures

No new conjecture file is opened. Neither universal termination of
\(X(r)\) nor an escaping member is established.

## Counterexamples

The finite trajectory from 6569 shows that the proved three-step rise
can precede a huge excursion and termination. The next OOE endpoint
need not belong to the same family. Result 1 rules out indefinite
consecutive repetition of that exact family, with a quantitative bound.
It does not imply descent after departure.

For the repair, an odd ideal endpoint must still be validated: at
\(x=5\), the odd-projected candidate is 5 whereas the actual prescribed
OOE endpoint is 6. Skipping the endpoint certificate would be unsound.

## Formalization

Current declaration-level coverage is recorded in Paper A, Appendix A,
and its [formalization map](../theory/juggler_finite_dynamics_formalization.md).
The canonical Lean files are in `formal/Problems/Juggler/` and are imported
by `Problems.JugglerPaper`. The theorem ledger distinguishes the compiled
statements from the additional written consequences. No general no-cycle
or escape-exclusion theorem is claimed.

## Results

The current statements and proofs are consolidated in **Appendix E.4--E.5** of
[Paper A](../theory/juggler_finite_dynamics_note.md).
That manuscript is the canonical editorial source. This dossier retains
the original branch budget, controls, limitations and decision record;
it is not a second editable copy of the proof.

## Open questions

For the family, the unresolved fate question concerns the orbit after
it leaves the exact three-step description. The finite valuation bound
does not supply a decreasing integer along every later Juggler step.

For arithmetic closure, the short-block repair and its next explicit
concatenation still evaluate constituent guards. A fixed formula for
the endpoint, remainder fields and entire guard of an arbitrary induced
word has not been proved. Repeated initialization of local remainders
would be sequential evaluation with additional bookkeeping.

## Decision

**PROMOTE** the scoped family-chain obstruction and exact remainder
repair. The first prevents the proposed family repetition mechanism;
the second corrects the previously unbounded quotient error and supplies
a necessary-and-sufficient short-block guard. Neither promotes a global
escape, termination, cycle-exclusion or uniform induction claim.

The one best next question is: **can the exact remainder and parity
guard of a whole induced return word be updated by one fixed formula
under both Euclidean substitutions, without traversing its constituent
guards?** This is a stricter target than repeating the successful
short-block calculation. No separate attack or larger computation is
automatically authorized by this record.

## Publication assessment

Status: **STRUCTURAL**. The results are now consolidated into Paper A,
Appendix E.4--E.5, with the formal scope recorded beside the claims.
The certified period floor remains 780239. This consolidation is a local
revision; it does not upload a new Zenodo version.

## Authorized whole-word continuation

The [fixed-residue guard gate](juggler_cycle_guard_residues.md) proves a
precise limitation of the next extension: even the exact first remainder
R=0 plus any fixed finite collection of source/endpoint/aggregate residues
does not determine the OOE hidden guard. The counterpair shares threshold
and return section. The absolute quotient repair above remains correct.
Full arithmetic closure and cycle-selected constraints remain open.

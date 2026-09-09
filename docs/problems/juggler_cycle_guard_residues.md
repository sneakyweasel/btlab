# Exact first remainders do not close a fixed-residue parity guard

Status: **CLOSE** the tested fixed-residue extension. Authorized continuation,
9 September 2026. Absolute-data arithmetic closure and global no-cycle remain open.

**The missing hidden parity survives every fixed choice of residue moduli,
even when the first square remainder is retained exactly.** The construction
below gives two exact OOE first-return blocks in the same threshold band and
the same return section. Their initialized first remainders are both zero,
their recorded residues agree, and their aggregate 2-adic valuations are
both 3; exactly one has the required E-source parity. This is a quantified
obstruction to a specified summary class, not a claim about every formula
using unbounded absolute inputs.

## Problem

The user authorized the next no-cycle question after the
[exact-remainder repair](juggler_cycle_remainder_transport.md).
Can the full guard of an arbitrary induced word be updated under both
Euclidean substitutions, without traversing its constituent guards?
The broad target requires a precise arithmetic model. This gate tests
the concrete proposal to retain the first exact remainder and compress
the other initialized quantities to finitely many residue classes.

## Exact statement

Write \(O(x)=\operatorname{isqrt}(x^3)\) and
\(E(x)=\operatorname{isqrt}(x)\). For a prescribed OOE block
\(x\to u\to v\to z\), its first remainder and endpoint aggregate are
\[
R_1=x^3-u^2,\qquad \mathcal E=x^9-z^8.
\]
On odd endpoints the full guard is \(x,u\) odd and \(v\) even.

For every fixed finite collection of positive integer moduli, there
are two exact OOE first returns sharing the full threshold and return
section, with equal \(R_1=0\), equal residues of \(x,u,z,\mathcal E\)
for every modulus in the collection, and equal
\(\nu_2(\mathcal E)=3\), but opposite guards. Hence no function of
just those data can recognize the guard on the entire geometric
return domain. Periodic-set membership is not assumed or established.

## Current literature

**Internal exact results; external priority not claimed.**
The word OOE and the two chronological updates
\((A,B)\mapsto(A,AB)\), \((A,B)\mapsto(AB,B)\) are established in the
[Euclidean-induction dossier](juggler_cycle_cubic_induction.md).
The existing exact-remainder repair remains valid. The
[GlobalDefect module](../../formal/Problems/Juggler/GlobalDefect.lean)
already supplies aggregate composition; it is not a new theorem here.
The dyadic factorization and mismatch identities below are elementary
background checks applied to these proposed summaries. No literature
survey or novelty claim beyond this project is made.

## Branch budget

Mathematical target: Can fixed, explicitly initialized arithmetic fields determine the endpoint and complete parity guard of every Euclidean-induced return word, with update formulas under both (A,B) -> (A,AB) and (AB,B) that avoid traversing constituent guards?

Novelty hypothesis: Exact square remainders or a parity-sensitive aggregate may admit a composition identity carrying more than endpoint parity, and perhaps a nonnegative cycle obstruction.

Falsifier: The candidate is the existing aggregate-defect identity, a packed parity list, a mismatch count initialized by traversal, or a fixed-register evaluator whose expression still grows with the word.

Already killed by?: Endpoint-only guards, bounded additive pure-power substitution, generic local-cell reformulations and the unweighted aggregate modulo 2 are closed. The exact-remainder short-block repair survives; this gate asks for a new uniform update identity rather than repeating it.

Existing machinery: Exact square cells, repaired OOE quotient, OE/OOE/OOEOE identities, GlobalDefect composition, Euclidean rank towers, seven archived threshold cycles, and their lossless exact traces.

Maximum Phase-0 scope: Analytic audit of exact-remainder, dyadic-residue and nonnegative parity-aggregate candidates under the two substitutions. At most a finite set of explicit discriminating traces and replay of the seven archived cycles; no new source census, cycle search, trajectory cap extension or descent floor. Formalization and probe packaging only after a nontrivial statement survives.

Promotion criterion: A faithful whole-word arithmetic closure theorem with a precise complexity bound, or a new proved restriction on a cycle beyond the original full-word guard and finance.

Stop criterion: Preserve any scoped mathematical result, identify the exact missing invariant, and CLOSE the tested reformulation or PARK the unresolved broader target without automatically opening another branch.

Exact verification scope, fixed after the analytic counterfamily survived separate audits and before probe implementation: the six literal even moduli Q=2,6,16,210,65536,4294967296, with the least admissible b=3 mod4 for each; the two closed-form OOE traces per modulus; and only the seven previously archived threshold cycles. No parameter or word census.


## Balanced-ternary formulation

All fields are integers; the obstruction is independent of their representation.

## Why BT may be relevant

No balanced-ternary advantage is used or claimed.

## Candidate operations / invariants

The candidates were fixed residue data plus an initialized exact first
remainder, the dyadic valuation of the global aggregate, and a
nonnegative parity-error quantity. A fixed count of unbounded integer
registers is a different model from a fixed collection of residue classes.
Any future claim must specify both the retained quantities and the
permitted initialization and update operations.

## Experiments

The [exact probe](../../src/research/juggler_sequence/cycle_guard_residues.py)
replays [summary.json](../../data/research/juggler/cycle_guard_residues/summary.json):

    python -m research.juggler_sequence.cycle_guard_residues

The [tests](../../tests/research/juggler_sequence/test_cycle_guard_residues.py)
certify every adjacent square cell, all common residues, the opposite
guards, and the shared threshold/first-return section. They also check
that the earlier absolute quotient repair correctly distinguishes the pair.
This prevents interpreting the present obstruction as a refutation of
that repair.

The six literal even moduli are \(2,6,16,210,65536,4294967296\), with
two closed-form blocks per modulus. For each, the probe takes the least
\(b\equiv3\bmod4\) satisfying the proved bound. These are verification
instances of a quantified construction, not a source census.
Seven previously archived threshold cycles supply the dyadic and parity-energy
checks. The odd-fixed-point valuation is tested only when the minimum
is odd; the other archived cycles are not silently assigned that hypothesis.
No cycle search, trajectory extension or descent-floor increase is performed.

## Conjectures

No new conjecture file is opened. Uniform arithmetic closure on full
absolute data and a contradiction on periodic sets remain unproved.

## Counterexamples

Result 1 gives the infinite counterfamily for every fixed collection
of residue moduli. The two blocks share exact threshold cells and
first-return geometry, but only one satisfies the prescribed parity.
They are not asserted to be periodic points.

## Formalization

Current declaration-level coverage is recorded in Paper A, Appendix A,
and its [formalization map](../theory/juggler_finite_dynamics_formalization.md).
The canonical Lean files are in `formal/Problems/Juggler/` and are imported
by `Problems.JugglerPaper`. The theorem ledger distinguishes the compiled
statements from the additional written consequences. No general no-cycle
or escape-exclusion theorem is claimed.

## Results

The current statements and proofs are consolidated in **Appendix E.6** of
[Paper A](../theory/juggler_finite_dynamics_note.md).
That manuscript is the canonical editorial source. This dossier retains
the original branch budget, controls, limitations and decision record;
it is not a second editable copy of the proof.

## Open questions

The counterfamily closes fixed residue summaries of the specified
initialized data. It leaves formulas using full absolute quotients,
newly certified later remainders, precision increasing with depth,
or restrictions valid only on periodic points open.
The exact-remainder quotient repair already uses full values, and
continues to distinguish the constructed pair correctly.

Neither aggregate saturation nor mismatch-energy bookkeeping supplies
a new restriction on possible cycle counts, a decreasing quantity,
or a wrong-parity intersection theorem.

## Decision

**CLOSE** the tested fixed-residue extension and the proposed
aggregate/energy bookkeeping shortcuts. Preserve the exact counterfamily.
The broader absolute-data closure target remains open; no claimed
complexity lower bound applies to all integer-register algorithms.

The one best next question is: **can exact periodicity force a
wrong-parity carry in the joint OOE/OE first-return partition, uniformly
over the threshold?** This places the missing constraint on the
cycle-selected absolute carries. Another fixed residue modulus or
another open-block endpoint identity will not answer it.

## Publication assessment

Status: **STRUCTURAL**. The results are now consolidated into Paper A,
Appendix E.6, with the formal scope recorded beside the claims.
The certified period floor remains 780239. This consolidation is a local
revision; it does not upload a new Zenodo version.

## Authorized periodicity continuation

The [periodic carry gate](juggler_cycle_periodic_carries.md) uses a
complete periodic set to derive the additional necessary bound
M<m^3-m^(15/8) for m>=7 in the cubic-height class. Its exact proof
uses adjacent return images and absolute square cells. It leaves
the fixed-residue obstruction above intact and does not exclude
the remaining threshold cycles or taller cycles.

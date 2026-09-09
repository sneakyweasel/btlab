# Exact parity carries and failure of a bounded substitution rule

Status: **CLOSE** for the tested bounded additive substitution.
Authorized continuation, 9 September 2026. The broader arithmetic
closure question remains open.

**An OE block has an exact parity guard using one integer quotient and
a three-valued correction. That correction rule does not close under
the tested pure-power substitution at the next OOE return.** An infinite
family of fully parity-valid blocks has a one-integer endpoint correction,
while the substituted internal quotient is wrong by
\(36r^2\) or \(36r^2+1\). Its clipped displacement error is exactly
\(27r^2\). These are statements about finite blocks and a specified
substitution rule; no cycle is excluded.

## Problem

The [preceding induction gate](juggler_cycle_cubic_induction.md) proved
symbolic closure and short endpoint identities but retained every
internal parity condition. The user authorized its next question:
can fixed arithmetic data carry those conditions through induction?
This investigation tests one concrete quotient-and-correction family.

## Exact statement

Initially \(O(x)=\lfloor\sqrt{x^3}\rfloor\) and
\(E(x)=\lfloor\sqrt x\rfloor\), with chronological word concatenation.
The exact OE endpoint is \(y=\lfloor x^{3/4}\rfloor\).
After expressing its hidden intermediate state using a quotient and
a uniformly bounded correction, ask whether the same family survives
OOE by replacing the eliminated \(O(x)\) with \(x^{3/2}\) in that
quotient, with a correction bounded independently of the source.

A meaningful broader closure would need fixed meanings for its
arithmetic fields, fixed endpoint and guard formulas, and fixed update
formulas under both Euclidean substitutions. Formula length and nesting
depth must be controlled as well as field count. Initializing the fields
by traversing the whole word, or packing its parity list into one integer,
does not meet this gate. A guard-recognition domain cannot already assume
all the hidden parities. The counterfamily below satisfies all of them,
so it is stronger than a failure on a wrongly prescribed branch.

## Current literature

**Internal exact calculation; external priority not claimed.** The
starting rank geometry is [Paper A, Section 3.10](../theory/juggler_finite_dynamics_note.md).
The short endpoint identities and faithful tower predicates are in
the preceding induction dossier. The secondary fiber observation below
is a consequence of the existing
[cube-fiber results](juggler_oe_fiber_share.md), not a new fiber theorem.
No literature survey or general complexity lower bound is claimed.

## Branch budget

The following gate was written before implementation.

- **Target:** exact arithmetic data preserving hidden parity under
  Euclidean return-word substitution.
- **Novelty hypothesis:** absolute endpoint cells give a quotient and
  a bounded carry that might remain closed under substitution.
- **Falsifier:** replacing an eliminated source by its pure power needs
  an unbounded correction, or exact evaluation still needs an additional
  source-dependent residue with no closed update.
- **Already killed by?:** endpoint-only omission, generic local-cell
  descriptions, residue-only slogans, and the original word recursion.
  The present test requires a specific new exact arithmetic identity.
- **Existing machinery:** exact OE/OOE/OOEOE endpoint identities,
  square cells, rank-prefix towers, and transported floor loss.
- **Maximum Phase-0 scope:** the OE quotient law and one OOE substitution;
  literal boundary and infinite-family controls. No enlarged source
  scan, cycle census, floor, orbit cap, or separate attack.
- **Promotion criterion:** faithful closure with a stated uniform
  complexity bound or a new decreasing cycle quantity.
- **Stop criterion:** record the exact law and failure of the tested
  extension, then decide without automatically opening another route.

## Balanced-ternary formulation

All states, quotients and square remainders are integers. Balanced-ternary
representation changes none of the equations or parity conditions.

## Why BT may be relevant

No representation advantage or new dependency on the BT core is used.

## Candidate operations / invariants

Given an OE source and endpoint, divide \(x^3-y^4\) by \(2y^2\), clip
the quotient at \(2y\), and use two square comparisons to select a
correction in \(\{0,1,2\}\). The full source square remainder becomes
relevant when the source itself is the output of an earlier floor.
The total mismatch count of a return tower is additive, but evaluating
it from the original states already performs all the parity tests;
its existence does not supply a compressed recognition rule.

## Experiments

The existing [induction verifier](../../src/research/juggler_sequence/cycle_cubic_induction.py)
now has the explicit mode:

    python -m research.juggler_sequence.cycle_cubic_induction --guard-carries

It replays [guard_carries.json](../../data/research/juggler/cycle_cubic_induction/guard_carries.json)
using integers throughout, with
[regression tests](../../tests/research/juggler_sequence/test_cycle_cubic_induction.py).

- 4,351 square-cell boundary instances: \(1\le y\le32\),
  \(0\le c\le2y\), \(u=y^2+c\), and offsets
  \(0,1,2u-1,2u\), deduplicated.
- The exact sharp OE example \(93\to896\to29\).
- Six literal members of the proved OOE family:
  \(r=3,5,11,101,10^6+1,10^{20}+1\).
- Four cube-fiber controls at \(s=3,5,11,101\), containing respectively
  3, 4, 8 and 68 source points.

The first controls verify the general square-cell normal form below;
their radicands need not be cubes. The OOE family controls separately
check genuine Juggler source parities, all exact cells, cubic height,
the sharp quotient inequalities, and the one-integer endpoint identity.
These controls illustrate the quantified proofs; they do not establish
them by exhaustion. No cycle search or expanded source scan is performed.

## Conjectures

No new conjecture file is opened. General arithmetic guard closure
remains unproved, and the present family does not refute it.

## Counterexamples

Result 2 is an infinite counterexample to a bounded additive correction
for the specified quotient substitution. Every source parity is valid.
The block is not closed. No family member is shown to lie on a periodic
orbit, so a representation using additional global cycle constraints
is not refuted. Its correction magnitude is unbounded but
has a simple formula on this family, so it is not an impossibility
theorem for fixed-dimensional arithmetic data or parity-only formulas.

## Formalization

Current declaration-level coverage is recorded in Paper A, Appendix A,
and its [formalization map](../theory/juggler_finite_dynamics_formalization.md).
The canonical Lean files are in `formal/Problems/Juggler/` and are imported
by `Problems.JugglerPaper`. The theorem ledger distinguishes the compiled
statements from the additional written consequences. No general no-cycle
or escape-exclusion theorem is claimed.

## Results

The current statements and proofs are consolidated in **Appendix E.3** of
[Paper A](../theory/juggler_finite_dynamics_note.md).
That manuscript is the canonical editorial source. This dossier retains
the original branch budget, controls, limitations and decision record;
it is not a second editable copy of the proof.

## Open questions

Retaining the exact source square remainder avoids the false replacement
in Result 2. A useful induction theorem would need fixed update formulas
for such data, with bounded expression length and nesting, through both
substitutions. The current computation does not provide them. Neither
the number of fields required nor the impossibility of a better parity
formula has been proved.

## Decision

**CLOSE** the tested bounded additive carry extension. Result 1 supplies
an exact one-block guard; Result 2 refutes its proposed pure-power
substitution, even on genuine blocks in cubic bands. The broader
arithmetic closure tactic remains open and is not promoted. A larger
scan would not repair this infinite counterfamily.

The one best next question for this arithmetic direction is:
**can the exact square-remainder information be updated through both
Euclidean substitutions by fixed formulas, without reconstructing the
entire intermediate word?** Any continuation must specify those formulas
before more computation. This record does not automatically start it.

## Publication assessment

Status: **STRUCTURAL**. The results are now consolidated into Paper A,
Appendix E.3, with the formal scope recorded beside the claims.
The certified period floor remains 780239. This consolidation is a local
revision; it does not upload a new Zenodo version.

## Authorized exact-remainder continuation

[Finite family chains and remainder transport](juggler_cycle_remainder_transport.md)
proves that this exact three-step family cannot concatenate indefinitely:
the 2-adic valuation of a continuing parameter minus 1 decreases by 2.
All six retained parameter examples reach 1 in finite exact computations.
Keeping the actual source square remainder also repairs the suffix
quotient to within one integer and recovers the full OOE guard.
The bounded additive replacement refuted here remains false; the new
repair retains additional absolute-state information. General orbit
escape, universal family termination and uniform word closure remain open.


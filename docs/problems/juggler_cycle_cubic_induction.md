# Euclidean induction of cubic-band Juggler cycles

Status: **PARK**. Authorized bounded investigation, 9 September 2026.

**Exact rank induction closes with two symbolic branches. A uniformly
controlled arithmetic description including every parity condition has
not been proved.** Exact endpoint identities survive for OE, OOE and
OOEOE. An infinite counterfamily shows why their endpoint values and
endpoint parity cannot replace the eliminated source-parity conditions.
This is not a no-cycle proof or a new numerical period bound.

## Problem

Test the first-ranked no-cycle attack after the user's "Proceed":
Euclidean induction of the exact rank rotation in a cubic band, preserving
absolute floor cells and parity. The underlying cycle order is already
proved in [Paper A, Section 3.10](../theory/juggler_finite_dynamics_note.md).
The prior [absolute-cell investigation](juggler_cycle_absolute_cells.md)
left uniform wrong-parity intersection open.

## Exact statement

Let a finite sorted invariant set have lower and upper rank lengths
\(a,b>0\), and successor rank \(i\mapsto i+b\pmod{a+b}\).
Initially its branch maps are
\(O(x)=\lfloor\sqrt{x^3}\rfloor\) and \(E(x)=\lfloor\sqrt x\rfloor\).
Does successive induction on a rank prefix preserve a family of return
maps **and full source-parity predicates** with complexity bounded
independently of the original period, or supply a decreasing arithmetic
quantity that contradicts a parity-compatible cycle?

This gate addresses the class \(M<m^3\), where \(m>1\) and \(M\) are the
cycle extrema. Taller cycles remain separate. The conclusions below do
not settle the existence of a stronger arithmetic representation.

## Current literature

**Reproduced elementary induction and root identities; external priority
not claimed.** This is an internal closure audit built on Paper A's
proved rank permutation. No external literature survey or new general
theory of induction is claimed. The distinction from the closed
[method ceilings](juggler_cycle_method_ceilings.md) is the explicit test
of arithmetic identities for globally constrained return words. A nested
word rewrite alone would add no cycle obstruction.

## Branch budget

The triage was written before substantial implementation.

- **Target:** faithful, uniformly controlled arithmetic closure under
  Euclidean induction.
- **Novelty hypothesis:** the proved global permutation may restrict
  return words enough to yield exact endpoint and parity identities.
- **Falsifier:** only symbolic closure survives; internal parity
  conditions keep growing, or a proposed shortcut fails an exact block.
- **Already killed by?:** generic peak-valley composition, floor-Hardy
  rewrites, unconditional mechanical windows and finance-only improvements.
  This expressly authorized gate must produce an additional identity.
- **Existing machinery:** Paper A's rank rotation, exact integer cells,
  seven archived threshold cycles, and the altered-map controls.
- **Maximum Phase-0 scope:** analytic first returns and parity transport,
  small bounded source tests and archived cycles. No enlarged cycle
  census, descent floor, large-orbit cap or second attack.
- **Promotion criterion:** an arithmetic closure or decreasing quantity
  stronger than evaluating the entire original word.
- **Stop criterion:** retain scoped identities and obstructions; park the
  broader tactic if no faithful arithmetic closure is obtained.

## Balanced-ternary formulation

The states and integer square cells may be represented in balanced
ternary. Their values, ordering and parity conditions are unchanged.

## Why BT may be relevant

No representation advantage or dependence on the core BT package is
used in this investigation.

## Candidate operations / invariants

Chronological concatenation \(AB\) means execute \(A\), then \(B\):
\(F_{AB}=F_B\circ F_A\). The exact predicate composition is
\(P_{AB}(x)=P_A(x)\land P_B(F_A(x))\).
Tower length, letter counts and the total logarithmic exponent are
preserved by induction. Counting two named branches does not bound
the complexity of their arithmetic predicates.

## Experiments

The [exact verifier](../../src/research/juggler_sequence/cycle_cubic_induction.py)
and [tests](../../tests/research/juggler_sequence/test_cycle_cubic_induction.py)
replay [controls.json](../../data/research/juggler/cycle_cubic_induction/controls.json).
Run \(\texttt{python -m research.juggler_sequence.cycle_cubic_induction}\).
All archived comparisons use integers; no numerical roots or logarithms
enter this final verification.

For each selected word, all 32,767 odd sources from 3 through 65,535
were checked for its exact source parities and an odd final output.
Every fully admissible trace found also satisfies
\(\max(\text{trace})<\min(\text{trace})^3\). For each such trace, with
\(o_W\) odd letters, length \(k\), and final value \(y\), the verifier
checks the exact odd-projection cell
\[
y^{2^k}\le x^{3^{o_W}}<(y+2)^{2^k}.
\]

| Word | Formal exponent | Admissible odd endpoints | Projection failures |
|---|---|---:|---:|
| O | \(3/2\) | 16,379 | 0 |
| OE | \(3/4\) | 8,181 | 0 |
| OOE | \(9/8\) | 4,125 | 0 |
| OOEOE | \(27/32\) | 1,002 | 0 |
| \((OOE)^2OE\) | \(243/256\) | 152 | 0 |
| \((OOE)^3OE\) | \(2187/2048\) | 14 | 0 |
| \(AB^2,\ A=OOE,\ B=(OOE)^2OE\) | \(531441/524288\) | 0 | 0 |

The last row has no admissible sample; it gives no positive evidence for
that word's endpoint formula. These finite checks do not prove a uniform
identity. They replace an exploratory floating screen on exactly the
same range; the range was not enlarged.

Separately, literal first returns verify every induction stage for the
1,024 rank-length pairs \(1\le a,b\le32\), including nonprimitive
permutations. The seven already archived threshold cycles at
\(b=3,9,29\) verify all exact return traces and preservation of their
original number of parity mismatches through every stage. This reuses
existing cycles and performs no cycle search.

## Conjectures

No new conjecture file is opened. A uniform endpoint formula for all
induced words, and a bounded family also carrying parity, remain unproved.

## Counterexamples

Result 3 gives an infinite family of threshold OE blocks at unbounded
scales whose odd endpoints hide an odd intermediate E-source. Literal
examples for \(s=3,5,101\) are retained in the control data. These are
blocks, not closed cycles, and they do not refute guarded compression.
The exact admissible trace \(201\to2849\to152068\to389\), while
\(\lfloor201^{9/8}\rfloor=390\), also shows that OOE cannot universally
be replaced by the ordinary floor without its one-integer correction.

## Formalization

Current declaration-level coverage is recorded in Paper A, Appendix A,
and its [formalization map](../theory/juggler_finite_dynamics_formalization.md).
The canonical Lean files are in `formal/Problems/Juggler/` and are imported
by `Problems.JugglerPaper`. The theorem ledger distinguishes the compiled
statements from the additional written consequences. No general no-cycle
or escape-exclusion theorem is claimed.

## Results

The current statements and proofs are consolidated in **Appendix E.1--E.2** of
[Paper A](../theory/juggler_finite_dynamics_note.md).
That manuscript is the canonical editorial source. This dossier retains
the original branch budget, controls, limitations and decision record;
it is not a second editable copy of the proof.

## Open questions

The rank algorithm reduces the number of retained states, but its
faithful expanded predicate still contains every original parity test.
This is a fact about that representation, not a lower bound for all
possible compressed representations. Short endpoint identities and
fixed-word asymptotic error bounds have not supplied a uniform bound on
the guards or a terminal contradiction.

## Decision

**PARK.** Retain the exact short-return identities, the faithful tower
recursion, and the infinite obstruction to omitting internal parity.
The tested endpoint-only shortcut is refuted. The broader induction
tactic is not refuted, but its promotion criterion has not been met.
The one best next question is: **can a finite collection of arithmetic
quantities, closed under the exact Euclidean substitutions, determine
every transported parity predicate without evaluating the full word?**
Repeating the same word recursion or increasing the source scan does
not answer that question. This decision does not automatically open
another attack.

## Publication assessment

Status: **STRUCTURAL**. The results are now consolidated into Paper A,
Appendix E.1--E.2, with the formal scope recorded beside the claims.
The certified period floor remains 780239. This consolidation is a local
revision; it does not upload a new Zenodo version.

## Authorized parity-carry continuation

The next bounded question is answered in
[Exact parity carries](juggler_cycle_guard_carries.md). An OE quotient
and three-valued correction give its exact hidden guard. An infinite
fully parity-valid OOE family defeats the tested pure-power substitution:
the quotient discrepancy grows as 36r^2 and its clipped offset error is
exactly 27r^2 despite a one-integer endpoint correction. That extension
is CLOSE; this dossier's broader arithmetic closure question remains open.


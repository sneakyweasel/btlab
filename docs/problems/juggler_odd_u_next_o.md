# Juggler odd \(u\) next `O`

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a bunched-short
tail table, not a leftover-suffix path, not a predecessor-cell census,
not a \(Z_5\) family, not a length-11 assembler, not a four-even leftover
cell, and not a claim that every positive integer reaches 1.

The terminal-cluster program stays frozen. This is the designated
next question of the promoted \(W_5\) second-`OO` branch: odd
\(u\) after the first \(n^5\) corridor.

## Envelope scope

A failed exponent comparison means that the inherited upper envelope does
not certify the proposed descent or cell bound. It gives no lower bound on
an actual orbit and does not prove absence of `FiniteProgress`. Negative
claims labelled REFUTED below concern deductions from this envelope test;
separate explicit orbit counterexamples retain their stated finite scope.

## Problem

If \(u=T(z)\) is odd, what inherited corridor does the next
`O` occupy, and does the even pullback return to a named
\(C_1\)–\(C_4\) band?

## Exact statement

Assume \(n\ge 2\) follows \(W_5=M(\mathtt{OOE})^5\) with
\(M=\mathtt{OOEOOOEOOEEOOE}\), that \(x_5\), \(y=T(x_5)\),
and \(z=T(y)\) are odd, and that \(u=T(z)\) is odd. Write
\(v=T(u)\). The Phase-0 questions are:

1. the inherited envelope of \(v\), not generic \(v<n^{12}\)
   from \(u<n^8\);
2. the first integer \(m\) with \(v<n^m\);
3. whether even \(v\) resets to \(C_1\), \(C_2\), \(C_3\), or
   \(C_4\);
4. whether the integers \(3,4,5,8,11\) are a new rung law
   or the crossings of
   \(\alpha_k=(3/2)^k\cdot 3^{19}/2^{29}\).

Lower bounds \(v\ge n^8\) or \(v\ge n^5\) are **not**
axioms of the lost eighth-power cell.

## Current literature

- Odd \(y\) gives \(z<n^5\); odd \(z\) gives \(u<n^8\);
  even \(z\) resets below \(n^{5/2}\); even \(u\) resets
  below \(n^4\) —
  **EXACT — HUMAN PROOF** (`J-cyclemin-w5-second-oo-z-fifth`).
- The inherited envelope certifies \(u<n^5\) —
  **REFUTED**.
- Odd \(x_5\) gives \(y<n^4\); `OEE` contracts —
  **EXACT — HUMAN PROOF**.
- \(W_5\) cube cell \(x_5<n^3\) —
  **EXACT — HUMAN PROOF**.
- Bunched-short / \(Z_5\) / terminal cells —
  **PARK**. Frozen. Not reopened.

Project relationship: **extended**. The designated next
question of the promoted second-`OO` branch.

## Branch budget

```text
Mathematical target     odd-u next-O corridor / first integer
Novelty hypothesis      n^{11}; even reset to C_1-C_4
Falsifier               only generic 12; no finite ceiling;
                        even v is a new unbounded hierarchy
Existing machinery      u < n^8; power_bound_word
Maximum Phase-0 scope   v gaps; even n^6; crossings; 501;
                        no Lean
Promotion criterion     exact v-envelope sharper than generic
                        plus a parity split
Stop criterion          generic 3/2 only; suffix automaton;
                        Z5 / length-11 / four-even / p-adic
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- \(W_5+\mathtt{OOOO}\) has length 33 and 23 odds, so
  \(v^{2^{33}}\le n^{3^{23}}\) —
  **EXACT — HUMAN PROOF**.
- The tenth-power cell fails:
  \(3^{23}>10\cdot 2^{33}\) —
  **EXACT — HUMAN PROOF**. The envelope does not exclude crossing
  \(n^8\); no orbit realizing such a crossing is asserted.
- The eleventh-power cell holds:
  \(3^{23}<11\cdot 2^{33}\), hence
  \(v\le n^{3^{23}/2^{33}}<n^{11}\) —
  **EXACT — HUMAN PROOF**. Slack under \(11\) is
  \(346101685\). This is the first integer, not a
  convenient one.
- Inherited beats generic \(v<n^{12}\) from \(u<n^8\):
  \(3^{23}<12\cdot 2^{33}\) —
  **EXACT — HUMAN PROOF**.
- \(v\ge n^8\) is forced —
  **REFUTED** as a deduction.
- The inherited envelope certifies an even-\(v\) reset to \(C_1\)–\(C_4\) —
  **REFUTED**. \(3^{23}>4\cdot 2^{34}\), and also
  \(n^2\), \(n^3\), and \(n^5\) fail.
- Even \(v\) resets below \(n^6\):
  \(3^{23}<6\cdot 2^{34}\) —
  **EXACT — HUMAN PROOF**. Same comparison as the
  generic-\(12\) gap. This is a new even-reset band,
  still finite, not an unbounded hierarchy. Even \(v\)
  cannot start \(L\).
- The inherited tests certify `OE`/`OOE`/`OEE` from \(u\) below \(n\) —
  **REFUTED**.
- After \(W_5\) plus \(k\) extra odds the first integers
  are \(3,4,5,8,11\) for \(k=0,\ldots,4\). These are the
  crossings of \(\alpha_k=(3/2)^k\cdot 3^{19}/2^{29}\) —
  **EXACT — HUMAN PROOF**. \(n^{11}\) is not a new
  structural rung.
- The post-\(L\) odd residual has a finite set of
  formal envelope exponents under arbitrary repeated `O` updates —
  **REFUTED**. Repeated `O` multiplies the ceiling by
  \(3/2\).
- The envelope certifies a next `O` from odd \(v\) below \(n^{16}\) —
  **REFUTED**. It stays below \(n^{17}\). That is the
  leftover, not a hierarchy.
- \(501\) realizes odd \(u\) —
  **REFUTED**.
- same episode signature recurs — not claimed
- bunched-short `CycleMin` is impossible — not claimed
- every cycle itinerary is impossible — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.odd_u_next_o`
- Records: [juggler_odd_u_next_o.md](../research/juggler_odd_u_next_o.md),
  [juggler_odd_u_next_o.json](../research/juggler_odd_u_next_o.json)
- Tests: `tests/research/juggler_sequence/test_odd_u_next_o.py`
- The envelope core is in `CycleMinEnvelopes.lean`; see Formalization. No
  `sorry`. No halt theorem.

## Conjectures

None opened.

## Counterexamples

The hypothesis that only generic \(v<n^{12}\) survives, or
that \(n^{11}\) is a new structural rung, is **REFUTED**
by

\[
3^{23}>10\cdot 2^{33},\qquad 3^{23}<11\cdot 2^{33},\qquad
3^{23}<12\cdot 2^{33}.
\]

The claim that this envelope certifies an even-\(v\) return to
\(C_1\)–\(C_4\) is **REFUTED**: the first integer-power upper
bound supplied by the test is \(n^6\). No lower bound follows.

The formal envelope iteration has infinitely many distinct exponents
under \(\mathrm{O}:\alpha\mapsto\tfrac32\alpha\). This refutes
a finite state set for that iteration, without proving that actual
orbits realize arbitrarily long odd continuations.

`501` never follows \(W_5\). No \(W_5\) follower occurs in
the Phase-0 window \(12\le n<801\).

## Formalization

The envelope core is formalized in
[CycleMinEnvelopes.lean](../../formal/Problems/Juggler/CycleMinEnvelopes.lean).
The canonical ledger rows `J-cyclemin-odd-u-v-eleventh`
name the matching declarations. Negative declarations with
`exponent_not_lt` in their names prove only failure of the exponent
test. They do not prove non-descent or non-termination.

## Results

Classification **ODD_U_NEXT_O_GREEN**.

If \(u\) is odd, then

\[
v^{8589934592}\le n^{94143178827}<n^{94489280512}=(n^{11})^{8589934592},
\]

so

\[
v\le n^{3^{23}/2^{33}}<n^{11}.
\]

The primary object is the rational ceiling
\(3^{23}/2^{33}\). The integer \(11\) is where that
ceiling crosses. Inherited history still beats generic
\(n^{12}\).

The envelope does not certify an even-\(v\) reset to a previously
named \(C_1\)–\(C_4\) band. It instead gives:

\[
v\text{ even}\Rightarrow T(v)\le n^{3^{23}/2^{34}}<n^{6}.
\]

That is a downward reset from \(n^{11}\), but a new even
band. The leftover is odd \(v\), whose next `O` stays
below \(n^{17}\).

This is not \(Z_5\), not a length-11 census, not a four-even
assembler, and not a halt theorem.

## Open questions

The eleventh-power bound and even-\(v\) sixth-power reset are
formalized in `v_bound` and `v_even`. The parity-persistence question is the
separate branch
[juggler_parity_persist.md](juggler_parity_persist.md).
Do not reopen bunched-short cells. Do not write \(Z_5\).
Do not assemble `no_cycle_itinerary_length_eleven`. Do not
build a \(p\)-adic system. Do not add another power-bound
phase.

## Decision

**PROMOTE**. The inherited constraint survives one more
`O`: \(v\le n^{3^{23}/2^{33}}<n^{11}\), strictly below
generic \(n^{12}\). Even \(v\) resets below \(n^6\); this envelope
does not certify the narrower \(C_1\)–\(C_4\) bound. The integers \(3,4,5,8,11\) are
crossings of a single rational sequence, not a new rung
law. The exponent-chain approach remains constrained, but
it is no longer producing named even-resets into old
corridors.

Best next question: does a parity constraint force the
odd-\(u\) run to hit an even landing before \(\alpha\)
grows another \(3/2\), or has the leftover become an
unconstrained odd run?

## Publication assessment

Status: `THEOREM`.

A named exact eleventh-power envelope, failure of its exponent test
for the \(C_1\)–\(C_4\) even reset, and the identification of the
integer sequence as rational crossings. Not a Juggler
totality result and not a finite exponent-state system.

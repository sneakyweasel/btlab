# Exact mixed-pair descent for the modified Juggler map

Status: **PROMOTE** the bounded structural result below. The map is A095396,
with even exponent \(2/3\), not the original Juggler map. Evidence is
**EXACT — HUMAN PROOF**, supported by finite integer regressions.
No global termination or research-priority claim is made.

## Problem

Which two-step descent statements survive when the even exponent changes
from \(1/2\) to \(2/3\), reciprocal to the odd exponent \(3/2\)?

## Exact statement

For \(n\in\mathbb N\), define the unrestricted branch functions
\[
O(n)=\lfloor n^{3/2}\rfloor=\operatorname{isqrt}(n^3),\qquad
E(n)=\lfloor n^{2/3}\rfloor=\operatorname{icbrt}(n^2).
\]
Let \(F(n)=O(n)\) for odd \(n\), and \(F(n)=E(n)\) for even \(n\).

1. \(E(O(n))=n\) if \(n\) is a perfect square, and \(E(O(n))=n-1\)
   otherwise. The nonsquare case necessarily has \(n>0\).
2. \(O(E(n))\le n\), with equality if and only if \(n\) is a perfect cube.
3. If \(n\) is odd and \(F(n)\) is even, then \(F^2(n)=n-1\).
4. If \(n>0\) is even and \(F(n)\) is odd, then \(F^2(n)<n\).

In particular there is no positive two-cycle with two distinct elements.
This is only a consequence for length two; longer cycles and termination
are not settled.

## Current literature

[A095396](https://oeis.org/A095396) defines this map; the local entry
revision is #17, 28 December 2018. Its comments compare it with A094683.
The source is the local OEIS export of 20 September 2026, revision
`9cee00061c60192aafbc74726ce4a83ca7040d81`
(OEIS Foundation, CC BY-SA 4.0).

The [existing neighbourhood dossier](juggler_oeis_neighbourhood.md) and
[negative knowledge](../negative_knowledge.md) explicitly left this variant
untested. That is an observation about this repository, not a statement that
the elementary floor identities are absent from the literature.

Project relationship: **extended** locally. Novelty: **OPEN**; no broad
priority claim is supported by a single OEIS entry.

## Branch budget

```text
Mathematical target     Which descent lemmas survive when the even exponent becomes 2/3?
Novelty hypothesis      Reciprocal exponents may yield a useful floor-sensitive lemma.
Falsifier               Only the existing exponent-product inequality remains.
Already killed by?      No: the OEIS dossier explicitly leaves this variant untested.
Existing machinery      Juggler word bounds and exact integer arithmetic.
Maximum Phase-0 scope   Mixed two-step words, equality cases, finite regressions.
Promotion criterion     A precise consequence beyond renaming the exponent bound.
Stop criterion          No additional consequence, or established prior art covering it.
```

## Balanced-ternary formulation

No special numeral representation is used. The proof concerns ordinary
nonnegative integers and exact square and cube roots.

## Why BT may be relevant

No role is claimed.

## Candidate operations / invariants

The exponent product is one, but floors cannot simply be cancelled.
The exact equality conditions, together with actual branch parity, determine
whether the formal cancellation can be realized by an orbit.

## Experiments

Runner: `python tools/lab.py run research.juggler_sequence.modified_juggler_descent --write`.

[Probe](../../src/research/juggler_sequence/modified_juggler_descent.py),
[tests](../../tests/research/juggler_sequence/test_modified_juggler_descent.py), and
[exact report](../../data/research/juggler/modified_juggler_descent/verification.json).

All four assertions were checked at \(0\le n\le10000\), with the positive
domain enforced for actual EO pairs. This contains 2495 actual OE pairs and
2494 actual EO pairs. The first examples are \(7\to18\to6\) and \(2\to1\to1\).
The tests independently check the first 32 OEIS map values and square/cube
boundaries for roots up to \(10^{40}+1\); no floating-point roots are used.

## Conjectures

None. In particular the finite tests do not imply that every orbit reaches 1.

## Counterexamples

The unrestricted branch compositions need not strictly descend:
\(E(O(9))=E(27)=9\), but the intermediate value 27 is odd, so OE is not
realized; \(O(E(8))=O(4)=8\), but 4 is even, so EO is not realized.
Thus neither formal equality is an actual two-cycle.

These witnesses are regression tests in the branch test file above.

## Formalization

Formalpedia was searched for floor composition and odd-even descent before
adding this statement. The complete interface of
`Problems.Juggler.power_bound_follows`
was inspected: it concerns the original map's `floorPower`, so it is
not a Lean proof of the modified map's identity.

No new Lean module was added and no Lean verification label is claimed.

## Results

### Exact branch identities — written proof

For \(n=0\) both statements are immediate. Suppose \(n\ge1\), and set
\(b=O(n)\), \(a=E(b)\). By the defining integer root inequalities,
\[
a^3\le b^2\le n^3,
\]
so \(a\le n\). Also
\[
n^{3/2}-(n-1)^{3/2}\ge1.
\]
For \(n=1\) this is equality; for \(n\ge2\) it follows by integrating
\((3/2)\sqrt x\ge3/2\) over \(n-1\le x\le n\).
Since \(b>n^{3/2}-1\), it follows that
\(b>(n-1)^{3/2}\), hence \(E(b)\ge n-1\).

If \(a=n\), the displayed integer inequalities force \(b^2=n^3\).
Unique prime factorization then says \(n=t^2\) and \(b=t^3\).
Conversely, \(n=t^2\) gives exactly these values and \(E(b)=n\).
This proves assertion 1, including its exact one-unit loss off the squares.

For assertion 2, put \(a=E(n)\), \(b=O(a)\). Then
\[
b^2\le a^3\le n^2,
\]
so \(b\le n\). Equality forces \(a^3=n^2\), equivalently \(n=t^3\),
\(a=t^2\), by prime factorization. Conversely these perfect powers attain
equality.

### Realized pairs — written proof

For an actual OE pair, \(n\) is odd and \(O(n)\) is even. If \(n=t^2\),
then \(t\) and \(O(n)=t^3\) are odd, a contradiction. Assertion 1 therefore
gives \(F^2(n)=n-1\).

For an actual EO pair, \(n>0\) is even and \(E(n)\) is odd. Equality in
assertion 2 would give \(n=t^3\), so \(t\) is even and \(E(n)=t^2\) is even,
again a contradiction. Thus \(F^2(n)<n\).

For the two-cycle corollary, mixed pairs strictly descend. Two even steps
strictly descend for positive even starts. Two odd steps strictly increase
for starts at least 3; the remaining odd start 1 is fixed. None can form
a cycle with two distinct positive values.

Evidence: **EXACT — HUMAN PROOF**. Independent finite tests are
**COMPUTATIONALLY VERIFIED** on the stated ranges.

## Open questions

The recorded identities could be formalized using integer root cells.
No implication for the original map, long cycles or global termination has
been established. No broader variant family was investigated.

## Decision

**PROMOTE** the exact one-unit OE descent identity and its equality
classification into the local research record. This is more precise than
the exponent-product bound \(F^2(n)\le n\), and meets the predeclared
structural criterion. Promotion does not assert originality or paper readiness.

Best next question: can the four exact statements above be covered by a
small Lean interface for this modified map? Recorded, not opened.

## Publication assessment

Status: **STRUCTURAL**. A short written result with exact regression checks,
not a new paper or an addition to the existing manuscripts. Independent
review, priority assessment and any desired Lean proof remain separate.

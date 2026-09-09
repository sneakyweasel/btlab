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

The two new results are **AI-assisted written proofs**, with separate
AI audits of the algebra, valuation bound and scope. The repository tag
**EXACT — HUMAN PROOF** names this written-proof tier, not independent
human review. No new Lean verification is claimed.
The existing GlobalDefect composition theorem remains background and
retains its stated `follows` hypotheses for actual Juggler iteration.

## Results

### Result 1 — the exact growth family cannot repeat indefinitely

**J-cycle-ooe-family-chain-bound, EXACT — HUMAN PROOF.**
For an odd \(r\ge3\), the number \(k\) of consecutive transitions
\[
J^3(X(r_i))=X(r_{i+1}),\qquad r_i\ge3\text{ odd},\qquad r_0=r,
\]
is at most
\[
\boxed{\max\left(0,\left\lfloor
\frac{\nu_2(r-1)-2}{2}\right\rfloor\right).}
\tag{F1}
\]
Every immediate transition requires \(r\equiv1\pmod{48}\).
In particular no infinite consecutive family chain exists.

**Proof.** A transition \(r\to s\) is equivalent to
\[
s^8=r^9+9r-9. \tag{F2}
\]
An odd eighth power is \(1\bmod32\). Since \(r^9\equiv r\bmod32\),
(F2) gives \(10(r-1)\equiv0\bmod32\), hence \(r\equiv1\bmod16\).

There is also a restriction modulo 3. If \(r\equiv2\bmod3\), the
right side of (F2) is 2 modulo 3, impossible for an eighth power.
If \(3\mid r\), that right side has 3-adic valuation exactly 2:
\[
r^9+9r-9=9(r^9/9+r-1),
\]
and the parenthesis is \(-1\bmod3\). An eighth power has valuation
divisible by 8. Thus \(r\equiv1\bmod3\), giving the stated modulus 48.

Suppose the transition \(r\to s\) is itself followed by another
family transition. Then both \(r,s\equiv1\bmod16\). Factoring (F2)
after subtracting 1 yields
\[
s^8-1=(r-1)Q(r),\qquad
Q(r)=r^8+r^7+\cdots+r+10.
\]
Here \(Q(r)\equiv18\equiv2\bmod16\), so \(\nu_2(Q(r))=1\).
Also
\[
s^8-1=(s-1)(s+1)(s^2+1)(s^4+1).
\]
Each of the last three factors has 2-adic valuation 1. Consequently
\[
\boxed{\nu_2(s-1)=\nu_2(r-1)-2.} \tag{F3}
\]

In a chain with \(k\ge1\) transitions, all \(k\) source parameters
\(r_0,\ldots,r_{k-1}\) are \(1\bmod16\). Put \(a=\nu_2(r_0-1)\).
The first \(k-1\) transitions have continuing destinations, so (F3)
gives \(a-2(k-1)\ge4\). This is exactly (F1). If \(a<4\), the first
transition is already forbidden. The final endpoint parameter need not
itself be \(1\bmod16\); no drop is asserted after that final transition.

For completeness, continuing transitions also satisfy
\(\nu_3(s-1)=\nu_3(r-1)+2\). Indeed for \(r=1+3j\),
\[
Q(r)\equiv18+108j+756j^2\equiv18\pmod{27},
\]
so \(\nu_3(Q(r))=2\); for \(s\equiv1\bmod3\), the other factors of
\(s^8-1\) displayed above are not divisible by 3. This extra identity
is not needed for the finite bound.

**Scope.** This excludes escape by endless exact three-step concatenation
of this polynomial family. It does not exclude later re-entry after a
different number of steps, another growth pattern, a general escaping
orbit, or a nontrivial cycle. All six sampled parameters fail the
necessary \(1\bmod3\) condition, so their immediate nonreentry also has
a direct congruence certificate. Their later termination is established
separately by the finite traces.

### Result 2 — an exact remainder gives a uniform short-block repair

**J-cycle-ooe-exact-remainder-repair, EXACT — HUMAN PROOF.**
The following identity, quotient bound, guard and validated next
substitution specify exactly what the repair retains.

#### 1. Data and initialization are explicit


Consider \(x\overset O\longmapsto u\overset O\longmapsto v
\overset E\longmapsto z\), with positive integer states. Write
\[
X=x^3,\quad u=\operatorname{isqrt}(X),\quad
R=X-u^2,\quad B=X-R=u^2,\quad t=\sqrt X.
\tag{1}
\]
The exact remainder satisfies \(0\le R\le2u\) and
\(0\le\eta:=t-u<1\).

This is not a free parameter. Initialization computes the first O step
and stores \(R=X-u^2\), or retains that remainder from an already verified
step. If supplied independently, the record must certify that \(B\) is
a positive integer square and \(R\ge0,\ R^2\le4B\). Those conditions
give \(u^2\le X<(u+1)^2\) for the positive square root \(u\).
Testing that certificate may itself require a square-root operation.
Retaining \(R\) retains enough information to recover the eliminated
state exactly; it is not a finite-valued summary of that state.

The source and removed-state parities satisfy
\[
u\equiv u^2=B=x^3-R\equiv x-R\pmod2.
\tag{2}
\]
Thus for odd \(x\), the second O source is odd exactly when \(R\) is even.

A proposed suffix endpoint \(z\) must be validated before any quotient
bound is applied. Without recomputing \(u\), its exact condition is
\[
z^8\le B^3<(z+1)^8.
\tag{3}
\]
Indeed this is equivalent, by taking positive square roots, to
\(z^4\le u^3<(z+1)^4\), hence to
\(z=E(O(u))=\lfloor u^{3/4}\rfloor\).
An odd-projected ideal endpoint is only a candidate until (3) passes.

#### 2. Exact first-order transport identity

The ideal and actual suffix quotients, before outer floors, differ by
\[
\Delta=\frac{t^3-u^3}{2z^2}.
\]
Use the correction
\[
C=\frac{3tR}{4z^2}.
\]
Since \(R=(t-u)(t+u)\), direct expansion gives the exact identity
\[
C-\Delta
=\frac{(t-u)^2(t+2u)}{4z^2}
=\frac{\eta^2(t+2u)}{4z^2}.
\tag{4}
\]
In particular the first-order term overestimates the true transport,
with a nonnegative quadratic error.

For every \(u\ge3\) and valid endpoint \(z\), this error is less than 1.
First \(z\ge2\), and in fact \(z^2\ge u\). Otherwise
\(u\ge z^2+1\) would imply
\[
u^3\ge(z^2+1)^3>(z+1)^4,
\]
contrary to the endpoint cell. The strict polynomial difference is
\[
(z^2+1)^3-(z+1)^4
=z^3(z^3-4)+z(2z^3-3z-4)>0\qquad(z\ge2).
\]
Using \(\eta<1\) and \(t<u+1\) in (4) now gives
\[
0\le C-\Delta
<\frac{3u+1}{4z^2}
\le\frac{3u+1}{4u}
\le\frac56<1.
\tag{5}
\]
This is uniform; no cubic-band height hypothesis is needed beyond the
exact endpoint cell. Nontrivial odd OOE sources have \(x\ge3\) and
\(u\ge5\), so they are covered.

#### 3. The corrected quotient has a one-unit uncertainty

Let
\[
d=\left\lfloor\frac{u^3-z^4}{2z^2}\right\rfloor,\qquad
q=\left\lfloor\frac{t^3-z^4}{2z^2}-C\right\rfloor.
\tag{6}
\]
Equations (4)-(5) prove
\[
d\in\{q,q+1\}.
\tag{7}
\]
The corrected floor \(q\) is an integer and can a priori be \(-1\);
it must not silently be treated as a natural number. Since \(d\ge0\),
equation (7) ensures \(q+1\ge0\).

There is an exact integer implementation of this corrected quotient.
Set
\[
K=2X-3R=2u^2-R>0\qquad(u\ge3).
\]
Then
\[
q=
\left\lfloor
\frac{\operatorname{isqrt}(K^2X)-2z^4}{4z^2}
\right\rfloor.
\tag{8}
\]
Indeed the unfloored corrected numerator is
\(K\sqrt X-2z^4\), divided by \(4z^2\). For integer \(a\) and positive
integer \(b\),
\(\lfloor(\alpha-a)/b\rfloor=\lfloor(\lfloor\alpha\rfloor-a)/b\rfloor\);
also \(\lfloor K\sqrt X\rfloor=\operatorname{isqrt}(K^2X)\).
The outer division in (8) is mathematical floor division, including
negative numerators. No floating approximation is used.

Formula (8) avoids recomputing \(u=\operatorname{isqrt}(X)\) from the
retained record, but does perform a different exact square root on a
larger integer. No computational speedup is claimed.

#### 4. Four candidates recover the second hidden parity

Let \(c=v-z^2\), so \(0\le c\le2z\). The earlier exact OE normal form,
applied to the actual suffix source \(u\), gives \(d\ge c\), and
\(d-c\le2\) whenever \(c<2z\). If \(c=2z\), clipping determines \(c\)
directly.

Define
\[
h=\min(q+1,2z),\qquad N=z^2+h.
\]
Then
\[
v=N-\kappa,\qquad \kappa\in\{0,1,2,3\}.
\tag{9}
\]
For \(c<2z\), equation (7) gives
\(c\le h\le d+1\le c+3\); for \(c=2z\), \(h=c\).

The correction is recovered without computing \(u\): take the smallest
\(j\in\{0,1,2,3\}\) satisfying
\[
(N-j)^4\le B^3.
\tag{10}
\]
The endpoint and carry bounds guarantee that such a \(j\) exists.
Minimality, together with \(v\le N\) when \(j=0\), supplies the opposite
upper cell inequality. Thus \(j=\kappa\).
All candidates are positive because \(N\ge z^2\ge4\).

For odd retained endpoints \(x,z\), the full OOE source-parity guard is
therefore exactly:
\[
R\text{ even},\qquad N-\kappa\text{ even}.
\tag{11}
\]
Equivalently, the second condition is
\(\kappa\equiv h+1\pmod2\). Condition (3) has already certified the
endpoint itself. These tests are necessary and sufficient under the
validated remainder record.

The complete short-block procedure uses the data \((x,z,R)\),
integer powers and arithmetic, one exact square root in (8), and at most
four fourth-power comparisons. Both hidden source parities are recovered.
It repairs the precise quotient substitution that failed without \(R\).

#### 5. One next prefix substitution: OOE followed by OE

The next short prefix word \(OOEOE\) admits a faithful finite-depth
procedure using this repair. Let its proposed final endpoint be the odd
integer \(y\), and retain the same initialized remainder \(R\).

An admissible full word has an odd intermediate state after OOE, because
that state is the source of the next O. The previously proved OOE endpoint
identity therefore forces the candidate
\[
z_*=\text{largest odd integer at most }x^{9/8}.
\tag{12}
\]
This formula does not itself establish that the actual OOE endpoint is
odd. Proceed as follows:

1. Validate (3) at \(z=z_*\). If it fails, no OOE block with odd endpoint
   can supply the required intermediate state.
2. Run (8)-(11) at \((x,z_*,R)\). This verifies the entire OOE prefix,
   including its two hidden source parities.
3. Validate \(y^4\le z_*^3<(y+1)^4\).
4. Apply the existing exact OE quotient and carry guard to
   the source/endpoint pair \((z_*,y)\).

These conditions are jointly necessary and sufficient for the specified
OOEOE block with odd source, intermediate retained source, and final
endpoint. Necessity uses the conditional endpoint identity to justify
(12); sufficiency uses the explicit endpoint validations and exact guards,
not the ideal power alone.

This step adds a fresh, determined arithmetic residue
\(z_*^3-y^4\), its normalized quotient, and a guard evaluation.
It does not introduce an independently chosen defect. It is a valid
one-substitution algorithm, but it still evaluates the two constituent
guards and uses a specifically proved short-word endpoint identity.

#### 6. What has and has not closed

The positive result is a uniform first-order remainder repair:
the corrected suffix quotient differs from the exact quotient by at most
one, and four candidate cells determine both OOE source parities.
It is stronger than merely keeping the ideal endpoint floor bit.

The next particular concatenation also has an exact finite procedure.
However, no rule here replaces an arbitrary compound word by one
uniformly bounded expression for both its map and its complete guard.
Repeating the construction ordinarily adds more constituent endpoint
and guard evaluations. Reusing a fixed number of temporary registers
does not bound that expression length or evaluation work.

If another exact local remainder is retained, its initialization or update
must be specified: for a new O step \(a\mapsto b\), it is
\(a^3-b^2\), computed from that actual step or certified by the corresponding
square cell. Calling a growing aggregate defect one integer likewise
does not make its initialization, update, or transported guard free.
The already established aggregate-defect identities are background
machinery, not new results of this gate.

Thus exact remainder transport repairs this short-block carry failure.
Uniform Euclidean closure and a decreasing arithmetic invariant remain
unproved. This note neither proves that every fixed-data representation
must fail nor claims that fixed register count alone resolves the cycle
problem.

### Composition audit — the existing aggregate does not supply the missing guard

For a prescribed word with \(o\) odd letters and length \(L\), its
endpoint aggregate is
\[
E_W(x)=x^{3^o}-F_W(x)^{2^L}.
\]
Its exact composition law is already the GlobalDefect mechanism cited
above. It uses absolute intermediate-state data as well as residual
values; it is not a newly discovered fixed-data guard update.
For example the genuine EE blocks \(100\to10\to3\) and
\(676\to26\to5\) both have edge remainders \((0,1)\), while their
endpoint aggregates are 19 and 51. Retaining an absolute state repairs
that ambiguity; the example is not an obstruction to all larger records.

Moreover \(E_W(x)\equiv x-F_W(x)\pmod2\), since its source exponent
is odd and its nonempty-word endpoint exponent is even. This residue
forgets the interior parities. The known odd-cube OE fiber has both
valid and invalid guards with the same aggregate parity.
No impossibility for higher residues or cycle-selected formulas follows.

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

Status: **STRUCTURAL**. This dossier is the canonical written source for
the two new results and their exact finite controls. Paper A, its Lean
claims and its numerical period bound are unchanged by this gate.
Global no-cycle remains unproved.

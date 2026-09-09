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

These are **AI-assisted written proofs**, with separate AI audits of
the family, algebra and scope. No new Lean theorem or independent human
review is claimed. The repository tag **EXACT — HUMAN PROOF** refers to
the written-proof tier. Existing CubeFiber declarations support the
secondary known fiber result; they do not formally verify Results 1–2.

## Results

### Result 1 — a quotient normal form for the hidden OE guard

**J-cycle-oe-quotient-parity-carry, EXACT — HUMAN PROOF.**
The following general square-cell lemma gives the desired source/endpoint
formula.

Let \(N\ge1\) and \(y\ge1\) be integers satisfying
\[
y^4\le N<(y+1)^4.
\]
Put \(u=\lfloor\sqrt N\rfloor\), \(c=u-y^2\),
\(d=\lfloor(N-y^4)/(2y^2)\rfloor\), and \(h=\min(d,2y)\). Then
\[
0\le c\le2y,\qquad c=h-\kappa,\qquad \kappa\in\{0,1,2\}.
\tag{C1}
\]
For \(q=y^2+h\), the correction is exactly
\[
\kappa=
\begin {cases}
0,&q^2\le N,\\
1,&(q-1)^2\le N<q^2,\\
2,&N<(q-1)^2.
\end{cases}
\tag{C2}
\]
In the last case the lower cell \((q-2)^2\le N\) follows from (C1).
For an OE block with odd source \(x\) and odd endpoint \(y\), take \(N=x^3\).
Its hidden parity is correct if and only if \(h-\kappa\) is odd.

**Proof.** The fourth-power cell gives \(0\le c\le2y\). Write
\(N=(y^2+c)^2+\epsilon\), \(0\le\epsilon\le2(y^2+c)\). Then
\[
d=c+\left\lfloor\frac{c^2+\epsilon}{2y^2}\right\rfloor\ge c.
\]
If \(c\le2y-1\), then \(c^2+\epsilon\le6y^2-1\), giving
\(d-c\le2\). If \(c=2y\), clipping gives \(h=c\). Thus (C1) holds
in both cases, and the adjacent squares give (C2). Since \(y\) is odd,
\(u=y^2+c\) is even precisely when \(c\) is odd; the O source is already
correct by hypothesis. This proves the guard equivalence.

The correction 2 is attained on the genuine OE block
\(93\to896\to29\):
\[
d=h=57,\qquad c=896-29^2=55,\qquad\kappa=2.
\]
Thus two square comparisons, one integer quotient and clipping suffice
for this single word. The quotient itself is an unbounded integer.

### Result 2 — endpoint compression hides an unbounded substituted carry

**J-cycle-ooe-carry-substitution-obstruction, EXACT — HUMAN PROOF.**
The notation and proof below concern precisely the proposed extension
of Result 1 to an OOE suffix after eliminating its first source.

#### 1. The substitution


An OOE block starts at \(x\), has \(u=O(x)\), \(v=O(u)\),
and ends at \(z=E(v)\). Its OE suffix uses
\[
c_2=v-z^2,\quad
d_2=\left\lfloor\frac{u^3-z^4}{2z^2}\right\rfloor,\quad
h_2=\min(d_2,2z).
\]
The first result gives \(c_2=h_2-\kappa_2\), \(0\le\kappa_2\le2\),
but still uses the eliminated source \(u\).

The direct proposed flattening replaces \(u\) by \(x^{3/2}\), giving
\[
D=\left\lfloor\frac{x^{9/2}-z^4}{2z^2}\right\rfloor,\qquad
H=\min(D,2z).
\tag{9}
\]
The construction below tests exactly this replacement. The real power
and floor in (9) have their exact mathematical meaning; no floating
evaluation is involved.

#### 2. Infinite fully valid OOE family

For every odd integer \(s\ge3\), set
\[
\begin {aligned}
x&=s^8+8,\\
u&=s^{12}+12s^4,\\
v&=s^{18}+18s^{10}+54s^2-1,\\
z&=s^9+9s-1.
\end{aligned}
\tag{10}
\]
These satisfy \(O(x)=u\), \(O(u)=v\), and \(E(v)=z\), as the following
adjacent-square certificates show.

First,
\[
x^3-u^2=48s^8+512=:R_1.
\tag{11}
\]
For \(s\ge3\), \(0<R_1<s^{12}\le u<2u+1\), proving
\(u^2<x^3<(u+1)^2\). Indeed
\(s^{12}-48s^8=s^8(s^4-48)\ge33s^8>512\).

Writing \(v_0=v+1\), expansion gives
\[
v_0^2-u^3=216s^{12}+2916s^4.
\tag{12}
\]
This is positive and less than \(s^{18}\le v_0\):
each summand is less than \(s^{18}/2\), since
\(s^6\ge729>432\) and \(s^{14}>5832\).
Consequently \((v_0-1)^2<u^3<v_0^2\), so \(O(u)=v\).

Writing \(z_0=z+1\), one similarly obtains
\[
z_0^2-v=27s^2+1>0,\qquad
v-(z_0-1)^2=2s^9+18s-27s^2-2>0.
\tag{13}
\]
The last inequality follows from \(2s^9\ge4374s^2\) for \(s\ge3\).
Thus \(z^2<v<(z+1)^2\).

Since \(s\) is odd, \(x,u,z\) are odd and \(v\) is even.
Every prescribed branch and both retained endpoint parities are correct.
For the threshold \(b=s^8\), the block also satisfies
\[
b\le x,u,z<b^2\le v<b^3.
\tag{14}
\]
For example \(u<s^{16}\), so \(v<u^{3/2}<s^{24}\);
the remaining comparisons follow directly from (10).
This is not a failure produced by using a wrong branch or leaving
the cubic band.

The exact suffix cell displacement is
\[
c_2=v-z^2=2z-27s^2.
\tag{15}
\]

The ideal endpoint differs by only one integer:
\[
\lfloor x^{9/8}\rfloor=z+1=s^9+9s.
\tag{15a}
\]
To see this directly, the second derivative of \(t^{9/8}\) is
\((9/64)t^{-7/8}\), positive and decreasing. Taylor's formula between
\(s^8\) and \(s^8+8\) therefore gives
\[
0<x^{9/8}-(s^9+9s)<\frac9{2s^7}<1.
\]
Consequently the ideal radicand \(x^{9/2}\) is above \((z+1)^4\):
it does not belong to the original endpoint cell at \(z\).
Thus (9) tests a proposed closure extension; it is not a valid direct
application of the first normal-form theorem to that ideal radicand.
The actual suffix radicand \(u^3\) does belong to the cell at \(z\).

#### 3. Exact failure of the substituted carry baseline

Define the real difference before either outer floor:
\[
\Delta=
\frac{x^{9/2}-u^3}{2z^2}
=\frac{(u^2+R_1)^{3/2}-u^3}{2z^2}.
\tag{16}
\]
The derivative of \(t^{3/2}\), with
\(u<\sqrt{u^2+R_1}<u+1\), gives
\[
\frac{3uR_1}{4z^2}<\Delta<
\frac{3(u+1)R_1}{4z^2}.
\]
In fact
\[
36s^2<\Delta<36s^2+1.
\tag{17}
\]
To check both constants, subtract \(72s^2z^2\) from
\((3/2)uR_1\). The resulting polynomial is
\[
P=336s^{12}+144s^{11}+3384s^4+1296s^3-72s^2>0.
\]
The corresponding upper excess is \(P+72s^8+768\).
Dropping its negative term and using \(s\ge3\) gives
\[
P+72s^8+768<388s^{12}<2s^{18}<2z^2.
\]
For the coefficient 388, bound \(144s^{11}\) by \(48s^{12}\),
and each of \(3384s^4,1296s^3,72s^8,768\) by \(s^{12}\).
This proves (17).

Taking the difference of the two exact floors yields
\[
D-d_2\in\{36s^2,\ 36s^2+1\}.
\tag{18}
\]
As \(d_2\ge c_2\), equations (15) and (18) imply
\[
D\ge2z+9s^2>2z,\qquad
H=2z,\qquad H-c_2=27s^2.
\tag{19}
\]
Even after clipping, the substituted baseline therefore misses the
true suffix cell displacement by exactly \(27s^2\). In particular,
\(c_2=H-\kappa\) cannot hold with any uniform bound on \(\kappa\).

#### 4. Scope of the bounded result

The OE guard has an exact normal form: one quotient, clipping, and
a correction in \(\{0,1,2\}\) selected by two comparisons. It preserves
the hidden OE parity using the actual source and collapsed endpoint.

That particular carry representation does not remain closed when the
eliminated source is replaced by its continuous power in the next
quotient. The obstruction holds on infinitely many fully parity-valid
OOE blocks inside cubic bands.
The ideal endpoint floor bit is known exactly in (15a), but the
unclipped quotient difference (18) is still unbounded. Merely carrying
that endpoint bit does not turn the tested quotient substitution into
a bounded additive correction.

The lost information is the actual source square residue
\(R_1=x^3-u^2\). Keeping it or equivalent source information retains
the exact quotient; replacing it by the old bounded additive carry does
not. This does not prove that every substitution increases the number
of integer fields: fixed fields may themselves carry unbounded data,
and a stronger update rule has not been excluded. Nor does an unbounded
magnitude alone obstruct a parity-only rule. Here \(27s^2\) is always
odd, while (18) has a polynomial part plus a one-bit remainder.

The result rejects precisely the tested bounded additive cell-carry
flattening, not all bounded-dimensional arithmetic or parity
representations. No uniform guard-preserving Euclidean closure or
decreasing arithmetic invariant has been proved.

### Secondary scope check — interval guards versus arithmetic guards

The existing odd-cube fiber result supplies a useful caution.
For odd \(s\ge3\), put \(y=s^3\), \(N_s=\lfloor2s/3\rfloor\) and
\(x_j=s^4+2j\), \(0\le j\le N_s\). Then
\[
O(x_j)=s^6+3s^2j,\qquad F_{OE}(x_j)=s^3.
\]
The full guard holds exactly when \(j\) is odd. Hence a union of
\(K\) source intervals describing the guard requires
\(K\ge\lfloor(N_s+1)/2\rfloor\), which is unbounded.
Likewise a Boolean combination of \(K\) polynomial sign/equality tests
of degree at most \(D\) in the source requires \(N_s\le2KD\):
after fixing \(y\), their at most \(KD\) real roots partition the line
into at most \(2KD+1\) interval/point cells with constant truth value.
Alternating source samples must occupy distinct cells.

This narrow obstruction is compatible with a very short arithmetic rule:
on these odd-cube fibers the guard is simply \(x\equiv3\pmod4\).
It therefore excludes neither quotient/residue formulas nor general
arithmetic closure. Moreover, an injective cycle return can select at
most one source from a fixed common-output fiber. Alternation on the
whole fiber gives no complexity lower bound on cycle-selected ranks.
This is a consequence of the known CubeFiber identities, not a new
cycle obstruction or a general automaticity theorem.

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

Status: **STRUCTURAL**. Retain two scoped written results and their exact
controls. Paper A, its Lean claims and its numerical cycle-length bound
are not changed by this gate. Uniform wrong-parity intersection and
global no-cycle remain unproved.

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


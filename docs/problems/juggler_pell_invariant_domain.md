# Pell families do not close under the growing OOE return

Status: **CLOSE** this invariant-family construction. A uniform,
unconditional theorem locates every sufficiently indexed prescribed
OOE endpoint strictly between two consecutive Pell coordinates.
No invariant seed or escaping trajectory was constructed.

## Problem

Authorized continuation, 22 September 2026: test an explicit nonsquare
arithmetic domain after
[perfect-power continuation](juggler_power_family_reentry.md) failed.
The candidate is the odd nonsquare part of the solutions of one fixed
positive Pell equation \(x^2-Dy^2=1\).

The equation constrains the square of a state; it does not require the
state itself to be a square. Individual Pell coordinates can be squares,
so the candidate domain explicitly excludes those coordinates.

## Exact statement

For each integer \(m\ge2\), define
\[
X_0=1,\quad X_1=m,\quad X_{k+1}=2mX_k-X_{k-1}.
\]
Let \(O(x)=\lfloor x^{3/2}\rfloor\), \(E(x)=\lfloor\sqrt x\rfloor\),
and \(A=E\circ O\circ O\), the **prescribed** OOE map.
It agrees with \(J^3\) only when its source parities are odd, odd, even.

**Retained theorem, EXACT — HUMAN PROOF, AI-assisted written argument.**
For every \(m\ge2\), every \(k\ge2\), and
\(j=\lceil9k/8\rceil\),
\[
\boxed{X_{j-1}<A(X_k)<X_j.} \tag{1}
\]
The only prescribed returns to the same sequence at indices \(k=0,1\)
are \(A(1)=1,A(2)=1,A(3)=3,A(4)=4\); none has actual OOE guards.
For \(k=1,m\ge5\), \(X_1<A(X_1)<X_2\).

Consequently, **no actual OOE block starts and ends in the positive
\(x\)-coordinate set of the same fixed equation \(x^2-Dy^2=1\)**.
No nonempty subset of that coordinate set, however sparse, can be a
guarded OOE invariant domain. This covers the proposed nonsquare subset.

It does not exclude later re-entry after different branch words,
switching Pell equations, generalized equations with right side other
than 1, or general escaping Juggler trajectories.

## Current literature

- conrad-pell-equation-i: **KNOWN** generation of all positive Pell
  solutions by powers of the fundamental unit. Theorem 5.3 in
  [Keith Conrad, Pell's Equation, I](https://kconrad.math.uconn.edu/blurbs/ugradnumthy/pelleqn1.pdf)
  supplies that standard identification. The recurrence and conjugate
  formula below follow directly.
- The endpoint cells are already kernel-checked:
  [ReturnCells.lean](../../formal/Problems/Juggler/ReturnCells.lean),
  \(\texttt{ooe_upper_pow}\) and \(\texttt{ooe_lower_pow}\).
  Strict prescribed growth at \(x\ge5\) is
  \(\texttt{ooe_gt}\) in
  [RootCells.lean](../../formal/Problems/Juggler/RootCells.lean).
- [OOE escape families](juggler_ooe_escape_families.md) already treats
  full polynomial ranges, paired sparse sets, and narrow unshifted
  fixed-base tubes. Here the leading coefficient is \(1/2\), and the
  conclusion is an explicit single-block exclusion for all fixed
  positive Pell equations.
- The new bracketing application is **PROJECT-SPECIFIC**.
  External novelty is not claimed. No abc hypothesis or lower bound
  for linear forms in logarithms is used.

## Branch budget

~~~text
Mathematical target     A guarded OOE return preserving a fixed Pell family.
Novelty hypothesis      The quadratic-unit recurrence can preserve both
                        nonsquare membership and the branch conditions.
Falsifier               The OOE endpoint falls between consecutive Pell values.
Already killed by?      Residue and full polynomial families are closed;
                        the existing unshifted power-tube result does not
                        directly cover the Pell leading factor 1/2.
Existing machinery      Exact OOE endpoint loss below 2; strict growth;
                        Pell recurrence and conjugate formula.
Maximum Phase-0 scope   One closure derivation; the first 32 members of
                        31 fixed Pell recurrences, one block each.
Promotion criterion     A fixed seed with a proved continuation rule, or
                        a uniform obstruction to the candidate family.
Stop criterion          Membership or a branch condition is not preserved;
                        do not substitute longer finite runs for closure.
~~~

The gap calculation justified one theorem phase proving the uniform
bracket (1) and settling its small-index exceptions. No further family,
seed search, floor verification, or trajectory campaign was opened.

## Balanced-ternary formulation

None needed. The exact quadratic recurrence is independent of encoding.

## Why BT may be relevant

No representation advantage is asserted.

## Candidate operations / invariants

- Preserve membership in one positive Pell equation under OOE:
  **REFUTED**, even for arbitrary sparse subsets.
- Universal bracket (1): **EXACT — HUMAN PROOF**, written and AI-assisted.
- An invariant nonsquare domain outside this construction: **OPEN**.

## Experiments

The [regression checks](../../tests/research/juggler_sequence/test_pell_invariant_domain.py)
cover \(2\le m\le32\) and \(1\le k\le32\): 992 prescribed blocks.
All 961 cases with \(k\ge2\) satisfy (1). Exactly 86 checked blocks
have actual OOE source guards and odd exits; none returns to its Pell
sequence. The three nontrivial small prescribed hits are the exceptions
\(2\mapsto1,3\mapsto3,4\mapsto4\), all with failed guards.

Integer quadratic-ring multiplication independently validates the
recurrence coordinates and their Pell identities. Rational arithmetic
checks the uniform constants in the proof. These finite checks do not
establish the universal theorem; the argument below does.

## Conjectures

No conjecture adopted. The theorem is unconditional.

## Counterexamples

A fixed nonsquare seed passes all OOE guards but leaves its Pell domain:
\[
97\to955\to29512\to171.
\]
Here \(97^2-3\cdot56^2=1\), while \(171\equiv0\pmod3\) makes
\(171^2-3y^2=1\) impossible. Both endpoints are odd nonsquares and the
block grows. Membership, rather than those two properties, fails.

The formal loop \(3\to5\to11\to3\) uses E at the odd source 11.
Its actual last step goes to 36. It cannot be used as a small invariant
exception.

## Formalization

The endpoint cells and growth inputs have existing Lean declarations,
named above. The new Pell bracket and its corollary are written proofs,
not new Lean theorems. Independent human review and full Lean
verification of this application remain outstanding.

## Results

### 1. The exact quadratic-unit coordinate

Set \(\lambda=m+\sqrt{m^2-1}\). Its inverse is
\(m-\sqrt{m^2-1}\), so
\[
X_k=\frac{\lambda^k+\lambda^{-k}}2
=\frac{\lambda^k}{2}(1+\lambda^{-2k}). \tag{2}
\]
This expression has initial values 1 and \(m\) and satisfies the stated
recurrence. The coordinates increase strictly, with
\[
X_2=2m^2-1\ge7,\quad X_3=4m^3-3m\ge26,\quad
\lambda\ge2+\sqrt3>c:=11/3.
\]
If \((m,y_1)\) is the fundamental solution of a fixed positive Pell
equation, its positive \(x\)-coordinates are exactly the \(X_k\).

### 2. A uniform gap between possible indices

For \(k\ge2\), compare \(X_k^9\) with \(X_l^8\). Formula (2) gives
\[
R_{k,l}:=\frac{X_k^9}{X_l^8}
=\frac{\lambda^{9k-8l}}2
 \frac{(1+\lambda^{-2k})^9}{(1+\lambda^{-2l})^8}. \tag{3}
\]
Two rational inequalities, checked by clearing denominators, are
\[
U:=\frac{(1+c^{-4})^9}{2}<1,\qquad
V:=\frac{c}{2(1+c^{-6})^8}>
H:=\left(\frac{14}{13}\right)^8. \tag{4}
\]
For orientation only, \(U<0.526\), \(V>1.827\), and \(H<1.810\).
The proof and tests use the exact fractions.

If \(9k-8l\le0\), (3) gives \(R_{k,l}<U<1\).
If \(9k-8l\ge1\) and \(l\ge3\), it gives \(R_{k,l}>V>H\).
Thus the factor \(1/2\) leaves a gap around the value needed for return:
the integer exponent \(9k-8l\) cannot fill it.

### 3. Turning that gap into the endpoint bracket

The existing exact root bounds say
\[
A(x)^8\le x^9<(A(x)+2)^8, \tag{5}
\]
and \(A(x)>x\) for \(x\ge5\).

Put \(j=\lceil9k/8\rceil\). Then \(j\ge k+1\),
\(9k-8j\le0\), and the upper comparison in Section 2 gives
\(X_k^9<X_j^8\). By (5), \(A(X_k)<X_j\).

For the lower comparison put \(l=j-1\). If \(l=k\), prescribed growth
gives \(A(X_k)>X_l\), since \(X_k\ge7\).
Otherwise \(l\ge k+1\ge3\), and \(9k-8l\ge1\). Since \(X_l\ge26\),
\[
R_{k,l}>H\ge(1+2/X_l)^8.
\]
Hence \(X_k^9>(X_l+2)^8\). Combining this with (5) gives
\(A(X_k)+2>X_l+2\), proving the lower bound in (1).

### 4. Small indices and the actual-map corollary

For \(k=1,m\ge5\), prescribed growth gives \(A(m)>m\); the upper
endpoint bound gives
\[
A(m)\le m^{9/8}<m^2<2m^2-1=X_2.
\]
Direct roots give \(A(1)=1,A(2)=1,A(3)=3,A(4)=4\).
The sources 2 and 4 fail the first O guard; at sources 1 and 3 the
proposed E source is odd. None is an actual OOE return.

All fixed-Pell coordinates are now covered. Whenever the actual OOE
guards hold, \(J^3(X_k)=A(X_k)\) and the endpoint is outside the same
coordinate set. An invariant subset cannot contain even one such
transition. This conclusion is independent of its density, the choice
of indices, and whether its members are squares.

### 5. What the proof does not address

The seed 97 may follow arbitrary later branches; its eventual fate is
not determined here. A return after a longer word is not excluded.
Finite switching between different fixed Pell equations and the
families from \(x^2-Dy^2=N\) with \(N\ne1\) were not investigated.

Allowing a new arbitrary Pell equation at every step is not a useful
invariant: every integer \(n\ge2\) satisfies
\(n^2-(n^2-1)\cdot1^2=1\). A switching construction would need a
specified family and an actual preservation rule.

## Open questions

The general fixed-seed nonsquare invariant-domain construction remains
unresolved. This phase supplies an obstruction to one candidate class,
not an escaping orbit or a universal obstruction to escape.

## Decision

**CLOSE** the fixed positive-Pell invariant-domain route. The universal
single-block exclusion is stronger than the failed finite examples and
covers arbitrary sparse subsets. Retain it as a structural result;
the broader invariant-domain construction remains unresolved.

Best next question: can a guarded growing return preserve a domain that
switches between two specified Pell equations, such as \(D=2\) and
\(D=3\), with a fixed integer seed? This is not opened here.

## Publication assessment

Status: **STRUCTURAL**. The written application is AI-assisted and
awaits independent review. Papers A--D, releases, the certified floor,
and cycle-period bounds are unchanged.

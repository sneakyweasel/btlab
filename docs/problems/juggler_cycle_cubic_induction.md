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

**No new Lean verification is claimed.** The results below are
AI-assisted written proofs with a separate AI audit of the short-word
identities and hidden-guard family. The repository label
**EXACT — HUMAN PROOF** denotes this written-proof tier, not independent
human review. The previously compiled Cubic modules establish the
starting rank geometry; they do not formally verify these new results.

## Results

### Result 1 — exact rank induction and parity transport

**J-cycle-cubic-euclidean-induction, EXACT — HUMAN PROOF.**
The following proof reproduces the exact finite permutation induction
and specifies its faithful arithmetic interpretation.

#### 1. Scope and notation


Let a finite sorted invariant set have rank permutation

\[
T(i)=\begin{cases}i+b,&0\le i<a,\\i-a,&a\le i<a+b,\end{cases}
\qquad a,b>0.
\]

The lower and upper branches execute words A and B in the original
symbols O,E. Concatenation is chronological: AB executes A first and B
second, so F_AB=F_B composed with F_A. Initially a=o, b=e, A=O, B=E.
The original arithmetic maps are O(x)=isqrt(x^3), E(x)=isqrt(x).

All first-return assertions below concern the finite invariant set, not
every integer between its extreme values. A rank prefix corresponds to
the invariant-set points below a cut. Unoccupied integer gaps do not
automatically inherit the same return words.

#### 2. One subtractive step

If a>b, induce on D=[0,a). For 0<=i<a-b, one A step reaches i+b in D.
For a-b<=i<a, A reaches i+b outside D and B then reaches i-(a-b) in D.
Consequently the new data are

\[
(a,b;A,B)\longmapsto(a-b,b;A,AB).
\tag{S1}
\]

The new lower/upper cut is a-b; the new rotation increment remains b.

If b>a, induce on D=[0,b). For 0<=i<a, A reaches i+b outside D and B
then reaches i+(b-a) in D. For a<=i<b, B reaches i-a directly. Hence

\[
(a,b;A,B)\longmapsto(a,b-a;AB,B).
\tag{S2}
\]

The new lower/upper cut remains a; the new rotation increment is b-a.
These are genuine first returns: in the two-step case the first image
is outside D, and the second is inside it.

If a=b=d, every rank in [0,d) returns by AB and its induced rank is
unchanged. This is the terminal one-branch case.

#### 3. Accelerated formulas

If a=qb+r with q>=1 and 0<=r<b, induce directly on D=[0,b+r).
The exact return data are

\[
(a,b;A,B)\longmapsto(r,b;A,A^qB).
\tag{A1}
\]

For i<r the return is A, with image i+b. For r<=i<b+r, the return is
A^qB, with image i-r. Indeed i+jb is outside D for 1<=j<=q, the first
q states are lower-branch sources, and the q-th image lies in [a,a+b),
where B returns it to i-r. The actual original time is q|A|+|B|.

If b=qa+r with q>=1 and 0<=r<a, induce on D=[0,a+r). Then

\[
(a,b;A,B)\longmapsto(a,r;AB^q,B).
\tag{A2}
\]

For i<a the return is AB^q, with image i+r; its intermediate ranks
i+b-ja are outside D until j=q. For a<=i<a+r, B returns directly to
i-a. The compound return has original time |A|+q|B|.

When r=0, the nonempty branch alone remains and the induced permutation
is the identity on a prefix of length gcd(a,b).

These formulas prove symbolic two-branch closure under Euclidean
induction, including exact cuts and return times.

#### 4. Word and tower invariants

At every stage,

\[
a|A|+b|B|=L,\qquad
a\,v(A)+b\,v(B)=(o,e),
\tag{I}
\]

where L is the original number of states and v(W) records the original
O,E letter counts in W. Both identities follow immediately from S1/S2;
for example (a-b)|A|+b(|A|+|B|)=a|A|+b|B|.
The two word-count columns retain determinant 1 until termination,
because each update adds one column to the other.

Each retained rank supplies a return tower consisting of its successive
original states up to, but excluding, its next visit to the retained
prefix. These towers are disjoint and cover all original states. One
proof chooses the unique most recent retained state while traversing a
permutation cycle backwards. Every original cycle meets the prefix:
the original rank cycles are the residue classes modulo d=gcd(o,e),
and all prefixes used by induction have at least d elements.

At termination there are d towers of common word length L/d and common
letter counts (o/d,e/d). For a primitive cycle d=1; the one final return
word is exactly the entire minimum-based mechanical word, and its
return map fixes the original minimum. This alone is an exact rewriting
of closure, not a contradiction to closure.

#### 5. Every original parity check transfers

For an original word W=w_0...w_(k-1), define

\[
P_W(x)=\bigwedge_{0\le j<k}
\left[ F_{w_0...w_{j-1}}(x)\text{ has parity prescribed by }w_j\right].
\]

The empty prefix is the identity. In particular P_O(x) means x odd,
and P_E(x) means x even. The exact recursion is

\[
P_{AB}(x)=P_A(x)\wedge P_B(F_A(x)).
\tag{P1}
\]

The accelerated predicates are

\[
P_{A^qB}(x)=
\left(\bigwedge_{j=0}^{q-1}P_A(F_A^{j}(x))\right)
\wedge P_B(F_A^{q}(x)),
\tag{P2}
\]

\[
P_{AB^q}(x)=P_A(x)\wedge
\left(\bigwedge_{j=0}^{q-1}P_B(F_B^{j}(F_A(x)))\right).
\tag{P3}
\]

By the tower partition, parity compatibility at every original state is
equivalent to requiring its full return-word predicate at every retained
base state. Necessity and sufficiency both hold; no parity check may be
discarded just because its state is no longer retained as a base.

Consequently the fully expanded bookkeeping still contains exactly L
original parity tests across all bases at every stage, as quantified by
I. At a primitive terminal base the single predicate contains all L
tests. This is a statement about this faithful recursive representation,
not an information-theoretic impossibility theorem for every alternative
arithmetic representation.

#### 6. First induced pair relevant to cubic-band cycles

Under b<a<2b, the first two subtractive steps give

\[
(a,b;O,E)\to(a-b,b;O,OE)
\to(a-b,2b-a;OOE,OE).
\]

The next quotient is q=floor((a-b)/(2b-a)), if a-b>=2b-a. The resulting
compound upper word is (OOE)^q OE. Near the expansion boundary
a/b=log(2)/log(3/2), that quotient is 2. The quotient is not universally
2 without an additional verified count restriction. No zero-drift
identity is assumed.

#### 7. What this establishes and what it does not

Proved here: exact subtractive/accelerated first returns, cuts, tower
partition, count invariants, and a necessary-and-sufficient parity
transport recursion. The induction strictly reduces the number of base
ranks, while retaining all original cell/parity obligations in its return
maps and predicates.

The numerical rank reduction is therefore not yet a decreasing
arithmetic complexity: the terminal single-point condition is the
original full-word fixed-point and parity problem. Two named branches
do not mean a uniformly controlled arithmetic family. A retained
straight-line program or word substitution is genuine symbolic
compression, but does not itself supply an arithmetic closure theorem.

The arithmetic-compression route must separately prove a closed family
for both the endpoint maps and their parity predicates, or establish an
independent bound/decrease on their complexity. Exact identities for
endpoint maps alone cannot discharge P1-P3. Conversely this analysis
does not prove that no stronger arithmetic identity exists.

There is a further limitation even if an endpoint compression succeeds.
An induced lower branch increases on its base ranks; an upper branch
decreases. Since F_W(x)<=x^(p_W), where
p_W=(3/2)^(number of O)/(2^(number of E)), increasing lower branches
necessarily have p_W>1 (for source states greater than 1). On an induced
section consisting of odd source states, an exact representation by the largest odd
integer <=x^(p_W) would also force every decreasing upper branch to
have p_W<1. That could obstruct a nonterminal upper branch with the
wrong exponent sign. It does not automatically obstruct the terminal
fixed point: for p>1 and x^p<x+2, that odd projection still fixes odd x.
Indeed the invariant

\[
a\log p_A+b\log p_B=\Lambda
\]

retains the original positive total floor drift throughout induction.
A final endpoint identity alone can therefore return to the already
known near-convergent/finance difficulty. No new terminal contradiction
has been proved by the rank induction.

### Result 2 — short return identities and transported floor loss

**J-cycle-cubic-return-compression, EXACT — HUMAN PROOF.**
For \(z\ge1\), write \(Q(z)\) for the largest odd integer at most \(z\).
The endpoint conclusions below are conditional on an odd actual output;
they do not supply the internal source-parity guards.

#### 1. Exact root collapse


For a positive integer \(N\) and positive integers \(r,s\),
\[
\left\lfloor\left\lfloor N^{1/r}\right\rfloor^{1/s}\right\rfloor
=\left\lfloor N^{1/(rs)}\right\rfloor.
\tag{R1}
\]
Indeed, for each nonnegative integer \(k\), the left side is at least
\(k\) exactly when \(\lfloor N^{1/r}\rfloor\ge k^s\), equivalently
\(N\ge k^{rs}\). This is also the defining condition for the right side.
It follows that
\[
F_{E^k}(x)=\lfloor x^{1/2^k}\rfloor,\qquad
F_{OE^k}(x)=\lfloor x^{3/2^{k+1}}\rfloor.
\tag{R2}
\]
In particular,
\[
F_{OE}(x)=\lfloor x^{3/4}\rfloor
\tag{R3}
\]
for every positive integer \(x\), without parity assumptions.
If this output is odd, it is \(Q(x^{3/4})\).

#### 2. One genuine endpoint carry identity: OOE

Set \(r=x^{3/2}\), \(u=\lfloor r\rfloor\), and
\(v=F_{OOE}(x)\). Applying R3 at \(u\) gives the exact expression
\[
v=\lfloor u^{3/4}\rfloor.
\]
Since \(0\le r-u<1\), concavity of the power \(3/4\) gives
\[
0\le r^{3/4}-u^{3/4}<1.
\]
For example, the upper bound follows from
\((u+d)^{3/4}\le u^{3/4}+d^{3/4}\) for \(0\le d<1\).
Therefore, if \(H=\lfloor x^{9/8}\rfloor\),
\[
v\in\{H-1,H\},\qquad 0\le x^{9/8}-v<2.
\tag{C1}
\]
Consequently
\[
F_{OOE}(x)\text{ odd}\quad\Longrightarrow\quad
F_{OOE}(x)=Q(x^{9/8}).
\tag{C2}
\]
This is an exact endpoint identity, stronger than retaining the nested
floor program. It does not assume the full word predicate, so it applies
in particular to an admissible odd-to-odd return block.

The exact square-root trace
\(13\mapsto46\mapsto311\mapsto17\) illustrates the remaining distinction.
Its endpoints are odd and C2 holds, but the second prescribed O source
is even and the prescribed E source is odd. The endpoint identity is
not a branch-compatibility criterion.

#### 3. The next subtractive word OOEOE also compresses

Let \(u=F_{OOE}(x)\). For \(x\ge5\), monotonicity and
\(F_{OOE}(5)=6\) give \(u\ge6\). Put \(r=x^{9/8}\).
By C1, \(0\le r-u<2\). Concavity, or the decreasing derivative of
the power \(3/4\), now gives
\[
0\le r^{3/4}-u^{3/4}
\le\frac34u^{-1/4}(r-u)
<\frac32u^{-1/4}<1,
\]
where the last strict inequality follows from
\((3/2)^4=81/16<6\le u\).
As \(F_{OOEOE}(x)=\lfloor u^{3/4}\rfloor\), this proves
\[
0\le x^{27/32}-F_{OOEOE}(x)<2\qquad(x\ge5).
\tag{C3}
\]
Thus every odd output equals \(Q(x^{27/32})\).
For odd positive sources below 5, \(x=1\) is fixed and
\(F_{OOEOE}(3)=2\) is even. Hence
\[
x\text{ odd and }F_{OOEOE}(x)\text{ odd}
\quad\Longrightarrow\quad
F_{OOEOE}(x)=Q(x^{27/32})
\tag{C4}
\]
for all positive integer sources.

This proves another short-word output closure. It does not prove closure
under arbitrary Euclidean substitution, nor does it compress the hidden
parity predicates.

#### 4. An exact error identity explains the fixed-word limitation

Consider any word of length \(k\), with exponent
\(\alpha_j\in\{3/2,1/2\}\) at step \(j\). Let
\[
n_0=x,\quad n_j=\lfloor n_{j-1}^{\alpha_j}\rfloor,\quad
p_j=\prod_{\ell=1}^j\alpha_\ell,\quad
q_j=p_k/p_j,\quad
\varepsilon_j=n_{j-1}^{\alpha_j}-n_j\in[0,1).
\]
With \(p_0=1\), a telescoping sum gives the exact identity
\[
x^{p_k}-n_k
=\sum_{j=1}^k
\bigl[(n_j+\varepsilon_j)^{q_j}-n_j^{q_j}\bigr].
\tag{T1}
\]
Indeed, the \(j\)-th summand is
\(n_{j-1}^{p_k/p_{j-1}}-n_j^{p_k/p_j}\).
This identity is not a new independent error model: its
\(\varepsilon_j\) are the actual absolute floor remainders.

Suppose every nonempty proper prefix, \(1\le j<k\), has \(p_j>p_k\). Then \(0<q_j<1\)
for \(j<k\), while \(q_k=1\). Concavity gives
\[
0\le x^{p_k}-n_k
<1+\sum_{j=1}^{k-1}q_jn_j^{q_j-1}.
\tag{T2}
\]
Consequently the explicit sufficient condition
\[
\sum_{j=1}^{k-1}q_jn_j^{q_j-1}\le1
\tag{T3}
\]
implies \(n_k=Q(x^{p_k})\) whenever \(n_k\) is odd.
For example, if \(n_j\ge M\ge1\) and \(q_j\le1-\eta\) for all
nonempty proper prefixes, with \(\eta>0\), then
\[
(k-1)M^{-\eta}\le1
\]
suffices. For each fixed word satisfying the strict prefix inequalities,
\(n_j\to\infty\) as \(x\to\infty\); hence T3 eventually holds.

The words with exponents \(243/256\) and \(531441/524288\) in the
bounded control have all their nonempty proper prefix exponents above the final
one. Thus generic examples in which an initial square root amplifies a
floor error do not automatically falsify this prefix-induced family.
But T3 supplies no uniform induction invariant: the number of summands
can increase and the prefix-exponent gaps can shrink. The displayed
sufficient threshold depends on the word. This is a limitation of this
estimate, not a proof that every possible bounded representation fails.


### Result 3 — endpoints do not determine internal parity

**J-cycle-cubic-hidden-parity, EXACT — HUMAN PROOF.**


For every odd integer \(s\ge3\), take \(x=s^4\). Then
\[
O(x)=s^6,\qquad F_{OE}(x)=s^3=\lfloor x^{3/4}\rfloor.
\tag{G1}
\]
The source and endpoint are odd, and the collapsed cell is exact.
Nevertheless the E source \(s^6\) is odd. Thus the full predicate
\(P_{OE}(x)\) fails for every member of this infinite family.

This even respects the relevant threshold branch placement: for
\(b=s^3\), the source \(x=s^4\) lies below \(b^2=s^6\), and its
image is exactly the upper seam \(b^2\). The threshold rule executes OE,
but the Juggler rule at the seam does not execute E because \(b^2\) is odd.
An exact endpoint cell and odd retained endpoints therefore do not
determine whether this eliminated state has the required parity.

This is a counterexample to the proposed endpoint-only compatibility
shortcut. It is not a counterexample to C1-C4, to output compression on
fully parity-valid blocks, or to the possible existence of some stronger
arithmetic family carrying additional bounded data.

The faithful predicate is
\[
P_{AB}(x)=P_A(x)\wedge P_B(F_A(x)).
\]
Result 1 proves that its full tower expansion contains exactly the
original \(L\) parity obligations at every induction stage. In particular,
two named return branches are not by themselves bounded parity data.
This counts this exact recursive representation; it is not an
information-theoretic impossibility theorem about all alternative ones.


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

Status: **STRUCTURAL**. This canonical research dossier records a
completed bounded gate, with exact written statements and finite
integer controls. Paper A's text, Lean claims and numerical bounds are
not changed by this investigation. Uniform wrong-parity intersection
and global no-cycle remain open.

## Authorized parity-carry continuation

The next bounded question is answered in
[Exact parity carries](juggler_cycle_guard_carries.md). An OE quotient
and three-valued correction give its exact hidden guard. An infinite
fully parity-valid OOE family defeats the tested pure-power substitution:
the quotient discrepancy grows as 36r^2 and its clipped offset error is
exactly 27r^2 despite a one-integer endpoint correction. That extension
is CLOSE; this dossier's broader arithmetic closure question remains open.


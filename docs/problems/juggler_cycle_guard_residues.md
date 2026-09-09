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

**J-cycle-ooe-fixed-residue-obstruction, EXACT — HUMAN PROOF.**
This is an AI-assisted written proof, with separate AI audits of the
Taylor bounds, exact parities, common threshold/section, and scope.
The repository tag names its written-proof tier and does not claim
independent human review. No new Lean verification is claimed.

## Results

### Result 1 — a fixed residue summary fails even with exact first remainder zero

#### 1. The closure classes must be distinguished

A fixed number of integer registers need not contain a bounded amount
of information. In particular, the input x is unbounded, and an exact
first remainder R=x^3-u^2 together with x determines the eliminated
state u. A summary that retains full x is already injective in x;
collisions cannot prove that no arithmetic formula in those data exists.

There is a separate question whether fixed formulas evaluate the whole
guard without a number of root/endpoint/constituent-guard operations
that grows with the induced word. A constant-register loop through
every original letter is still replay. A cumulative Boolean violation
flag preserves all guards after replay, but does not initialize or
update a compound guard without that work.

The precise class refuted below retains the exact initialized first
square remainder and any fixed finite collection of residue classes
of the source, first image, final endpoint, and endpoint aggregate.
It may also retain the full common threshold and full common return
section. That class is narrower than full absolute-data arithmetic
closure, and narrower than formulas allowed to evaluate fresh square
cells at later intermediate states.

#### 2. Parametric pair for every fixed modulus

Let Q>=2 be any even integer, put c=Q-1, and choose an integer b with

\[
b\equiv3\pmod4,\qquad b^2>504c^5.
\tag{H}
\]

Such b exist arbitrarily large. For d in {1,-c}, define

\[
t_d=b^4+4d,\qquad x_d=t_d^2,\qquad u_d=t_d^3,
\]

\[
V_d=b^{18}+18db^{14}+126d^2b^{10}+420d^3b^6+630d^4b^2,
\tag{V}
\]

\[
Z_d=b^9+9db^5+\frac{45d^2b-1}{2}.
\tag{Z}
\]

Every t_d is a positive odd integer. The exact first O step is
O(x_d)=u_d, and its remainder is

\[
R_1=x_d^3-u_d^2=0.
\tag{R}
\]

The next two exact steps are

\[
v_1=O(u_1)=V_1,\qquad
v_{-c}=O(u_{-c})=V_{-c}-1,
\qquad E(v_d)=Z_d.
\tag{F}
\]

All x_d,u_d,Z_d are odd. Since V_d is odd, v_1 is odd and v_-c
is even. Consequently the d=-c OOE block is fully parity-valid,
whereas the d=1 block fails its final E-source guard. Their first
source and second O-source guards both hold.

#### 3. Exact proof of the floor formulas

The following Taylor bounds certify adjacent integer cells; no
floating calculation is used. Put A=b^4. From H, A>8c+4, so
A-4c>A/2 and all arguments below are positive.

For f(t)=t^(9/2), Taylor expansion through degree four at A gives

\[
(A+4d)^{9/2}=V_d+252d^5\xi^{-1/2},
\tag{T1}
\]

for some xi strictly between A and A+4d. Indeed the fifth derivative
divided by 5! is (63/256)t^(-1/2). The remainder has the sign of d
and satisfies

\[
0<|252d^5\xi^{-1/2}|
<\frac{504c^5}{b^2}<1.
\]

As V_d is an integer, its floor is V_1 on the positive side and
V_-c-1 on the negative side. Since O(u_d)=floor(t_d^(9/2)), this
proves the second step in F.

For g(t)=t^(9/4), the degree-two expansion is

\[
(A+4d)^{9/4}
=b^9+9db^5+\frac{45d^2b}{2}
 +\frac{15}{2}d^3\zeta^{-3/4},
\tag{T2}
\]

with zeta between A and A+4d. Its remainder has magnitude less than
15c^3/b^3. H implies b>4c, so that magnitude is less than
15/64<1/2. The polynomial part in T2 is a half-integer, because b
and d are odd. On either side its floor is therefore Z_d.
Exact root collapse gives

\[
E(O(u_d))=\lfloor t_d^{9/4}\rfloor=Z_d.
\]

Finally, V_d is odd since its leading term is odd and all remaining
coefficients are even. In Z_d the first two terms have even sum,
and 45d^2b-1 is 2 modulo 4 because b is 3 modulo 4. Hence Z_d is
odd. This proves every parity claim in Section 2.

#### 4. The threshold and the first-return section are shared

Put T=t_-c and use the single threshold

\[
B=T^2.
\]

The bound A>8c+4 gives T>8 and t_1<2T. Both blocks lie in the
same threshold band [B,B^3), with exactly the same OOE placements:

\[
B\le x_d,u_d,Z_d<B^2\le v_d<B^3.
\tag{B}
\]

Here x_d>=T^2, u_d>=T^3, and Z_d>=t_d^2>=T^2. Also
u_1=t_1^3<8T^3<T^4=B^2; x_d and Z_d are smaller than u_1.
The lower peak bound follows from
v_-c=floor(T^(9/2))>=T^4. Monotonicity gives v_1>=v_-c, while

\[
v_1^2\le t_1^9<512T^9<T^{12},
\]

so v_1<T^6=B^3.

Moreover Z_1<T^3=u_-c, since Z_1^4<=t_1^9<T^12.
Thus both blocks are genuine first returns to the same integer
prefix

\[
D=[B,Z_1+1)\cap\mathbb N
\tag{D}
\]

of the threshold band: their starting and final points lie in D,
and both intermediate points lie outside D. This is not a claim
that D is the prefix of a particular periodic set, or that either
starting point is periodic. The word OOE itself is a proved
Euclidean return word, rather than an arbitrary different-order word.

#### 5. All of the specified residue data agree

Because c=Q-1,

\[
t_1-t_{-c}=4Q,
\]

and direct subtraction in Z gives

\[
Z_1-Z_{-c}
=Q\left(9b^5+45b-\frac{45Qb}{2}\right).
\tag{M}
\]

The parenthesis is an integer since Q is even. Hence t_d, x_d,
u_d and Z_d agree between the two blocks modulo Q. Their OOE
endpoint aggregates

\[
\mathcal E_d=x_d^9-Z_d^8
\]

also agree modulo Q, and their exact first remainders are both zero.
The threshold B and return section D are the same full objects,
not merely congruent. The word and its incidence counts are the same.

The aggregate valuations also agree exactly: t_d is 5 modulo 8,
so x_d is 9 modulo 16. Every odd Z_d has Z_d^8=1 modulo 16;
therefore

\[
\mathcal E_d\equiv8\pmod{16},\qquad
\nu_2(\mathcal E_d)=3.
\tag{N}
\]

Nevertheless the two full OOE guards are opposite. No function of
just these common data can decide both. For any fixed finite list
of integer residue moduli, choose Q to be an even multiple of their
least common multiple. The same construction defeats that list.

This conclusion does not include an already evaluated second
intermediate-state parity or second square remainder: those data
would of course distinguish the two blocks. It also does not include
the full unbounded x_d, Z_d or aggregate values, which differ.

#### 6. Consequences for the uniform closure gate

The initial exact remainder does not make the later hidden guard a
function of finitely many residue classes of the other listed data.
This failure occurs for OOE, at a shared threshold and a shared
first-return section, with all endpoint validations exact. Enlarging
a fixed residue modulus cannot repair that particular summary class.

The existing corrected OOE formula is unaffected: it uses the full
absolute input and endpoint in nonlinear quotient and square-cell
comparisons. Those comparisons distinguish this pair. Likewise the
pair does not refute a future fixed-register representation retaining
and manipulating full absolute values.

Any claimed general closure must therefore state both its retained
data and its permitted evaluation/update operations. If later exact
remainders are initialized by replaying the relevant branch, the
formula has not eliminated that replay. If an unbounded list of
remainders is packed into one integer, fixed register count has not
bounded the information or evaluation work.

No cycle-specific contradiction follows from the pair: actual
periodic-set membership is not established, and rank geometry may
select a sparse subset of the possible return blocks. The result
refutes a uniform residue-only guard on the entire geometric return
domain, not the possible existence of a stronger invariant on cycles.


### Background audit — dyadic endpoint data saturate

For a nonempty prescribed word W of length L and o O letters, put
A=3^o, B=2^L and D_W(x)=x^A-F_W(x)^B. Suppose its endpoint y=F_W(x)
is odd. Then

\[
D_W(x)\equiv x^{3^o}-1\pmod{2^{L+2}}. \tag{D1}
\]

Indeed y²−1=(y−1)(y+1) is divisible by 8 for every odd y.
If an odd z satisfies z≡1 mod2^t with t≥3, then
z²−1=(z−1)(z+1) is divisible by 2^(t+1).
Induction gives y^(2^L)≡1 mod2^(L+2).
The case y=1 is immediate throughout.

Consequently every fixed modulus 2^K is saturated once L≥max(1,K−2):
the aggregate residue is determined by the source residue and O count,
independently of which odd endpoint is obtained. This includes both
Euclidean concatenation updates, since their return-word lengths add.
It does not say the source and word fail to determine the guard, nor
exclude precision growing with L.

At a prescribed-word odd fixed point x=y>1, necessarily A>B: every
positive prescribed trajectory has F_W(x)≤x^(A/B), and for x>1,
A<B would give F_W(x)<x; A=B is impossible for L≥1.
Now

\[
D_W(x)=x^B(x^{A-B}-1),\qquad
\nu_2(D_W(x))=\nu_2(x-1). \tag{D2}
\]

The exponent A−B is a positive odd integer. Factoring x^(A−B)−1
as (x−1) times a sum of A−B odd summands proves the valuation claim.
Thus this valuation has no automatic descent as the word is composed.
This is a standard algebraic consequence applied to the current
aggregate, not a new global-defect law or a contradiction to cycles.


### Background audit — a mismatch energy does not initialize itself

For a prescribed closed trace \(n_0,\ldots,n_L=n_0\), let
\(p_i=n_i\bmod2\), let \(\sigma_i\) be 1 for O and 0 for E, and put
\(m_i=p_i\mathbin{\oplus}\sigma_i\), where \(\oplus\) denotes XOR.
Thus \(m_i=1\) exactly at a wrong-parity source.
Writing \(h_i=3\) or 1 according to the letter, every edge remainder
satisfies
\[
r_i=n_i^{h_i}-n_{i+1}^2
\equiv p_i-p_{i+1}\pmod2.
\]
Consequently its discrepancy from the prescribed parity transition is
\[
(r_i\bmod2)\mathbin{\oplus}\sigma_i\mathbin{\oplus}\sigma_{i+1}
=m_i\mathbin{\oplus}m_{i+1}.
\]
Its nonnegative sum counts changes in mismatch status, not mismatches
themselves. On a cycle that sum is even; zero permits both all-correct
and all-wrong status. A known correct anchor excludes the latter,
but does not prove that the energy is nonzero.

The actual mismatch count \(M_W(x)=\sum m_i\) has the exact recursion
\[
M_{AB}(x)=M_A(x)+M_B(F_A(x)).
\]
It vanishes exactly when all guards hold. Its initialization still
requires the constituent statuses. Retaining a Boolean failure flag,
packing the statuses into one integer, or calling this sum an energy
does not furnish the missing arithmetic update. No impossibility for
all differently weighted absolute-data constructions is claimed.

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

Status: **STRUCTURAL**. This dossier is the canonical written source
for the new obstruction and its controls. Paper A's text, existing
Lean claims and certified period bound are unchanged by this gate.
Global no-cycle remains unproved.

## Authorized periodicity continuation

The [periodic carry gate](juggler_cycle_periodic_carries.md) uses a
complete periodic set to derive the additional necessary bound
M<m^3-m^(15/8) for m>=7 in the cubic-height class. Its exact proof
uses adjacent return images and absolute square cells. It leaves
the fixed-residue obstruction above intact and does not exclude
the remaining threshold cycles or taller cycles.

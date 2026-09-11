# Juggler OOE escape: obstructions to explicit invariant families

Status: **STRUCTURAL**. Decision: **PROMOTE** the construction obstructions.
This is the canonical proof owner for this gate. The results are AI-assisted
written proofs, independently checked by AI agents; independent human review
and Lean formalization of the new results remain outstanding. They construct
no escaping trajectory and prove no general no-escape or no-cycle theorem.

The latest authorized sparse-set construction attempt (Sections 5--7) is
**PARK**: no invariant collection with a fixed admissible seed was found.
The two-sided sparse phase template and narrow fixed-base power tubes are
excluded, with exact failures of the two tested one-sided seeds. These
additional restrictions leave arbitrary sparse survivor sets unresolved.


**Publication consolidation.** Paper A, Appendix E.7, now owns the
residue obstruction and the single-polynomial full-tail theorem.
The finite-union extension, polynomial-update templates and bounded
controls remain research results in this dossier; they are not added
to the publication or relabeled as Lean proofs.

## Problem

Can an explicit arithmetic family supply one actual trajectory consisting of
OOE blocks forever? The authorized gate tests eventually periodic domains
and finite collections of polynomial value families. These are construction
classes, not descriptions imposed on an arbitrary orbit.

## Exact statement

Write O(x)=isqrt(x^3), E(x)=isqrt(x), and A=E composed with O composed with O.
The map A is prescribed: it need not agree with Juggler at its intermediate
states. Put alpha=9/8. Existing exact endpoint and growth results give

\[
0\le x^\alpha-A(x)<2,\qquad A(x)>x\quad(x\ge5).
\tag{EF1}
\]

A sufficient escape certificate would be a nonempty set S of odd integers
at least 5 such that every x in S has O(x) odd, O(O(x)) even, and A(x) in S.
Then its actual OOE return states increase strictly forever. The intermediate
odd images exceed their sources as well, so the full orbit tends to infinity.
This conditional certificate is existing growth plus induction, not a new
construction or a proof that S is nonempty.

We prove the following restrictions on such a certificate.

1. No nonempty eventual union of odd residue classes works: each accepted
   class has arbitrarily large sources with even O(x).
2. If P is a polynomial of degree at least two, positive and integer valued
   on all sufficiently large integer parameters, at least one of every three
   sufficiently large consecutive parameters has A(P(n)) outside the full
   value family of P.
3. More generally, no finite union of full eventual polynomial value ranges
   of degrees at least two is eventually closed under prescribed A. This
   permits arbitrary switching of target family and arbitrary integer target
   parameters; no polynomial update rule is assumed.
4. Including degree-one families cannot give a fully guarded invariant S:
   such a family is an arithmetic progression, covered by restriction 1
   whenever its tail consists of odd integers.

Finite additions/deletions and fixed arithmetic progressions of parameters
do not change these conclusions. An arbitrary sparse parameter subset is
outside restrictions 2--4. The later continuation excludes sparse subsets
that retain both members of a unit-offset pair, and arbitrary sparse
integer-exponent selections inside fixed-base logarithmic tubes of width
less than 1/17. An individual orbit outside these classes is not excluded.

## Current literature

- [Paper A](../theory/juggler_finite_dynamics_note.md), Proposition E.1 and
  Theorem 3.39: bounded OOE endpoint loss and strict growth. **Reproduced**.
- [Family chains and remainder transport](juggler_cycle_remainder_transport.md):
  the family X(r)=r^8+8 cannot repeat indefinitely as that same family.
  Its valuation proof is not a rank function for arbitrary OOE returns.
- [Fixed residue guard limitations](juggler_cycle_guard_residues.md): fixed
  summaries of specified endpoint data do not determine the full guard.
  The present residue result instead directly excludes a proposed domain S.
- The finite van der Waerden theorem: for each number of colors and requested
  length there is a finite interval whose every coloring contains a
  monochromatic arithmetic progression of that length. The formulation used
  here is stated in the introduction of Landman, Robertson and Culver,
  [Some New Exact van der Waerden Numbers](https://arxiv.org/abs/math/0507019).
  This classical theorem is an external input, not a Juggler result.
- The polynomial-family statements are new applications in this laboratory;
  no claim of external mathematical novelty is made.

## Branch budget

```text
Mathematical target     An explicit invariant family of actual OOE returns
Novelty hypothesis      Uniform arithmetic preservation, or a precise
                        obstruction to the proposed construction class
Falsifier               Forced parity failure or incompatible polynomial
                        growth/parameter differences
Already killed by?      X(r)=r^8+8 repetition; fixed endpoint-residue guard
                        summaries; finite prefixes as an escape proof.
                        These do not exclude all full polynomial families.
Existing machinery      Exact OOE endpoint loss; strict growth; family-chain
                        theorem; square-cell verification
Maximum Phase-0 scope   Symbolic residue/polynomial closure; at most 20 OOE
                        returns from each odd start 5..20001; 15 family
                        parameters 3..31 with at most 12 returns each;
                        small fixed residue fixtures. No descent campaign.
Promotion criterion     A new uniform theorem with the construction class
                        and unresolved orbit question stated separately
Stop criterion          Close the failed construction classes; do not
                        replace a missing invariant set by finite prefixes
```

The initial polynomial-update test strengthens, within the same symbolic
finite-family scope, to arbitrary target parameters using integer finite
differences and finite coloring. No additional trajectory search is used.

## Balanced-ternary formulation

Sources, square margins, and integer finite differences may be encoded in
balanced ternary. The argument is independent of that representation.

## Why BT may be relevant

No representation-specific advantage is claimed. The obstruction concerns
exact integer arithmetic and polynomial growth rates.

## Candidate operations / invariants

- J-ooe-escape-residue-obstruction: **EXACT — HUMAN PROOF**, meaning the
  repository's written-proof category; the proof here is AI-assisted.
- J-ooe-escape-polynomial-obstruction: **EXACT — HUMAN PROOF**, with the
  same explicit AI-assisted and not-yet-Lean trust status.
- J-ooe-escape-shifted-valuation: **REFUTED** as a proposed monotone rank.
- Existence of an actual infinite all-OOE trajectory: unresolved.

## Experiments

The fixed runner is `research.juggler_sequence.ooe_escape_families`.
Its records are [controls.json](../../data/research/juggler/ooe_escape_families/controls.json).
Run without arguments to print a compact report; add `--write` to reproduce
that fixed artifact. All roots and parities are computed with integer
arithmetic. No failed block is followed by a generic trajectory continuation.

There are 9999 odd starting controls, each capped at 20 valid returns, and
15 family controls, each capped at 12 returns including the known first one.
No cap is reached. The observed maximum is five valid returns:

\[
7939\to24391\to86225\to356933\to1764655\to10653499.
\tag{EF2}
\]

At the last endpoint the next O image is the even integer 34772699236,
so the next OOE block fails its second O guard. This is a finite chain,
not a candidate infinite orbit. The 15 tested X(r)=r^8+8 sources all leave
that particular family at their first return and fail the following OOE
return. Those 15 observations are not a uniform theorem about departure.

The test module independently checks exact adjacent-square certificates,
the fixed negative witnesses, residue counterfamilies, and the bounded
report. Tests of arithmetic fixtures do not verify the asymptotic or
finite-coloring proofs below.

## Conjectures

No new conjecture or existence claim is registered.

## Counterexamples

The actual guarded return

\[
199\xrightarrow O2807\xrightarrow O148718\xrightarrow E385
\tag{EF3}
\]

raises nu_2(x-1) from 1 to 7. The bounded controls also give both increases
and decreases for nu_2(x+1) and nu_2(x-9), omitting a zero argument where
the finite valuation is undefined. Thus none of these three quantities is
a strictly decreasing rank on all valid OOE returns. This does not refute
a rank using additional unbounded remainder data.

## Formalization

Existing endpoint, growth, and single-family-chain kernels are in
`CubicReturn.lean`, `ReturnCells.lean`, and `FamilyChains.lean` as indexed
by Paper A. The new residue, curvature, finite-union, sparse-pair, and fixed-base
tube results in this dossier remain written proofs. The fixed Python controls are not Lean
formalizations. No new Lean module or trust claim is introduced by this gate.

## Results

### 1. Every odd residue class contains a wrong second-O guard

The canonical statement and adjacent-square proof are now Proposition
E.7 of [Paper A](../theory/juggler_finite_dynamics_note.md). Every odd
residue class contains arbitrarily large sources with an even first odd
image, so no nonempty eventual union of odd residue classes is a fully
guarded invariant OOE domain. The construction is retained by the exact
arithmetic controls here; edit its publication proof in the manuscript.

### 2. One polynomial family misses a return in every late triple

Let P have degree d>=2 and leading coefficient a>0, and suppose P(n) is a
positive integer for every sufficiently large integer n. Put
S_P={P(n):n>=n_0}; any finite exceptional initial values are immaterial.
Use the increasing inverse branch of P near positive infinity and define

\[
w(t)=P^{-1}(P(t)^\alpha),\qquad
C=a^{(\alpha-1)/d},\qquad\alpha=9/8.
\tag{EF6}
\]

Then w(t)~C t^alpha. Differentiating P(w(t))=P(t)^alpha twice gives

\[
w''(t)=\frac{\alpha(\alpha-1)P(t)^{\alpha-2}P'(t)^2
+\alpha P(t)^{\alpha-1}P''(t)-P''(w(t))w'(t)^2}{P'(w(t))}.
\]

Substitution of polynomial leading terms, with
w'(t)~C alpha t^(alpha-1), yields

\[
w''(t)\sim C\alpha(\alpha-1)t^{\alpha-2}
=\frac{9C}{64}t^{-7/8}>0.
\tag{EF7}
\]

This is obtained from the differentiated identity, not by differentiating
an uncontrolled little-oh remainder. If A(P(n))=P(s_n), the integer target
parameter s_n is eventually on the increasing inverse branch. By EF1,
the mean value theorem and P'(u)~ad u^(d-1),

\[
0\le w(n)-s_n=O(n^{-\alpha(d-1)})=o(n^{-7/8}).
\tag{EF8}
\]

If the three consecutive parameters n,n+1,n+2 all return to S_P, integrate
EF7 over the unit square to obtain

\[
s_{n+2}-2s_{n+1}+s_n
=\frac{9C}{64}n^{-7/8}(1+o(1)).
\tag{EF9}
\]

For sufficiently large n this integer is strictly between zero and one,
a contradiction. At least one of each late triple therefore leaves the
family. The lower density of departing parameters is at least 1/3; an
individual orbit uses a sparse parameter subsequence and is not excluded.

### 3. Finite collections cannot restore full polynomial closure

Let P_1,...,P_r be nonconstant polynomials of degrees d_j>=2 and positive
leading coefficients, each integer valued and positive at every parameter
in its eventual integer tail. Let S be the union of those value tails.
Choose i for which nu_2(d_i) is minimal. For each j put

\[
\rho_j=\frac{9d_i}{8d_j},\qquad k_j=\lceil\rho_j\rceil.
\tag{EF10}
\]

Every rho_j is nonintegral: the numerator has fewer factors of two than
the denominator. In particular k_j-1<rho_j<k_j. Also

\[
k_j<\rho_j+1\le\frac{\alpha d_i}{2}+1<\alpha d_i
=\rho_jd_j.
\tag{EF11}
\]

Let w_j(t)=P_j^{-1}(P_i(t)^alpha) on its increasing tail. For a constant
C_j>0 its fixed-order derivatives have the asymptotics

\[
w_j^{(k)}(t)\sim C_j(\rho_j)_k t^{\rho_j-k}
\quad\text{when }(\rho_j)_k\ne0.
\tag{EF12}
\]

Here (rho)_k=rho(rho-1)...(rho-k+1). To justify derivatives, write
t=z^(-q) with q a positive integer for which q rho_j is integral, and
write w_j=t^rho_j v(z). After dividing
P_j(w_j)=P_i(t)^alpha by t^(alpha d_i), the equation is analytic near
z=0,v=C_j and its derivative in v is nonzero. The analytic implicit
function theorem gives v(z)=C_j+O(z), with a convergent power series.
Termwise differentiation proves EF12 with a lower-order remainder.

At a parameter n whose return belongs to the j-th family, write
A(P_i(n))=P_j(s_n). The same inverse estimate as before gives

\[
s_n=w_j(n)+O(n^{-\rho_j(d_j-1)}).
\tag{EF13}
\]

For any fixed positive integer h, EF12 and repeated integration give

\[
\Delta_h^{k_j}w_j(n)
\sim C_j(\rho_j)_{k_j}h^{k_j}n^{\rho_j-k_j}.
\tag{EF14}
\]

The coefficient is positive, and this quantity tends to zero. By EF11,
the error from EF13 is smaller than this quantity. Consequently, if the
k_j+1 parameters n,n+h,...,n+k_j h all return into the j-th family, then
for all sufficiently large n their integer target parameters satisfy

\[
0<\Delta_h^{k_j}s_n<1,
\tag{EF15}
\]

which is impossible. The cutoff can be chosen uniformly for h in any fixed
finite set and for the finitely many target families.

Take K=1+max_j k_j and a finite van der Waerden window W for r colors and
length K. If every source P_i(n) for n in a sufficiently late window of
W consecutive integers returned into S, color each n by one target family
containing its return. A monochromatic length-K arithmetic progression has
step between 1 and W. Its first k_j+1 terms contradict EF15 for that color.
Thus every sufficiently late parameter window of this fixed length W has
a source whose return leaves S. In particular S is not eventually closed.
No numerical van der Waerden bound or uniform polynomial cutoff is claimed.

If a degree-one polynomial is integer valued on every integer in a tail,
its slope and constant are integers, and its range is an eventual arithmetic
progression. If that tail is not entirely odd it already violates the
proposed S condition. Otherwise Result 1 supplies a wrong guard in it.
Combining the linear and nonlinear cases excludes every finite union of
full eventual polynomial ranges as a fully guarded all-OOE invariant set.
For a fixed progression of parameters, replace P(n) by P(an+b).

### 4. Polynomial update templates give a separate path obstruction

For completeness, the initial template test needs no full parameter tails.
Let P_i be finitely many nonconstant positive-leading state polynomials and Q_e finitely
many nonconstant polynomial parameter updates. Parameters are integers
bounded below. If an edge i->j satisfies
A(P_i(t))=P_j(Q_e(t)) at arbitrarily large valid parameters, comparison of
leading growth gives

\[
9d_i=8d_j\deg Q_e,
\qquad\nu_2(d_i)=3+\nu_2(d_j)+\nu_2(\deg Q_e).
\tag{EF16}
\]

Each such edge decreases nu_2 of state degree by at least three. A path
starting at degree d_i has at most floor(nu_2(d_i)/3) such transitions.
The correct source sets of all other templates are bounded sets of integers,
hence finite. With finitely many templates their exceptional source values
are finite; an escaping path eventually leaves them and would need an
infinite sequence of decreasing degree valuations, impossible.

Constant state polynomials contribute only finitely many state values.
Those cannot sustain an escaping tail, or a nonempty finite invariant set
above four where A(x)>x, and do not change the full-family obstructions.

This path theorem permits sparse parameter sets but requires polynomial
updates. Result 3 permits arbitrary updates but requires full polynomial
value tails. These are different hypotheses and must not be combined to
claim exclusion of sparse orbits with nonpolynomial parameter updates.

### 5. Sparse paired phase families fail closure

The user authorized an attempt to construct a sparse invariant collection
with a fixed ordinary integer seed. The successful one-block construction
in [rank-curvature Result 23](juggler_cycle_rank_curvature.md) supplies a
specific candidate. For odd \(s\ge5\), use
\[
x_\pm=4s^2\pm1,\quad u_\pm=8s^3\pm3s,\quad
B_\pm=u_\pm^{3/4},\quad z_\pm=\lfloor B_\pm\rfloor=A(x_\pm).
\tag{EF17}
\]
Select a sparse set of parameters using the four smooth phase conditions
of that result; for any fixed positive phase-box width it contains
arbitrarily large parameters giving two guarded OOE returns. The natural
candidate includes both signs at each selected parameter, inside
\(\mathcal T=\{4t^2\pm1:t\ge1\text{ odd}\}\).

**Uniform obstruction.** For every \(s\ge5\), regardless of the phase
guards, at least one of \(z_-,z_+\) lies outside \(\mathcal T\).
Indeed the mean value theorem, \(5s^3<u_-<u_+<16s^3\), and the floor
error bounds give
\[
B_+-B_->\tfrac94s^{1/4}>3,\qquad
z_+-z_-<\tfrac{11}{2}s^{1/4},\qquad z_->2s^{9/4}.
\]
Consequently
\[
2<z_+-z_-<8\sqrt{z_-}.
\tag{EF18}
\]
Two distinct elements \(p<q\) of \(\mathcal T\) with the same
parameter differ by two. If their odd parameters are \(t<t'\), then
\(t'\ge t+2\), so
\[
q-p\ge16t+14>8\sqrt{4t^2+1}\ge8\sqrt p.
\]
Both alternatives contradict EF18. Thus no subset of \(\mathcal T\)
containing both signs at any parameter \(s\ge5\) can be forward
invariant under \(A\). This excludes arbitrarily sparse paired
selection, without assuming a full polynomial parameter tail. It does
not exclude a subset selecting at most one sign at each parameter.

**The two fixed one-sided candidates also fail.** The prior witness
\(s=19999\) belongs to the exact four-phase box with width \(3/4\).
Its two genuine first returns are
\[
\begin{aligned}
1599840003&\to63990400419995\to511884809359670004668\to22624871477,\\
1599840005&\to63990400539989\to511884810799490011418\to22624871509.
\end{aligned}
\tag{EF19}
\]
Both endpoints are 21 modulo 32, while every element of \(\mathcal T\)
is 3 or 5 modulo 32. More decisively, their next actual O images are
\[
O(22624871477)=3403135028556724,\qquad
O(22624871509)=3403135035776676,
\tag{EF20}
\]
both even. Each seed therefore completes exactly one consecutive OOE
block before its next second-O guard fails. All displayed roots and
parities are verified by exact adjacent-square inequalities. No state
beyond that failed branch is used to continue an actual OOE orbit.
The failure determines neither seed's later Juggler fate.

The fixed phase conditions do not automatically pass to an endpoint.
For \(z=\lfloor B\rfloor\) with \(B-z<\epsilon\),
\[
0\le B^{3/2}-z^{3/2}\le\tfrac32\epsilon\sqrt B.
\]
For fixed \(\epsilon\), this upper bound grows with height. Replacing
the next nested floor by a smooth phase therefore needs an additional
argument; one-block equidistribution supplies no inherited guard rule.
No claim that every sparse one-sided construction fails is made.

### 6. Narrow neighborhoods of fixed-base powers cannot contain an infinite OOE tail

This second construction attempt allows arbitrary sparse exponent sets
and arbitrary, possibly nonpolynomial, exponent updates. Fix a real base
\(c>1\) and \(0\le\epsilon<1/17\). There is no infinite prescribed
OOE chain \(x_{n+1}=A(x_n)\), \(x_0\ge5\), for which integers
\(d_n\) satisfy
\[
|\log_c x_n-d_n|\le\epsilon
\tag{EF21}
\]
at every sufficiently late index. In particular there is no nonempty
actual guarded invariant set whose large elements all lie in these tubes.

**Proof.** Put \(y=A(x)\), \(\alpha=9/8\), and
\(\beta(x)=\alpha\log_c x-\log_c y\). The exact endpoint cells give
\[
0\le\beta(x)<\log_c(1+2/y)\le\frac2{y\log c}.
\tag{EF22}
\]
The lower bound need not be strict for the prescribed map. Write
\(\theta=\log_c x-d\), \(\theta'=\log_c y-e\), where the two
integer exponents satisfy \(|\theta|,|\theta'|\le\epsilon\).
Then
\[
8e-9d=9\theta-8\theta'-8\beta(x),\qquad
|8e-9d|<17\epsilon+\frac{16}{y\log c}.
\tag{EF23}
\]
For example, above the explicit source threshold
\[
x>\max\left(5,c^\epsilon,
\frac{16}{(1-17\epsilon)\log c}\right),
\tag{EF24}
\]
strict growth \(y>x\) ensures \(d,e>0\) and makes the last bound
less than one. The integer in EF23 must vanish:
\[
8e=9d,\qquad v_2(e)+3=v_2(d).
\tag{EF25}
\]
For any \(k\) consecutive transitions above EF24 that remain in the
tubes, telescoping gives
\[
v_2(d_k)+3k=v_2(d_0),\qquad 3k\le v_2(d_0).
\tag{EF26}
\]
An infinite chain starting at \(x_0\ge5\) increases without bound,
eventually passes EF24 and cannot satisfy this finite bound forever.
This proves the theorem, including arbitrary sparse choices of exponents.
The width \(1/17\) is a sufficient bound, not a claimed optimal one.

Two corollaries follow. An infinite prescribed OOE tail cannot remain
within a fixed additive distance of powers of one fixed base, nor can
\(x_n/c^{d_n}\to1\) for integer exponents. In either case the
logarithmic error tends to zero, so EF21 eventually holds with, for
example, \(\epsilon=1/34\). These statements do not assume full
polynomial families or polynomial update rules.

For exact powers of a fixed odd integer base, EF25 also forces
\(d=8q\); the first two O images are \(c^{12q}\) and
\(c^{18q}\), both odd, so the required E-source guard fails at that
individual large transition. The broader tube obstruction does not
require any parity hypothesis. It excludes a candidate construction
class, not general escape or general infinite OOE chains.

### 7. Exact inverse cells do not provide the missing ordinary integer

The prescribed return has the exact inverse threshold
\[
K(y)=\left\lceil\left\lceil y^{4/3}\right\rceil^{2/3}\right\rceil,
\qquad A(x)\ge y\ \Longleftrightarrow\ x\ge K(y).
\]
The threshold and the unique predecessor formula
\(x=\lceil y^{8/9}\rceil\) for an actual equality \(A(x)=y\ge8\)
are already proved in [preimage-capacity Result 2](juggler_cycle_preimage_capacity.md).
Iterating the threshold equivalence gives
\[
A^n(x)=y\quad\Longleftrightarrow\quad
K^n(y)\le x<K^n(y+1).
\tag{EF27}
\]
The parity guards must still be checked on every intermediate state.
A fixed large terminal target has at most one predecessor at each
large stage; it does not generate a tree of alternative actual pasts.
Changing the terminal target can change the root of the resulting chain.

Let \(G_n\) be the set of odd starts at least five with \(n\) successive
guarded OOE returns, including odd exits. These sets decrease with \(n\).
Their intersection is an invariant survivor set, but defining it does
not prove it nonempty. Even proving every \(G_n\) unbounded would not
establish an ordinary integer in their intersection. A sufficient genuine
compactness argument would require one fixed finite initial set \(F\)
with \(F\cap G_n\ne\varnothing\) at every depth: decreasing nonempty
subsets of a finite set have nonempty intersection. No such \(F\), or
fixed seed surviving all depths, is supplied by the phase construction.

A separate arithmetic example shows the integer limitation precisely.
For \(n\ge1\), every class
\[
x\equiv\frac{4^n-1}{3}\pmod{4^n}
\tag{EF28}
\]
contains positive odd integers, and the classes are nested. A common
nonnegative integer would make \(3x+1\) divisible by every \(4^n\),
which is impossible. Their compatible 2-adic limit is not an ordinary
integer seed. This is a counterexample to that compactness inference,
not a counterexample involving actual OOE survivor sets.

**Scope and outcome of the sparse-set attempt.** The
[exact controls](../../data/research/juggler/ooe_escape_families/sparse_invariant_controls.json)
retain the two fixed seeds, the first failed guards, and small replays of
existing inverse-cell fixtures. No new seed census, descent campaign or
PDF work was performed. The paired-template and fixed-base tube
obstructions are AI-assisted written proofs with independent AI audits;
their new full statements are not Lean verified and need independent
human review. Existing Lean endpoint and growth theorems are inputs.

No sparse invariant collection with a fixed admissible seed was found.
The paired-template construction is **CLOSE**, and the narrow fixed-base
power construction is **CLOSE**. The requested general construction
remains **PARK**. Defining the infinite survivor set or merely producing
more finite prefixes does not discharge its nonemptiness obligation.


## Open questions

The existence of a single actual infinite all-OOE chain is unresolved.
An escape certificate could use a thin nonperiodic parameter set, a
nonpolynomial recurrence, or other block patterns. No cycle-specific rank
rotation or fixed cubic height section was transferred to an escaping orbit.
No failure of one OOE block determines the later fate of its actual orbit.

## Decision

**PROMOTE** the residue and polynomial-family construction obstructions.
The two elementary family descriptions cannot deliver the proposed escape
certificate. Their failure is not a no-escape theorem. The exact controls
also reject the three simple shifted valuations as uniform decreasing ranks.

The single best next question is whether an explicitly defined sparse
parameter set can be preserved by a nonpolynomial OOE return recurrence,
with nonemptiness established from a fixed ordinary integer start.
The authorized sparse-set attempt in Sections 5--7 did not construct it.
Moving-seed phase hits, inverse cells and an implicitly defined infinite
survivor set do not establish that nonemptiness. No further construction
branch is automatically pursued.

## Publication assessment

Status: **STRUCTURAL**. These are construction-class obstructions with a
clear written proof, not a resolution of the Juggler conjecture. Independent
human review and formalization are outstanding. Paper A, its generated
copies, and publication releases are not modified by this research gate.

The sparse-set continuation preserves the same publication boundary:
the new tube and paired-template theorems are independently AI-audited
written results; their real and complete invariant-set applications have
not been Lean verified. Exact fixture tests verify the recorded failures,
not infinite behavior. No escaping orbit, general no-escape theorem or
fixed admissible invariant seed is claimed. Paper A and PDFs are unchanged.

# Collatz merging fibres: residue coverage and a harmonic-weight obstruction

Status: **PROMOTE** (22 September 2026), for the exact structural comparison
and the finite-residue obstruction below. The fate-class harmonic-divergence
question remains open. This is a bounded response to the proposal to find
Paper C's fibres in another form on the Collatz side.

## Problem

Can complete Collatz merging families, their residue coverage, or a finite
residue-dependent weight supply Paper C's backward reciprocal-mass mechanism?

## Exact statement

For a sign s in {1,-1}, work on positive odd integers with

\[
 S_s(n)=\frac{3n+s}{2^{v_2(3n+s)}},\qquad R_s(n)=4n+s.
\]

A whole fate class is invariant in both directions. The old backward ray
{3*2^k} is not such a class and does not refute a fate-specific theorem.
The two statements established here are:

1. Every nonempty S_s fibre is one complete R_s ray. Its first 3^r members
   visit every residue modulo 3^r exactly once, for every r>=1.
2. For every r>=1, every weight h periodic modulo 3^r, zero on multiples
   of three and strictly positive elsewhere, and every fixed d>=1, the
   homogeneous d-generation reciprocal-mass operator has a residue a
   with L_s^d h(a)<h(a). For every fixed d this gives infinitely many
   genuine large odd targets with deficient actual weighted reciprocal mass.

The second assertion covers all such weights and levels by a kernel-checked
coefficient proof and a written actual-integer error estimate. It concerns a uniform
fibre inequality; it is not an obstruction to every argument using full fate
closure, nonperiodic weights, variable stopping depths, or height windows.

## Current literature

- `zarnowski-2008-congruence-structure`: Theorem 3 and Remark 1 record
  congruence merging and the familiar 4n+1 identity. Our fibre parametrization
  is **KNOWN** mathematics, with an elementary signed derivation below.
- `tao-2019-almost-all-collatz`: Section 1.4, Lemma 1.12, gives precisely
  the finite geometric recurrence used here after converting probabilities
  to densities. Remark 1.13 identifies the stationary 3-adic process;
  Proposition 1.14 supplies fine-scale mixing. The operator is **KNOWN**.
  The identification was checked against Tao's explicit mod-9 distribution.
- `krasikov-lagarias-2003-difference-inequalities`: the x^0.84 ancestor lower
  bound alone does not imply divergent reciprocal mass.

Primary texts read for this phase:
[Zarnowski](https://www.fq.math.ca/Papers1/46_47-2/Zarnowski_1-09.pdf) and
[Tao, Section 1.4](https://arxiv.org/html/1909.03562#S1.SS4).
The all-level finite-weight obstruction is a **PROJECT-SPECIFIC** consequence
isolated here; no claim of literature priority is made.

## Branch budget

- **Target:** whether grouped fibres force reciprocal-mass growth in a fate class.
- **Novelty hypothesis:** forward closure and whole halving families compensate
  for individual poor fibres.
- **Falsifier:** persistent deficient residue classes without a compensating
  closure inequality.
- **Already killed by?:** neither the backward-only ray nor the fixed 1/50-grid
  ceiling addresses these complete, unrounded odd-return fibres.
- **Existing machinery:** Paper C mass production, signed inverse maps,
  checked ancestor density, and the actual orbit code.
- **Maximum Phase-0 scope:** exact grouped operator, value/residue tests, and
  one attempt to compensate by positive finite residue weights.
- **Promotion criterion:** a mass-growth theorem or a precise obstruction
  separating that construction from the still-open fate question.
- **Stop criterion:** do not insert an unproved distribution assumption for
  an individual fate class or launch a larger table search.

The user's follow-up specifically requested inspection of actual map values;
the forward enumeration and the fibre comparison below implement it.

## Balanced-ternary formulation

Residues modulo 3^r describe the merging family's coverage and the inverse
integrality restrictions. Balanced digits change their notation only.

## Why BT may be relevant

The distinction between ternary residue coverage and ordinary height is
central. No representation change supplies a height or termination estimate.

## Candidate operations / invariants

- S_s: one odd step followed by every available halving.
- R_s: move to the next larger sibling with the same S_s image.
- h(n)/n: reciprocal weight modified by a finite ternary residue table.
- L_s: the exact homogeneous inverse coefficient, with the affine correction
  bounded separately. It is not silently identified with actual mass.

## Experiments

Run `python -m research.collatz.fibre_mass`. It prints exact examples,
signed mod-9 tables, and three exact iterated layers; it writes no files.
The tests independently enumerate both actual odd maps through n=19999,
compare complete fibres at odd targets through 299, and check residue
coverage modulo 81 from all odd seeds through 101. Exact rational tests
exercise nonconstant weights at moduli 3,9,27 and fixed depths through 3.
These finite checks support the implementations; the proofs below supply
the unbounded quantifiers.

| Target | Juggler even predecessors | Positive Collatz odd-return predecessors |
|---|---|---|
| 5 | 26,28,30,32,34 | 3,13,53,213,853,... |
| 7 | 50,52,54,56,58,60,62 | 9,37,149,597,2389,... |
| 11 | 122,124,...,142 | 7,29,117,469,1877,... |
| 13 | 170,172,...,194 | 17,69,277,1109,4437,... |

Juggler's displayed cells use one even step. The Collatz column uses one
odd step followed by all halvings; these are different but explicitly
specified observation times. Both columns consist of actual integer values.

## Conjectures

No new conjecture is promoted from the samples. The existing question is
whether every nonempty full fate class has divergent reciprocal mass,
and whether one can quantify that growth strongly enough to be useful.

## Counterexamples

Even after discarding multiples of three, a uniform one-generation gain
is false. With h=1 on units, the coefficients K_s=L_s h are:

| a mod 9 | 1 | 2 | 4 | 5 | 7 | 8 |
|---|---|---|---|---|---|---|
| K_+(a) | 20/21 | 40/21 | 17/21 | 10/21 | 5/21 | 34/21 |
| K_-(a) | 34/21 | 5/21 | 10/21 | 17/21 | 40/21 | 20/21 |

Each row has mean exactly one. At an actual odd target m=7 mod 9,
the positive-map fertile fibre has normalized actual mass less than 1/3.
Indeed its model coefficient is 5/21 and its actual coefficient is at most
that times 1/(1-1/(2m)); m>=7 makes this at most 10/39<1/3.
This holds on the whole odd progression, not just for small examples.

## Formalization

The homogeneous coefficient obstruction in Section 3 is now kernel-checked
in `Problems.Collatz.FibreMass`, including the concrete signed operator,
its infinite-series convergence, its mean, and every finite level and
fixed positive depth. The [proof map](../theory/collatz_fibre_mass_lean_note.md)
separates this result from the remaining written statements. Its stronger
form allows zero weights on other unit residues, provided the weight at
-s is positive. The actual predecessor bijection, one-generation affine
error, deficient progression and divergent reciprocal mass are now
kernel-checked in `FibreActual`, `FibreMassError` and `FibreDeficit`.
The [actual-mass proof map](../theory/collatz_actual_fibre_mass_lean_note.md)
records the exact scope. Full sibling residue coverage, the fixed-depth
actual error for d>1 remain written proofs with exact-arithmetic checks.
The coefficient-series implication at a given nonperiodic target is now
kernel-checked in `FibreGeneration`, using the generic disjoint-generation
theorem in `BTCalculus.PreimageGenerations`; see its
[proof map](../theory/collatz_generation_mass_lean_note.md). The existence
of a nonperiodic odd unit in every full fate class remains a separate
written argument. Independent review remains open.
Ledger labels stay **EXACT — HUMAN PROOF** pending advisory statement
coverage; the compiled results also record kernel trust.

## Results

### 1. The geometric fibre and its full ternary coverage

**EXACT — HUMAN PROOF; KNOWN mechanism.** For a positive odd target m,
an odd predecessor must be

\[
 n_k=\frac{2^k m-s}{3},\qquad k\ge1,\quad 2^k m\equiv s\pmod3.
\]

If 3 divides m there are none. Otherwise precisely one parity of k works,
and n_k is positive and odd. Consecutive permissible exponents differ by
two, so n_(k+2)=4n_k+s. Conversely 3R_s(n)+s=4(3n+s), proving
S_s(R_s(n))=S_s(n). Thus this is the complete fibre, not just a subfamily.

For every j>=0,

\[
 R_s^j(n)=4^j n+s\frac{4^j-1}{3}.
\]

For i>j, its difference from R_s^j(n) is
4^j(4^(i-j)-1)(3n+s)/3. Since 3n+s is a unit, the elementary
lifting identity v_3(4^t-1)=1+v_3(t) yields

\[
 v_3\bigl(R_s^i(n)-R_s^j(n)\bigr)=v_3(i-j).
\]

Consequently two indices give the same residue modulo 3^r exactly when
they agree modulo 3^r. The first 3^r indices therefore cover all residues.
For the seed 3 the first nine mod-9 residues are
3,4,8,6,7,2,0,1,5, and then 3 again. Modulo 3, siblings simply advance
by s; exactly one in every three is divisible by three and has no odd
predecessor. Such a leaf still belongs to the fate class.

Uniformity in the sibling index is not uniform reciprocal mass:
3R_s^j(n)+s=4^j(3n+s), so reciprocal weights decay geometrically.
A complete residue sweep at level r costs a factor 4^(3^r-1) in
this shifted height. This explicitly separates residue coverage from
the size-sensitive averaging needed by Paper C.

### 2. Exact coefficient operator and actual integer error

Put M=3^r, r>=1. Extend h periodically from residues modulo M, with
h=0 on multiples of three. For a residue a modulo 3M define

\[
 (L_s h)(a)=\sum_{\substack{k\ge1\\2^ka\equiv s\ (3)}}
       \frac3{2^k}h\left(\frac{2^ka-s}{3}\right).
\]

The summand's h-factor has period P=2M in k. Thus the infinite sum is
exactly the sum over k=1,...,P divided by 1-2^(-P). This is the operator
in `residue_transfer`, and is Tao's Lemma 1.12 in density normalization.

For an actual positive odd unit m let W_h(m) be the sum of h(n)/n over
its actual odd unit predecessors. If H=max h, then

\[
 \left|mW_h(m)-(L_s h)(m)\right|
 \le\frac{H}{m-1/2}.
\]

**Proof.** Each actual summand, after multiplying by m, is
(3/2^k)h(n)/(1-s/(2^k m)). Subtract its homogeneous term, use
1/(1-1/(2m)), and sum 3*H/(4^k*m) over all k>=1. The sum of 4^(-k)
is 1/3. The correction is positive for s=1 and negative for s=-1.
No floating-point limit or height-free transfer is used.

The same separation works at every fixed depth. Set D_d=(3/2)^d-1.
Along a d-step inverse path its endpoint has form
n=R*(m-s*D), with R=2^(sum k_i)/3^d and
D=sum_(j=1)^d 3^(j-1)/2^(k_1+...+k_j)<=D_d.
For m>D_d all intermediate values are positive. If W_(h,d) is the
actual weighted mass of the unit d-generation endpoints, then

\[
 |mW_{h,d}(m)-L_s^d h(m)|
 \le\frac{D_d}{m-D_d}L_s^d h(m)
 \le\frac{3^d H D_d}{m-D_d}.
\]

The first inequality follows term by term from 1/(1-s*D/m), and the
second bounds the total coefficient by the unrestricted geometric
sum 3^d. Determinism of S_s makes the inverse path to an endpoint
unique at a fixed depth, so this counts endpoints without multiplicity.

### 3. No positive finite ternary table gives uniform harmonic reproduction

**EXACT — HUMAN PROOF.** For every h strictly positive on the unit
residues and every d>=1, some unit residue a modulo 3^d M satisfies

\[
 (L_s^d h)(a)<h(a\bmod M).
\]

**Proof.** For each fixed k, the map
b -> 2^(-k)(3b+s) modulo 3M bijects the M child classes with the
admissible parent classes. Summing over a therefore gives

\[
 \sum_{a\bmod3M}(L_s h)(a)=3\sum_{b\bmod M}h(b).
\]

The right side is also the sum of h(a mod M) over parent classes.
All nonunit parent terms vanish. Iterate to get the factor 3^d.
If every unit row were at least its parent weight, equality of finite
sums would force equality at every row.

But at a=-s modulo 3^d M the k=1 branch repeatedly returns -s at
the next lower modulus. Its coefficient is 3/2 at each step. Hence

\[
 (L_s^d h)(-s)\ge(3/2)^d h(-s)>h(-s),
\]

a contradiction. This proof covers every table size, every choice of
positive weights, and every fixed grouping depth, without a grid.

For d=1, choose a deficient row with gap delta>0. The error estimate
above shows that every sufficiently large odd m in that row has
mW_h(m)<=h(m)-delta/2; it suffices that m>=1/2+2H/delta.
That entire progression has divergent reciprocal sum. Thus globally
discarding a finite-reciprocal-mass set of poor targets cannot repair
this uniform inequality, even after removing the old multiples-of-three
ray. An individual fate class might meet that progression sparsely;
no lower bound on that intersection is inferred from residue coverage.
For d>1 the fixed-depth error estimate gives the same conclusion by
taking m>D_d+2*3^d*H*D_d/delta. The one-layer sharper constant is retained
because it makes the mod-9 example especially transparent.

### 4. A precise remaining route for actual positive Collatz fates

For the plus map put K_d=L_+^d 1_units. At a positive odd unit target a,
K_d(a) is the sum of 3^d/2^(k_1+...+k_d) over its valid d-generation
unit inverse paths. Every such path consists of actual positive odd
integers. Its endpoint n is at most a*2^(k_1+...+k_d)/3^d, since each
inverse step subtracts 1/3. Consequently the actual reciprocal mass
of generation d is at least K_d(a)/a.

If a is nonperiodic for S_+, different generations are disjoint: an
endpoint in two generations would force a positive return time at a.
Therefore the explicit sufficient condition

\[
 \sum_{d\ge0}K_d(a)=\infty
\]

would imply divergent harmonic mass of the ancestor set of a, and hence
of any fate class containing it. This is a proved implication with an
**OPEN** premise, not a new lower bound. It avoids repeated counting of
cycle points. It is stated only for plus; the minus affine inequality
runs the other way.

This full coefficient-to-actual-ancestor implication is now kernel-checked
in `Problems.Collatz.FibreGeneration.ancestor_reciprocals_not_summable`.
Its generation comparison uses the actual predecessor bijection and the
concrete infinite coefficient operator. Its counting proof uses extended
nonnegative sums and needs no prior finiteness of actual generation masses.
The series-divergence premise itself is still open.

Every nonempty full plus fate class contains a nonperiodic odd unit:
it contains an odd unit after forward iteration, whose fibre has
infinitely many unit siblings. At most one of these can be periodic,
since a function is injective on its periodic points. Thus there is
no additional existence assumption hidden in the proposed target.

### 5. Polynomial affine loss for negative-map generations

For the minus map, put K_d^-=L_-^d 1_units. At every nonperiodic positive
odd target a, the actual unit-generation mass is at least
K_d^-(a)/(a*(d+1)^(1/6)). On an actual depth-d path the source states are
distinct odd integers at least five. Their exact affine correction is
product_j(1-1/(3*x_j)); its sixth power is at least 1/(d+1).
Thus the stronger-than-unweighted divergence premise
sum_d K_d^-(a)/(d+1)^(1/6)=infinity implies divergent actual ancestor
reciprocal mass. The complete operator identity, path comparison and
ordinary reciprocal-series conclusion are kernel-checked in
`Problems.Collatz.FibreDistortion`; see the
[proof map](../theory/collatz_negative_generation_mass_lean_note.md).

The divergence premise remains open. This does not reinstate uniform
fixed-depth reproduction or establish a termination theorem. Periodic
targets are excluded, and the repeated path at 1 is an exact control
showing why that hypothesis matters. Independent review and advisory
coverage remain pending; the ledger retains its HUMAN PROOF label.

## Open questions

Can the series in Result 4 be shown to diverge at at least one actual
nonperiodic odd unit in every full fate class? Tao's averaged residue
mixing does not by itself control these prescribed integer targets.
The exact modular recurrence and its agreement with Tao identify the
arithmetic object; they do not supply the missing pointwise estimate.
For the minus map, the corresponding sufficient series is the corrected
one in Result 5. No divergence theorem for it is asserted.

## Decision

**PROMOTE** the structural comparison and the all-level finite-weight
obstruction. A finite ternary weight table cannot furnish the proposed
uniform reciprocal-mass production, even with any fixed number of
generations grouped together. The broader fate-specific question remains
open. **PROMOTE** the 23 September polynomial negative affine bound and
the complete conditional criteria for both signs. The nonperiodic-target
series in Results 4 and 5 are the remaining arithmetic questions; this
phase stops without asserting their divergence.

## Publication assessment

Status: `STRUCTURAL`. The geometric fibres and stochastic recurrence
are classical. The project-specific contribution is the precise uniform
weight obstruction and its connection to the actual integer mass error.
No independent priority or paper claim; no Juggler manuscript is changed.

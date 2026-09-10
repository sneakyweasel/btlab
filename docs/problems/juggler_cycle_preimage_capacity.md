# Exact preimage capacity and the missing common-set deficit

Status: **CLOSE** ordinary multiplicity, smooth inverse density, fixed-target
Hall counting, and the fixed-prefix/power-subtraction mechanisms scoped below.
Completed 10 September 2026. An exact deficit for the shared retained set
remains unproved. Elementary guard-filtered packing and a quantitative
joint-prefix bound are retained; no strict deficit or numerical
height/period improvement is obtained.

## Problem

Can a population forced by the cubic-cycle ranks exceed the exact guarded
integer preimage capacity of a proper retained interval?

## Exact statement

Use \(O(x)=\lfloor x^{3/2}\rfloor\), \(E(x)=\lfloor\sqrt{x}\rfloor\),
and chronological return words \(A=OOE\), \(B=OE\). For fully guarded
candidate source sets \(D_A,D_B\), distinguish raw preimage counts from
the sets \(\Gamma_A,\Gamma_B\) of distinct supported targets.

This gate proves exact inverse and collision diagnostics, retains an
explicit fourth-power guard subtraction, and derives the necessary
common-set capacity inequalities. The authorized continuation in Results
9–12 pulls middle joint support back to guarded AA sources, applies the
current cumulative prefix count, and proves the limitations of that
estimate and the specified power deletions. It proves no interval
whose mandatory population exceeds its guarded support. In particular,
closing ordinary counting does not refute a possible stronger inequality
using exact integer support and complete cyclic placement.

## Current literature

**PROJECT-SPECIFIC diagnostics; no external priority claim.** The
[initialized-seam dossier](juggler_cycle_return_seam.md) supplies the
existing infinite guarded family and states the capacity question.
The [cubic dossier](juggler_cycle_cubic_band.md),
[direction changes](juggler_cycle_direction_change.md),
[later returns](juggler_cycle_later_returns.md), and
[negative knowledge](../negative_knowledge.md) delimit the available
rank, grid, and return results.

The rank counts, deterministic-fibre matching argument, and Euclidean
tower decomposition below are direct consequences of existing
machinery, not new cycle theorems. The exact inverse and in-band
multiplicity diagnostics explain the limitations of the proposed
counting shortcut. Results 9–12 additionally use the current
[Paper B](../theory/juggler_parity_discrepancy_note.md), Theorem 3.1 and
Corollaries 4.6 and 4.10, only as cumulative counts on free original
sources. This bounded comparison does not open a paper-merger program
or assume a short-interval or full-AA density theorem.

## Branch budget

- **Target:** a strict guarded-capacity deficit beyond existing spacing
  and grid bounds, on the same retained integer set.
- **Novelty hypothesis:** simultaneous source and target requirements
  remove more candidates than the common ranks permit.
- **Falsifier:** raw multiplicity counts the same target repeatedly,
  inverse-width estimates recover spacing, or a matching argument
  merely restates closure.
- **Already killed by?:** finite local seams and relaxed real-cell
  averaging are closed; this gate addresses global selected populations.
- **Existing machinery:** exact square cells, cubic rank rotation,
  ordered A/B returns, inverse ceilings, and the prior guarded family.
- **Maximum Phase-0 scope:** symbolic inverse, collision, rank and Hall
  proofs; the three existing parameters
  \(u=2^{32}+65,2^{40}+65,2^{64}+65\), with four prescribed boundary
  pairs per parameter. No interval, source, orbit, rank or residue census.
- **Promotion criterion:** an independently established strict deficit
  for a population mandatory in every actual cycle.
- **Stop criterion:** CLOSE ordinary counting if it supplies no such
  deficit. Do not turn repeated candidate pruning into a new cycle search.

**Authorized quantitative continuation (10 September 2026).** The target
is an upper bound on middle joint support below its required rank count.
The novelty hypothesis is a quantitative loss from both A requirements;
the falsifier is a fixed-density or endpoint-error allowance that still
exceeds the population. Existing raw Hall and smooth packing shortcuts
remain closed. Scope: one exact pullback, available prefix estimates,
rank-scale comparison and the two stated power-hole budgets. No new
source, orbit, rank, residue or matching census. Promote only a strict
deficit or stronger cycle restriction; otherwise record the estimate's
precise limitation and stop this mechanism.

## Balanced-ternary formulation

All source values, polynomial margins, root ceilings, cardinalities and
rational bounds are exact integers or rationals with canonical
balanced-ternary representations.

## Why BT may be relevant

No representation advantage is used or claimed.

## Candidate operations / invariants

The registered statement is **J-cycle-preimage-capacity-diagnostics**,
labelled **EXACT — HUMAN PROOF**. This repository tier denotes an
AI-assisted written proof cross-checked by other AI agents. It does not
mean independent human review or Lean verification.

Its components are exact A inverse support, actual B collisions,
distinct-target capacities, and the precise limitations of ordinary
matching and inverse-density comparisons. The continuation is registered
as **J-cycle-joint-prefix-capacity**, in the same written-proof tier.
Its canonical proof is Results 9–12 below; the prefix-count proof remains
owned by Paper B.

## Experiments

The [runner](../../src/research/juggler_sequence/cycle_preimage_capacity.py),
[tests](../../tests/research/juggler_sequence/test_cycle_preimage_capacity.py),
and [record](../../data/research/juggler/cycle_preimage_capacity/summary.json)
use only the three previously selected \(u\) values above. For each, four
symbolically prescribed \((v,j)\) boundary pairs check the B collision
identities and their common-band placement. Formula checks also cover the
exact counts, the explicit A guard-hole diagnostic, and stated scope.
The four pairs use \(v\in\{r^2+2,2r^2-1\}\) and
\(j\in\{1,2\lfloor(v+1)/4\rfloor-1\}\).

    python -m research.juggler_sequence.cycle_preimage_capacity

The finite controls check implementation. The universal statements are
proved below from exact inequalities and counts, without enumerating the
displayed parameter intervals or claiming complete target support.

The continuation in Results 9–12 is analytic and adds no runtime probe
or computed source count. Existing controls check the earlier exact
diagnostics; registration and link tests do not verify the new asymptotic
arguments. Those were reviewed as written proofs by other AI agents.

## Conjectures

No new conjecture file. The actual no-cycle problem remains open.

## Counterexamples

There are arbitrarily many distinct guarded B predecessors of one target,
inside the already surviving numerical band. Consequently raw preimage
multiplicity can exceed distinct target support by an unbounded factor.

Conversely, exact guard holes exist: odd fourth-power sources cannot
follow A or B, and odd ninth-power targets cannot have a guarded A
predecessor. These facts do not imply that a hypothetical selected
interval must contain a hole or suffer a population deficit.

## Formalization

No new Lean theorem is claimed. The new diagnostics are written proofs.
Existing actual-cycle results retain the coverage listed in
[Paper A's formalization map](../theory/juggler_finite_dynamics_formalization.md).
No Paper A or release-copy update is part of this gate.

## Results

**Theorem (J-cycle-preimage-capacity-diagnostics).** Results 1–4 establish
the exact inverse, support-hole and in-band multiplicity statements.
Results 5–8 identify the necessary selected populations and the
limitations of ordinary counting. None constructs or excludes a
complete retained set.

### 1. Candidate sources and distinct target support

In the initialized geometry let \(m<w<z<a<b<t\). Let \(D_A\) be the odd
integers in \([m,a]\) which follow A with odd retained output in \([z,t]\);
let \(D_B\) be the corresponding guarded B sources in \([b,t]\) with
odd output in \([m,w]\). In both definitions impose the required cubic
band and first-return placement of intermediate states. Set
\(\Gamma_A=A(D_A)\), \(\Gamma_B=B(D_B)\), as sets of distinct integers.

For \(J\subseteq[m,w]\), put
\[
N_B(J)=\#\{x\in D_B:B(x)\in J\}.
\]
Every actual retained set satisfies
\[
\#(Y\cap J)\le\#(\Gamma_B\cap J)\le N_B(J).
\tag{PC1}
\]
Multiplicity at one target cannot supply any other target. The analogous
distinct-support inequality holds on A's target range.

### 2. A has at most one integer predecessor at large targets

The prescribed collapse \(A(x)=\lfloor\lfloor x^{3/2}\rfloor^{3/4}\rfloor\)
gives an exact integer inverse threshold. Put
\(K(y)=\lceil\lceil y^{4/3}\rceil^{2/3}\rceil\) for integer \(y\ge1\).
Then \(A(x)\ge y\) if and only if \(x\ge K(y)\), by successively
replacing each floor inequality with its integer ceiling. Hence
\(A(x)=y\) if and only if \(K(y)\le x<K(y+1)\).

If the prescribed word A sends an integer \(x\) to an integer \(y\ge8\),
then
\[
\boxed{x=\lceil y^{8/9}\rceil.}
\tag{PC2}
\]
Thus exact nested square cells and all three source guards decide whether
this sole candidate belongs to \(D_A\); the ceiling alone is insufficient.

To prove uniqueness, write \(h=O(x)\), \(v=O(h)\), \(y=E(v)\).
The lower cells give \(y^8\le x^9\), hence \(x\ge y^{8/9}\).
The upper cells give
\[
h^3<(y+1)^4,\qquad
x^3<(h+1)^2<\bigl((y+1)^{4/3}+1\bigr)^2.
\]
By concavity,
\[
\begin{aligned}
\bigl((y+1)^{4/3}+1\bigr)^{2/3}-y^{8/9}
&<\tfrac89y^{-1/9}+\tfrac23y^{-4/9}\\
&\le\frac{11}{9\,2^{1/3}}<\frac{44}{45}<1.
\end{aligned}
\]
The last comparison uses \(2^{1/3}>5/4\), since \(128>125\). Consequently
\(y^{8/9}\le x<y^{8/9}+1\), which identifies its only possible integer.

In particular, for an integer interval \([p,q]\) with \(p\ge8\),
\[
\#(\Gamma_A\cap[p,q])
\le\#\bigl((2\mathbb Z+1)\cap
[\lceil p^{8/9}\rceil,\lceil q^{8/9}\rceil]\cap[m,a]\bigr).
\tag{PC3}
\]
This discards all guards. For an exact guard subtraction, put
\(L_J=\max(m,K(p))\), \(H_J=\min(a,K(q+1)-1)\).
Let \(N_{\rm odd}(L,H)\) count odd integers in \([L,H]\), and let
\(P_4(L,H)=\#\{c\ge1:c\text{ odd},\ L\le c^4\le H\}\).
Both are zero for an empty interval. The guard holes proved below give
\[
\boxed{\#(\Gamma_A\cap[p,q])
\le N_{\rm odd}(L_J,H_J)-P_4(L_J,H_J).}
\tag{PC3a}
\]
For the whole selected A block this yields the necessary arithmetic bound
\[
\boxed{\alpha\le(a-m)/2+1-P_4(m,a).}
\tag{PC3b}
\]
It strictly improves unfiltered odd-source packing whenever an odd fourth
power is present. No available population bound forces a strict deficit.

There are exact holes. If \(s\ge3\) is odd, then \(x=s^4\) has
\(O(x)=s^6\) odd: it fails B's E guard, and its next O image \(s^9\)
is also odd, so it fails A's final E guard. Similarly, an odd target
\(y=r^9\), \(r\ge3\), has sole possible A source \(x=r^8\).
Its prescribed trace is \(r^8\to r^{12}\to r^{18}\to r^9\);
the final E source is odd, so \(y\notin\Gamma_A\).

This latter hole lies inside the prior family's target band:
its anchors satisfy \(z<r^9<t\) and \(m<r^8<a\). It is a genuine missing
candidate, not proof that the selected Y must contain that integer.
It also ensures \(P_4(m,a)\ge1\), since \(r^8=(r^2)^4\).

### 3. Uniform exact guarded B collisions

Let \(v\ge3\) be odd. For every odd integer \(j\) with
\(1\le j\le(v-1)/2\), define
\[
x_{v,j}=v^4+2j,\quad H_{v,j}=v^6+3v^2j,\quad y_v=v^3.
\]
Then
\[
\boxed{x_{v,j}\xrightarrow O H_{v,j}\xrightarrow E y_v}
\tag{PC4}
\]
is an actual guarded B passage. Its distinct sources all have the same
target, and their number is \(\lfloor(v+1)/4\rfloor\).

Indeed, the exact O-cell margins are
\[
x_{v,j}^3-H_{v,j}^2=3v^4j^2+8j^3>0,
\]
\[
(H_{v,j}+1)^2-x_{v,j}^3
=2v^6+6v^2j+1-3v^4j^2-8j^3
>\tfrac54v^6-v^3>0,
\]
using \(j<v/2\). The E margins are
\[
H_{v,j}-y_v^2=3v^2j>0,\qquad
(y_v+1)^2-H_{v,j}>\tfrac12v^3+1>0.
\]
Odd \(v,j\) make \(x_{v,j},y_v\) odd and \(H_{v,j}\) even.
Counting the odd j gives the stated multiplicity.

### 4. The collisions occur throughout a proper interval of the prior band

Use the existing family, \(r\ge67,\ r\equiv3\pmod {16}\), with
\[
\begin{gathered}
m=r^6+3r^2-3,\quad a=r^8+8,\\
b_-=r^8+4r^4-4r^2+2,\quad b_+=b_-+2,\\
t=r^9+9r-1,\quad w=\lfloor t^{3/4}\rfloor,\quad
M=r^{18}+18r^{10}+54r^2-1.
\end{gathered}
\]
For every odd \(v\) with \(r^2+2\le v\le2r^2-1\), and every j in
Result 3, the entire passage lies in the prescribed band:
\[
\boxed{b_+<x_{v,j}<t<H_{v,j}<M,\qquad m<y_v<w.}
\tag{PC5}
\]
It works for either face, including every previously guarded lift
\(r=u^4+2,\ u\ge2^{32},\ u\equiv65\pmod {2048}\).

For the source lower bound,
\((r^2+2)^4-b_+=8r^6+20r^4+36r^2+12>0\).
For the upper bound, \(x_{v,j}<16r^8+2r^2<r^9<t\).
The targets satisfy
\((r^2+2)^3>m\) and \(y_v<8r^6<w\), since
\(w>r^{27/4}-1>8r^6\). Finally
\[
r^{12}<H_{v,j}<64r^{12}+12r^6<r^{18}<M.
\]
Here \(r^{12}>t\); also \(H_{v,j}>y_v^2>m^2\). Thus the interior
is above the cut and outside the retained interval until its return.

Let
\[
J_r=[(r^2+2)^3,(2r^2-1)^3]\subset(m,w).
\]
There are exactly \(n=(r^2-1)/2\) exhibited cube targets. Sources for
different v are distinct, since their blocks lie below \(v^4+v\),
whereas the next block starts above \((v+2)^4\).
Writing \(v_i=r^2+2+2i\), \(0\le i<n\), gives
\[
\left\lfloor\frac{v_i+1}{4}\right\rfloor
=\frac{r^2+3}{4}+\left\lfloor\frac i2\right\rfloor.
\]
As n is even, the exact exhibited source count is
\[
\boxed{\sum_{i=0}^{n-1}\left\lfloor\frac{v_i+1}{4}\right\rfloor
=\frac{3r^4-2r^2-1}{16}.}
\tag{PC6}
\]
Hence \(\#(\Gamma_B\cap J_r)\ge(r^2-1)/2\) and
\(N_B(J_r)\ge(3r^4-2r^2-1)/16\). These are partial lower bounds,
not complete counts of all candidates or supported targets.

More decisively, the singleton \(J=\{(r^2+2)^3\}\) satisfies
\[
\#(\Gamma_B\cap J)=1,\qquad N_B(J)\ge(r^2+3)/4.
\tag{PC7}
\]
The ratio is unbounded in this same numerical band. The singleton is
not asserted to contain a selected cycle state. The displayed cube
support does not verify its targets' A-source guards.

### 5. Exact rank populations and the common-set intersections

Let \(Y=\{y_0<\cdots<y_{\alpha+\beta-1}\}\) be a hypothetical actual
retained set at the existing large-minimum cutoff, with
\(\alpha>\beta>0\), \(\gcd(\alpha,\beta)=1\). The known rotation gives
\[
A(y_i)=y_{i+\beta}\ (i<\alpha),\qquad
B(y_{\alpha+j})=y_j\ (j<\beta).
\tag{PC8}
\]
Here \(m=y_0,w=y_{\beta-1},z=y_\beta,a=y_{\alpha-1},
b=y_\alpha,t=y_{\alpha+\beta-1}\). Therefore
\[
\boxed{\begin{aligned}
\beta&\le\#(D_A\cap\Gamma_B\cap[m,w]),\\
\alpha-\beta&\le\#(D_A\cap\Gamma_A\cap[z,a]),\\
\beta&\le\#(D_B\cap\Gamma_A\cap[b,t]).
\end{aligned}}
\tag{PC9}
\]
The selected low, middle and high blocks have exactly those populations.
Each is simultaneously a source block and a target block for the same Y.

For any rank interval \([y_j,y_k]\), the population is \(k-j+1\).
Targets of rank \(r\ge\beta\) have A predecessor rank \(r-\beta\);
targets of rank \(r<\beta\) have B predecessor rank \(\alpha+r\).
These formulas yield the corresponding subinterval versions of (PC9).
No independent selection of fresh predecessors is allowed.

### 6. The precise Hall and density limitations

For a fixed finite target set Z, with predecessors chosen freely from
\(D_A\cup D_B\), existence of distinct predecessors is equivalent to
each target having a nonempty permissible fibre. Distinct targets'
fibres are disjoint because the map is deterministic on disjoint
source branches. Choosing one element in each nonempty fibre proves
sufficiency; necessity is immediate. Every ordinary Hall inequality
then follows from these singleton conditions.

This does not solve the actual problem: the chosen predecessors must
be exactly the same Y as the targets, in their required rank positions.
On a fixed Y, full guarded closure and injectivity construct a return
permutation; requiring its prescribed primitive matching and first-return
placement constructs an actual cycle. Writing these conditions is not
a new obstruction. Repeated exhaustive pruning would be a cycle search.

The inverse-width bound also has a precise limitation. For selected
A targets \([y_{j+\beta},y_{k+\beta}]\), uniqueness in Result 2 identifies
their inverse endpoints as \(y_j,y_k\). Discarding guards in (PC3) gives
\[
k-j+1\le (y_k-y_j)/2+1,
\]
exactly the old odd-source spacing inequality. The corresponding B
predecessor ranks are \(\alpha+j,\ldots,\alpha+k\); a count using those
selected endpoint intervals gives their spacing inequality as well.
A continuous containing inverse interval can only weaken that bound.

Likewise the ideal power map preserves the logarithmic rank measure:
\(d(\log\log x^p)=d(\log\log x)\) for \(x>1,p>0\).
A smooth inverse density by itself transports packing rather than
proving an arithmetic deficit. Exact missing support, such as Result 2,
can strengthen these bounds; no uniform shortage is proved here.

### 7. Mandatory grid counts and known Euclidean towers

If existing grid results give \(\ell_i\le y_i\le u_i\), then for a
numerical interval \(J=[c,d]\),
\[
\#\{i:\ell_i\ge c,\ u_i\le d\}\le\#(Y\cap J).
\tag{PC10}
\]
Only windows wholly inside J give this mandatory population. Windows
merely intersecting J do not. A nontrivial interval-packing condition
before Y is chosen requires distinct candidate witnesses; once an
actual Y is supplied, its distinct selected states already witness it.
No grid lower count exceeding a capacity in (PC9) is obtained here.

The same-set rank intersections also reconstruct known induction.
Write \(\alpha=q\beta+r_0\), \(0\le r_0<\beta\). Starting at rank
\(j<\beta\), A adds \(\beta\) until the B-source block is reached:
there are \(q+1\) A steps if \(j<r_0\), and q if \(j\ge r_0\).
B then returns the rank to
\[
j\longmapsto
\begin{cases}j+\beta-r_0,&j<r_0,\\j-r_0,&j\ge r_0.\end{cases}
\tag{PC11}
\]
Thus the return words are \(A^{q+1}B,A^qB\), with rotation
\(-r_0\) modulo \(\beta\). Their internal A-source population is
\(\alpha-\beta=r_0q+(\beta-r_0)(q-1)\).
If \(r_0=0\), all base ranks are fixed, so primitivity forces
\(\beta=1\); no extra transfer is supplied at that terminal step.

These are exactly the existing Euclidean towers, including the current
\(A^3B/A^2B\) case. At the integer-candidate level the support
intersections can remove states through genuine extra guard conditions.
Merely restating or iterating the finite-depth rank chains does not,
however, produce a depth-uniform arithmetic invariant or a deficit.

### 8. Scope of the diagnostic conclusion

The collision family disproves treating raw multiplicity as distinct
matching capacity. The Hall and inverse-width arguments identify
specific automatic or already known conditions. They do not prove that
all support capacities are sufficient, that every target is supported,
or that an actual retained set exists. The A holes show why blanket
surjectivity would also be false. The guard-filtered packing improvement
(PC3a–b) is retained; it yields no strict deficit or numerical bound update.

The exact shared-source/support intersections in (PC9) remain the
arithmetic content missing from these shortcuts. None of the partial
support families satisfies or refutes the complete cyclic requirement.

### 9. Exact joint pullback and an available quantitative bound

**Theorem (J-cycle-joint-prefix-capacity).** Results 9–12 record the
authorized quantitative continuation of this gate. They use the current
[Paper B](../theory/juggler_parity_discrepancy_note.md), Corollary 4.10,
as an AI-assisted written proof dependency. They prove a necessary
capacity bound and limitations of the specified estimates, not a deficit.

Keep the actual cubic-cycle anchors of Result 5, with \(m\ge8\),
\(A(m)=z\le a\), and \(A(a)=t>a\). Set
\[
H=K(a+1)-1,\qquad
\mathcal X_{AA}=\{x\in[m,H]\cap\mathbb Z:x\in D_A,\ A(x)\in D_A\}.
\]
The exact threshold identity gives \(m\le H<a\). There is a bijection
\[
\boxed{A:\mathcal X_{AA}\longrightarrow D_A\cap\Gamma_A\cap[z,a].}
\tag{PC12}
\]
Indeed monotonicity puts every source's first output in \([z,a]\).
Conversely, every target in the intersection has a predecessor in
\(D_A\), whose output at most a forces its source at most H. Result 2
gives uniqueness, since these targets are at least 8.

Both passages retain all the guards and band conditions in \(D_A\).
There are six operations \(OOEOOE\) and an odd final output, so the
seven consecutive state parities are \(OOEOOEO\). The intermediate
A output lies in the retained section \([m,t]\): these are two A
returns, not one AA first return. A free candidate need not belong to Y.
The required sources in the actual Y have ranks
\(0,\ldots,\alpha-\beta-1\); hence \(\alpha-\beta\le\#\mathcal X_{AA}\).

For an integer target interval \(J=[r,s]\subseteq[z,a]\), its exact
source interval is
\[
I_J=[\ell,h],\quad
\ell=\max(m,K(r)),\qquad h=\min(a,K(s+1)-1).
\]
The bijection restricts to the joint capacity inside J and its fully
guarded AA sources in \(I_J\). Each such source has prefix \(OOEOO\).
Write \(F_5(N)=\#\{1\le n\le N:\operatorname{word}_5(n)=OOEOO\}\).
Paper B gives \(F_5(N)=N/32+O(N^{47/48})\). Fix \(C_5>0\) with
\(|F_5(N)-N/32|\le C_5N^{47/48}\) for all integers \(N\ge1\),
enlarging it to cover small N if necessary, and set \(F_5(0)=0\).
Subtract the cumulative estimates at h and \(\ell-1\):
\[
\boxed{\#(D_A\cap\Gamma_A\cap J)
\le U_5(\ell,h):=\frac{h-\ell+1}{32}
+C_5\bigl(h^{47/48}+(\ell-1)^{47/48}\bigr).}
\tag{PC13}
\]
This applies when \(I_J\) is nonempty; an empty inverse interval has
capacity zero. In particular,
\[
\boxed{\alpha-\beta\le U_5(m,H).}
\tag{PC14}
\]
The constant exists by the cited theorem; no numerical value or effective
cutoff is certified here. This counts a free source superset, so it makes
no density assertion about the selected sparse set Y. The initial O
already imposes oddness: the coefficient is \(1/32\) among all integers.
The unproved full seven-parity density \(1/128\) is not used.

When \(h^{47/48}=o(h-\ell)\), (PC13) has leading term one sixteenth
of ordinary odd-source packing. Otherwise it need not improve that
packing; one may take the minimum with (PC3a). This is a quantitative
necessary inequality, but no strict deficit or numerical period/height
improvement follows from the comparison obtained here.

### 10. A uniform limitation of cumulative endpoint errors

Consider any sequence of candidate parameter tuples with \(m\to\infty\)
and \(L=o(m^{47/48})\). For every nonempty integer source interval
\([\ell,h]\) with \(\ell\ge m\),
\[
U_5(\ell,h)\ge C_5m^{47/48}>L
\tag{PC15}
\]
eventually, uniformly over all these intervals. Every mandatory selected
population is at most L. Thus this particular bound cannot certify a
deficit on any such interval, regardless of its length or location.
If exact odd-source packing already passes, taking its minimum with
\(U_5\) supplies no new rejection in this regime.

The shorter available prefixes have different error exponents:

| Prefix | Current Paper B result | Cumulative main term | Positive error allowance |
|---|---|---|---|
| OO | Theorem 3.1 | \(N/4\) | \(C_2N^{5/6}\) |
| OOEO | Corollary 4.6, the corresponding sign class | \(N/16\) | \(C_4N^{23/24}\log^3(2N)\) |
| OOEOO | Corollary 4.10 | \(N/32\) | \(C_5N^{47/48}\) |

Choose all constants positive and fixed. Subtraction gives an upper
expression containing the corresponding positive error at h. Therefore
the stronger regime
\[
\boxed{L=o(m^{5/6})}
\tag{PC16}
\]
makes all three displayed endpoint-subtraction bounds exceed L on every
nonempty source interval, uniformly. The \(47/48\) condition alone
must not be used to assert failure of the shorter-prefix estimates.

These statements lower-bound the *upper expressions*, not the actual
discrepancy or true support size. Errors may cancel; the cumulative
theorems do not certify that cancellation. No estimate with error
\(O((h-\ell)^{47/48})\), or other length-scaled replacement, is imported
from Paper B. Empty intervals and genuinely sharper arithmetic or
localized estimates are outside this limitation.

### 11. A fixed positive whole-block allowance is also too large

There is a separate limitation even if the error could be removed.
Suppose along a hypothetical sequence of actual cubic-cycle parameters
\(m,L\to\infty\) one additionally has \(0<\Lambda\le C_0/L\),
where \(\Lambda=o\log3-L\log2\) and \(C_0\) is fixed. This extra
surplus hypothesis is not known for every actual cycle; the
[period-upper-bound dossier](juggler_cycle_period_upper_bound.md)
leaves it open.

Put \(T=\log3\), \(\vartheta=\log2/\log3\). The rank identities give
\[
\alpha=2o-L,\quad \beta=2L-3o,\quad
\alpha-\beta=(5\vartheta-3)L+5\Lambda/T.
\tag{PC17}
\]
Here \(5\vartheta-3>0\), because \(2^5>3^3\). The retained set consists
of the first \(\alpha+\beta\) original sorted states, so its ranks agree
with those used by the grid. Apply that grid at rank \(\alpha-1\) and
at rank 1 to obtain
\[
\log\frac{\log a}{\log m}=\frac{(\alpha-1)T}{L}+O(\Lambda),
\qquad
L\le\frac{T+C_0}{\log(\log(m+2)/\log m)}=O_{C_0}(m\log m).
\tag{PC18}
\]
For the second bound, the first odd state after the minimum is at least \(m+2\); its
grid coordinate is at most \((T+C_0)/L\). The first bound and (PC17)
imply \(a=m^{4/3+o(1)}\). Concavity bounds both ceiling errors in K,
giving \(K(y)=y^{8/9}+O(1)\). Consequently
\[
H=m^{32/27+o(1)},\qquad \frac{H-m+1}{L}\longrightarrow\infty.
\tag{PC19}
\]
For example, eventually \(H\ge m^{1+5/54}\), which together with
\(L=O(m\log m)\) proves the second assertion.

Any proposed whole-middle upper bound of the form
\(\rho(H-m+1)+E\), with fixed \(\rho>0\) and \(E\ge0\), thus
eventually exceeds L, even when E is zero. Such a bound cannot fall
below the required population \(\alpha-\beta\). This does not assert
a positive density for the true joint support, nor existence of a
cycle sequence satisfying the extra hypothesis.

For the illustrative scale \(m\asymp L^2/(\log L)^p\), with fixed real
p and \(\Lambda=O(1/L)\), (PC16) holds and the sharper relative estimate
\(a\sim m^{4/3}\) follows since \(\log m=o(L)\). Then
\[
H\asymp\frac{L^{64/27}}{(\log L)^{32p/27}},\qquad
\frac HL\longrightarrow\infty.
\tag{PC20}
\]
A varying coefficient would need to be at most order
\(L/H\asymp L^{-37/27}(\log L)^{32p/27}\) even before the error
could allow a deficit. This is a scale comparison, not a construction
of tuples passing every known cycle constraint.

### 12. Structured fourth-power deletions cannot be counted twice

In the odd source interval \([m,H]\), define
\[
S=\{x:x=c^4\text{ for odd }c\},\qquad
Q=\{x:A(x)=d^4\text{ for odd }d\},
\]
with both sets restricted to that interval. Let \(P_k(u,v)\) count odd
kth powers in \([u,v]\). Unique A predecessors and monotonicity give
\(\#Q\le P_4(A(m),A(H))\). Moreover \(A(c^{32})=c^{36}\), so
\(\#(S\cap Q)\ge P_{32}(m,H)\). Therefore
\[
\#(S\cup Q)\le P_4(m,H)+P_4(A(m),A(H))-P_{32}(m,H).
\tag{PC21}
\]
These are upper budgets on possible exclusions. They cannot be
subtracted as guaranteed deletions from a candidate upper bound.

Every member of S already fails the third guard of \(OOEOO\), by
\(c^4\to c^6\to c^9\) with odd \(c^9\). Thus its removal is already
included in \(F_5\); subtracting \(P_4(m,H)\) again is invalid.
Among sources that pass the prefix, membership in Q forces the second
A passage's final E guard to fail. These possible new deletions number
at most
\[
P_4(A(m),A(H))-P_{32}(m,H)\le\tfrac12H^{9/32}+1,
\tag{PC22}
\]
since the 32nd-power sources already failed the prefix and
\(A(H)\le H^{9/8}\). No positive uniform lower count of these extra
deletions is proved.

Even the total budget satisfies
\[
\#(S\cup Q)\le\tfrac12H^{1/4}+\tfrac12H^{9/32}+2=o(H).
\tag{PC23}
\]
When \(H/m\to\infty\), subtracting at most this budget from a bound
with fixed positive leading term \(\rho H+o(H)\) cannot remove that
leading term. On \(H\asymp m^{32/27}\), the two power scales are
\(m^{8/27}\) and \(m^{1/3}\). This closes this specified pair of
power-subtraction mechanisms in the whole-block comparison; it does
not close every possible arithmetic support restriction.

## Open questions

It remains unproved whether some interval's mandatory selected
population exceeds its exact common-source/support capacity after all
cycle constraints are imposed. The case \(M\ge m^3\) remains separate.

## Decision

**CLOSE** ordinary multiplicity, smooth inverse density and fixed-target
Hall counting as routes to a new obstruction. The authorized continuation
also closes the displayed cumulative-prefix bounds as interval-deficit
certificates in (PC15–16), and fixed positive whole-block allowances plus
the stated fourth-power deletions in the conditional regime (PC18–19).
The necessary quantitative bound (PC14) is retained. These scoped
limitations do not close or refute an exact shared-support deficit
theorem. No further local prefix or capacity census is authorized by
this conclusion.

Exactly one remaining question: **can the common retained set force a
strict interval deficit in one of (PC9), beyond the already established
spacing, grid and Euclidean-rank constraints, with an arithmetic bound
small enough to avoid the quantified limitations (PC15–23)?** This is
unresolved; rephrasing the common-set condition or assuming a fixed
positive density does not answer it. No follow-on gate is launched here.

## Publication assessment

Status: **STRUCTURAL**. Exact scoped written diagnostics, with
AI-assisted review and fixed implementation controls. Independent human
review and Lean verification remain outstanding. No numerical
height/period improvement, descent or no-cycle theorem is claimed. Paper A and its
release copies, certified floor \(350000000\), and period bound
\(780239\) are unchanged by this gate.

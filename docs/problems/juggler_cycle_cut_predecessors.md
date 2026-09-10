# Exact cut predecessors: thin alignment and a two-sign family

Status: **CLOSE** the predecessor-only mixed-loss sign obstruction.
Completed 10 September 2026. No actual cycle or new cycle bound is obtained.
This dossier is the canonical written source for this gate.

## Problem

Do simultaneous exact odd O-predecessors of both terminal cut states
remove the harmful mixed-cell configurations left by the previous gates?

## Exact statement

In an actual primitive cubic-band cycle the common terminal prefix ends
in O. Thus both cut states \(h,s\) must be images of odd integer sources.
The [weighted-remainder gate](juggler_cycle_weighted_remainders.md) identified
this condition as absent from the earlier
[local joint-cell family](juggler_cycle_terminal_joint_cells.md).

We impose both predecessor cells, every guard along the displayed mixed
paths, and the surviving smooth height inequalities. The results are a
necessary thin-alignment condition for nonpositive mixed loss, a positive
loss theorem for cube minima, and an infinite integer family with both
signs despite both predecessors. Complete periodicity, adjacent rank
selection and shared terminal \(P/Q\) paths are not supplied by the family.

## Current literature

**PROJECT-SPECIFIC internal extension; no external priority claim.**
Prerequisites are [Paper A](../theory/juggler_finite_dynamics_note.md), the
two preceding dossiers, and [negative knowledge](../negative_knowledge.md).
The lower OOE family comes from the
[exact-remainder transport gate](juggler_cycle_remainder_transport.md).
All cells needed here are proved again below so this dossier owns the
new result. No external theorem or parity-distribution heuristic is used.

## Branch budget

- **Target:** determine whether both exact odd predecessors constrain the
  mixed loss enough to remove the harmful sign.
- **Novelty hypothesis:** the sparse integer O-image lattice excludes the
  previously permitted cell faces.
- **Falsifier:** a symbolic guarded family survives both predecessor cells
  and has both mixed-loss signs.
- **Already killed by?:** independent local cells, residue summaries and
  real-cell averaging are closed; this tests the missing exact integer
  predecessors, not those relaxations.
- **Existing machinery:** exact square cells, rank rotation, terminal
  factorization, original OOE/OE return section and transported word loss.
- **Maximum Phase-0 scope:** symbolic families and fixed exact controls
  \(r=67,83,2^{32}+3\); no source, orbit, rank or floor census.
- **Promotion criterion:** a new necessary restriction on actual cycles.
- **Stop criterion:** CLOSE the predecessor-only sign obstruction if an
  infinite family survives; identify the precise remaining joint condition.

## Balanced-ternary formulation

Every displayed source, remainder, polynomial certificate and rational
coefficient bound is exact and has a balanced-ternary representation.

## Why BT may be relevant

No representation advantage is used or claimed.

## Candidate operations / invariants

The exact O-predecessor candidate for an integer target \(z>1\) is
\(A(z)=\lceil\sqrt[3]{z^2}\rceil\). It must be odd and obey
\(A(z)^3<(z+1)^2\). There is at most one integer predecessor because
\((n+1)^{3/2}-n^{3/2}>1\) for \(n\ge1\).
The new result tracks how that absolute lattice condition restricts
\(\Delta=s^{3/4}-h^{3/4}-(q-t)\).

The two registered statements have label **EXACT — HUMAN PROOF**:
J-cycle-cut-predecessor-alignment and J-cycle-cut-predecessor-two-signs.
This is the repository tier for AI-assisted written proofs, cross-checked
by other AI agents. It does not mean independent human review or Lean.

## Experiments

The [runner](../../src/research/juggler_sequence/cycle_cut_predecessors.py),
[tests](../../tests/research/juggler_sequence/test_cycle_cut_predecessors.py),
and [record](../../data/research/juggler/cycle_cut_predecessors/summary.json)
use only \(r=67,83,2^{32}+3\). All eight distinct actual edges are checked
at each parameter, using integer square roots and exact powers.
The last minimum exceeds \(2^{192}\), activating both published DC/LR
cutoffs. The record verifies the exact predecessor ceilings, shared
anchors, opposite sign certificates, and height margins.

    python -m research.juggler_sequence.cycle_cut_predecessors

The probe also supplies 25 rational coefficient-dominance certificates
valid for every \(r\ge67\). These finite coefficient comparisons prove
positivity on an infinite parameter ray; they are not a parameter scan.
The universal family depends on the polynomial and analytic proofs below,
not on the three fixed evaluations.

## Conjectures

No new conjecture file. Global no-cycle and full cyclic matching remain open.

## Counterexamples

Result 4 refutes a universal sign from simultaneous predecessor and mixed
cells, even when all displayed guards and current smooth height conditions
hold. The same \(m,h,M,t,q\) admits both signs when the upper odd predecessor
is moved by two. The family is not asserted to extend to a cycle or the
complete original return seam. The finite regressions are linked above.

## Formalization

No new Lean theorem is claimed. Existing cubic order and return estimates
remain as recorded in
[Paper A's formalization map](../theory/juggler_finite_dynamics_formalization.md).
The new alignment theorem and family are written proofs only.

## Results

### 1. Exact hypotheses and loss decomposition

Use \(O(x)=\lfloor x^{3/2}\rfloor\), \(E(x)=\lfloor\sqrt x\rfloor\).
Suppose the displayed integer paths have all their actual source guards:

\[
a\xrightarrow O h\xrightarrow O M\xrightarrow E t,
\qquad
b\xrightarrow O s\xrightarrow E m\xrightarrow O q,
\]

with \(a<b\) odd, \(h,m,t,q\) odd, \(s,M\) even, and
\(h<m^2<s\), \(M<m^3\), \(m>1\). In a genuine cycle the relevant
states are also at least \(m\); the first two results below do not
need that additional lower bound.

The exact OE root collapse gives

\[
t=\lfloor h^{3/4}\rfloor.
\]

Write

\[
\epsilon_t=h^{3/4}-t\in[0,1),\qquad
\epsilon_q=m^{3/2}-q\in[0,1),
\]

and define the mixed signed loss

\[
\Delta=s^{3/4}-h^{3/4}-(q-t)
       =\bigl(s^{3/4}-m^{3/2}\bigr)+\epsilon_q-\epsilon_t.
\tag{CP1}
\]

No full periodicity or terminal P/Q closure is assumed unless explicitly
stated. In particular, constructing these paths is not constructing a cycle.

### 2. Nonpositive loss requires a unique, closely aligned odd predecessor

**Theorem.** If \(\Delta\le0\), then

\[
q<s^{3/4}<q+1,\qquad
\lfloor s^{3/4}\rfloor=q.
\tag{CP2}
\]

If also \(m\ge8\), then

\[
0<b-m^{4/3}<H(m)<\frac{91}{108}<1,
\tag{CP3}
\]

where

\[
H(m)=\frac89m^{-1/6}+\frac23m^{-2/3}+\frac8{27}m^{-5/3}.
\]

Consequently \(b=\lceil m^{4/3}\rceil\), this unique ceiling is odd,
and its distance above \(m^{4/3}\) is \(O(m^{-1/6})\). In particular,
a cube minimum or an even ceiling is incompatible with \(\Delta\le0\).
The condition is necessary, not sufficient for nonpositive loss.

**Proof.** Since \(s>m^2\), one has
\(s^{3/4}>m^{3/2}\ge q\). On the other hand, (CP1) gives

\[
s^{3/4}-q=\Delta+\epsilon_t<1,
\]

proving (CP2). In particular,

\[
s<(m^{3/2}+1)^{4/3}.
\]

For \(A=m^{3/2}\), integrate the increasing derivative of \(A^{4/3}\)
over an interval of length one, then use concavity of the cube root:

\[
(A+1)^{4/3}-A^{4/3}
<\frac43(A+1)^{1/3}
\le\frac43\sqrt m+\frac4{9m}.
\]

Thus the exact even-source remainder obeys the sharper face restriction

\[
0<R_s:=s-m^2<\frac43\sqrt m+\frac4{9m}.
\tag{CP4}
\]

The O cell at \(b\) gives \(b^{3/2}<s+1\), while \(s>m^2\)
gives \(b>m^{4/3}\). By concavity of the power \(2/3\),

\[
\begin{aligned}
b-m^{4/3}
&<(s+1)^{2/3}-(m^2)^{2/3}\\
&\le\frac23m^{-2/3}(R_s+1)<H(m).
\end{aligned}
\]

For \(m\ge8\), use
\(m^{-1/6}\le1/\sqrt2<3/4\),
\(m^{-2/3}\le1/4\), and \(m^{-5/3}\le1/32\). These give
\(H(m)<2/3+1/6+1/108=91/108\).
An integer strictly between \(m^{4/3}\) and \(m^{4/3}+1\) must be
its ceiling; if the real endpoint is already integral there is no such
integer. This proves all assertions.

An exact endpoint interpretation of (CP2) is

\[
F_{OE}(s)=F_{EO}(s)=q,
\qquad F_{OOE}(b)=F_{OEO}(b)=q.
\tag{CP5}
\]

The first O at the even state \(s\) is off-domain. Equation (CP5)
does not claim that the OOE alternative has actual guards. It identifies
the required equality of two prescribed endpoints, rather than providing
a forbidden second actual cycle return.

This restriction uses the exact odd predecessor of \(s\). It remains
valid with the additional predecessor of \(h\), but does not derive a
separate benefit from that additional edge.

### 3. A quantitative positive-loss theorem for cube minima

**Theorem.** If \(m=c^3\), with odd integer \(c\ge3\), then the
hypotheses of Result 1 imply

\[
\Delta>2\sqrt c-1>0.
\tag{CP6}
\]

**Proof.** Because \(s=O(b)>m^2=c^6=O(c^4)\), monotonicity and
oddness of \(b,c^4\) give \(b\ge c^4+2\). The exact first permitted
odd source has

\[
O(c^4+2)=c^6+3c^2.
\]

Indeed, the difference of its radicand and the proposed lower square is
\(3c^4+8>0\), while the upper-square difference is
\(2c^6-3c^4+6c^2-7>0\). Hence \(R_s\ge3c^2\).

The E cell at \(s\) gives \(s<(m+1)^2\). The decreasing derivative
of the power \(3/4\), together with (CP1), yields

\[
\Delta>
\frac{3R_s}{4\sqrt{m+1}}-1
\ge\frac{9c^2}{4\sqrt{c^3+1}}-1.
\]

Finally, \(9c^2/(4\sqrt{c^3+1})>2\sqrt c\) is equivalent after
squaring to \(17c^3>64\), valid already for \(c\ge2\).
This proves (CP6). Positive mixed loss alone does not contradict a cycle;
its role in the complete weighted P/Q comparison remains uncontrolled.


### 4. An infinite two-face family with both predecessors

#### 4.1. Family and conclusions

For every integer \(r\ge67\) with \(r\equiv3\pmod {16}\), set

\[
\begin{aligned}
a&=r^8+8, & h&=r^{12}+12r^4,\\
M&=r^{18}+18r^{10}+54r^2-1,
&t&=r^9+9r-1,\\
b_-&=r^8+4r^4-4r^2+2, & b_+&=b_-+2,\\
m&=r^6+3r^2-3, & q&=(8r^9+36r^5-36r^3+27r-1)/8,\\
s_-&=m^2+6r^2-1, &s_+&=s_-+3r^4+5.
\end{aligned}
\]

Then all the following are exact, genuine Juggler edges with the indicated source guards:

\[
a\mathrel{\mathop\longrightarrow^O}h
 \mathrel{\mathop\longrightarrow^O}M
 \mathrel{\mathop\longrightarrow^E}t,
\qquad
b_\pm\mathrel{\mathop\longrightarrow^O}s_\pm
 \mathrel{\mathop\longrightarrow^E}m
 \mathrel{\mathop\longrightarrow^O}q.
\]

Their complete numerical ordering is

\[
\boxed{m<a<b_-<b_+<t<q<h<m^2<s_-<s_+<M<m^3.}
\]

The states \(a,b_-,b_+,h,m,t,q\) are odd, and \(M,s_-,s_+\) are even. Moreover,

\[
\boxed{m^3-M>2m^2,\qquad
\Delta(h,s_-)<-3/4,\qquad
\Delta(h,s_+)>2r-1>r.}
\]

Thus even the same \((m,h,M,t,q)\), together with exact odd O predecessors of both mixed sources, permits either sign. These are open guarded passages: the ordering does not assert that these are all the states between the extrema, that \(h,s_\pm\) are adjacent in a complete cycle, or that the two passages extend to a common closed P/Q pair.

#### 4.2. Integrality and parity

The parity of every displayed integer except \(q\) follows directly from odd \(r\). For \(r=16j+3\), write

\[
q=r^9+\frac92(r^5-r^3)+\frac{27r-1}{8}.
\]

Here \(r^5-r^3=r^3(r^2-1)\) is divisible by 8, so the middle term is divisible by 4. The last term is \(54j+10\), an even integer. Therefore \(q\) is an odd integer. This verifies the actual O/E guards at every shown edge, not merely guards for a prescribed threshold map.

#### 4.3. Exact square-cell certificates

For a proposed edge \(n\mapsto y\), put \(N=n^3\) for O and \(N=n\) for E. Strict positivity of both \(N-y^2\) and \((y+1)^2-N\) proves the exact floor cell. In this family these differences are:

| Edge | \(N-y^2\) | \((y+1)^2-N\) |
|---|---|---|
| \(a\to h\) | \(48r^8+512\) | \(2r^{12}-48r^8+24r^4-511\) |
| \(h\to M\) | \(2r^{18}-216r^{12}+36r^{10}-2916r^4+108r^2-1\) | \(216r^{12}+2916r^4\) |
| \(M\to t\) | \(2r^9-27r^2+18r-2\) | \(27r^2+1\) |
| \(b_-\to s_-\) | \(12r^{10}-21r^8+56r^6-144r^4+144r^2-56\) | \(2r^{12}-12r^{10}+33r^8-68r^6+162r^4-168r^2+73\) |
| \(b_+\to s_+\) | \(2r^{12}-12r^8-4r^6-72r^4+120r^2-105\) | \(24r^8-8r^6+96r^4-144r^2+132\) |
| \(s_-\to m\) | \(6r^2-1\) | \(2r^6-4\) |
| \(s_+\to m\) | \(3r^4+6r^2+4\) | \(2r^6-3r^4-9\) |

For the last O edge, the integer numerators are

\[
\begin{aligned}
64(m^3-q^2)={}&16r^9-864r^8+216r^6+72r^5-3240r^4\\
 &-72r^3+4455r^2+54r-1729,\\
64((q+1)^2-m^3)={}&112r^9+864r^8-216r^6+504r^5+3240r^4\\
 &-504r^3-4455r^2+378r+1777.
\end{aligned}
\]

Here is a uniform elementary positivity certificate, which also applies to the polynomials below. If \(P(r)=Ar^d+\sum_{j<d}p_jr^j\), \(A>0\), then for \(r\ge67\),

\[
 P(r)/r^d\ge A-B(P),\qquad
 B(P)=\sum_{p_j<0}|p_j|67^{j-d}.
\]

For every polynomial in the table and below, \(B(P)<A/2\), with the single exception of \(64(m^3-q^2)\). For that exception,

\[
B(P)=864/67+3240/67^5+72/67^6+1729/67^9<13<16=A.
\]

These are finite rational coefficient comparisons, proving positivity throughout the infinite parameter domain. They are reproduced by the canonical probe's coefficient certificates; no parameter census is involved. The known \(a,h,M,t\) block also appears in the exact-remainder transport dossier linked above, but its full cell certificates have been included here.

#### 4.4. Ordering and height margin

The new nontrivial differences, in addition to the positive cell differences above, are

\[
\begin{aligned}
a-m&=r^8-r^6-3r^2+11,\\
b_--a&=4r^4-4r^2-6,\\
t-b_+&=r^9-r^8-4r^4+4r^2+9r-5,\\
8(q-t)&=36r^5-36r^3-45r+7,\\
8(h-q)&=8r^{12}-8r^9-36r^5+96r^4+36r^3-27r+1,\\
m^2-h&=6r^8-6r^6-3r^4-18r^2+9,\\
M-s_+&=r^{18}-r^{12}+18r^{10}-6r^8+6r^6-12r^4+66r^2-14.
\end{aligned}
\]

All are positive by the coefficient bound in Result 4.3. The omitted adjacent differences \(b_+-b_-=2\), \(s_--m^2=6r^2-1\), and \(s_+-s_-=3r^4+5\) are immediate. Finally,

\[
\begin{aligned}
m^3-M-2m^2={}&9r^{14}-11r^{12}+9r^{10}-66r^8\\
 &+66r^6-99r^4+63r^2-44>0.
\end{aligned}
\]

This proves both \(M<m^3\) and the claimed margin. In particular these families lie below the previously excluded upper height strips: their deficit exceeds \(2m^2\), hence exceeds \(m^{15/8}\), \(\tfrac12m^{253/128}\), and \(\tfrac12m^\theta\) for

\[
\theta=381/128-3^{41}/2^{65}<2.
\]

The DC/LR assertions are used only in their established scale domains. For sufficiently large members, \(m\ge2^{128}\) and both domains apply. Height feasibility is not cyclic placement.

#### 4.5. Negative sign with the lower predecessor

Put \(e_h=h^{3/4}-t\). Concavity gives

\[
h^{3/4}=r^9(1+12/r^8)^{3/4}<r^9+9r=t+1,
\]

so \(e_h<1\). The exact square comparison

\[
64\bigl(M-(t+7/8)^2\bigr)
=16r^9-1728r^2+144r-65>0
\]

and \(h^{3/4}\ge\sqrt M\) give \(e_h>7/8\).

The exact runner uses the slightly stronger lower bound
\[
e_h\ge1-\frac{27}{2r^7}>\frac78.
\]
For completeness, the second derivative of \(x^{3/4}\) is increasing on
\([1,\infty)\), so integration gives
\[
(1+u)^{3/4}\ge1+\frac34u-\frac3{32}u^2\qquad(u\ge0).
\]
Substituting \(u=12/r^8\) in \(h^{3/4}=r^9(1+u)^{3/4}\) proves the
displayed bound. It justifies the sharper rational negative-loss
certificate in the archived controls.


For the EO loss put

\[
u=3r^{-4}-3r^{-6}>0,\qquad
T=r^9+\tfrac92r^5-\tfrac92r^3+\tfrac{27}{8}r=q+1/8.
\]

Since the third derivative of \((1+u)^{3/2}\) is negative, its quadratic Taylor polynomial at zero is an upper bound. Thus

\[
m^{3/2}\le T-\frac{27}{4r}+\frac{27}{8r^3}.
\]

Concavity of \(x^{3/4}\), and \(m>r^6\), imply

\[
\begin{aligned}
s_-^{3/4}
&\le m^{3/2}+\frac{3(6r^2-1)}{4\sqrt m}\\
&<T-\frac{27}{4r}+\frac{27}{8r^3}+\frac9{2r}<T.
\end{aligned}
\]

The last inequality is equivalent to \(r^2>3/2\). Hence
\(s_-^{3/4}-q<1/8\), and subtracting \(e_h>7/8\) proves

\[
\boxed{\Delta(h,s_-)<-3/4.}
\]

#### 4.6. Positive sign with the next odd predecessor

The two EO outputs remain the same, since both \(s_-\) and \(s_+\) are in the exact square cell of \(m\). Nevertheless, writing \(R_+=s_+-m^2\), we have \(R_+>3r^4\). Since

\[
s_+<(m+1)^2,\qquad
m+1=r^6+3r^2-2<(r^3+1)^2,
\]

the decreasing derivative of \(x^{3/4}\) gives

\[
\begin{aligned}
s_+^{3/4}-m^{3/2}
&\ge\frac{3R_+}{4s_+^{1/4}}\\
&>\frac{9r^4}{4(r^3+1)}>2r.
\end{aligned}
\]

The final inequality follows from \(r^3>8\). Since \(q<m^{3/2}\), we obtain \(s_+^{3/4}-q>2r\). Together with \(e_h<1\), this proves

\[
\boxed{\Delta(h,s_+)>2r-1>r.}
\]


### 5. The missing original return seam

For a hypothetical actual cycle, the two predecessor states occupy sorted
ranks \(o-e-1,o-e\). In the retained return section, write
\(A=OOE\) and \(B=OE\). The selected paths give \(A(a)=t\), \(B(b)=m\).
The complete return model also requires
\[
w=B(t),\qquad z=A(m)=B(q),
\]
with all their actual guards and odd ordered endpoints \(w<z\).
The local family in Result 4 does not assert these extensions.

If the extensions and their lower bound \(m\) are supplied, the existing
transported-loss estimate for \(AB=OOEOE\), whose exponent is \(27/32\),
gives at \(m\ge2^{24}\)
\[
z-w<\frac{27}{32}m^{-5/32}(b-a)+\frac98.
\]
Indeed the proper tail exponents are \(9/16,3/8,3/4,1/2\), so the
one-sided AB loss is less than \(1+(35/16)m^{-1/4}<9/8\);
the BA loss is nonnegative. This is a consequence of the existing word
machinery after all actual guards are provided. It yields no improvement
to the current height strips in this gate.

The terminal suffix always begins OE: it starts as OE, and every suffix
update appends a word on the right. Thus requiring the whole original
seam is a principled joint consistency test. Even that finite rectangle
would remain weaker than complete cyclic matching.

## Open questions

No obstruction has been proved for the complete selected integer
\(P/OE/EO/Q\) passage. Positive mixed loss alone, including at cube minima,
does not control the preceding prefix amplification. The regime
\(M\ge m^3\) remains outside this gate.

## Decision

**CLOSE** the predecessor-only sign obstruction. The necessary alignment
window is real and excludes nonpositive loss at cube minima, but the
noncube polynomial family realizes the thin window and retains both
signs with the exact predecessor guards. No new actual cycle restriction
or numerical period improvement is obtained.

Exactly one best next question: **does the entire initialized return-seam
rectangle \(A(a)=t,\ B(b)=m,\ A(m)=z,\ B(t)=w\), with all guards and the
cycle's quantitative gap constraints, still admit such an infinite
family?** A failure of the present family would not settle that question.
If a family satisfies the whole rectangle, stop extending this finite
local construction and require a genuinely cyclic matching restriction.
No further gate or computation is opened by this decision.

## Publication assessment

Status: **STRUCTURAL**. Exact scoped alignment and counterfamily results,
with AI-assisted proofs and fixed controls. Independent human review
and Lean verification remain outstanding. No Paper A or release copy
is updated by this Phase-0 gate. The certified floor \(350000000\) and
period lower bound \(780239\) are unchanged.


## Follow-up

The next finite question posed above is resolved in the canonical
[initialized return-seam dossier](juggler_cycle_return_seam.md).
An infinite congruence subfamily supplies the missing actual guards and
the named scalar bounds while retaining both signs. That follow-up closes
the finite initialized-seam obstruction; complete cyclic matching remains
open. The original results and their scope above are unchanged.

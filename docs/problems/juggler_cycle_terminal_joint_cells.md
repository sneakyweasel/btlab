# Joint terminal cells: exact local obstructions and the missing cyclic bound

Status: **PARK** the full joint cyclic question. Completed 10 September 2026.

This dossier is the canonical written source for this new gate. The preceding
DC/LR height theorems and terminal factorization remain consolidated in
[Paper A](../theory/juggler_finite_dynamics_note.md), Sections 3.12–3.13 and
Appendix F. The new results below have not been added to Paper A.

## Problem

Determine whether the shared absolute cells of the terminal prefix, mixed
passage and suffix force a contradiction for an actual cubic-band cycle.

## Exact statement

Let a hypothetical primitive actual Juggler cycle have minimum \(m\ge5\),
maximum \(M<m^3\), and sorted states
\[
c_0=m<c_1=v<\cdots<c_{L-1}=M,\qquad o+e=L.
\]
The established cubic order has odd sources below \(m^2\), even sources
above it, and rank rotation \(i\mapsto i+e\pmod L\), with \(\gcd(e,L)=1\).
Set
\[
h=c_{o-1},\quad s=c_o,\quad t=c_{e-1}=E(M),\quad q=c_e=O(m).
\]
Here \(O(x)=\lfloor x^{3/2}\rfloor\), \(E(x)=\lfloor\sqrt x\rfloor\),
and words are chronological. At the terminal two-base section,
\[
U(m)=v,\quad V(v)=m,\quad UV=P\,OE\,Q,\quad VU=P\,EO\,Q,
\]
with genuine guarded paths
\[
(m,v)\xrightarrow{P}(h,s)
\xrightarrow{OE/EO}(t,q)\xrightarrow{Q}(m,v).
\tag{TJ1}
\]
The question is whether the joint cells on these complementary paths imply
strict contraction of the complete positive gap, contradicting closure.

No such cyclic inequality is established here. The exact results are a
complementary-path cancellation theorem, sharp local even-branch distortion,
and an infinite mixed-cell family with both signs of the paired loss.
The local families satisfy all guards on their displayed edges and the
published smooth height restrictions, but supply neither periodicity nor
closed \(P/Q\) paths.

## Current literature

**PROJECT-SPECIFIC internal extension; no external priority claim.**
Prerequisites are [Paper A](../theory/juggler_finite_dynamics_note.md), the
[later-return dossier](juggler_cycle_later_returns.md), and the
[negative-knowledge record](../negative_knowledge.md), especially its terminal
prefix/suffix and fixed-minimum error limitations. The proof uses elementary
square cells, exact word substitutions and secants. No new external theorem
or heuristic parity distribution is invoked.

## Branch budget

- **Target:** one strict comparison between terminal prefix amplification
  and the actual mixed/suffix contraction.
- **Novelty hypothesis:** complementary periodic placement constrains signed
  floor-remainder differences more strongly than separate cell bounds.
- **Falsifier:** the proposed aggregate is only closure, or fully guarded
  local cells defeat its assumed sign or vanishing relative error.
- **Already killed by?:** terminal closure and unweighted defect composition
  are already insufficient; a fictitious same-word terminal edge and an
  unproved contracting terminal exponent are forbidden premises.
- **Existing machinery:** exact square remainders, cyclic rank rotation,
  guarded Euclidean induction, terminal \(P/Q\) factorization and DC/LR strips.
- **Maximum Phase-0 scope:** symbolic identities and families; exactly the
  three fixed parameter pairs listed under Experiments. No source, orbit,
  rank or floor census and no increase of any computational cap.
- **Promotion criterion:** a new cycle-specific inequality after all actual
  placements and guards are imposed.
- **Stop criterion:** retain precise local obstructions and PARK if the
  proposed cyclic aggregate cancels and no independent weighted bound remains.

## Balanced-ternary formulation

Every displayed cell, rank, gap and polynomial identity is an exact integer
relation and has a canonical balanced-ternary representation.

## Why BT may be relevant

No representation advantage is used or claimed in this gate.

## Candidate operations / invariants

The exact candidates are adjacent-gap secants, their signed square-remainder
corrections, and signed differences of transported absolute losses. The
identities and families below have repository label **EXACT — HUMAN PROOF**;
this denotes a written argument developed and cross-checked with AI assistance,
not independent human review or Lean verification. The termwise vanishing-error
and mixed-only fixed-sign shortcuts are **REFUTED** by those families.

## Experiments

The bounded [runner](../../src/research/juggler_sequence/cycle_terminal_joint_cells.py),
[tests](../../tests/research/juggler_sequence/test_cycle_terminal_joint_cells.py),
and [record](../../data/research/juggler/cycle_terminal_joint_cells/summary.json)
use exactly
\[
(r,a)=(9,5),\quad(17,17),\quad(2^{64}+1,2^{128}+1).
\]
Here \(r\) selects the mixed family and \(a\) the two even-cell faces below.

    python -m research.juggler_sequence.cycle_terminal_joint_cells

The records check exact cells, source/output parities, rational secant
coefficients, polynomial sign certificates and height margins. The last pair
activates both previously published height cutoffs. These are fixed controls
of symbolic families, not a source search or periodic-orbit evidence.
The universal claims depend on the proofs below, not these three evaluations.

## Conjectures

No new conjecture file is opened. The full cyclic joint-cell question remains
open; a local counterfamily does not refute it.

## Counterexamples

The two even-cell faces in Result 4 refute a uniform \(1+o(1)\) relative gap
approximation under their complete local parity guards. The two mixed faces
in Result 5 refute either universal sign for the mixed paired loss, even below
all currently excluded smooth height strips. Their exact regression controls
are the tests linked above. No family is asserted to be a cycle or to realize
the common terminal \(P/Q\) placement.

## Formalization

No new Lean theorem is claimed for this gate. Its prerequisites are the
compiled return modules recorded in
[Paper A's formalization map](../theory/juggler_finite_dynamics_formalization.md),
including `ReturnCycleTransfers`, `ReturnTransferHeight` and `ReturnOrbitStrips`.
Their cycle-specific height theorems do not formalize the new families or
settle the joint cyclic question posed here.

## Results

### 1. Deletion identities and complete adjacent-gap coverage

At every induced stage,
\[
U=OQ,\qquad V=PE. \tag{TJ2}
\]
Initially \(U=OOE,V=OE,P=O,Q=OE\). Under a left substitution
\((U,V)\mapsto(U,UV)\), replace \(P\) by \(UP\): then \(UV=(UP)E\).
Under a right substitution \((U,V)\mapsto(UV,V)\), replace \(Q\) by
\(QV\): then \(UV=O(QV)\). This proves (TJ2) inductively. In particular,
\[
|P|=|V|-1,\quad |Q|=|U|-1,\quad
p_P=2\mu,\quad p_Q=\tfrac23\lambda,
\tag{TJ3}
\]
where \(\lambda=p_U,\mu=p_V\). Every \(V\) ends in \(OE\) and every
\(U\) starts with \(OO\); hence \(P\) ends and \(Q\) starts with \(O\).

Let \(u=|U|\), \(v_\ell=|V|\). The initial letter-count determinant
\(o_Ue_V-o_Ve_U=1\) is preserved by both column additions. At termination,
\(L=u+v_\ell\) and \(o=o_U+o_V\), so
\[
o_UL-ou=1,\qquad eu\equiv1\pmod L. \tag{TJ4}
\]
Starting at gap rank zero, the gap-rank orbit is \(j_k=ke\pmod L\).
At \(k=|P|=L-u-1\), (TJ4) gives \(j_k=o-1\), the cut \((h,s)\).
The next rank is the wrap \(L-1\); one more is \(e-1\), the gap \((t,q)\).
The remaining \(|Q|=u-1\) steps return to zero. Coprimality makes all ranks
before this return distinct. Thus the common \(P,Q\) paths traverse every
ordinary internal same-branch gap transition exactly once. The cut and wrap
are precisely the two exceptional transitions replaced by the mixed passage.

This establishes shared geometry, not independence of the two traces.
It supplies no additional ordered gap at the wrap.

### 2. The aggregates that cancel

For any function \(\phi\) on the states and constants \(a_O,a_E\), define
\[
D_j=\phi(c_{j+1})-\phi(c_j),\qquad
\delta_i=\phi(c_i)+a_{b_i}-\phi(c_{\sigma(i)}).
\]
On a common-branch edge,
\(D_{j+e\bmod L}-D_j=\delta_j-\delta_{j+1}\). Summing over internal
edges other than the cut gives exactly
\[
D_{o-1}-D_{e-1}
=\delta_0-\delta_{o-1}+\delta_o-\delta_{L-1}. \tag{TJ5}
\]
The source gaps omit the cut and the image gaps omit \(e-1\); within each
branch the defect differences telescope. For \(\phi(x)=\log\log x\),
\(a_O=\log(3/2),a_E=-\log2\), these are the nonnegative exact floor
 defects. Substitution of the four extrema images makes (TJ5) a boundary
identity. The unweighted sum retains no interior remainder restriction.

For a common edge \(x<y\) of exponent \(n\in\{1,3\}\), put
\(a=\lfloor\sqrt{x^n}\rfloor<b=\lfloor\sqrt{y^n}\rfloor\) and
\(R_x=x^n-a^2,R_y=y^n-b^2\). Exact subtraction gives
\[
\frac{b-a}{y-x}
=\frac{S_n(x,y)}{a+b}
 \left(1-\frac{R_y-R_x}{y^n-x^n}\right),\quad
S_1=1,\quad S_3=x^2+xy+y^2. \tag{TJ6}
\]
Write \(d=v-m,G=s-h,k=q-t\). Multiplying actual secants along \(P\)
and \(Q\) gives \((G/d)(d/k)=G/k\); multiplying by the mixed secant
\(k/G\) gives one. The corresponding unweighted square-gap sum is
\[
M^2-m^2-(q^2-t^2)
=h^3-m^3+M-s-[(R_h-R_m)+(R_M-R_s)],
\]
where \(R_m=m^3-q^2,R_h=h^3-M^2,R_s=s-m^2,R_M=M-t^2\).
It too becomes an identity after substitution. A new cyclic restriction must
therefore constrain the signed corrections with their nonconstant weights.

### 3. The exact signed-loss target

Let \(e_W(x)=x^{p_W}-F_W(x)\), and define
\[
\Delta_P=e_P(v)-e_P(m),\quad
\Delta_B=e_{EO}(s)-e_{OE}(h),\quad
\Delta_Q=e_Q(q)-e_Q(t).
\]
Set \(a=p_P,b=p_Q,c=3/4\) and use actual interval secants
\[
A_P=\frac{v^a-m^a}{d},\quad A_B=\frac{s^c-h^c}{G},\quad
A_Q=\frac{q^b-t^b}{k}.
\]
Then
\(G=A_Pd-\Delta_P\), \(k=A_BG-\Delta_B\), and
\(d=A_Qk-\Delta_Q\). Consequently closure requires
\[
(A_PA_BA_Q-1)d=A_BA_Q\Delta_P+A_Q\Delta_B+\Delta_Q. \tag{TJ7}
\]
For open traces, strict contraction of the final gap is equivalent to the
right side being strictly greater than \((A_PA_BA_Q-1)d\). This is a
precise target for an independent bound, not such a bound itself. The factors
are secants on different actual intervals; their product cannot be replaced
by the product of ideal exponents.

The mixed term retains its initialized remainders through
\[
\begin{aligned}
e_{EO}(s)&=s^{3/4}-m^{3/2}+\frac{R_m}{m^{3/2}+q},\\
e_{OE}(h)&=\frac{R_h}{(h^{3/2}+M)(h^{3/4}+\sqrt M)}
             +\frac{R_M}{\sqrt M+t},
\end{aligned} \tag{TJ8}
\]
where \(s=m^2+R_s\). The first difference in (TJ8) is exactly
\(R_s(s^2+sm^2+m^4)/[(s^{3/2}+m^3)(s^{3/4}+m^{3/2})]\).
Parity forces \(R_s,R_h,R_M\) odd and \(R_m\) even, but does not order the
positive terms on the two sides. Result 5 establishes both signs explicitly.

### 4. Sharp even-cell distortion below the height strips

**Theorem.** For even positive \(x<y\) with distinct odd outputs
\(a=E(x)<b=E(y)\), put \(k=b-a\). Then
\[
\frac23\le K_E:=\frac{(b-a)(a+b)}{y-x}<2,
\qquad
\frac23<D_E:=\frac{b-a}{\sqrt y-\sqrt x}<2. \tag{TJ9}
\]
The lower \(K_E\) bound is attained; its upper bound and both \(D_E\)
bounds are sharp at arbitrarily large minima.

*Proof.* Here \(k\ge2\), \(1\le R_x\le2a-1\) and
\(1\le R_y\le2b-1\). For \(N=k(a+b)\),
\(y-x=N+R_y-R_x\). Since
\[
N-(4b-4)=(k-2)(2a+k-2)\ge0,
\]
we obtain \(y-x\le N+2b-2\le3N/2\). Conversely
\(y-x\ge N+2-2a>N/2\), since \(N/2\ge2a+2\).
This proves the \(K_E\) interval. Write
\(\theta_x=\sqrt x-a,\theta_y=\sqrt y-b\in[0,1)\). Then
\[
D_E=\frac{k}{k+\theta_y-\theta_x}
\in\left(\frac{k}{k+1},\frac{k}{k-1}\right)\subset(2/3,2).
\]

For odd \(a\ge5\), the damping and amplification faces respectively are
\[
(x_-,y_-)=(a^2+1,(a+3)^2-2),\quad
(x_+,y_+)=((a+1)^2-2,(a+2)^2+1).
\]
All inputs are even, both output pairs are \((a,a+2)\), and direct square
comparison gives
\[
K_E(x_-,y_-)=\frac23,\qquad
K_E(x_+,y_+)=\frac{2(a+1)}{a+3}\longrightarrow2.
\]
With
\(\ell(r)=1/(\sqrt{r^2+1}+r)<1/(2r)\) and
\(u(r)=2/(r+1+\sqrt{(r+1)^2-2})<1/r\), the ideal root gaps are
\(3-u(a+2)-\ell(a)\) and \(1+\ell(a+2)+u(a)\). Thus
\[
\frac23<D_E(x_-,y_-)<\frac{4a}{6a-3},\qquad
\frac{4a}{2a+3}<D_E(x_+,y_+)<2,
\]
proving sharpness without a scan. All sources are at most \(a^2+6a+7\), and
\[
a^2+6a+7<a^3-a^2\quad(a\ge5),
\]
because \(a^3-2a^2-6a-7\ge3(a-1)^2-10>0\). Outputs lie in \([a,a^2)\).
Hence these guarded open blocks lie below every published smooth height strip
at its stated cutoff; no cycle membership is supplied. \(\square\)

For comparison, odd sources \(1\le m\le x<y\) satisfy
\(y^{3/2}-x^{3/2}\ge3\sqrt m\). Their endpoint-error difference has
absolute value below one, so
\[
\left|\frac{O(y)-O(x)}{y^{3/2}-x^{3/2}}-1\right|<\frac1{3\sqrt m}.
\tag{TJ10}
\]
The analogous vanishing relative approximation for guarded \(E\) edges is
therefore specifically unavailable.

### 5. Opposite mixed-loss signs in the surviving cubic region

**Theorem.** Let \(r\ge9\), \(r\equiv1\pmod4\), and define
\[
\begin{gathered}
m=r^2,\quad K=r^2-1,\quad h=K^2+1,\quad M=K^3+3K/2,\\
t=r^3-(3r+1)/2,\quad q=r^3,\\
s_-=m^2+1,\qquad s_+=m^2+2m-1.
\end{gathered}
\tag{TJ11}
\]
Both exact guarded passages \(h\xrightarrow O M\xrightarrow E t\) and
\(s_\pm\xrightarrow E m\xrightarrow O q\) satisfy
\[
m\le t<q<h<m^2<s_-<s_+<M<m^3,
\]
with \(m,h,t,q\) odd and \(M,s_\pm\) even. Nevertheless
\[
\Delta_B(s_-)<-\frac12,\qquad \Delta_B(s_+)>r. \tag{TJ12}
\]
Their deficit obeys \(m^3-M>2m^2\), so both survive every published smooth
height restriction, including sharp LR on its stated domain.

*Proof.* \(K\) is divisible by eight; this gives integrality and all stated
parities, including odd \(t\) from \(r\equiv1\pmod4\). Exact expansions give
\[
\begin{aligned}
h^3-M^2&=3K^2/4+1>0,\\
(M+1)^2-h^3&=2K^3-3K^2/4+3K>0,\\
4(M-t^2)&=4r^3+9r^2-6r-11>0,\\
4((t+1)^2-M)&=4r^3-9r^2-6r+11>0.
\end{aligned}
\]
The last two inequalities hold for \(r\ge5\): substituting \(r=5+z\)
leaves only positive coefficients. Thus \(O(h)=M,E(M)=t\).
The remaining cells follow from \(m^2\le s_\pm<(m+1)^2\) and \(m^3=q^2\).
For the order, \(h-q=r^2(r-2)(r+1)+2>0\),
\(M-s_+=r^4(r^2-4)+(5r^2-3)/2>0\), and the other comparisons follow
directly. The common output gap is \((3r+1)/2\); the input gaps are
\(2r^2-1\) and \(4r^2-3\), so both mixed passages strictly contract.

The height deficit is
\[
m^3-M=3r^4-\tfrac92r^2+\tfrac52>2r^4,
\]
since its difference from \(2r^4\) is
\(((r^2-4)(2r^2-1)+1)/2>0\). This exceeds \(m^{15/8}\),
\(\tfrac12m^{253/128}\), and \(\tfrac12m^\theta\), where
\(\theta=381/128-3^{41}/2^{65}<2\). Taking \(r\ge2^{64}+1\) activates
both large-minimum cutoffs. This assertion concerns those smooth inequalities;
it does not assert the remaining cycle-selected return constraints.

Set \(B=r^3-3r/2+3/(4r)>0\). Then
\[
M-B^2=3r^2/4-1/4-9/(16r^2)>0,
\]
so \(h^{3/4}>\sqrt M>B\). Concavity gives
\((r^4+1)^{3/4}\le r^3+3/(4r)\). Subtracting the common output gap yields
\(\Delta_B(s_-)<-1/2\).
For the other face, \(s_+<(r+1)^4\), and the decreasing derivative gives
\[
s_+^{3/4}-h^{3/4}>
\frac{3(4r^2-3)}{4(r+1)}=3r-3+\frac3{4(r+1)}.
\]
Hence \(\Delta_B(s_+)>3r/2-7/2+3/[4(r+1)]>r\) for \(r\ge9\).
This proves (TJ12). \(\square\)

The two choices keep \(m,h,M,t,q\), their guards and three constituent cells
unchanged; only the exact even source in \(m\)'s square cell changes.
Moreover \(R_m=0\) exactly. Thus neither sign failure comes from an
uninitialized first remainder or independently chosen floor phases.
No common \(P/Q\) or actual periodic set is constructed.

### 6. The terminal exponent premise that remains unavailable

Let \(\Lambda=o\log3-L\log2>0\). The determinant (TJ4) yields
\[
\log\lambda=\frac{u\Lambda+\log3}{L},\qquad
\log\mu=\frac{v_\ell\Lambda-\log3}{L}.
\tag{TJ13}
\]
Thus \(\lambda>1\) and \(p_Q>2/3\), but \(\mu<1\), \(p_P<2\), or a
contracting terminal suffix do not follow. Actual decrease \(V(v)=m<v\)
can coexist with an ideal exponent above one when floor loss is uncontrolled.
The deletion identity also gives the prescribed comparison
\[
F_V(m)=E(h)<m=F_V(v).
\]
Its last \(E\) guard at odd \(h\) is wrong. It is not actual descent from a
cycle state and cannot supply the missing guarded terminal edge.

## Open questions

The genuinely cyclic constraint on the signed, weighted adjacent remainder
differences in (TJ6)–(TJ7) remains unknown. The local families do not determine
whether their permitted faces can occur together in complementary terminal
paths. No new height, minimum, period or no-cycle restriction is obtained.
The regime \(M\ge m^3\) is outside this gate.

## Decision

**PARK** the full joint cyclic question. The exact shared-path sums and products
cancel to boundary or closure identities; the local E distortion remains of
order one, and the mixed loss has both signs even in the surviving smooth
height region. CLOSE only the corresponding termwise approximation and
mixed-only fixed-sign shortcuts, not all inequalities using actual cyclic cells.

The one best next question is: **does cyclic rank placement impose a strict
bound on the signed, weighted adjacent-remainder differences that makes the
complete paired return contract?** No continuation or larger search is
authorized by this PARK decision.

## Publication assessment

Status: **STRUCTURAL**. This dossier records exact scoped obstructions and the
remaining cyclic requirement. It is separate from the already consolidated
Paper A and carries no external novelty or Lean claim for the new results.
AI-assisted cross-checking is not independent human review. No published
Zenodo record, descent floor, certified period bound or global no-cycle status
is changed by this gate.

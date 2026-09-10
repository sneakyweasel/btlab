# Cycle-period upper bounds: a surplus window and structural limits

Status: **PARK** the actual-cycle estimate. Bounded phase, 10 September 2026.
No new period exclusion, descent floor, or termination theorem is claimed.

The authorized parity follow-up on the same date is recorded in Result 5.
It sharpens independent loss bookkeeping but finds no new restriction on
the count pair. No new theorem-ledger claim is added for that reformulation.

## Problem

Can exact primitive Juggler closure force
\(L\Lambda\le C\), where
\(\Lambda=o\log3-L\log2\) and \(C\) is independent of the
cycle minimum and period? Such a theorem would give a period upper
bound depending on the minimum. It would not by itself give an absolute
upper bound on all cycle periods.

## Exact statement

Let \(m>1\) be the minimum of a hypothetical primitive cycle of
length \(L\) and odd count \(o\). The proved loss window is
\[
0<b(m):=\log\frac{\log(m^2+1)}{2\log m}
\le\Lambda<\log\frac{\log(m+L)}{\log m}.
\tag{1}
\]
If additionally \(L\Lambda\le C\), then
\[
L\le C/b(m)<C(m^2+1)\log(m^2+1).
\tag{2}
\]
These are `J-cycle-loglog-surplus-window`, **EXACT — HUMAN PROOF**.
The additional hypothesis is not proved here.

There are, however, primitive formal mechanical words with coprime
counts, minimum possible odd count, all noncontracting prefixes,
initial \(OO\), terminal \(EOE\), and \(L\Lambda\to\infty\).
This is `J-cycle-period-surplus-word-obstruction`, **EXACT — HUMAN PROOF**.
They are words, not realized integer cycles. An archived exact
threshold-map cycle separately disproves the special inference
\(L\Lambda<\log3\) from that relaxed map's closure and order.
It does not disprove the existence of a larger uniform constant.

## Current literature

The ingredients are internal: [Paper A](../theory/juggler_finite_dynamics_note.md)
contains the last-even cell, the logarithmic defect identity, and the
conditional sorted-grid period comparison; the
[cubic-band dossier](juggler_cycle_cubic_band.md) contains the saved
threshold controls. Adjacent-convergent arithmetic is also used in
[Paper D](../theory/juggler_near_convergent_diophantine_note.md).
The [negative-knowledge record](../negative_knowledge.md) already excludes
automatic parity transfer from threshold closure and real-cell averaging.

These are elementary deductions and scoped counterexamples, with no
external priority claim. The repository label HUMAN PROOF denotes an
AI-assisted written argument cross-checked by AI agents; independent
human review and Lean verification are not claimed.

## Branch budget

- **Target:** test a uniform upper bound on \(L\Lambda\) for actual
  primitive cycles, rather than repeat an existing floor campaign.
- **Novelty hypothesis:** actual parity might force a stronger rational
  approximation than minimal odd count and mechanical order alone.
- **Falsifier:** the proposed structural deduction also applies to a
  relaxation where \(L\Lambda\) is unbounded.
- **Already killed by?:** rank/real-cell averaging and local seam-only
  arguments do not establish actual parity. They are not reopened.
- **Existing machinery:** exact logarithmic loss, compulsory final
  loss, continued fractions, mechanical words, saved threshold data.
- **Maximum Phase-0 scope:** the loss window, a formal counterfamily,
  and one saved 14-edge control; no orbit search, runtime probe,
  new floor, or Paper A edit.
- **Promotion criterion:** a new restriction sufficient to bound
  \(L\Lambda\) on actual cycles.
- **Stop criterion:** only conditional bounds and structural
  insufficiency; record the missing arithmetic input and stop.

### Authorized parity follow-up

- **Mathematical target:** can all integer parity guards force
  \(0<o/L-\log2/\log3\le K/L^2\), equivalently
  \(L\Lambda\le K\log3\)?
- **Novelty hypothesis:** absolute integer cells might couple parity
  to surplus beyond word order and separate loss bounds.
- **Falsifier:** the deduction discards guards, confuses compulsory
  lower loss with upper loss, or recovers an existing packing bound.
- **Already killed by?:** fixed residue summaries, local seam signs,
  ordinary preimage capacity, and real-cell averaging are closed in
  the negative-knowledge record; those constructions are not repeated.
- **Existing machinery:** initialized losses, full edge parity,
  cubic rank/grid bounds and the existing endpoint-aggregate identity.
- **Maximum Phase-0 scope:** a written global parity/loss audit and
  two fixed exact open-edge regression tests; no search or new probe.
- **Promotion criterion:** a new count-pair restriction from actual
  parity, not a renamed version of the desired estimate.
- **Stop criterion:** if only independent cell caps, spacing and
  known aggregate arithmetic survive, record that limit and stop.

## Balanced-ternary formulation

None is needed. The variables are integer cycle states, parity counts,
and ordinary rational approximants.

## Why BT may be relevant

No representation advantage is used or claimed.

## Candidate operations / invariants

The candidate \(L\Lambda\) couples period and logarithmic surplus.
The exact initialized defects below retain the true floor cells.
Taking an upper bound on each defect and a lower bound on the last
defect separately does not force this candidate to be bounded.

## Experiments

[Exact regression tests](../../tests/research/juggler_sequence/test_cycle_period_upper_bound.py)
replay the archived \(S_5\) cycle and check fixed arithmetic controls
for the word construction. Two further tests cover the four transition
parities and sharp even-to-odd cell endpoints at fixed odd targets.
They are open-edge controls, not additional cycle examples, and no
finite test is the proof of a quantified statement.
No new data census, probe, threshold sweep, or Lean module.

## Conjectures

The existence of a uniform \(C\) for all actual primitive cycles
remains unproved and unrefuted. No new conjecture file is opened.
In particular, the sharper choice \(C=\log3\) is not promoted from
the continued-fraction convergent case to all cycles.

## Counterexamples

Results 3 and 4 distinguish a family of formal words from a single
exact wrong-parity threshold cycle. Neither is a Juggler cycle.
The unbounded-family assertion belongs only to Result 3.

## Formalization

No new Lean claim. Existing exact cells and the recorded logarithmic
identity supply the inputs, but the new combinations below are written
proofs. No manuscript or existing formal theorem is silently strengthened.

## Results

### 1. Exact loss window and the conditional period upper bound

Let \(x_0=m\), \(x_L=m\), and \(y_i=x_{i+1}\). Write
\(h_i=3\) at an odd source and \(h_i=1\) at an even source.
The exact floor cell gives
\[
\rho_i=x_i^{h_i}-y_i^2,\qquad 0\le\rho_i<2y_i+1,
\]
and the logarithmic defect is
\[
\delta_i=\log\frac{h_i\log x_i}{2\log y_i}
=\log\left(1+\frac{\log(1+\rho_i/y_i^2)}{2\log y_i}\right)\ge0.
\]
All logarithms are defined because the minimum exceeds one. Telescoping
the \(\log\log x_i-\log\log y_i\) terms proves the exact identity
\[
\sum_{i=0}^{L-1}\delta_i=o\log3-L\log2=\Lambda.
\tag{3}
\]

The last source \(p\) is even and \(m\) odd. Thus
\(p\ge m^2+1\), and
\(\delta_{L-1}\ge b(m)>0\). This proves the lower side of (1).
For the upper side, the strict upper floor cell gives
\[
\delta_i<g(y_i),\qquad
g(t)=\log\log(t+1)-\log\log t
=\int_t^{t+1}\frac{ds}{s\log s}.
\]
The function \(g\) is positive and decreasing for \(t>1\).
Primitivity makes the \(L\) targets distinct integers at least
\(m\), so their sorted list has entry \(j\) at least \(m+j\).
Consequently
\[
\Lambda<\sum_{j=0}^{L-1}g(m+j)
=\log\frac{\log(m+L)}{\log m},
\]
which proves (1). Also
\[
b(m)=\int_{m^2}^{m^2+1}\frac{ds}{s\log s}
>\frac1{(m^2+1)\log(m^2+1)}.
\]
Combining this with \(L\Lambda\le C\) proves (2), whose
asymptotic form is \(C/b(m)\sim2Cm^2\log m\). No cubic-height
hypothesis was used. \(\square\)

### 2. The two unconditional sides do not produce an upper period

Combining just the two sides of (1) yields
\[
L>\sqrt{m^2+1}-m,
\tag{4}
\]
whose right side is less than one. It is a vacuous lower bound for
a positive integer period, not an upper bound. The simpler loss cap
also gives only \(L\Lambda<L^2/(m\log m)\).

An actual upper convergent with denominator exactly \(L\) satisfies
\(\Lambda<\log3/L\), so (2) applies with \(C=\log3\) in that
subclass. If \(o/L\) reduces by \(g=\gcd(o,L)\) and the reduced
fraction is an upper continued-fraction convergent, the same argument
gives only \(L\Lambda<g^2\log3\). Primitivity of an actual cycle
does not by itself imply coprime counts outside the cubic band.

Under the additional \(M<m^3\) hypothesis, Paper A's existing
sorted-grid comparison and \(\Lambda\le C/L\) give the stronger
\[
L\le\frac{\log3+C}{\log(\log(m+2)/\log m)}=O_C(m\log m).
\]
Neither bound is an absolute cap: a lower bound on \(m\) cannot
be substituted into these increasing upper-bound functions.

### 3. Coprime mechanical words can have unbounded period times surplus

Put \(\alpha=\log2/\log3\). Take infinitely many adjacent upper
and lower convergents \(p/q>\alpha>r/s\), so
\[
\varepsilon=p-\alpha q>0,\qquad
\eta=\alpha s-r>0,\qquad ps-rq=1,
\]
with \(q\to\infty\) and \(\varepsilon\to0\). Define
\[
k=\left\lceil\frac{\eta+1/4}{\varepsilon}\right\rceil,
\qquad o=kp+r,\qquad L=kq+s.
\]
Then
\[
\frac14\le o-\alpha L=k\varepsilon-\eta
<\frac14+\varepsilon.
\tag{5}
\]
For all sufficiently large pairs, this lies in \((0,1)\), so
\(o=\lceil\alpha L\rceil\), the least expanding odd count.
The identity \(oq-Lp=rq-sp=-1\) proves \(\gcd(o,L)=1\).
Since \(L\ge q\to\infty\),
\[
L\Lambda=L(o-\alpha L)\log3\ge\tfrac14L\log3\longrightarrow\infty.
\tag{6}
\]

Realize these counts as the binary mechanical word with prefix counts
\(a_j=\lceil jo/L\rceil\). For \(j>0\),
\(a_j\ge jo/L>\alpha j\), hence every prefix is formally
noncontracting. At an even letter \(j\),
\(a_j=a_{j+1}>\alpha(j+1)\), also satisfying the stronger
even-endpoint envelope. Because \(o/L\to\alpha\in(1/2,2/3)\),
the word begins \(OO\) and ends \(EOE\). Coprime counts make
this binary word primitive: a repeated shorter word would divide
both counts and \(L\). Thus all these necessary word properties
coexist with (6). \(\square\)

No integer states or floor-cell realization have been constructed.
In particular, the rational mechanical word is not assumed equal to
the irrational greedy hug word at every prefix. That stronger
identification is not a theorem about arbitrary actual cycles.

### 4. Exact threshold closure does not force the convergent constant

The previously saved \(S_5\) cycle is
\[
(5,11,36,6,14,52,7,18,76,8,22,103,10,31).
\]
It uses the odd power below \(25\) and the square root above.
All 14 integer floor cells close exactly, the sorted rank rule holds,
and \((L,o)=(14,9)\) is coprime. Nevertheless
\[
L\Lambda>\log3
\quad\Longleftrightarrow\quad 3^{125}>2^{196}.
\tag{7}
\]
Thus \(9/14-\alpha>1/14^2\), ruling out convergent status.
There are eight wrong-parity states. This is not a Juggler cycle,
not a refutation for actual cycles, and not a proof of unbounded
\(L\Lambda\) even among threshold cycles.

### 5. What exact integer parity adds, and what it does not

This continuation is a **REPARAMETERIZATION** of exact cell, packing
and grid information, not a newly promoted count-pair theorem.
The algebra is written explicitly to prevent confusing its two directions.

For an actual edge \(x\to y>1\), set
\(d=(x-y)\bmod2\in\{0,1\}\). Since \(h\in\{1,3\}\) is odd,
the integer remainder satisfies the sharper exact bounds
\[
\rho=x^h-y^2\equiv d\pmod2,\qquad d\le\rho\le2y-d.
\tag{8}
\]
Define, for \(\varepsilon\in\{0,1\}\),
\[
H_\varepsilon(y)=
\log\frac{\log(y^2+2y-\varepsilon)}{2\log y}.
\]
The initialized loss is increasing in \(\rho\), so
\[
\boxed{\sum_{i:d_i=1}b(y_i)\le\Lambda
\le\sum_i H_{d_i}(y_i).}
\tag{9}
\]
The lower bound records every parity switch, not only the final one.
The upper bound still permits first-order floor losses.

Indeed, for every odd integer \(y\ge3\), both
\[
y^2+1\xrightarrow E y,\qquad
y^2+2y-1\xrightarrow E y
\tag{10}
\]
are exact, correctly guarded even-to-odd steps. Their remainders are
\(1\) and \(2y-1\), attaining respectively \(b(y)\) and
\(H_1(y)\). As \(y\to\infty\),
\[
b(y)\sim\frac1{2y^2\log y},\qquad
H_1(y)\sim\frac1{y\log y},\qquad
H_0(y)-H_1(y)\sim\frac1{2y^2\log y}.
\tag{11}
\]
The last difference is exactly the integral of \(1/(s\log s)\)
from \(y^2+2y-1\) to \(y^2+2y\). Thus parity shaves a lower-order
amount off the independent upper cap; it does not justify replacing
that cap by the much smaller compulsory loss. These are single open
edges, not cycles or counterexamples to a full-cycle bound.

For completeness, the parity-aware global packing formula can be stated
without a cubic-height assumption. Put \(e=L-o\), let \(R\) count
cyclic odd runs, let \(t\) be the least odd integer at least
\(\lfloor m^{3/2}\rfloor\), and write
\[
S_\varepsilon(a,q)=\sum_{j=0}^{q-1}H_\varepsilon(a+2j).
\]
An empty sum is zero. Then
\[
\Lambda\le S_1(m,R)+S_0(t,o-R)
 +S_1(m^2+1,R)+S_0(m^2+1,e-R).
\tag{12}
\]
To verify this, the EO, OO, OE and EE classes have counts
\(R,o-R,R,e-R\). Their targets are respectively odd at least \(m\),
odd at least \(t\), even at least \(m^2+1\), and even at least
\(m^2+1\). Each class has distinct targets, separated by at least two.
The functions \(H_\varepsilon\) decrease for \(y>1\): in
\(H_\varepsilon(y)=\log(1+\log(1+2/y-\varepsilon/y^2)/(2\log y))\),
the positive numerator decreases and the denominator increases.
Applying (9) to each sorted target class proves (12).
Cross-class disjointness is not fully used, so this is a relaxed budget,
not an optimal packing theorem. It supplies no uniform \(L\Lambda\) cap.

Inside the cubic band, the rank rule gives \(R=e\) and no EE edges.
For sorted states \(c_j\), (9) specializes to
\[
\Lambda\ge\sum_{j=0}^{e-1}\bigl(b(c_j)+b(c_{o+j})\bigr).
\tag{13}
\]
Also \(c_1\ge m+2\), and the existing grid implies
\[
L\log\frac{\log(m+2)}{\log m}
\le\log3+(L-1)\Lambda.
\tag{14}
\]
Both give lower constraints on surplus; solving (14) for an upper
period again requires the unproved \(L\Lambda\le C\).

Endpoint congruences do not supply the missing input either. For odd
\(m>1\) and positive expanding counts, the existing aggregate obeys
\[
\nu_2\!\left(m^{3^o}-m^{2^L}\right)=\nu_2(m-1).
\tag{15}
\]
Factor out the odd \(m^{2^L}\); the remaining exponent
\(3^o-2^L\) is odd, so its geometric sum is odd. Further,
\(m\equiv1\pmod Q\) makes this aggregate zero modulo any fixed
\(Q\), independently of the approximation quality of \(o/L\).
This is a limitation of that aggregate, not of all arithmetic using
full absolute data. The stronger existing hidden-guard obstruction is
recorded in [the fixed-residue dossier](juggler_cycle_guard_residues.md).

No bound of order \(L^{-2}\) on the odd-share error follows from this
audit. The exact cells still couple all states around the same cycle;
neither the independent cap nor the open edges settle that coupling.

## Open questions

No new parity-sensitive estimate was found that bounds \(L\Lambda\)
on actual cycles. Formal words fail to supply it; the threshold control
also prevents assuming the sharp convergent case automatically.
The authorized follow-up recovers sharper parity endpoints and known
packing/aggregate constraints, but no new count restriction. The full
absolute cyclic system is neither solved nor refuted. Simply asking for
the same estimate with all guards restored is not a new research mechanism.

## Decision

**PARK** the uniform actual-cycle surplus bound. Retain (1)–(2) and
the formal-word obstruction. The attempted deductions from mechanical
order, minimal odd count, or separate terminal-loss and distinctness
bounds are closed in the precise senses above. No actual cycle was
constructed and no new unconditional period upper bound was proved.

The authorized parity follow-up also stops: its independent cell caps,
run-class packing, grid spacing and endpoint congruences do not furnish
the missing period coupling. No additional executable branch is identified.
A reopening would require a specified new global arithmetic estimate,
not another local guard, a larger census, or the renamed target itself.

## Publication assessment

Status: `STRUCTURAL`. A proof-only laboratory record, not a new paper.
No Paper A change, release rebuild, Lean module, or computation campaign.

# Absorbed cylinders at growing depth

Date: 9 September 2026. Status: **CLOSE** for the unrestricted cylinder
attack; the stopped live-pressure problem remains open.

## Problem

Does the full, unstopped log-log-depth cylinder hypothesis survive the
mass of orbits that have already reached the odd absorbing state 1?

## Exact statement

**Theorem (`J-absorbed-cylinder`, EXACT — HUMAN PROOF).** Fix
\(N_0\ge2\) and \(C>1\), and put
\(L(y)=\log_2(\log(2y)/\log N_0)\), \(d(y)=\lceil CL(y)\rceil\).
There are dyadic scales \(y_k\to\infty\), for every sufficiently large
integer \(k\), such that \(L(y_k)=k+O_{N_0}(1)\),
\(d(y_k)>k+5\), and
\[
\#\{n\text{ odd in }(y_k,2y_k]:
  \mathrm{word}_{d(y_k)}(n)=O E^{k+4}O^{d(y_k)-k-5}\}
\ \ge\ \frac{y_k}{216\log y_k}.
\tag{1}
\]
Every start in this cylinder reaches 1 at time \(k+5\).
Consequently, the former **all-word** version of \(\mathrm H(C,A)\)
is false for every \(C>1,A>1\). The former **all-prefix** version of
\(\mathrm H_q(C,A)\) is false for every \(C>1,A>1,q<1\).
Neither assertion concerns the stopped live pressure.

## Current literature

This is a derived consequence of the repository's even-block estimate
and OEE block-average production, not a new exponential-sum theorem:
[fate contagion, Lemma 2.1, Proposition 3.4 and Lemma 4.1](../theory/juggler_fate_contagion_note.md).
The abstract fair-to-fixed-depth-then-all-odd obstruction was already
recorded in [the Tao note, §10.4](../theory/juggler_tao_reduction_note.md).
Here the obstruction is realized by the exact Juggler map on infinitely
many scales, with a quantitative lower bound. No external novelty or
priority claim is made.

## Branch budget

- **Target:** one growing-depth terminating cylinder lower bound.
- **Novelty hypothesis:** conserved harmonic mass in an even inverse
  tree, followed by a fixed OEE lift, refutes the unstopped hypothesis.
- **Falsifier:** a depth-dependent loss in that lift sufficient to
  destroy the harmonic lower bound.
- **Already killed by?:** not the closed support-concentration or
  external-averaging programs: this tests a literal hypothesis on
  actual map cylinders, not a proposed estimate for live mass.
- **Existing machinery:** exact even blocks; the OEE production; the
  known seed-tree harmonic argument; dyadic pigeonhole.
- **Maximum Phase-0 scope:** one human proof and finite arithmetic
  regression checks; no orbit census, floor raise or Paper A edit.
- **Promotion criterion:** a lower bound uniform in the growing depth.
- **Stop criterion:** an unproved parity-mixing input. Once the full
  hypothesis is refuted, stop; do not open another pressure formulation.

## Balanced-ternary formulation

None is needed. The objects are inverse blocks, parity words and
harmonic counting measure.

## Why BT may be relevant

No representation-dependent mechanism is used or claimed.

## Candidate operations / invariants

For a finite set \(B\) write \(h(B)=\sum_{n\in B}1/n\). The useful
invariant is a lower bound for the harmonic mass of a single-generation
even inverse tree, not pointwise density throughout its support.

## Experiments

No asymptotic claim is inferred from a finite experiment.
[Regression tests](../../tests/research/juggler_sequence/test_absorbed_cylinder.py)
check small exact inverse trees, OEE fibers, word indexing and the
elementary constants in the proof. No new probe or data artifact is
needed for this proof-only phase.

## Conjectures

The all-word assertion is recorded separately as
`juggler_unstopped_cylinder_bound` (REFUTED). The existing
`juggler_loglog_depth_cylinder_bound` record retains only the restricted
bad-word and live-pressure questions as ACTIVE. Its older combined
record must not be read as saying that the full hypothesis is still open.

## Counterexamples

The counterexample is an infinite exact-map family, not a finite
numerical violation. Start with the seed 4 and iterate even inverse
blocks; apply one OEE inverse production to the resulting generation.
The relevant dyadic block is selected by harmonic pigeonhole, not by
assuming equidistribution inside every block.

## Formalization

The new analytic theorem is **not Lean-verified**. Its exact even-block
and transparent-root identities already occur in `FateContagion.lean`
and `LogLogClock.lean`. The existing `FateChernoff.lean` conditional
union bound already assumes estimates only on bad words; it does not
assume or prove the refuted estimate on all words. No Lean file is
changed and no weaker compiled statement is presented as (1).

## Results

### Proof of the theorem

**1. Even inverse generations retain harmonic mass.** Let
\(B_0=\{4\}\) and
\[
B_{k+1}=\bigsqcup_{a\in B_k}E(a),\qquad
E(a)=\{b\text{ even}:a^2\le b<(a+1)^2\}.
\]
Disjointness follows because an integer has a unique image. Repeated
square-root nesting gives
\[
B_k\subseteq[4^{2^k},5^{2^k}),\quad
J^k(a)=4,\quad \mathrm{word}_k(a)=E^k\quad(a\in B_k).
\]
Lemma 2.1 of the fate note gives
\[
h(B_{k+1})\ge(1-2\,4^{-2^k})h(B_k).
\]
All factors lie in \([0,1]\). The finite-product inequality
\(\prod(1-x_j)\ge1-\sum x_j\), and
\(\sum_{j\ge0}4^{-2^j}\le\sum_{r\ge1}4^{-r}=1/3\), imply
\[
h(B_k)\ge\frac14\prod_{j<k}(1-2\,4^{-2^j})\ge\frac1{12}.
\tag{2}
\]
This is a harmonic-mass statement, not the unproved assertion that an
even inverse tree is uniformly distributed in its containing interval.

**2. One fixed-depth odd lift.** Let \(U(a)\) be the exact OEE
production of Proposition 3.4:
\[
U(a)=\{n\text{ odd in }[a^{8/3},(a+1)^{8/3}):
 \lfloor n^{3/4}\rfloor\text{ even},\quad
 \lfloor n^{3/2}\rfloor\text{ even}\}.
\]
Every \(n\in U(a)\) has word OEE and \(J^3(n)=a\). Distinct
\(a\)'s give disjoint intervals. That proposition and its weighted
form in §4.1 give, uniformly for all sufficiently large integers \(a\),
\[
h(U(a))\ge\frac1{3a}
 (1-\varepsilon_B(a)-8/(3a))\ge\frac1{6a},
\]
where \(\varepsilon_B(a)\to0\). There is no growing-depth discrepancy
estimate here: the only analytic estimate has the fixed word OEE.

For \(A_k=\bigsqcup_{a\in B_k}U(a)\), the smallest leaf tends to
infinity. Thus, for every sufficiently large \(k\),
\[
h(A_k)\ge\frac1{72},\qquad
A_k\subseteq[4^{(8/3)2^k},5^{(8/3)2^k}).
\tag{3}
\]
Every member has the common prefix \(OE^{k+4}\): the OEE lift,
then \(k\) even steps to 4, then \(4\to2\to1\). Hence it reaches
1 at time \(k+5\), and all remaining letters are O.

**3. Dyadic extraction.** The interval in (3) meets at most
\[
\frac{8\log(5/4)}{3\log2}\,2^k+2\le3\,2^k
\]
blocks \((2^r,2^{r+1}]\). Therefore one such block, with \(y_k=2^r\),
contains harmonic mass at least \(1/(216\,2^k)\) from \(A_k\).
Since \(n>y_k\) on that block,
\[
\#(A_k\cap(y_k,2y_k])\ge\frac{y_k}{216\,2^k}.
\]
Intersection with the support in (3) also implies
\[
\tfrac83\,2^k\log4-\log2\le\log y_k
 \le\tfrac83\,2^k\log5.
\tag{4}
\]
In particular \(\log y_k\ge2^k\), giving (1), and
\(L(y_k)=k+O_{N_0}(1)\). Since \(C>1\), eventually
\(d(y_k)>k+5\), so the common prefix extends to the single full word
stated in the theorem.

**4. These are genuinely absorbed, non-bad cylinders.** On the
whole dyadic block, not just the selected subset, (4) gives
\[
\log\bigl((2y_k)^{3/2^{k+5}}\bigr)
\le\tfrac14\log5+\tfrac3{32}\log2<\log2.
\]
The last strict inequality is equivalent to \(5^8<2^{29}\).
Consequently any start in that block with prefix \(OE^{k+4}\)
has \(J^{k+5}(n)\le n^{3/2^{k+5}}<2\), and positivity forces
\(J^{k+5}(n)=1\). The same envelope crosses below every fixed
\(N_0\ge2\); these prefixes are not \(L(y_k)\)-bad. In particular
the *entire* prefix cylinder, including any starts not constructed
in \(A_k\), sends all its mass to an odd next letter.

**5. Contradictions to the two unrestricted hypotheses.** The old
full-cylinder right side is
\[
2^{-d(y_k)}y_k+y_k(\log y_k)^{-A}
=O_{N_0,C}(y_k(\log y_k)^{-C})+y_k(\log y_k)^{-A}
=o(y_k/\log y_k)
\]
when \(C>1,A>1\), contradicting (1). For the old full-prefix split
bound, take \(t=k+5<d(y_k)\) and \(w=OE^{k+4}\). Step 4 gives
\(\#[wO]_{y_k}=\#[w]_{y_k}\ge y_k/(216\log y_k)\). Thus the required
inequality \((1-q)\#[w]_{y_k}\le y_k(\log y_k)^{-A}\) fails for every
fixed \(q<1,A>1\). This proves both refutations. \(\square\)

### What survives

The restrictions to bad words and bad prefixes remove this family.
The Tao and Paper C source statements now make those restrictions
explicit. For the biased-prefix argument, after the first envelope
crossing one may set subsequent artificial letters to E; the conditional
odd excess is then zero, and paths which never cross are unchanged.
The same martingale proof applies. This is a correction of scope, not
evidence that the restricted hypothesis holds.

The live pressure already discards this family once it enters
\([1,N_0]\). It is unchanged and unproved. There is no decrease in the
known failure-density upper bound, and neither cycles nor escape have
been excluded.

## Open questions

Can the existing live tilted-share estimate be proved at depths
proportional to \(\log\log y\)? No new estimate for it is obtained here.

## Decision

**CLOSE.** The unstopped attack is refuted by an actual-map infinite
family. Retain the quantitative theorem and correct the hypothesis
scope; do not attempt to rescue full-word equidistribution or run a
larger census. The mathematical termination frontier is unchanged.

**Best next question:** Can one prove a sublinear cumulative positive
excess for the existing live tilted odd share at the optimizing tilt
and a depth constant whose rate exceeds the contagion threshold?

## Publication assessment

Status: **THEOREM**. A useful correction and exact-map obstruction
derived from existing estimates, not a standalone termination paper.

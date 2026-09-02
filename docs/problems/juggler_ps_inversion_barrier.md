# Juggler PS-inversion of the fixed harmonic (the sub-density barrier)

Status: **CLOSE** (the m-variable Piatetski–Shapiro inversion is a
genuinely different computation from every recorded n-variable route:
it removes all brackets exactly and reduces the sole unbuilt axis to
clean two-monomial exponential sums. Those sums need cancellation
**below the PS density** \(M^{2/3}\); exponent pairs give
\(M^{(5/4)p+q}\), the door needs \((5/4)p+q<2/3\), and the known hull
bottoms out at \(95/112\approx 0.848\) (Bourgain). The \(\beta\)-half's
"every node" weakens to "all but vanishing mass", but its natural
second-moment implementation re-concentrates on the individual \(k=1\)
harmonic. The rate-free conjecture stays ACTIVE; its difficulty now
has a classical name.)

Successor of
[juggler_rate_free_floor_hardy](juggler_rate_free_floor_hardy.md)
(**CLOSE**), attacking the boxed external pair that record left: prove
rate-free equidistribution of \(f(\lfloor h(n)\rfloor)\) with nonlinear
Hardy \(f,h\) — instance \(f(m)=m^{9/4}\), \(h(n)=n^{3/2}\) — or find a
route to the node-wise E-share \(\beta>\beta_*\approx 0.36907\) that
does not pass through that composition. Not a reopen of the closed
abstract Hardy-along-PS *transfer* (this is a computation with the
exact indicator, not a citation of Boshernitzan on a subsequence), not
PET, not Theorem R, not a \(K_3\) bound, and not a Paper B edit.

## Problem

Whether the exact Piatetski–Shapiro indicator inversion proves
\(S_c(N)=\sum_{n\le N}e\bigl(c\lfloor n^{3/2}\rfloor^{9/4}\bigr)=o(N)\)
for fixed \(c\neq 0\) — the single unproved axis of the rate-free
tower target — and whether any node-mass relaxation of Lemma B
(`J-rate-free-density-one`) changes the species of what termination
needs.

## Exact statement

Let \(v(n)=\lfloor n^{3/2}\rfloor\) (strictly increasing), and

\[
r(m)=\#\{n:\ v(n)=m\}
=\lceil (m+1)^{2/3}\rceil-\lceil m^{2/3}\rceil\in\{0,1\}.
\]

**1. Inversion identity (EXACT — HUMAN PROOF; elementary).**

\[
S_c(N)=\sum_{n\le N}e\bigl(c\,v(n)^{9/4}\bigr)
=\sum_{m\le v(N)}r(m)\,e\bigl(c\,m^{9/4}\bigr).
\]

The floor leaves the phase and enters the summation set; no bracket
remains. With \(\psi(t)=\{t\}-\tfrac12\) and
\(w(m)=(m+1)^{2/3}-m^{2/3}\),
\(r(m)=w(m)+\psi(-(m+1)^{2/3})-\psi(-m^{2/3})\) exactly.

**2. Main-term power saving (EXACT — HUMAN PROOF; classical van der
Corput, no new ledger row).** On a dyadic block \(m\sim M_1\) the
third derivative of \(c\,m^{9/4}\) is \(\asymp|c|M_1^{-3/4}\),
one-signed; the third-derivative test gives
\(\ll M_1^{7/8}+M_1^{5/8}\), and partial summation against the
decreasing weight \(w\asymp M_1^{-1/3}\) gives \(M_1^{13/24}\) per
block, hence

\[
\Bigl|\sum_{m\le M}w(m)\,e(c\,m^{9/4})\Bigr|\ll_c M^{13/24}
= N^{13/16}.
\]

The smooth part of the inversion is **never** the obstruction; the
whole door is the \(\psi\)-fluctuation correlation.

**3. Vaaler reduction of the fluctuation (KNOWN technique).** With
truncation \(J=M^{2/5}\), the Vaaler error terms cost
\(O(M/J+J^{1/2}M^{1/3}+J^{-1/2}M^{2/3})
=O(M^{3/5}+M^{8/15}+M^{7/15})\), all below the density \(M^{2/3}\)
(the \(j\)-majorant sums \(\sum_m e(jm^{2/3})\) fall to the classical
second-derivative test, \(\lambda_2\asymp|j|M_1^{-4/3}\)). What
survives is the family of clean two-monomial sums

\[
T_j(M)=\sum_{m\le M}e\bigl(c\,m^{9/4}-j\,(m+\delta)^{2/3}\bigr),
\qquad \delta\in\{0,1\},\ 1\le|j|\le J,
\]

with Vaaler weights \(\ll 1/|j|\). Sufficient for the axis:
\(|T_j|\ll M^{2/3}/\log^2 M\) uniformly. On blocks
\(M_1\gg M^{0.27}\) the \(9/4\)-term dominates every derivative
uniformly in \(|j|\le J\); smaller blocks are trivially below
density.

**4. The sub-density barrier (KNOWN; the stop).** The trivial count of
nonzero terms in \(S_c(N)\) is \(N=M^{2/3}\): the needed bound on
\(T_j\) is cancellation **below the density of the PS image** — a
demand the PS-primes literature never meets at large outer amplitude
(its outer phases are small; here \(c\,m^{9/4}\) has derivative
\(\asymp M^{5/4}\gg 1\)). An exponent pair \((p,q)\) gives the block
bound \(M_1^{(5/4)p+q}\); the door needs

\[
\tfrac54 p+q<\tfrac23 .
\]

Van der Corput derivative tests give \(7/8\) (both \((1/6,2/3)\) and
\((1/14,11/14)\) land exactly on \(7/8\); \(k=3,4,5\) derivative tests
give \(1-\frac{k-9/4}{2^k-2}\ge 7/8\) with the best value \(7/8\) at
\(k=3,4\)). The known hull's minimum of the functional is
\(\tfrac54\cdot\tfrac{13}{84}+\tfrac{55}{84}=\tfrac{95}{112}\approx
0.848\) at Bourgain's pair (`bourgain-2017-exponent-pair`). The
exponent-pair conjecture point \((0,1/2)\) gives \(1/2<2/3\) and would
prove the axis **with power savings**. The gap \(0.848\to 0.667\) is
roughly half the distance to the conjecture: the door is unbuilt
because it sits beyond the Bombieri–Iwaniec frontier, not because the
inversion was missing.

**5. No family average over \(j\) (KNOWN; CC-shaped).** The Vaaler
weight \(1/|j|\) concentrates at \(j=1\), and the difference structure
\(e(-j(m+1)^{2/3})-e(-jm^{2/3})\) trades its gain \(\asymp|j|M^{-1/3}\)
exactly against the \(1/|j|\) weight over the \(\asymp M^{1/3}\)
relevant \(j\): the individual \(T_1\) must be bounded. Mean-value /
large-sieve over the \(j\)-family ignores the \(m^{9/4}\) oscillation
and returns \(M/\sqrt J\gg M^{2/3}\). This is Proposition CC's
"\(k=1\) carries weight one" (`J-dispersion-count-route`) recurring in
the \(j\)-aisle.

**6. Vanishing-bias-mass relaxation of Lemma B (EXACT — HUMAN PROOF;
no new ledger row).** Let \(\mu\) be a subsequential limit of the
depth-\(d\) class frequencies as in Lemma B, fix
\(\beta>\beta_*\), and call \(\sigma\) *biased* if
\(\mu(\sigma O)>(1-\beta)\mu(\sigma)\). If the total \(\mu\)-mass of
biased itineraries of length \(k\) is \(\le\varepsilon_k\) with
\(\frac1d\sum_{k<d}\varepsilon_k\to 0\), then density-one finite
descent still holds. *Proof.* The expected number of biased nodes on
a \(\mu\)-random path of length \(d\) is \(\le\sum\varepsilon_k=o(d)\);
Markov bounds paths hitting \(\ge\delta d\) biased nodes by
\(o(1)/\delta\). On the rest, count odds at unbiased nodes only:
the Lemma B node factor \(1+(x-1)\mu(\sigma O)/\mu(\sigma)\le
\beta+(1-\beta)x\) (for \(x\ge1\)) applies at each unbiased node and
factor \(1\) elsewhere, so
\(\mathbb E[x^{U_d}]\le(\beta+(1-\beta)x)^d\); never-contracting needs
\(o_d\ge\gamma d\), \(\gamma=\log2/\log3\), and \(o_d\le U_d+\delta d\)
on the good event, giving the Chernoff rate
\(D\bigl(\tfrac{\gamma-\delta}{1-\delta}\,\|\,1-\beta\bigr)>0\) for
\(\delta<(\gamma-(1-\beta))/\beta\). Let \(d\to\infty\), then
\(\delta\to 0\). \(\square\)

**7. The relaxation does not change the species (KNOWN).** The natural
route to \(\varepsilon_d\to0\) is the class-count variance; expanding
the class indicator squares the same kernels, so the variance is
\(\sum_k w_k|K(k)|^2/N^2\) with weight \(\asymp1\) at \(k=1\): it needs
\(|K(1)|=o(N)\) — the identical fixed harmonic of item 4. Proposition
CC applies verbatim. Quick kills for the other "different route"
candidates: short-interval letter equidistribution dies at depth 2
(the parity partition of \(x\)-space has cell width
\(\asymp\tfrac23 x^{-1/2}<1\), no interval structure survives —
cf. `J-hug-flow-image-gap`); \(x\mapsto x^{3/2}\) generates a
singly-generated semigroup, so no \(\times2\times3\)-type rigidity;
subshift/unique-ergodicity arguments cannot see natural density.

Scope: items 1–5 treat the single-floor depth-3 axis (the first
unproved node, OOOO fifth letter). Deeper tower levels compound
floors; the twice-iterated inversion is exactly the small-amplitude
Kolesnik regime and is out of scope here.

## Current literature

Project relationship: **known** (van der Corput tests, Vaaler,
exponent-pair hull) / **extended** (the inversion applied at large
outer amplitude; the PS literature keeps outer phases small) /
**reproduced** (the CC-shaped weight concentration).

- `kuipers-niederreiter-1974-uniform-distribution` — derivative tests.
- `bourgain-2017-exponent-pair` — the pair \((13/84,55/84)\); hull
  minimum \(95/112\) of the barrier functional (new registry row).
- Paper B §3 — the Vaaler idiom this record reuses.
- `J-dispersion-count-route` (Proposition CC) — the weight-one
  concentration, recurring here in the \(j\)-family.
- [juggler_rate_free_floor_hardy](juggler_rate_free_floor_hardy.md) —
  the audit this record extends: the "Hardy-along-PS" row there closed
  the abstract *transfer*; the indicator *computation* was not run.

## Branch budget

```text
Mathematical target     does the m-variable PS-indicator inversion (a
                        computation, not the closed abstract subsequence
                        transfer) prove S_c(N) = o(N) for the fixed
                        harmonic, and does any node-mass relaxation of
                        Lemma B change the needed species?
Novelty hypothesis      the audit dismissed PS machinery as rated /
                        small-amplitude in the n-picture without running
                        the inversion; in the m-picture brackets
                        disappear and classical two-monomial sums might
                        close the door; separately "every node" may
                        weaken to "all but vanishing mass"
Falsifier               the m-picture needs cancellation below the PS
                        density M^{2/3} and the exponent-pair functional
                        (5/4)p+q sits above 2/3 on the known hull; the
                        L^2 route re-concentrates on the k=1 harmonic
Existing machinery      Vaaler idiom (Paper B), vdC derivative tests,
                        Lemma B domination + Chernoff, Proposition CC,
                        exact big-integer fractional parts
Maximum Phase-0 scope   desk derivation + one probe (identity seal,
                        |S|/sqrt N, main-term dyadics, T_j at j in
                        {1,2,5}); no Lean, no paper edits, no new N_0
Promotion criterion     an o(N) proof for the fixed harmonic, a known
                        exponent pair with (5/4)p+q < 2/3, or an
                        eps_d-route avoiding the k=1 harmonic
Stop criterion          the barrier lands beyond the known exponent-pair
                        hull and the relaxation collapses to the same
                        harmonic -> record placement, CLOSE
```

## Balanced-ternary formulation

None required. The objects live on \(\mathbb T\) and in classical
exponential-sum theory.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Inversion identity \(S_c(N)=\sum r(m)e(cm^{9/4})\) —
  **EXACT — HUMAN PROOF** (elementary; sealed exactly by the probe)
- Main-term saving \(\ll_c M^{13/24}=N^{13/16}\) —
  **EXACT — HUMAN PROOF** (classical vdC \(k=3\); no new ledger row)
- Vaaler reduction to \(T_j\) with sufficient bound
  \(M^{2/3}/\log^2M\) — **KNOWN** technique, correctly budgeted at
  \(J=M^{2/5}\)
- Sub-density barrier \((5/4)p+q<2/3\) vs hull minimum \(95/112\) —
  **KNOWN** (exponent-pair hull; Bourgain)
- \(j\)-family average — fails; weight re-concentrates at \(j=1\)
  (**KNOWN**, CC-shaped)
- Vanishing-bias-mass relaxation of Lemma B —
  **EXACT — HUMAN PROOF** (this record; no new ledger row)
- Variance route to \(\varepsilon_d\to0\) — collapses to \(|K(1)|=o(N)\)
  (**KNOWN**, Proposition CC verbatim)
- Short-interval / rigidity / subshift routes to \(\beta\) — dead on
  arrival (cell width \(<1\) at depth 2; singly-generated semigroup;
  densities invisible) — **KNOWN**
- Equidistribution of \(\{v^{9/4}\}\) — not claimed

## Experiments

`src/research/juggler_sequence/ps_inversion_barrier.py`
(`PS_INVERSION_BARRIER_GREEN`), summary at
`data/research/juggler/ps_inversion_barrier/summary.json`. All
\(m^{9/4}\) fractional parts are exact big-integer fourth roots
(\(\lfloor m^{9/4}2^s\rfloor=\operatorname{isqrt}(\operatorname{isqrt}
(m^9\cdot 2^{4s}))\), \(s=64\)); no float phase at amplitude
\(10^{15}\).

- **Seal:** \(|S_n-S_m|=0.0\) at \(N=10^4\) (\(M=10^6\));
  \(\sum r(m)=N\), \(r\in\{0,1\}\) everywhere.
- **Weyl sums:** \(|S_{1/2}(N)|/\sqrt N=1.067\) (all \(n\)), \(0.804\)
  (odd \(n\)) at \(N=2^{21}\) — square-root scale throughout the
  checkpoint ladder.
- **Main term:** \(|W(M)|/M^{13/24}=0.0013\) at \(M=2^{23}\) — deep
  inside the proved envelope.
- **Fluctuation:** \(|T_1|/\sqrt M=2.03\), \(|T_2|/\sqrt M=2.17\),
  \(|T_5|/\sqrt M=0.32\) at \(M=2^{23}\); against the density scale,
  \(|T_j|/M^{2/3}\le 0.153\). Empirically the sums sit at the EPC
  (square-root) scale: the statement looks true; only the proof is
  missing.

## Conjectures

None new. `juggler_tower_rate_free_equidistribution` stays **ACTIVE**;
its single-floor axis is now placed at the sub-density exponent-pair
frontier.

## Counterexamples

None. Both novelty hypotheses died by obstruction (the density barrier
vs the known hull; weight re-concentration), not by a counterexample.
No orbit is claimed to fail equidistribution.

## Formalization

None. Lean-ifying van der Corput tests or the Vaaler budget ahead of
the missing exponent pair would be machinery gravity.

## Results

Classification **PS_INVERSION_SUB_DENSITY_BARRIER**.

- The inversion is exact and bracket-free; the smooth main term has
  unconditional power savings \(N^{13/16}\). The entire door is the
  \(\psi\)-fluctuation correlation.
- That correlation is a family of clean two-monomial sums
  \(T_j=\sum_{m\le M}e(cm^{9/4}-jm^{2/3})\) needing **sub-density**
  cancellation \(o(M^{2/3})\): needed \((5/4)p+q<2/3\); van der Corput
  \(7/8\); known hull minimum \(95/112\) (Bourgain); EPC \(1/2\).
- No family average helps: the \(1/j\) weight re-concentrates at
  \(j=1\) (CC-shaped).
- Lemma B's "every node" weakens to "all but vanishing \(\mu\)-mass of
  biased nodes" (new small lemma), but the variance route to that mass
  needs the same individual \(k=1\) harmonic: the species does not
  change.
- Empirics: every hard sum sits at square-root scale through
  \(2^{21}\)/\(2^{23}\).
- Not claimed: equidistribution; density-one; a \(K_3\) bound; any new
  exponent pair. No new ledger row.

## Open questions

- The BI-only question is answered **NO** by
  [juggler_bi_resonance_limit.md](juggler_bi_resonance_limit.md)
  (needed \(p<2/27\); method ceiling \(3/20\); margin \(81/40\)).
  The remaining external question is the boxed pair of
  [exponent_pair_two_monomial.md](../theory/exponent_pair_two_monomial.md):
  prove \(\tfrac54 p+q<\tfrac23\) for an exponent pair applicable to
  \(cm^{9/4}-jm^{2/3}\). That is classical exponential-sum theory,
  not a laboratory branch and not a Juggler construction.

## Decision

**CLOSE.** The stop criterion fired exactly as named: the m-picture
converts the unbuilt composition into classical two-monomial sums, but
they must beat the PS density \(M^{2/3}\), and the known exponent-pair
hull stops at \(95/112\approx0.848\) — roughly halfway to the
conjecture point that would finish it. The \(\beta\)-half's node-mass
relaxation is recorded but collapses to the same \(k=1\) harmonic.
`juggler_tower_rate_free_equidistribution` stays ACTIVE as the
external problem, now with a classical name for its difficulty. Best
next question: none from this laboratory; the remaining pair is
exported at
[exponent_pair_two_monomial.md](../theory/exponent_pair_two_monomial.md).

## Publication assessment

Status: `STRUCTURAL`. Two small exact lemmas (main-term saving;
bias-mass relaxation) plus a sharp classical placement of the door's
difficulty. Not a paper claim; no Paper A or Paper B edit.

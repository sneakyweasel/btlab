# Lachesis log-log clock: the exponent walk as the basin's scale spectrum

Status: **PARK** (the bridge is exact and cheap; its one operational
consequence is dominated by a floor raise)

Child of [juggler_fate_contagion.md](juggler_fate_contagion.md) and the
flight extract. Not a halt theorem, not a period bound, not a floor
raise, and it excludes no fate. It changes what
[Corollary 4.3](../theory/juggler_fate_contagion_note.md) says about
the Lachesis class, and nothing else.

## Problem

Paper D's firewall states the gap in one sentence: Paper A constrains
the *states* of a hypothetical cycle (minimum above \(3.5\cdot 10^8\),
period at least \(780239\)); Paper C Theorem 1 constrains the *basin*
(log-count \(\gg(\log x)^{0.448}\)); the two constraints do not meet.
Do they describe the same object in different coordinates?

## Exact statement

**Proposition 1 (rotation; EXACT — HUMAN PROOF).** For every start and
every \(t\), the exponent walk \(u_t=o_t\log_2 3-t\) satisfies
\[
u_t\equiv o_t\,\alpha \pmod 1,\qquad \alpha=\log_2 3-1=\log_2(3/2),
\]
because \(t\) and \(o_t\) are integers and \(\log_2 3=1+\alpha\). Along
a cycle of period \(L\) the odd count \(o_t\) takes every value
\(0,\ldots,o\), so the walk values mod 1 are exactly the rotation orbit
\(\{j\alpha\}_{j<o}\).

**Observation 2 (clock; OBSERVATION, one-sided half Lean).**
\(\log_2\log J^t(n)=\log_2\log n+u_t+\varepsilon_t\). The one-sided half
is the height law (flight note §2, `aboveAnchor_height_of_walk`); the
two-sided half is the transport bound of §6,
\(\Delta\le 1.05\,t/\min\), giving
\(\varepsilon_t=\log_2(1-\Delta_t/\log n)\). Measured on 200 odd starts
per scale at \(10^{12}\)–\(10^{100}\), above \(N_0\):
\(\max\lvert\varepsilon\rvert=2.07\cdot 10^{-10}\) in u-units. The
transport bound on a hypothetical cycle gives
\(1.72\cdot 10^{-4}\) at \(n=3.5\cdot 10^8,\ L=780239\), and
\(5.13\cdot 10^{-6}\) at \(n=10^{10}\).

**Observation 3 (single-seed burst; COMPUTATIONALLY VERIFIED).** The
\(E\)-tree of a seed \(m\) occupies, at generation \(k\), the interval
from \(m^{2^k}\) to \((m+1)^{2^k}\) with internal density \(2^{-k}\),
hence natural density \(\approx 1/m\) at that scale. Verified exactly:
\(m=101,\ k=2\) gives \(1040603\) members at scale \(1.0824\cdot 10^8\),
density \(0.009614\) against \(1/m=0.009901\).

**Consequence 4 (every block; CONJECTURE
`juggler_lachesis_basin_every_block`).** Write \(c(x)=\log_2\log x\).
The scales carrying \(E\)-tree bursts of a backward-closed class are
\(\{c(m)+k\}\) over its seeds \(m\) and \(k\ge 0\), so the covered
scales mod 1 are \(\{c(m)\bmod 1\}\). By Propositions 1–2 the cycle
states of a Lachesis basin sit at \(c(n)+u_t\), an equidistributed
rotation orbit with largest gap \(5.10\cdot 10^{-6}\) at \(L=780239\)
(\(5.19\cdot 10^{-6}\) at \(478245\); \(5.01\cdot 10^{-6}\) at
\(1082233\)) — far finer than the \(1.72\cdot 10^{-4}\) clock defect,
and both far below 1. Hence a Lachesis basin is **not lacunary**: it
carries natural density \(\gtrsim 1/n\) on every dyadic block, where
\(n\) is the cycle minimum.

This is the third case, missing from contagion note §5.3, which treats
only the single seed (lacunary, and the reason pointwise density fails)
and the interval \([1,N_0]\) (uniform). For the Lachesis class it
upgrades Corollary 4.3 from *some* \(y\) in a range to *every* dyadic
block. It excludes nothing.

**Refutation 5 (the census is dominated; REFUTED).** Density
\(\sim 1/n\) means \(M\) samples give \(M/n\) expected basin members, so
a census of \(M\) samples tests cycle minima only up to \(\sim M\).
Certifying that every \(n\le M\) reaches 1 costs \(M\) *shallow* orbits
instead of \(M\) orbits at scale \(10^{100}\) run to depth \(\approx
500\), and returns a certificate rather than a statistic. The census is
strictly worse than the floor campaign already parked at
\(5.54\cdot 10^8\).

## Current literature

- Contagion note Theorem 4.2 / Corollary 4.3 / §5.3 (`extended`): the
  log-count bound and its "infinitely many blocks" natural-density
  corollary; §5.3's single-seed lacunarity is the objection this branch
  routes around for Lachesis.
- Paper A §5 Ostrowski / rotation layer (`reproduced`): the walk as a
  rotation is that machinery read mod 1.
- Flight note §2 height law and §6 return quantization (`reproduced`):
  the two halves of the clock.
- Paper D §7 firewall (`extended`): this is a partial crossing of the
  stated gap, on the basin side only.
- Three-distance theorem (`known`): the gap structure of
  \(\{j\alpha\}\).

## Branch budget

```text
Mathematical target     Do Paper A's cycle walk and Paper C's basin density describe
                        the same object in different coordinates?
Novelty hypothesis      log log x_t = log log n + u_t log 2 + defect, so the walk is
                        the log-log clock; the scales at which a Lachesis basin shows
                        E-tree bursts are the walk values mod 1, and along a cycle
                        those are an equidistributed rotation orbit.
Falsifier               the defect is O(1) in u-units, drowning the correspondence.
Existing machinery      flight note Sec.2 height law (Lean), Sec.6 transport,
                        contagion note Cor 4.3 and Sec.5.3, tao_reduction.
Maximum Phase-0 scope   measure the defect on real orbits; rotation gaps; single-seed
                        E-tree density; price the resulting census.
Promotion criterion     defect << 1 in u-units at cycle scales.
Stop criterion          defect O(1), or the conclusion is Cor 4.3 restated.
```

## Balanced-ternary formulation

None. The objects are the exponent walk of a Juggler orbit, its
reduction mod 1, and the natural density of an \(E\)-forest on dyadic
blocks.

## Why BT may be relevant

Not relevant here; recorded for the template. The relevant numeration
is Ostrowski for \(\alpha=\log_2(3/2)\), already in
`OstrowskiNumeration.lean`.

## Candidate operations / invariants

- \(u\mapsto u\bmod 1\), the clock circle — **EXACT — HUMAN PROOF**
  (Proposition 1).
- \(c(x)=\log_2\log x\), the clock — **OBSERVATION** with a Lean
  one-sided half (Observation 2).
- \(m\mapsto\) burst scales \(m^{2^k}\) — **COMPUTATIONALLY VERIFIED**
  (Observation 3).
- Rotation gap as basin scale coverage — **CONJECTURE** (Consequence 4).
- Census reach versus floor reach — **REFUTED** (Refutation 5).

## Experiments

`python -m research.juggler_sequence.lachesis_loglog_clock` writes
`data/research/juggler/lachesis_loglog_clock/summary.json`:
`clock_defect_census` (200 orbits per scale, \(10^{12}\)–\(10^{100}\)),
`cycle_clock_defect_bounds`, `rotation_coverage` (the three certified
periods), `etree_density` (\(m\in\{11,101\}\), generations 1–2), and
`census_price`. Fast test:
`tests/research/juggler_sequence/test_lachesis_loglog_clock.py`.

## Conjectures

`conjectures/active/juggler_lachesis_basin_every_block.json`.

## Counterexamples

None. Refutation 5 is a cost argument, not a witness.

## Formalization

None yet. Proposition 1 is one line of integer arithmetic and is the
natural Lean candidate; the one-sided half of Observation 2 is already
`aboveAnchor_height_of_walk`. No `sorry` is introduced because no Lean
file is added.

## Results

| Statement | Tag |
|---|---|
| Walk mod 1 is the rotation orbit by \(\log_2(3/2)\) | **EXACT — HUMAN PROOF** |
| Clock defect \(2.07\cdot 10^{-10}\) realised, \(1.72\cdot 10^{-4}\) bounded on a cycle | **OBSERVATION** |
| Single-seed \(E\)-tree density \(1/m\) at each burst scale | **COMPUTATIONALLY VERIFIED** |
| A Lachesis basin is not lacunary; density \(\approx 2/n\) on every block, \(y<10^{85142}\) | **CONJECTURE** |
| \(E\) contributes \(2/m\), \(OE\) contributes \(\approx 1/3\) of that; no special blocks | **COMPUTATIONALLY VERIFIED** |
| Per-block \(E\) law exact to \(0.5\%\); one burst gives \(S/(x\lvert B\rvert)\in(1/x,2/x]\) | **COMPUTATIONALLY VERIFIED** |
| Contagion-visible density \(\in[1,3]\cdot\sum_C 1/x/\ln y\), with \(\sum_C 1/x\ge\theta(L)\ln n\) by Lean finance | **COMPUTATIONALLY VERIFIED** (law) + **EXACT — LEAN VERIFIED** (finance half) |
| Upper bound on the full basin is the free term \(\psi_F\) | **REPARAMETERIZATION** |
| Clotho basin every-block at \(y\) iff \(O(y)\ge O^*(y)\); window \(s^*-q^*\approx 0.004\) to \(10^{100}\) | **CONJECTURE** (gaps **COMPUTATIONALLY VERIFIED**) |
| The deep natural-density census is dominated by a floor raise | **REFUTED** |

**Observation 6 (the OE detour costs; COMPUTATIONALLY VERIFIED).** The
two contagion productions are two translations of the same clock:
\(E\) sends \(c\) to \(c+1\), and \(OE\) sends \(c\) to
\(c+\beta\), \(\beta=\log_2(4/3)=0.415037\), via
\(\lfloor\sqrt{\lfloor n^{3/2}\rfloor}\rfloor=\lfloor n^{3/4}\rfloor\)
(checked on \([2,60000)\)). One production step from a single seed \(m\)
contributes to the natural density of the block containing its image:

| \(m\) | \(E\): \(m\times\)density | \(OE\): \(m\times\)density | \(OE/E\) |
|---|---|---|---|
| 101 | 1.9610 | 0.4235 | — |
| 1001 | 1.9960 | 0.3993 | 0.200 |
| 5001 | 1.9992 | 0.7015 | 0.351 |
| 10001 | 1.9996 | 0.6497 | 0.325 |

So \(E\) gives exactly \(2/m\) and every \(OE\) detour costs a factor
\(\approx 1/3\) while buying only a new clock offset.

**Consequence 7 (no special blocks).** A dyadic block is a \(c\)-window
of width \(\approx 1/\log y\): \(1.46\cdot 10^{-2}\) at \(10^{30}\),
\(4.34\cdot 10^{-4}\) at \(10^{1000}\) — always wider than the
\(\alpha\)-gap \(5.101\cdot 10^{-6}\) out to
\(\log y=1/5.101\cdot 10^{-6}\), i.e. \(y<10^{85142}\). So a cycle-state
*pure-\(E\)* burst already lands in every block on that range, and by
Observation 6 no \(OE\) path can improve on it. The basin's per-block
density is \(\approx 2/n\) uniformly; there are no special blocks.

Corollary 4.3's amplification is therefore in **log-count**, not in
per-block natural density: the \(OE\) steps reach new scales, which the
logarithmic integral sees and a single block does not. Its constant
carries the seed's \(1/n\), so the factor \((\log y)^{\lambda-1}\) is not
an absolute density.

**Observation 8 (per-block law; COMPUTATIONALLY VERIFIED).** On the
dyadic block \(B\), the \(E\)-closure of a finite seed set \(S\) has
density exactly
\[
\sum_{x\in S}\sum_{k\ge 1}\frac{\lvert[x^{2^k},(x+1)^{2^k})\cap B\rvert}{\lvert B\rvert}\,2^{-k},
\]
verified to \(0.5\%\) (measured/predicted \(0.996\)–\(1.005\)) on a
\(40\)-seed closure to \(4\cdot 10^7\). One landing burst from \(x\) at
scale \(S=x^{2^k}\) contributes \(S/(x\lvert B\rvert)\in(1/x,2/x]\),
so the floor constant is \(1\), not the \(2\) of Observation 3 (which
normalised by \(S/2\)). \(OE\) bursts land at clock offset \(\beta\), in
*other* blocks — six blocks of the test carry \(OE\) density with zero
\(E\) density — and add \(8\)–\(32\%\) where both land; the aggregate
factor \(9/7\)–\(3/2\) is not a per-block credit.

**Consequence 9 (the finance link).** For a Lachesis basin the seeds are
the cycle states, which land in every block by Consequence 4, so the
contagion-visible block density at scale \(y\) satisfies
\[
\frac{1}{\ln y}\sum_{x\in C}\frac1x\ \le\ \delta_{E{+}OE}(y)\ \le\ \frac{3}{\ln y}\sum_{x\in C}\frac1x .
\]
The inverse sum is a Paper A object. The Lean inv-sum form of finance,
`cycleMin_finance_inv_sum`, gives \((3^o-2^L)\ln n\le 3^o\sum 1/x\),
i.e. \(\sum_{x\in C}1/x\ge\theta(L)\ln n\); every state \(\ge n\) gives
\(\sum 1/x\le L/n\); floor above cap is the finance kill of the pair
(\(n=10^{10},\ L=780239\)). At \(n=3.5\cdot 10^8,\ L=780239\),
\(\theta=3.471\cdot 10^{-6}\):

| \(y\) | \(\sum 1/x\) floor \(\theta\ln n\) | cap \(L/n\) | density floor | density cap | \(2/n\) |
|---|---|---|---|---|---|
| \(10^{12}\) | \(6.83\cdot 10^{-5}\) | \(2.23\cdot 10^{-3}\) | \(2.47\cdot 10^{-6}\) | \(2.42\cdot 10^{-4}\) | \(5.7\cdot 10^{-9}\) |
| \(10^{30}\) | | | \(9.89\cdot 10^{-7}\) | \(9.68\cdot 10^{-5}\) | |
| \(10^{68}\) | | | \(4.36\cdot 10^{-7}\) | \(4.27\cdot 10^{-5}\) | |

A cycle that barely survives finance has \(\sum 1/x\) pinned, hence a
basin whose contagion-visible density is pinned to within the constant.
This is the first statement in which Paper A's finance and Paper C's
basin appear in one inequality. It bounds the \(E{+}OE\) part only.

**Proposition 10 (the upper bound is the free term; REPARAMETERIZATION).**
An upper bound on the *full* basin's block density is \(\psi_F\): the
even members at scale \(y\) are the \(E\)-blocks of members at
\(\sqrt y\), the \(OE\)-type odd members are fibers of members at
\(y^{3/4}\) (Paper B, unconditional), and the \(OO\)-type odd members
are the odd preimages of the odd images at \(y^{3/2}\) — the free term
of fate note (6.1). Dropping \(\psi\le 1\) there is exactly the upper
recursion for the failure density (Tao note §11.2), and \(\psi_F\) is
the infinite-depth live mass of the \(OO\) cylinder (Prop. 11.1), i.e.
the pressure hypothesis. Unconditionally the only upper bound is
\(1-\)density\((R)\), and the \(E\)-tree of \([1,N_0]\) alone gives
density\((R)\ge\log N_0/(2\log y)\approx 0.06\) at \(10^{68}\)
(contagion note §5.3). So the two-sided constraint on the full basin is
\(2.5\cdot 10^{-6}\lesssim\delta\le 0.94\) at \(10^{12}\); the firewall
is crossed from below only.

**Consequence 11 (Clotho criterion; CONJECTURE
`J-clotho-basin-every-block-criterion`).** Proposition 1 does not know
whether the orbit closes. For a divergent orbit the states below \(y\)
sit at clock positions \(c(n)+j\alpha\), \(j\le O(y)\), where \(O(y)\)
is the odd count before the walk first exceeds
\(u(y)=\log_2(\ln y/\ln n)\). The basin has a burst in the block at
\(y\) iff one of those points lies within \(1/\ln y\) of \(c(y)\) mod 1;
sufficient is \(\mathrm{gap}(O(y))\le 1/\ln y\), with
\(\mathrm{gap}(O)\) the largest gap of \(\{j\alpha\}_{j\le O}\),
non-increasing in \(O\). Let \(O^*(y)=\min\{O:\mathrm{gap}(O)\le
1/\ln y\}\). Reaching \(u(y)\) in at least \(O^*\) odd steps caps the
walk gain per odd step at \(u/O^*\), i.e. the odd share at
\(s^*=1/(\log_2 3-u/O^*)\):

| \(y\) | \(1/\ln y\) | \(O^*(y)\) | \(u(y)\) | gain per odd step | \(s^*-q^*\) |
|---|---|---|---|---|---|
| \(10^{12}\) | 3.62e-2 | 40 | 0.490 | 0.01225 | 0.00491 |
| \(10^{30}\) | 1.45e-2 | 146 | 1.812 | 0.01241 | 0.00498 |
| \(10^{68}\) | 6.39e-3 | 305 | 2.993 | 0.00981 | 0.00393 |
| \(10^{100}\) | 4.34e-3 | 358 | 3.549 | 0.00991 | 0.00397 |
| \(10^{300}\) | 1.45e-3 | 1635 | 5.134 | 0.00314 | 0.00125 |
| \(10^{1000}\) | 4.34e-4 | 12275 | 6.871 | 0.00056 | 0.00022 |

(\(O\cdot\mathrm{gap}(O)\) swings between \(1.26\) and \(6.56\) with
the continued fraction of \(\alpha\) — three-distance.) The all-odd
rate \(0.585\) is far outside the window at every scale. The \(p=19\)
hug near-return rate \(\theta_{19}/12=0.00163\) per odd step is inside
up to \(10^{300}\) but *outside* at \(10^{1000}\), where the gate is
\(0.00056\); the \(p=84\) rate \(\theta_{84}/53=5.7\cdot 10^{-5}\) is
inside everywhere tested, and \(p=1054\) gives \(9.5\cdot 10^{-8}\). So
the gate tightens with \(y\) and pushes a persistent escaper down the
near-return spectrum \(19\to 84\to 1054\to\cdots\) — the same
Diophantine ladder as the cycle periods (§6 of the flight note). A
Clotho basin is every-block at scale \(y\) exactly when the divergent
orbit is a critical-share escaper up to that scale, hugging a deep
enough near-return; a fast escaper has a lacunary basin, like a single
seed.
The density is then \(\approx(K/\ln y)\sum_{x_t\le y}1/x_t\),
\(K\in[1,3]\); the partial sum is \(\ge 1/n\) and, unlike the cycle's,
is not pinned by finance.

Both fates now share one visibility law: block density
\(\approx(K/\ln y)\times\)(inverse sum of the landing seeds). For
Lachesis the sum is fixed and finance-pinned; for Clotho it is a partial
sum gated by the escape rate.

## Open questions

Beyond \(y\approx 10^{85142}\) the \(\alpha\)-gaps exceed the block
width and pure-\(E\) coverage lapses for a cycle of period \(780239\);
there the \(OE\) offsets matter and the every-block statement is not
claimed. Longer periods push the threshold out (gap
\(2.68\cdot 10^{-6}\) at \(L=8632083\)). Nothing in this branch needs
that range.

For Clotho the gate is \(O(y)\ge O^*(y)\). Flight note §5.5 (recurrent
hug domination) says a divergent orbit re-enters hug-like phases from
every record, but does not by itself bound \(O(y)\) from below at every
scale. Whether it does is the open question.

## Decision

`PARK`. The bridge is exact, cheap, and previously unmade: it fills the
third case of contagion note §5.3 and gives the Lachesis class an
every-block density statement instead of an infinitely-often one. But
both ingredients are existing laboratory machinery, and the single
operational consequence — a deep natural-density census — is strictly
dominated by the floor campaign already parked at \(5.54\cdot 10^8\).
Nothing here excludes a fate or moves a period bound. Recording it and
stopping.

The upper-bound question is answered: it is the free term, so the
firewall is crossed from below only, and the lower bound is now
Paper A's inverse sum divided by \(\ln y\).

The Clotho question is answered by Consequence 11: yes, gated by the
escape rate, and the gate sits exactly on the critical-share regime.

Best next question: does recurrent hug domination (flight note §5.5)
force \(O(y)\ge O^*(y)\approx 1.3\)–\(6.6\,\ln y\) at every scale for
every persistent divergent orbit — making every Clotho basin every-block
unconditionally, as every Lachesis basin is?

## Publication assessment

Status: `STRUCTURAL`. Proposition 1 is exact but elementary;
Consequence 4 is the paper-relevant statement and is a conjecture whose
proof would be a paragraph in the contagion note, not a manuscript. Not
a `PAPER_CANDIDATE`.

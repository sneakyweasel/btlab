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
carries natural density \(\gtrsim 1/n\) on every dyadic block with
\(y\ge n^{2^{1+u_{\max}}}\), where \(n\) is the cycle minimum and
\(u_{\max}=\log_2(\ln M/\ln n)\ge 1\) its walk height (Paper A:
\(M\ge(n+1)^2\)). Bursts begin at \(n^2\) (generation \(1\) of the
minimum) and there are none below it; between \(n^2\) and the threshold
only the states with \(u_t\le c(y)-c(n)-1\) contribute and coverage is
not guaranteed. At \(n=3.5\cdot 10^8\): \(y\ge 10^{34}\) if
\(u_{\max}=1\), \(10^{69}\) if \(u_{\max}=2\), \(10^{137}\) if \(3\).
(This threshold was missing from the first draft, whose tables at
\(10^{12}\) and \(10^{30}\) were therefore not valid; corrected below.)

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
  routes around for Lachesis. Consolidated 5 Sep 2026: §5.3 now carries
  the third seed-set case, labelled CONJECTURE there. Paper C is
  untouched (a conjecture does not belong in a manuscript under
  review), and Paper A is untouched (AGENTS.md forbids editing it from
  a Phase-0 branch).
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

`formal/Problems/Juggler/LogLogClock.lean` (imports `Dynamics` only;
registered in the barrel and in `LAYERS`; no `sorry`):

- `fract_mul_sub_nat_eq_fract_mul_sub_one`: for every real \(x\) and
  naturals \(o,t\), \(\{ox-t\}=\{o(x-1)\}\).
- `fract_walk_eq_fract_rotation`: \(\{\mathrm{walk}\,o\,t\}=\{o\cdot\alpha\}\)
  with `walk o t = o * logb 2 3 - t` and `alphaClock = logb 2 3 - 1`
  — Proposition 1.
- `fract_walk_depends_only_on_odd_count`: the walk mod 1 does not see
  the length, only the odd count.
- `sqrt_cell`, `even_chain_mem_burst`: an even chain of length \(k\)
  from \(n\) to \(m\) forces \(m^{2^k}\le n<(m+1)^{2^k}\) — the
  interval half of Observation 3.
- `even_chain_log_offset`: the same in the clock,
  \(2^k\log m\le\log n<2^k\log(m+1)\) for \(m\ge 1\).
- `WalkStep`, `hug_band_step_exists`: from any \(u\in[0,1+\alpha)\)
  some step stays in the band — the hug band is invariant.
- `narrow_band_dead`, `dead_zone_nonempty`: every band \([0,w)\) with
  \(w<1+\alpha\) has a nonempty dead zone \([w-\alpha,1)\) from which no
  step stays — the hug band is the *minimal* invariant band.
- `no_even_step_below_one`, `odd_steps_below_one_le_one`: below \(1\)
  no even step is possible and at most one odd step fits
  (\(\alpha>1/2\), i.e. \(9>8\)).
- `band_step_forced_odd`, `band_step_forced_even`,
  `band_successor_unique`: inside the band the letter is forced and the
  successor is unique — the band walk is the lift of the rotation, and
  the word is the hug itinerary.
- `one_lt_logb_two_three`, `logb_two_three_lt_two`, `half_lt_alphaClock`:
  \(1<\log_2 3<2\) and \(\alpha>1/2\).

Not formalized: the count of the chain (\(\approx m^{2^k-1}\)), the
gap sizes of the rotation orbit, the clock defect, the finance link
(whose Lean half is the existing `cycleMin_finance_inv_sum`), and every
density statement. The one-sided height law remains
`aboveAnchor_height_of_walk`.

## Results

| Statement | Tag |
|---|---|
| Walk mod 1 is the rotation orbit by \(\log_2(3/2)\) | **EXACT — LEAN VERIFIED** (`fract_walk_eq_fract_rotation`) |
| Even chain of length \(k\) lands in \([m^{2^k},(m+1)^{2^k})\); clock offset exactly \(k\) | **EXACT — LEAN VERIFIED** (`even_chain_mem_burst`, `even_chain_log_offset`) |
| Clock defect \(2.07\cdot 10^{-10}\) realised, \(1.72\cdot 10^{-4}\) bounded on a cycle | **OBSERVATION** |
| Single-seed \(E\)-tree density \(1/m\) at each burst scale | **COMPUTATIONALLY VERIFIED** |
| A Lachesis basin is not lacunary; density \(\gtrsim 1/n\) on every block with \(n^{2^{1+u_{\max}}}\le y<10^{85142}\) | **CONJECTURE** |
| The hug band \([0,\log_2 3)\) is the minimal invariant band; below \(1\) at most one odd step | **EXACT — LEAN VERIFIED** (`hug_band_step_exists`, `narrow_band_dead`, `odd_steps_below_one_le_one`) |
| Inside the band the letter is forced; the band word is the hug itinerary | **EXACT — LEAN VERIFIED** (`band_successor_unique`) |
| Band residence is hug-prefix realization: \(2^{-L}\), depth \(28=\log_2(2\cdot 10^8)\) | **REPARAMETERIZATION** |
| A failure with \(k\) leading even steps is \(\ge 261^{2^k}\) (Lean floor); \(\ge(N_0+1)^{2^k}\) certified | **EXACT — LEAN VERIFIED** (`not_reachesOne_even_chain_ge`) |
| \(E\) contributes \(2/m\), \(OE\) contributes \(\approx 1/3\) of that; no special blocks | **COMPUTATIONALLY VERIFIED** |
| Per-block \(E\) law exact to \(0.5\%\); one burst gives \(S/(x\lvert B\rvert)\in(1/x,2/x]\) | **COMPUTATIONALLY VERIFIED** |
| Contagion-visible density \(\in[1,3]\cdot\sum_C 1/x/\ln y\), with \(\sum_C 1/x\ge\theta(L)\ln n\) by Lean finance | **COMPUTATIONALLY VERIFIED** (law) + **EXACT — LEAN VERIFIED** (finance half) |
| Upper bound on the full basin is the free term \(\psi_F\) | **REPARAMETERIZATION** |
| Clotho basin every-block at \(y\) iff \(O(y)\ge O^*(y)\); window \(s^*-q^*\approx 0.004\) to \(10^{100}\) | **CONJECTURE** (gaps **COMPUTATIONALLY VERIFIED**) |
| Slow escape forced by hug domination; realised flights meet the gate | **REFUTED** (structural + seven high-flyers, \(28\)–\(650\times\) too fast) |
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
| \(10^{100}\) | \(6.83\cdot 10^{-5}\) | \(2.23\cdot 10^{-3}\) | \(2.97\cdot 10^{-7}\) | \(2.90\cdot 10^{-5}\) | \(5.7\cdot 10^{-9}\) |
| \(10^{300}\) | | | \(9.89\cdot 10^{-8}\) | \(9.68\cdot 10^{-6}\) | |

(Valid for \(y\ge n^{2^{1+u_{\max}}}\); the \(10^{100}\) row needs
\(u_{\max}\le 2.5\). The first draft tabulated \(10^{12}\) and
\(10^{30}\), below the threshold — withdrawn.)

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
the continued fraction of \(\alpha\) — three-distance.) The gate is
meaningful only for \(u(y)\ge\log_2 3\), i.e. \(y\ge n^3\): the hug
band \([0,\log_2 3)\) is the minimal invariant band of the walk (Lean
`hug_band_step_exists`, `narrow_band_dead`, `dead_zone_nonempty`), and
below \(1\) no even step is possible and at most one odd step fits
(`no_even_step_below_one`, `odd_steps_below_one_le_one`), so for
\(y<n^3\) every orbit has \(O(y)\le 2<O^*(y)\) and no basin is
every-block there. At \(n=3.5\cdot 10^8\) the \(10^{12}\) row
(\(u=0.49\)) is vacuous. The all-odd rate \(0.585\) is far outside the
window at every scale. The \(p=19\)
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

**Refutation 12 (slow escape is not forced; REFUTED
`J-clotho-slow-escape-not-forced`).** Two ways. *Structurally:* every
flight-note law bounds escape from *below* —
\(a_k\ge\mathrm{hugOdds}(k)\) (`aboveAnchor_prefix_odds_ge_hug`),
\(u_k\ge 0\), \(u_k\ge\log_2(\log x_k/\log n)\), hug excess
\(\to\infty\), linear peak growth — and none from above; the gate
\(O(y)\ge O^*(y)\) is an upper bound on escape speed, and nothing in
the laboratory supplies one. *Empirically:* on the seven canonical
high-flyers, at the first passage of every recorded decade from
\(10^6\) to \(10^{5000}\), the gate is never met:

| \(n\) | steps | \(10^{100}\): \(O\), gain | \(10^{1000}\): \(O\), gain | \(10^{5000}\): \(O\), gain | gate at \(10^{5000}\) |
|---|---|---|---|---|---|
| 48443 | 59 | 11, 0.401 | 19, 0.407 | 26, 0.387 | 0.0006 |
| 275485 | 140 | 9, 0.467 | 15, 0.502 | 21, 0.469 | 0.0006 |
| 412027 | 113 | 14, 0.297 | 39, 0.192 | 51, 0.192 | 0.0006 |
| 463157 | 48 | 9, 0.460 | 15, 0.498 | 21, 0.466 | 0.0006 |
| 1122603 | 257 | 14, 0.289 | 23, 0.320 | 67, 0.145 | 0.0006 |

Gain per odd step at passage runs \(0.08\)–\(0.58\) against gates of
\(0.0006\)–\(0.04\): \(28\times\) to \(650\times\) too fast at every
decade, the slowest passage anywhere being \(1122603\) at
\(10^{5000}\) at \(240\times\). (Rows with \(u(y)<\log_2 3\), i.e.
\(y<n^3\) — decades below \(15\) for the \(10^5\) anchors, below
\(19\) for the \(10^6\) ones — are vacuous by Consequence 11; the
genuine rows still never meet the gate.) Random odd starts near \(10^6\) never
meet it either. So Consequence 11 stays conditional on slow escape, and
slow escape is neither forced nor observed: a persistent thread whose
basin is every-block would be unlike every flight ever realised. The
flights that exist are bursts, and bursts come back down.

**Obstruction 13 (no rate on hug excess; CONJECTURE
`J-clotho-hug-excess-rate`, PARK).** A rate on
\(a_k-\mathrm{hugOdds}(k)\to\infty\) would bound \(O(y)\) from above
and make every Clotho basin provably lacunary — cycles every-block,
escapes lacunary. The only rate the laboratory has is pigeonhole: a
descent-free flight with walk in \([0,B)\) has distinct states in
\([n,n^{2^B})\), so it leaves the band or cycles within \(n^{2^B}\)
steps; at the hug band \(B=\log_2 3\) that is \(n^3\approx 4\cdot
10^{25}\) at \(n=3.5\cdot 10^8\), against a gate \(O^*(y)\) of
\(40\)–\(12275\). Linear peak growth reaches walk
\(\log_2(1+\log(1+k/n)/\log n)\), negligible for \(k\ll n\). A usable
rate would say that no descent-free flight keeps odd share
\(\le s^*(y)\) for \(\approx 1.6\,O^*(y)=2\)–\(10\ln y\) steps: a
single-orbit parity statement at depth \(\asymp\ln y\), exponentially
deeper than the depth-\(\log\log y\) wall of the Tao reduction, on
exactly the pointwise object averages are silent about. The evidence
(seven high-flyers \(28\)–\(650\times\) above the gate) says the
statement is true; the method is not in the laboratory. Not opened.

**Observation 14 (the band word is forced; EXACT — LEAN VERIFIED).**
Inside the band the letter has no freedom: from \(u<1\) the even step
goes negative, so the letter is odd; from \(u\ge 1\) the odd step
exceeds \(1+\alpha\), so the letter is even (`band_step_forced_odd`,
`band_step_forced_even`, `band_successor_unique`). A band-confined walk
is therefore the lift of the rotation by \(\alpha\), and its parity word
is the mechanical word of that rotation — the hug itinerary — fixed by
the starting walk alone.

**Consequence 15 (residence is prefix realization; REPARAMETERIZATION
`J-hug-band-residence-is-prefix-realization`).** Hence staying in the
band for \(L\) steps *is* realizing one specific prefix of length \(L\),
which is the closed branch
[hug prefix realization](juggler_hug_prefix_realization.md): the
extremal hug cylinder tracks \(2^{-L}\) on \([3,2\cdot 10^8]\) with fill
to depth \(28\), and \(\log_2(2\cdot 10^8)=27.6\). Band residence is
exactly the fair-coin maximum \(\log_2 N\) over \(N\) starts — no
anomaly. The pigeonhole bound of Obstruction 13 (\(n^3\approx
4\cdot 10^{25}\)) is off by the whole scale: reality is \(\approx 28\).
My "best next question" of the previous phase was therefore not a new
question. Do not reopen it as a branch.

## Interaction with the fates and with termination

**One visibility law for the three Moirai.** For a backward-closed
class with seed set \(S_0\) (its minimal elements), the \(E\)-visible
natural density on the dyadic block at scale \(y\) is
\[
\delta_E(y)\ \approx\ \frac{K}{\ln y}\sum_{x\in S_0,\ \text{landing}}\frac1x,\qquad K\in[1,2],
\]
by Observations 3 and 8 and the rotation of Proposition 1. The three
fates differ only in \(S_0\):

| fate | \(S_0\) | how it fills the clock circle | \(\sum 1/x\) | \(\delta_E\) at \(10^{68}\) |
|---|---|---|---|---|
| Atropos | the interval \([1,N_0]\) | continuously; bursts tile | \(\approx\ln N_0=19.7\) | \(\approx 0.06\) (contagion note §5.3, \(\log N_0/(2\log y)\), recovered) |
| Lachesis | the cycle \(C\) | rotation orbit, \(o\ge 492276\) points, gaps \(5\cdot 10^{-6}\) | \([\theta(L)\ln n,\ L/n]=[6.8\cdot 10^{-5},2.2\cdot 10^{-3}]\) (Lean finance) | \([4\cdot 10^{-7},4\cdot 10^{-5}]\), \(y\ge n^{2^{1+u_{\max}}}\) |
| Clotho | orbit states below \(y\) | rotation orbit of length \(O(y)\), gated by \(O(y)\ge O^*(y)\) | \(\ge 1/n\), unpinned | every-block only under slow escape |

So the certified floor's own \(E\)-forest is \(10^4\)–\(10^5\) times
more visible than any finance-surviving cycle at every block — the
quantitative reason the census sees \(R\) and nothing else, and why a
census can never be the instrument (Refutation 5). The interval seed
needs no rotation; the cycle seed needs Proposition 1; the escape seed
needs Proposition 1 *and* slow escape, which is neither forced nor
observed (Refutation 12).

**The floor stratifies \(F\) by parity, at every depth (EXACT — LEAN
VERIFIED, `not_reachesOne_even_chain_ge`).** A failure whose first
\(k\) states are even is \(\ge 261^{2^k}\) at the Lean floor, and
\(\ge(N_0+1)^{2^k}\) at the certified floor: \(F\) is purely odd on
\((N_0,(N_0+1)^2)\), its \(E^k\)-cylinder is empty below
\((N_0+1)^{2^k}\). This is the depth-\(k\) form of the fate note's
"\(\min F\) is an \(OO\)-start", and it is the burst interval of
Observation 3 read from the floor upward: the even members of any
fate class arrive in bursts whose scales are the iterated squares of
the floor and of the class's odd members.

**The termination reductions.**

- *Contagion (Theorem 1).* Its mechanism — even blocks are intervals,
  \(OE\) fibers — is the \(E\)-burst and the \(\beta\)-translation of
  this branch; its log-count growth \((\log x)^{0.448}\) comes from
  the \(OE\) steps reaching *new scales*, which the block density
  never sees (Consequence 7). The two are not in tension: contagion
  integrates over scales, this branch fixes one.
- *The exact map and the free term.* Everything here bounds fate
  classes from below. The upper bound is \(\psi_F\), and \(\psi_F\) is
  the pressure hypothesis (Proposition 10). Nothing in this branch
  moves the pressure form; the firewall is crossed from below only.
- *The Tao depth.* Survivors at depth \(d\) have odd share \(\approx
  q^*\) whatever the selector (the first turn's redundancy); a
  persistent slow escaper sits at share in \((q^*,q^*+0.004)\) — on
  the pressure threshold, from above. A single thread is measure zero
  there; a cloud would contradict the census's tilted share \(0.50\).
  The gate therefore places any every-block Clotho basin exactly on
  the boundary the pressure hypothesis draws, and nowhere else.
- *What a cycle would cost the conjecture.* Corollary 4.5 says the
  conjecture is failure log-count \(o((\log x)^\lambda)\). A cycle
  would give failure density \(\ge c/\ln y\) on every block above
  \(n^{2^{1+u_{\max}}}\), hence log-count \(\gg\ln\ln x\) from the
  \(E\)-forest alone — far weaker than Theorem 1's
  \((\log x)^{0.448}\), as it must be, but pinned to Paper A's
  \(\theta(L)\ln n\) rather than to an unnamed constant.

**Termination itself.** Every statement of this branch is conditional
on \(F\ne\emptyset\) and describes what \(F\) would look like: not
lacunary above \(n^{2^{1+u_{\max}}}\) for a cycle, gated for an
escape, parity-stratified by the floor below \(N_0^2\), and invisible
to any census the floor does not already dominate. None excludes
\(F\). What the branch adds to the conjecture side is negative and
precise: the natural instrument is dominated, and the rate that would
make escape basins lacunary is a single-orbit statement at depth
\(\ln y\).

## Open questions (continued)

None owned by this branch. What is missing is still a *rate* — an upper
bound on \(O(y)\), not a bound on band residence — and Obstruction 13
records why the laboratory cannot supply one.

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

Slow escape is not forced and not observed (Refutation 12); a rate
that would settle the Clotho side is behind the wall (Obstruction 13).
The exact layer — Proposition 1 and the burst interval — is now Lean.

The residence question is answered and was not new (Consequence 15).
The branch owns no open question: its exact layer is Lean, its
quantitative layer is measured, its one operational proposal is
refuted, and the object it would need — a rate on escape speed — is
recorded as out of reach with the reason.

Best next question: none from this branch. The nearest live target is
the laboratory's existing one, unchanged by this work: the pressure
form `J-tao-pressure-form`.

## Publication assessment

Status: `STRUCTURAL`. Proposition 1 is exact but elementary;
Consequence 4 is the paper-relevant statement and is a conjecture whose
proof would be a paragraph in the contagion note, not a manuscript. Not
a `PAPER_CANDIDATE`.

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
| A Lachesis basin is not lacunary; density \(\gtrsim 1/n\) on every block | **CONJECTURE** |
| The deep natural-density census is dominated by a floor raise | **REFUTED** |

## Open questions

Consequence 4 pins only the cycle-states' own contribution, uniformly at
\(1/n\). Corollary 4.3's amplified density
\(\gg(\log y)^{\lambda-1}\) — about \(6\%\) at \(y=10^{68}\) — comes
from the full backward closure and sits on blocks this branch does not
locate. Whether the same rotation fixes those blocks, or only the
\(1/n\) floor, is the one open question.

## Decision

`PARK`. The bridge is exact, cheap, and previously unmade: it fills the
third case of contagion note §5.3 and gives the Lachesis class an
every-block density statement instead of an infinitely-often one. But
both ingredients are existing laboratory machinery, and the single
operational consequence — a deep natural-density census — is strictly
dominated by the floor campaign already parked at \(5.54\cdot 10^8\).
Nothing here excludes a fate or moves a period bound. Recording it and
stopping.

Best next question: does the rotation also fix which dyadic blocks
carry Corollary 4.3's amplified density \(\gg(\log y)^{\lambda-1}\), or
only the \(1/n\) cycle-state floor?

## Publication assessment

Status: `STRUCTURAL`. Proposition 1 is exact but elementary;
Consequence 4 is the paper-relevant statement and is a conjecture whose
proof would be a paragraph in the contagion note, not a manuscript. Not
a `PAPER_CANDIDATE`.

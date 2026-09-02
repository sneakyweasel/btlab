# Juggler walk-excursion structure

Status: **ACTIVE** (Phase 0 decided)

Refinement of the coupled walk charge
([juggler_cycle_walk_charge.md](juggler_cycle_walk_charge.md)).
Not a halt theorem, not a floor raise, not a uniform \(B/\theta\)
claim, and not a reopen of the closed Christoffel leftover-cell
slogan.

## Problem

The walk DP prices every nonnegative closed exponent walk. After
it killed \(L=50508\), the question is whether its maximizer is an
arbitrary huge computation or a continued-fraction excursion
problem for \(\alpha=\log_2(3/2)\). Does every maximizer split into
near-return blocks whose types are semi-convergents of \(\alpha\),
and does that explain the already-observed uniform charge-per-letter?

## Exact statement

**Near-return cut (definition).** Exact returns \(u_k=0\) at
\(k>0\) force \(3^a=2^k\), which is impossible. A primitive block
is a first descent back into the band \([0,1)\) after leaving it.
The walk cannot take \(E\) in that band.

**Maximizers are CF excursions (COMPUTATIONALLY VERIFIED).**
Every feasible walk-DP maximizer with \(L\le 24\), and the
leftover maximizers at \(L=19,84,1054\), splits into primitive
blocks of types \((2,1)\) and \((1,1)\) only. Both are
semi-convergents of \(\alpha\). No non-CF primitive appeared.
The bunched long types \(O^{12}E^7\), \(O^{29}E^{17}\),
\(O^{41}E^{24}\), \(O^{53}E^{31}\) are legal near-returns and
semi-convergents, but they are not maximizers: charge is decreasing
in \(u\), so the optimizer hugs the floor.

**Leftover maximizer is the Christoffel word
(COMPUTATIONALLY VERIFIED).** The reconstructed maximizer at
\((19,12)\), \((84,53)\), and \((1054,665)\) equals the ceiling
Christoffel word of slope \(o/L\) already computed in
[juggler_cycle_christoffel.md](juggler_cycle_christoffel.md).
This is a statement about the *charge relaxation*, not about
realized cycle itineraries. The one-parameter leftover-cell slogan stays
**REFUTED**.

**Charge-per-letter is uniform (COMPUTATIONALLY VERIFIED).**
On the committed 19-row walk-charge survey at floor \(26254995\),

\[
\frac{B(L,n)}{L/(n\ln n)}=C
\]

with \(C\in[0.04799,0.04809]\), relative \(B/L\) spread
\(2.21\cdot 10^{-3}\). The density is the hugging mix of
\(\mathtt{OOE}\) and \(\mathtt{OE}\), not one cheap valley per 19
letters.

**Uniform ratio \(B/\theta<1\) at a fixed floor is false
(COMPUTATIONALLY VERIFIED; same shape as the Baker dominance).**
Kill margin is \(\theta/(1.2 B)\). \(B/L\) is constant while
\(\theta/L\) tracks Diophantine quality, so \(L=176251\) has
margin \(0.159\) at the same floor that kills \(50508\) with
margin \(1.120\). Improving the parity constant from one valley
per \(\sim 2.7\) letters to one per \(\sim 3\) does not change the
Baker slogan: along convergents of \(\log 2/\log 3\), \(n_{\max}\)
grows without bound. Do not reopen
`juggler_baker_kills_near_convergents`.

No cycle of any length — not claimed.

## Current literature

- Coupled walk charge, transport lemma, certified survey —
  **EXACT — HUMAN PROOF** / **COMPUTATIONALLY VERIFIED**
  ([juggler_cycle_walk_charge.md](juggler_cycle_walk_charge.md))
- Valley-coupling circuit table
  \((12,7),(29,17),(41,24),(53,31)\) —
  **CLOSE**
  ([juggler_cycle_valley_coupling.md](juggler_cycle_valley_coupling.md))
- Two-type cheap cap; interleaved \(\mathtt{OOE}/\mathtt{OE}\) is
  CycleMin-illegal —
  **EXACT — HUMAN PROOF**
  ([juggler_cycle_cyclic_valley.md](juggler_cycle_cyclic_valley.md)).
  The DP admits those itineraries because it is a \(u\ge 0\) relaxation
- Christoffel leftover-cell reduction —
  **REFUTED** (`juggler_christoffel_one_parameter`)
- Beatty identification of leftover \(L\) —
  **KNOWN**
- Baker/Rhin transfer —
  **REFUTED** (`juggler_baker_kills_near_convergents`)
- Survivor lattice —
  **COMPUTATIONALLY VERIFIED**
  (`RunSurvivorLattice.lean`)
- Every start reaches 1 — not claimed

Project relationship: **extended** (structure of the already
certified walk DP; not a new finance identity).

## Branch budget

```text
Mathematical target     Is every walk-DP maximizer a concatenation
                        of near-return blocks whose (odd, even)
                        types are semi-convergents of α = log2(3/2),
                        and does that explain the already-observed
                        uniform charge-per-letter?
Novelty hypothesis      The DP is optimal control of a reflected
                        irrational walk. That is not the CLOSED
                        Christoffel leftover-cell slogan (realized
                        words need not be c_L) and not a floor raise.
Falsifier               A feasible maximizer whose primitive
                        near-return types are not semi-convergents
                        of α; or charge-per-letter not constant
                        once leftover-height carry is accounted for.
Existing machinery      walk_budget / deficit_D; survey.json;
                        Christoffel CF table; valley-coupling
                        (12,7),(29,17),(41,24),(53,31);
                        RunSurvivorLattice basis
Maximum Phase-0 scope   Path reconstruction + near-return split on
                        small L and on CF lengths 19, 84, 1054;
                        B/L table from the committed survey; no
                        Lean, no Paper A, no N0 raise, no new
                        leftover DP, no knapsack over the lattice
Promotion criterion     Maximizers match the CF-excursion family
                        and B/L is explained by that density
Stop criterion          A non-CF maximizer; or the statement is
                        KNOWN Beatty / CLOSED Christoffel under
                        a change of language
```

## Balanced-ternary formulation

None required. The walk lives on the exponent lattice
\(\mu a-b\); the map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Semi-convergents of \(\alpha=\log_2(3/2)\) as \((a,r)\) —
  **KNOWN** (continued fractions)
- Near-return cut at the band \([0,1)\) —
  **COMPUTATIONALLY VERIFIED** (matches \(\mathtt{OOE}\) as the
  first closed block)
- Walk-DP maximizer at leftover \((L,o_{\min})\) equals the
  Christoffel word of slope \(o/L\) —
  **COMPUTATIONALLY VERIFIED** on \(L=19,84,1054\)
- Survey charge density \(C\approx 0.04805\) —
  **COMPUTATIONALLY VERIFIED**
- Uniform \(B/\theta<1\) at fixed \(N_0\) —
  **REFUTED** by the committed survey row \(L=176251\)
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_walk_excursion`
- Artifacts: `data/research/juggler/cycle_walk_excursion/summary.json`
- Tests: `tests/research/juggler_sequence/test_cycle_walk_excursion.py`

No CLI. No new Lean. Paper A is unchanged. The certified
walk-charge DP is not edited.

## Conjectures

`juggler_walk_excursion_optimum`: every walk-DP maximizer with
nonnegative closed surplus is a concatenation of
semi-convergents of \(\alpha\), and at leftover \((L,o_{\min})\)
it is the Christoffel word of slope \(o/L\) — **ACTIVE**. Phase 0
supports it on \(L\le 24\) and on \(19,84,1054\). The human
density bound is the remaining statement.

## Counterexamples

None against the excursion-optimum claim. The uniform-ratio dream
\(B\le(1-\varepsilon)\frac56\theta\) at a fixed floor is
counterexampled by the committed survey row \(L=176251\)
(margin \(0.159\)).

## Formalization

None. `cycle_walk_charge.py` is unchanged. No
`WalkExcursion.lean`, no `sorry`. Paper A is unchanged. Not a
halt theorem.

## Results

Classification **WALK_EXCURSION_GREEN**.

- Census: \(123/123\) feasible maximizers with \(L\le 24\) are
  CF concatenations; zero non-CF witnesses
- \(L=19\): word `OOEOOEOOEOEOOEOOEOE` equals \(c_{19}\); types
  \(5\times(2,1)+2\times(1,1)\)
- \(L=84\): equals \(c_{84}\); \(22\times(2,1)+9\times(1,1)\)
- \(L=1054\): equals \(c_{1054}\); \(276\times(2,1)+113\times(1,1)\)
- Survey \(C_{\mathrm{median}}=0.04805\), relative \(B/L\) spread
  \(2.21\cdot 10^{-3}\)
- Uniform \(B/\theta\) at floor \(26254995\) is already false

## Open questions

A human proof that the Christoffel / hugging word of slope
\(o/L\) attains the walk DP, together with an explicit
\(C_*\) such that \(B\le C_* L/(n'\ln n')\). That is the next
question, not this phase. Do not raise \(N_0\), do not run a
lattice knapsack, and do not claim a uniform \(B/\theta\) gap.

## Decision

**PROMOTE.** Phase-0 maximizers are CF-excursion concatenations —
in fact the two smallest types, and on leftover lengths the
Christoffel word itself — and the survey \(C\approx 0.048\) is
that hugging density. This is not the closed leftover-cell slogan
and not a reparameterization of Beatty alone: it identifies the
adversary of the certified walk charge. The uniform-ratio dream
at a fixed floor is recorded as false and is not promoted.

Best next question: can one prove that the mechanical word of
slope \(o/L\) maximises the walk charge and satisfies
\(B\le C_* L/(n'\ln n')\) for an explicit \(C_*\)?

## Publication assessment

Status: `STRUCTURAL`.

A laboratory identification of the walk-charge adversary. It
collapses the exponential DP to one mechanical word on leftover
lengths, and it kills the uniform \(B/\theta\) programme at fixed
\(N_0\). Not a paper candidate until the density bound is a
human proof. Not a halt theorem.

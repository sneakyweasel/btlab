# Juggler fan multi-point Diophantine constraints (Attack A)

Status: **ARCHIVED** (Phase 0 decided)

Successor of the fan-minimum reduction
([juggler_cycle_walk_fan_minimum.md](juggler_cycle_walk_fan_minimum.md)).
The \(2^p\) versus \(3^q\) literature gives neighbor-separation and
polynomial gap floors, but those fire only if one CycleMin cycle
forces two distinct fan-quality \((L,o)\) relations at once. This
branch asks whether CycleMin / hug / \(m\)-circuit geometry actually
forces that. Not a Baker-constant import (that transfer stays
REFUTED), not a halt theorem, not a floor raise, and not a Paper A
edit.

## Problem

A huge partial quotient of \(\log 2/\log 3\) creates a *fan* of
semiconvergents \(L_k=q+kQ\), and the walk-finance required
improvement can fall to \(R_{\min}\approx e^{4/(a+2)}\). Baker-type
lower bounds cannot prevent that. Does a genuine Juggler cycle
require several related logarithmic approximations simultaneously,
so that the classical separation of neighboring powers of \(2\) and
\(3\) can kill the fan without bounding the partial quotients?

## Exact statement

Distinguish two neighbor relations.

**Exponent-neighbors (KNOWN, literature).** If \(2^L\) is
unusually close to a \(3\)-power, then \(2^{L\pm 1}\) sits in the
middle of the neighboring \(3\)-powers
(`mathoverflow-2012-powers-2-3`, `tao-2011-hilbert-seventh-powers-2-3`).
On leftover-quality lengths this is quantitative: at \(L=50508\),
\(\theta(L+1)/\theta(L)\approx 4.59\cdot 10^4\); at \(L=176251\),
\(\approx 9.26\cdot 10^4\). All nine leftover-quality competition
rows have neighbor ratio \(\ge 4.59\cdot 10^4\).

**Fan-neighbors (PROJECT-SPECIFIC, already the fan obstruction).**
Consecutive semiconvergents \(L_k,L_{k+1}=L_k+Q\) can both be
Dirichlet-good (\(\theta L=O(1)\)). Fan A first pair
\(176251,478245\) has \(\theta\)-ratio \(0.982\); fan B all four
pairs have ratio in \([0.222,0.767]\). This is *not* the
exponent-shift geometry, and it does not yield a contradiction.

**No forced second fan-quality return (COMPUTATIONALLY VERIFIED).**
The cheapest walk (hug / IET) on leftover seeds
\(19,84,1054,25781,50508,176251\) factors as \(\mathtt{OE}\) and
\(\mathtt{OOE}\) only. Those circuits have \(\theta\in\{5/9,1/9\}\),
not fan quality. CycleMin integer return \(T^\ell(n)=n\) is forced
only at \(\ell=L\), not at a parent length \(q\) or \(Q\). The
parent step \(Q\) is a wrong-side convergent (\(\theta(Q)\approx 2/3\)).

**Arithmetic splits are lattice identities, not returns
(COMPUTATIONALLY VERIFIED).** Among the quality set of \(88\)
lengths there are \(88\) sums \(L=a+b\) with both parts in the set,
five of them with two Dirichlet-good parts (all of the form
\(1054+\)seed or \(25781+25781\)). Equal valleys at the same \(n\)
are already REFUTED
([juggler_cycle_equal_valleys.md](juggler_cycle_equal_valleys.md)).
The hug itinerary does not use those parts as returning circuits.

**Slogan.** A CycleMin cycle of fan-member length forces two or
more distinct fan-quality \((L,o)\) relations simultaneously —
**REFUTED**.

No cycle of any length — not claimed.

## Current literature

Stored under `literature/`. Project relationship in parentheses.

- Wu–Wang linear-independence measure of \(1,\log 2,\log 3\),
  \(\mu(\log 3)\le 5.1163051\) — **known**
  (`wu-wang-2014-irrationality-measure-log3`). Implies
  \(a_{j+1}\lesssim q_j^{3.1163+\varepsilon}\), not \(a_{j+1}=O(1)\).
  Does not kill fans. Attack C is the fan-growth quantification
  ([juggler_cycle_walk_fan_growth.md](juggler_cycle_walk_fan_growth.md)).
- Salikhov \(\mu(\ln 3)\le 5.125\) — **known**
  (`salikhov-2007-irrationality-measure-ln3`).
- Rhin effective measure, later improved by the two records above
  — **known** (`rhin-1987-pade-irrationality`). Already the
  constant of the REFUTED Baker transfer.
- Laurent–Mignotte–Nesterenko two-logarithms — **known**
  (`laurent-mignotte-nesterenko-1995-two-logarithms`).
- Tao exposition of Baker \(\Rightarrow\)
  \(|3^p-2^q|\ge(c/q^C)3^p\) — **known**
  (`tao-2011-hilbert-seventh-powers-2-3`). Polynomial normalized
  gap; survivors sit closer than this floor.
- Neighbor-separation of powers of \(2\) and \(3\) (exponent shift
  by one) — **known** (`mathoverflow-2012-powers-2-3`).
- Chim explicit two \(p\)-adic logarithms — **known**
  (`chim-2025-p-adic-two-logarithms`). Attack B is the
  archimedean / \(p\)-adic coupling
  ([juggler_cycle_padic_coupling.md](juggler_cycle_padic_coupling.md)),
  now CLOSE.
- Simons–de Weger Collatz \(m\)-cycle financing — **known**
  (`simons-de-weger-2005-collatz-m-cycles`); the Baker half stays
  REFUTED for Juggler
  ([juggler_cycle_gap_baker.md](juggler_cycle_gap_baker.md)).
- Fan-minimum law \(R_{\min}\approx e^{4/(a+2)}\) — laboratory
  **COMPUTATIONALLY VERIFIED**
  ([juggler_cycle_walk_fan_minimum.md](juggler_cycle_walk_fan_minimum.md)).
- Walk-excursion hug types \((2,1)\) and \((1,1)\) — laboratory
  **COMPUTATIONALLY VERIFIED**
  ([juggler_cycle_walk_excursion.md](juggler_cycle_walk_excursion.md)).
- Equal valleys leftover-killer — **REFUTED**
  ([juggler_cycle_equal_valleys.md](juggler_cycle_equal_valleys.md)).
- Every start reaches 1 — not claimed.

Project relationship: **refuted** as a slogan that one cycle forces
two incompatible fan-quality approximations. The cited bounds
themselves remain **known**.

## Branch budget

```text
Mathematical target     Does a CycleMin cycle whose length is a fan
                        member force two or more distinct fan-quality
                        logarithmic approximations simultaneously?
Novelty hypothesis      Neighbor-separation of powers of 2 and 3 can
                        kill a fan if one cycle needs two incompatible
                        (L, o) pairs
Falsifier               Every exact cycle constraint reduces to one
                        (L, o); hug circuits are only OE/OOE;
                        fan-neighbors are Q-steps (both can be good),
                        not exponent-neighbors
Existing machinery      Competition exact thetas; hug itinerary;
                        walk-excursion types; m-finance / equal
                        valleys; Baker transfer REFUTED
Maximum Phase-0 scope   Neighbor-quality profile, hug-circuit census,
                        parent/leftover splits, L vs L+1 comparison;
                        literature records. No Baker import, no Lean,
                        no floor raise
Promotion criterion     A forced second fan-quality pair incompatible
                        with neighbor-separation
Stop criterion          No forced second pair, or the pairs are known
                        short Beatty letters / non-returning
                        concatenations
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Exponent-neighbor ratio \(\theta(L\pm 1)/\theta(L)\) on leftover
  quality — **KNOWN** (literature) plus
  **COMPUTATIONALLY VERIFIED** instances
- Fan-neighbor \(\theta\)-ratio along \(L_k=q+kQ\) —
  **COMPUTATIONALLY VERIFIED**; both sides can be Dirichlet-good
- Hug circuit type set \(\{(\mathtt{OE},\mathtt{OOE})\}\) on leftover
  seeds through \(176251\) — **COMPUTATIONALLY VERIFIED**
- Forced second fan-quality \((L,o)\) pair — **REFUTED**
- Wu–Wang bound as a leftover killer — not tested; Baker-type
  imports stay REFUTED
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_fan_multipoint`
- Artifacts: `data/research/juggler/cycle_fan_multipoint/summary.json`
- Tests: `tests/research/juggler_sequence/test_cycle_fan_multipoint.py`

No CLI, no Lean, no new big-int certification, no floor work.

## Conjectures

`juggler_fan_multipoint_constraints` — **REFUTED**. A CycleMin
cycle of fan-member length forces two or more distinct fan-quality
logarithmic relations simultaneously, so that
exponent-neighbor separation kills the fan.

## Counterexamples

- Hug itineraries of \(19,84,1054,25781,50508,176251\) have only circuit
  types \((1,1)\) and \((2,1)\). Letter counts match:
  \(5415\cdot 2+13226\cdot 3=50508\).
- At leftover seeds, \(\theta(L\pm 1)\) is \(O(1)\) while
  \(\theta(L)\sim 1/L\); the cycle does not constrain the neighbor.
- Fan A pair \(176251,478245\): \(\theta\)-ratio \(0.982\), both
  Dirichlet-good — Q-step neighbors are not exponent-neighbors.
- Two-good arithmetic split \(1054+50508=51562\) is a lattice
  identity; hug(\(51562\)) is still only \(\mathtt{OE}/\mathtt{OOE}\).
  The double \(25781+25781\) is archived equal-valleys.

## Formalization

None. No `FanMultipoint.lean`, no `sorry`. Paper A is unchanged.
Not a halt theorem. No ledger row: the positive identities are
archived walk-excursion / equal-valleys / CF geometry.

## Results

Classification **FAN_MULTIPOINT_CLOSED**.

- Hug circuits only \(\mathtt{OE}/\mathtt{OOE}\) on six leftover
  seeds through \(176251\)
- Exponent-neighbors on leftover-quality rows: min ratio
  \(4.59\cdot 10^4\) (at \(50508\))
- Fan-neighbors: \(\theta\)-ratios in \((0.22,0.98]\); both sides
  can be Dirichlet-good
- \(88\) leftover sums, five two-good, none a forced return
- Parent step \(Q\) has \(\theta\approx 2/3\) (wrong-side
  convergent), not a cheap circuit
- Attacks B (p-adic coupling) and C (Wu–Wang fan growth)
  were recorded here and are now decided elsewhere

## Open questions

None on this slogan. Do not reopen Baker / Rhin as a leftover
killer, and do not import a better irrationality measure to beat
the lattice. Attack B is CLOSE
([juggler_cycle_padic_coupling.md](juggler_cycle_padic_coupling.md));
Attack C is PROMOTE
([juggler_cycle_walk_fan_growth.md](juggler_cycle_walk_fan_growth.md)).

## Decision

**CLOSE.** The Phase-0 falsifier fired: the cheapest CycleMin walk
imposes one global \((L,o)\) pair plus many short Beatty circuits,
not two incompatible fan-quality approximations. The literature's
exponent-shift separation is real and strong on leftover seeds, but
a cycle of length \(L\) does not need \(\theta(L\pm 1)\) small.
Fan-neighbors are a different geometry and are the already-named
obstruction \(R_{\min}\approx e^{4/(a+2)}\). Arithmetic two-good
splits are lattice identities, not second returns.

Best next question: none from multi-point constraints; Attack B
is CLOSE and Attack C is the quantitative fan-width bound.

## Publication assessment

Status: `ARCHIVED`.

A finite elimination of the multi-point slogan, together with a
stored literature digest that separates exponent-neighbors from
fan-neighbors and records why stronger Baker constants cannot kill
survivor fans. Not a paper candidate and not a halt theorem.

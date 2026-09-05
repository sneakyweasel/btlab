# Geometric \(\{(3/2)^n\}\) versus the Juggler laboratory (placement)

Status: **CLOSE** (classical OPEN; three different \(3/2\) objects;
no lab layer transfers; flavor-adjacent only)

Whether the sequence \(\{(3/2)^n\}\) is uniformly distributed in
\([0,1]\) is a named open problem since Vijayaraghavan (1940). It
shares constants and a Mahler-style digit flavor with Juggler, not
theorems. This record places the question relative to the proved
layers and refuses a wrap. Not a halt theorem, not a density
theorem, not a Paper A or Paper B edit, and not a reopen of the
odd-tower fragment, the Baker cycle transfer, or the floor-Hardy
door.

## Problem

Does any laboratory layer constrain the uniform distribution (or
even the density) of \(\{(3/2)^n\}\) in the unit interval, or is
the problem an imported classical question with no Juggler door?

## Exact statement

Write \(\{x\}=x-\lfloor x\rfloor\). Let
\[
a_n=\Bigl\{\Bigl(\tfrac32\Bigr)^n\Bigr\}
=\frac{3^n\bmod 2^n}{2^n},\qquad n=1,2,3,\dots.
\]
Weyl's criterion says \(\{a_n\}\) is uniformly distributed in
\([0,1]\) if and only if
\(\frac1N\sum_{n\le N}e\bigl(h(3/2)^n\bigr)\to 0\) for every
integer \(h\neq 0\). Questions: (a) does a proved Juggler layer
give any new constraint on \(\{a_n\}\) (oscillation, density, or
those Weyl sums); (b) is a transfer from Paper B, walk charge,
Baker/Rhin, fate/Tao, or Collatz base-\(3/2\) numeration a door?

## Current literature

Classical status, all **KNOWN** (no lab proof claimed):

- Infinitely many limit points — Vijayaraghavan 1940
  (`vijayaraghavan-1940-fractional-parts-powers`); also Pisot
  1938 for a wider algebraic class.
- Oscillation \(\limsup a_n-\liminf a_n\ge 1/3\) —
  Flatto–Lagarias–Pollington 1995
  (`flatto-lagarias-pollington-1995-range-fractional-parts`);
  in general \(\Omega(p/q)>1/p\).
- Metric almost-all: \(\{\alpha^n\}\) is uniformly distributed for
  almost every \(\alpha>1\) (Koksma; packaged in
  `kuipers-niederreiter-1974-uniform-distribution`). Integers and
  Pisot numbers are exceptional (\(\{\alpha^n\}\to 0\)). The
  rational \(3/2\) is not a Pisot number, so it is a candidate,
  not a counterexample.
- **OPEN:** oscillation \(>1/2\) (Vijayaraghavan's question);
  infinitely many limit points in both \([0,1/2)\) and
  \([1/2,1)\); density in \([0,1]\); uniform distribution.
- **OPEN, adjacent:** Mahler's \(Z\)-numbers (1968,
  `mahler-1968-powers-of-3-2`) — no \(\xi>0\) with
  \(\{\xi(3/2)^n\}<1/2\) for all \(n\). Distinct from
  \(\xi=1\).
- Computational, not a proof: discrepancy censuses to
  \(n\le 10^8\) are consistent with uniformity; Waring's
  inequality \(a_n\le 1-(3/4)^n\) is verified to
  \(n\le 4.7\cdot 10^8\). Finite checks are not theorems.

Laboratory neighbors (already decided; not re-tested):

- Odd-tower fragment — **CLOSE**
  ([juggler_odd_tower_fragment](juggler_odd_tower_fragment.md)):
  Mahler *flavor* only; no transfer in either direction.
- Baker/Rhin on \(\lvert 3^o-2^L\rvert\) — **REFUTED** as a
  cycle killer
  ([juggler_cycle_gap_baker](juggler_cycle_gap_baker.md)).
- Paper B nested \(\lfloor n^{3/2}\rfloor\) parity — **EXACT —
  HUMAN PROOF** at depths \(\le 4\); polynomial-floor phases,
  not \(e(h(3/2)^n)\).
- Walk charge / Ostrowski — rotation by
  \(\log_2(3/2)\) and \(\log(3/2)/\log 3\); linear
  \(\{k\alpha\}\), not \(\{\alpha^n\}\).
- Collatz rational-base \(3/2\) numeration
  (`src/research/collatz/rational_base.py`) — a representation
  gadget, not this sequence.
- External leftover pattern
  ([exponent_pair_two_monomial](../theory/exponent_pair_two_monomial.md))
  — for leftovers *born from* Juggler; this problem is imported.

Project relationship: **independent** (placement of an external
question; no new mathematics).

## Branch budget

- **Target:** is \(\{(3/2)^n\}\) uniformly distributed in
  \([0,1]\), and does any lab layer constrain it?
- **Novelty hypothesis:** a Juggler theorem or probe yields a
  new constraint (oscillation, density, or Weyl sums).
- **Falsifier:** every candidate layer is linear-rotation,
  polynomial-floor, or an already-closed transfer.
- **Existing machinery:** walk charge / Ostrowski; Paper B;
  Baker/Rhin (REFUTED for cycles); Collatz \(3/2\)-numeration;
  odd-tower CLOSE.
- **Maximum Phase-0 scope:** literature check plus placement
  analysis; dossier, journal, and negative-knowledge line only.
  No probe, no Lean, no `research/three_halves/`.
- **Promotion criterion:** a statement about \(\{(3/2)^n\}\)
  that is not `KNOWN` and uses a lab layer.
- **Stop criterion:** no layer applies and the problem is
  classical OPEN \(\to\) CLOSE as a Juggler branch.

## Balanced-ternary formulation

None required. The sequence is \(3^n\bmod 2^n\) on ordinary
integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Identity \(a_n=(3^n\bmod 2^n)/2^n\) — **KNOWN**
- Three-object distinction (odd-branch exponent
  \(\lfloor n^{3/2}\rfloor\); walk rotation
  \(\{k\log_2(3/2)\}\); geometric \(\{(3/2)^n\}\)) —
  **EXACT — HUMAN PROOF** (definitions)
- Paper B / van der Corput / two-monomial leftover as a Weyl
  attack on \(e(h(3/2)^n)\) — wrong exponential-sum species
  (polynomial phase versus lacunary geometric phase)
- Walk charge / Denjoy–Koksma / Ostrowski as an attack — wrong
  dynamics (isometric rotation versus expanding carry map)
- Baker/Rhin on \(\lvert o\log 3-L\log 2\rvert\) as an attack
  — wrong linear form (two-term cycle gap versus three-term
  \(\lvert n\log(3/2)-\log m\rvert\)); the two-term transfer
  is already **REFUTED**
- Fate contagion / Tao pressure — Juggler preimage geometry;
  silent on \(\{(3/2)^n\}\)
- GPU census past \(n=10^8\) — **OBSERVATION** at best, behind
  existing literature; not a theorem
- Uniform distribution, density, or \(\Omega(3/2)>1/2\) — not
  claimed

## Experiments

None. A larger discrepancy census would add no mathematical
consequence (machinery gravity; finite checks are not proofs).

## Conjectures

None opened. Uniform distribution of \(\{(3/2)^n\}\) is a
classical OPEN question and is not conjectured in
`conjectures/`.

## Counterexamples

None. Negative knowledge honored: the odd-tower Mahler-flavor
refusal, the Baker cycle transfer, the ambient-to-orbit
transfer, and the Paper A \(\times\) Paper B merge were cited,
not re-tested.

## Formalization

None. Lean-ifying Vijayaraghavan or Flatto–Lagarias–Pollington
would be a new formal area, not Juggler progress.

## Results

**Placement (answers the standing question; EXACT — HUMAN
PROOF).** (i) The laboratory's \(3/2\) is the odd-branch
exponent in \(\lfloor n^{3/2}\rfloor\) and the rotation slope
\(\log_2(3/2)\) (equivalently
\(\theta=\log(3/2)/\log 3=1-\log 2/\log 3\)). The sequence
\(\{(3/2)^n\}\) is a third object. (ii) After \(j\) odd steps a
tower state is \(\asymp n^{(3/2)^j}\); there \((3/2)^j\) is a
real growth weight, and the walk tracks
\(\{j\log_2(3/2)\}\), the logarithm of that weight. Taking
fractional parts after the exponential is the linear-versus-
geometric gap. (iii) Paper B, the two-monomial leftover, walk
charge, Baker/Rhin on cycle gaps, fate/Tao, and Collatz
base-\(3/2\) numeration each fail to apply, by index, by
dynamics, or by a recorded kill. (iv) The only in-repo Mahler
citation was already a flavor line with no transfer
([juggler_odd_tower_fragment](juggler_odd_tower_fragment.md)).
The laboratory has no machinery for \(\{(3/2)^n\}\).

No new ledger row. The identity
\(a_n=(3^n\bmod 2^n)/2^n\) is elementary and **KNOWN**.

## Open questions

- Uniform distribution of \(\{(3/2)^n\}\) — classical OPEN,
  now placed: imported, incomparable to the Juggler layers,
  beyond current lab machinery. Any future attack needs a
  genuinely new handle on lacunary geometric Weyl sums or on
  the expanding carry map, not a wrap of Paper B, walk charge,
  or Baker.
- The Juggler-native questions that only *look* nearby remain
  the existing frontier: rate-free nested floor-power
  equidistribution (`juggler_tower_rate_free_equidistribution`),
  the Paper B level-3 kernel, Tao pressure at depth
  \(\asymp\log\log y\), and the external two-monomial
  exponent-pair leftover. Those are still not
  \(\{(3/2)^n\}\).

## Decision

**CLOSE.** The stop criterion fired: every candidate layer is
linear-rotation, polynomial-floor, or an already-closed
transfer, and the problem is classical OPEN. Shared wallpaper
(the pair \((2,3)\), a Mahler-style digit flavor) is not a
theorem. Nothing here justifies a probe, a Lean module, or
`research/three_halves/`. Best next question: none on this
line. The live Juggler questions are the four named in
**Open questions**; do not open them from this record.

## Publication assessment

Status: `ARCHIVED`. A placement record with no new theorem;
not a paper candidate.

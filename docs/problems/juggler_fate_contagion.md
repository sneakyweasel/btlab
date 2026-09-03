# Juggler fate contagion: logarithmic density of the fate classes

Status: **PROMOTE** (Phase 0 decided; note written; Lean skeleton green)

The three fates of a Juggler start — reach \(1\), enter a nontrivial
cycle, escape to infinity — are the three cases through which any
termination proof would have to pass. This branch asks the
quantitative question the trichotomy leaves open: how thin can a fate
class be? Answer: not thin. Every fate that occurs at all occurs on a
set whose logarithmic counting function is \(\gg(\log x)^{\lambda}\)
for every \(\lambda<0.405\). Note:
[juggler_fate_contagion_note.md](../theory/juggler_fate_contagion_note.md).
Not a halt theorem, not a cycle exclusion, not a divergence exclusion,
not a Paper A or Paper B edit.

## Problem

Lower-bound the counting function of any nonempty backward-closed set
(\(J(n)\in A\Rightarrow n\in A\)) of Juggler starts — in particular of
\(R=\{n:\ n\ \text{reaches}\ 1\}\), of the failure set
\(F=\mathbb N\setminus R\), of the basin of any cycle, and of the set
of divergent starts.

## Exact statement

**Theorem 4.2 (EXACT — HUMAN PROOF, `J-fate-log-density`).** Let
\(\lambda^{**}=0.4050\ldots\) be the root of
\(2^{-\lambda}+\tfrac5{21}(\tfrac38)^\lambda+\tfrac2{21}(\tfrac34)^\lambda=1\).
For every nonempty backward-closed \(A\subseteq\mathbb N\) and every
\(\lambda<\lambda^{**}\) there are \(c,x_0>0\) with
\(\sum_{n\in A,\,n\le x}1/n\ge c(\log x)^\lambda\) for \(x\ge x_0\).
With only the block average (no sweep lemma) the same holds for
\(\lambda<\lambda^*=0.3774\ldots\), the root of
\(2^{-\lambda}+\tfrac13(\tfrac38)^\lambda=1\).

**Corollary 4.3.** For every \(X\ge x_0\) some \(y\in(\sqrt X,X]\) has
\(\#(A\cap(y/2,y])\ge c\,y(\log y)^{\lambda-1}\).

**Corollary 4.4 (contagion).** Each realized fate class satisfies
both. If one start fails to reach \(1\), the failures have
logarithmic count \(\gg(\log x)^{\lambda}\) and natural density
\(\gg(\log y)^{\lambda-1}\) on infinitely many dyadic blocks.

**Corollary 4.5 (equivalence).** For any \(N_0\) with
\([1,N_0]\subseteq R\): every start reaches \(1\) iff the starts whose
orbit never enters \([1,N_0]\) have logarithmic count
\(o((\log x)^{\lambda})\) for some \(\lambda<\lambda^{**}\).

Inputs: the even block \(E(m)\) (Lemma 2.1, Lean), the OE fiber
\(\Phi(m)=\{n\ \text{odd}:m^4\le n^3<(m+1)^4\}\) (Lemma 2.2, Lean), the
sweep lemma (Lemma 3.1: an increasing sequence with steps in
\([a,\tfrac{21}{20}a]\subseteq(0,\tfrac12]\) and \((H-1)a\ge 12\) puts
at least \(H/7\) points in each half of the circle), the fiber parity
lemma (Lemma 3.2: \(G_m\ge H_m/7\) on good fibers, \(m\ge 10^6\)), the
thinness of bad fibers (Lemma 3.3: \(\sum_{m\ \text{bad},\,m>U}1/m\le 306U^{-1/3}\)),
and the block average (Proposition 3.4:
\(|U(m')|=\tfrac14\#\{\text{odd}\ n\in I(m')\}+O(m'^{11/9}\log m')\) by
Vaaler, the second-derivative test, and Kusmin–Landau).

## Current literature

- Krasikov–Lagarias, Collatz preimage trees \(\gg x^{0.84}\)
  (`known`): the Collatz analogue of contagion is a power below one,
  which is why almost-all theorems do not imply Collatz. For the
  Juggler map the even preimage interval gives a log power: `extended`
  in kind, `independent` in method.
- Terras / Everett (Collatz finite stopping time, density one) and
  Tao (almost all orbits attain almost bounded values) (`known`):
  Corollary 4.5 is the statement that a Tao-type theorem with a
  bounded target and a mild rate would prove the Juggler conjecture.
- Paper B, Lemmas 3.3 and 3.5 (van der Corput second-derivative
  test, Vaaler) (`reproduced` as tools); Theorem 4.1 (depth-one
  parity, classical). Proposition 3.4 is the two-monomial variant on
  the sub-dyadic interval \(I(m')\). Paper B's short-interval wall is
  *not* hit because the recursion needs only lower bounds.
- Paper A, Lemma 1.1 / Lean `cycles_or_escapes` (`reproduced`,
  refined to `fate_trichotomy` with basins named).
- No published lower bound on the counting function of the Juggler
  starts that reach \(1\) was found (search 3 Sep 2026).

## Branch budget

```text
Mathematical target     How thin can a fate class be? Lower-bound the counting
                        function of any nonempty backward-closed set of starts.
Novelty hypothesis      Even preimages are intervals and OE-preimages are fibers of
                        floor(n^{3/4}) on which floor(n^{3/2}) sweeps mod 1, so a
                        lower-bound recursion needs only per-fiber positive
                        proportions and closes with an explicit exponent.
Falsifier               A positive-density set of fibers with vanishing proportion of
                        even floor(n^{3/2}); or block averages away from 1/4.
Existing machinery      even_preimage_iff, odd_preimage_unique, cycles_or_escapes,
                        ReachesOne, EscapesToInfinity, Ancestor; Paper B Lemmas 3.3/3.5.
Maximum Phase-0 scope   exact fiber census (m < 1e5 plus spot ranges), block census,
                        certified closure of the Lean seed [1,260] to 1e9, human proof,
                        Lean for the exact layer. No N_0 raise, no finance edit.
Promotion criterion     censuses match the lemmas; theorem proved with explicit lambda.
Stop criterion          falsifier observed, or the recursion cannot be closed.
```

## Balanced-ternary formulation

None. The objects are one-step preimage cells, fractional parts of
\(n^{3/2}/2\), and a functional inequality for the logarithmic
counting function.

## Why BT may be relevant

Not relevant here; recorded for the template.

## Candidate operations / invariants

- Backward closure of every fate class; forward closure of \(R\), \(F\),
  \(D\) — **EXACT — LEAN VERIFIED** (`J-fate-classes-backward-closed`).
- Even block \(E(m)\subseteq A\), \(|E(m)|\ge m\) — **EXACT — LEAN VERIFIED**.
- OE fiber: \(\lfloor\sqrt{\lfloor\sqrt N\rfloor}\rfloor=m\iff m^4\le N<(m+1)^4\);
  odd \(n\) in the cell with even \(\lfloor n^{3/2}\rfloor\) has
  \(J^2(n)=m\) — **EXACT — LEAN VERIFIED** (`J-fate-oe-fiber-cell`).
- Sweep lemma and fiber parity \(G_m\ge H_m/7\) on good fibers —
  **EXACT — HUMAN PROOF** (`J-fate-fiber-sweep`); census: mean
  \(0.5000\), min on good fibers \(0.328\), all sub-\(1/7\) fibers
  flagged bad — **COMPUTATIONALLY VERIFIED**.
- Block average \(\tfrac14\) with error \(m'^{11/9}\log m'\) —
  **EXACT — HUMAN PROOF** (classical tools); census deviation at
  square-root scale — **COMPUTATIONALLY VERIFIED**.
- Log-density theorem and corollaries — **EXACT — HUMAN PROOF**
  (`J-fate-log-density`, `J-fate-contagion-equivalence`).
- Certified closure of \([1,260]\) has density \(0.45\)–\(0.49\) on
  dyadic blocks to \(10^9\), recursion coefficients realised
  \(0.9998\) and \(0.3332\) — **COMPUTATIONALLY VERIFIED**.

## Experiments

- Probe: `research.juggler_sequence.fate_contagion`
  (`python -m research.juggler_sequence.fate_contagion --closure-limit 1e9`).
- Artifact: `data/research/juggler/fate_contagion/summary.json`
  (`classification`, `fiber_census`, `block_census`, `closure`,
  `lambda_roots`).
- Tests: `tests/research/juggler_sequence/test_fate_contagion.py`.

## Conjectures

None opened. The natural-density version pointwise in \(x\), and
\(\lambda\to 1\) (positive logarithmic density of \(R\)), are recorded
as out of reach in §5.2–5.3 of the note, not as conjectures.

## Counterexamples

None. The exceptional fibers (\(\alpha_m\) within \(22m^{-1/3}\) of
\(0\) or \(2m^{-1/3}\) of \(\tfrac12\)) are the predicted ones; the
worst good fiber in the census sits at \(\alpha_m\approx\tfrac13\)
with proportion \(0.328\).

## Formalization

`formal/Problems/Juggler/FateContagion.lean`: `BackwardClosed`,
`reachesOne_backwardClosed`, `not_reachesOne_backwardClosed`,
`ancestor_backwardClosed`, `escapes_backwardClosed`,
`reachesOne_floorPower`, `escapes_floorPower`, `even_block_mem`,
`even_block_card`, `sqrt_sqrt_eq_iff`, `floorPower_oe_fiber`,
`oe_fiber_mem`, `oe_fiber_disjoint`, `Periodic`, `fate_trichotomy`,
`reachesOne_not_escapes`, `cycle_basin_not_escapes`,
`reachesOne_not_cycle_basin`; odd generation (Theorem 6.1):
`ForwardClosed`, `exists_odd_ancestor`, `exists_odd_ancestor_ge_three`,
`nonempty_iff_odd_image_mem`, `odd_mem_iff`; envelope descent into
the floor: `iterate_le_of_envelope`, `mem_of_envelope_floor`,
`reachesOne_of_itinerary_envelope`. Imported by `Problems.Juggler`. No
`sorry`. The analytic counting (Lemmas 3.1–3.3, Proposition 3.4,
Theorem 4.2) is not formalized.

## Results

- Theorem 4.2, Corollaries 4.3–4.5 of the note (human proof).
- Lean exact layer as listed.
- Censuses: `FATE_CONTAGION_RECURSION_CONSISTENT`.

## Open questions

- The free term (note §6.2): the \(S\)-fairness of the failure set —
  equivalent to the conjecture. Localizing Paper B's Theorems 4.4/4.7
  to intervals of length \(\ge P^{1/2+\varepsilon}\) would add the
  \(OOEE\) production and raise \(\lambda^{**}\) to \(\approx 0.527\)
  (not verified; recorded in §6.3).
- Pointwise natural density \(\#(R\cap[1,x])\gg x(\log x)^{\lambda-1}\)
  for all \(x\): the fixed-ratio induction does not close; the E-tree
  of \([1,N_0]\) gives it for \(\log x\ll N_0\log N_0\) only.
- \(\lambda\to 1\): needs the full descent-certificate mass, i.e. an
  almost-all-descent theorem with a rate; depth five would give
  \(\approx 0.75\) heuristically (Paper B classes on sub-dyadic
  intervals).
- Whether any almost-all statement of the Corollary 4.5 (3) type is
  provable: it is the Juggler analogue of Tao's theorem with a bounded
  target. Not attempted.

## Decision

`PROMOTE`. The theorem is new for this map, elementary at depth two,
and answers a question the laboratory had always disclaimed ("not a
density of starts that reach 1"). Its consequence — the conjecture is
equivalent to an almost-all statement with a logarithmic rate — is a
genuine structural difference from Collatz and the sharpest honest
reformulation of the termination problem available here. It excludes
no fate. Best next question: is there a Juggler analogue of Tao's
almost-bounded-values theorem, in logarithmic density, with target
\([1,N_0]\) and rate \((\log x)^{-0.6}\)? That is a Paper-B-scale
program, not a Phase 0, and is not opened here.

## Publication assessment

Status: `THEOREM` (human proof with classical inputs; Lean exact
layer). A short standalone note is plausible after the constants are
tightened (\(\tfrac17\to\tfrac13\) on good fibers) and the
Proposition 3.4 constant is made explicit; not a paper claim yet.

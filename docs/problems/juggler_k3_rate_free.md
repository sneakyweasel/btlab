# Juggler K3 rate-free reduction (what density one actually needs)

Status: **PROMOTE** (two reduction lemmas recorded; the quantitative
K3/HH line stays PARKED; the rate-free tower target recorded as the
single active conjecture)

The K3 wall review's question: the BB/GG/JJ obstruction ladder blocks
every known route to the *power-savings* kernel bound
(Conjecture V / HH). Does the goal — density-one finite descent —
actually need power savings? Answer: no. Per-fixed-depth
**qualitative** equidistribution suffices, and even a node-wise
**biased split** above the contraction threshold
\(\beta_*=1-\log 2/\log 3\approx 0.36907\) suffices. The needed
input's species changes from analytic (rated) to ergodic
(rate-free), which the three obstruction layers do not formally
block. Not a K3 bound, not a density-one claim, and not a reopen of
the toolkit line.

## Problem

Weakest hypothesis under which the Juggler descent program yields
density-one finite descent, given that all rated (power-savings)
routes to the level-3 kernel are closed by named obstructions.

## Exact statement

**Lemma A (rate-free reduction; EXACT — HUMAN PROOF).** Suppose that
for **each fixed** depth \(d\), every parity class
\(w\in\{O,E\}^d\) satisfies \(\#w(N)=2^{-d}N+o(N)\) as
\(N\to\infty\) (no rate required, non-uniform in \(d\)). Then the
set of starts admitting a finite descent certificate has natural
density one.

*Proof.* Proposition J (`J-equidistribution-implies-density-one`,
Paper B Proposition 6.1) is the inequality
\[
\#\{n\le N:\ \text{no contracting prefix of length}\le d\}
\ \le\ \frac{N_d}{2^{d}}N+N_dE_d(N),
\qquad N_d\le 2^{d}e^{-cd},
\quad c=2\bigl(\tfrac{\log 2}{\log 3}-\tfrac12\bigr)^2>0.0342,
\]
where \(E_d(N)\) bounds the class-count errors at depth \(d\) and
\(N_d\) is the exact number of length-\(d\) words with no contracting
prefix --- a dynamic program over \((t,o_t)\), the closed form being
Hoeffding applied to the endpoint alone; every start whose word has an
exponent-negative prefix (\(3^{a_k}<2^k\)) descends below itself
unconditionally, because floors only lose:
\(x_k\le n^{3^{a_k}/2^k}<n\) (Lean `power_bound_word`,
`J-power-envelope-contraction`). Fix \(d\) and let \(N\to\infty\)
**first**: the hypothesis gives \(N_dE_d(N)=o(N)\) for the
\(N_d\)-term sum, so the non-certified set has upper density
\(\le N_d/2^d\), and \(\le e^{-cd}\) via the closed form. This holds
for every \(d\); let \(d\to\infty\). Carrying \(N_d\) rather than the
closed form does not change the limit --- the rates agree to one part
in eighty --- but it is what the sum actually has: \(4\) terms at
\(d=5\) rather than \(32\), and \(2114\) at \(d=16\) rather than
\(65536\). \(\square\)

**Lemma B (biased-split reduction; EXACT — HUMAN PROOF).** Full
equidistribution is not needed. Suppose for each fixed \(d\) and
every itinerary \(\sigma\) of length \(<d\),
\[
\limsup_{N\to\infty}\frac{\#(\sigma O)(N)}{\#\sigma(N)}\ \le\
1-\beta \quad\text{for some fixed }\beta>\beta_*=1-\frac{\log 2}{\log 3}.
\]
Then density-one finite descent holds.

*Proof.* Let \(\mu_N(\sigma)=\#\sigma(N)/N\) and let \(\mu\) be any
subsequential limit (exists by finiteness at each depth; the bound
passes to \(\mu(\sigma O)\le(1-\beta)\mu(\sigma)\)). For \(x\ge 1\),
induction on depth gives the generating-function domination
\[
\sum_{|\sigma|=d}\mu(\sigma)\,x^{o(\sigma)}\ \le\
\bigl(\beta+(1-\beta)x\bigr)^d ,
\]
since each node contributes
\(1+(x-1)\,\mu(\sigma O)/\mu(\sigma)\le 1+(x-1)(1-\beta)\).
Chernoff at \(\gamma=\log 2/\log 3\): the \(\mu\)-measure of
\(\{o_d\ge\gamma d\}\) — which contains every never-contracting itinerary
— is at most \(e^{-D(\gamma\,\|\,1-\beta)\,d}\), with relative
entropy \(D>0\) exactly when \(\gamma>1-\beta\), i.e.
\(\beta>\beta_*\). Certificates as in Lemma A; let \(d\to\infty\).
\(\square\)

**Target (CONJECTURE,
`juggler_tower_rate_free_equidistribution`).** For each fixed
depth, the parity classes carry their Bernoulli densities —
equivalently the floor-power tower
\((\{n^{3/2}\},\{v^{3/2}\},\{z^{3/2}\},\dots)\) equidistributes
jointly, without rate. This is strictly weaker than Conjectures K,
V, and HH.

## Current literature

Project relationship: **extended** (weakens the recorded
hypothesis of `J-equidistribution-implies-density-one`; re-aims the
parked K3 line at a rate-free target).

- Bergelson–Leibman: bounded generalized polynomials (arbitrary
  finite bracket depth, **polynomial** entries) are nilmanifold
  observables; equidistribution follows from the nil-machinery
  without Fourier-expanding the brackets.
- Frantzikinakis 2009 (*Equidistribution of sparse sequences on
  nilmanifolds*): integer-part **removal step** for Hardy-field
  functions; Richter 2022 (*Uniform distribution in nilmanifolds
  along functions from a Hardy field*); Tsinas 2023 (pointwise
  convergence along Hardy functions). Hinges for the door: Hardy
  entries and single floors are handled, **nested floor-power
  brackets are not in the published theory**.
- arXiv 2510.20562 (2025): prime counting in *twice-iterated*
  Piatetski–Shapiro sequences \(\lfloor\lfloor h^{c_1}\rfloor^{c_2}\rfloor\)
  via Kolesnik's method — classical toolkit, **small amplitudes
  only** (\(|h|<X^\delta\), exponents \(\gamma<1\)); confirms nested
  floors are an active frontier and does not touch the
  amplitude-product class.
- The wall: `J-k3-toolkit-obstruction` (BB),
  `J-intra-block-harmonic-obstruction` (GG),
  `J-derandomization-obstruction` (JJ) — all three block **rated**
  mechanisms (differencing, character windows, shift
  de-randomization). None names a rate-free ergodic obstruction.

## Branch budget

- **Target:** does density-one descent need the rated kernel bounds,
  or does a rate-free / biased fixed-depth hypothesis suffice — and
  is the rate-free tower question ergodically reachable?
- **Novelty hypothesis:** the wall blocks rates; the goal is
  monotone in depth, so rates are not needed — a permanent
  weakening of the Proposition J hypothesis.
- **Falsifier:** (a) the reduction breaks (certificates need more
  than exponent-negativity, or the limit order is illegitimate);
  (b) floor-removal self-similarity obstructs characteristic
  factors as it obstructs harmonics.
- **Existing machinery:** Proposition J's inequality,
  `power_bound_word` (Lean), the exact linearizations, the
  two-step-parity censuses, the BB/GG/JJ records.
- **Maximum Phase-0 scope:** the two lemmas checked and recorded;
  one literature check; one exact probe (never-negative DP profile,
  biased-adversary DP, dyadic tower census); records. No Paper B
  edits, no toolkit re-entry, no new Lean.
- **Promotion criterion:** the lemmas survive scrutiny and change
  the species of the needed kernel input.
- **Stop criterion:** falsifier (a) fires, or the reduction is
  already recorded → CLOSE.

## Balanced-ternary formulation

None required. The reduction lives on parity itineraries and class
densities; the tower lives on the 3-torus.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Never-negative word count \(C_d\) (exact DP over
  \((k,a)\)-states, condition \(3^{a_k}\ge 2^k\)) — the exact
  \(1-\rho_d\) profile that Proposition J's Hoeffding term
  majorizes. **COMPUTATIONALLY VERIFIED** through \(d=200\):
  \(C_{200}/2^{200}=3.06\cdot 10^{-6}\), empirical rate \(0.0635\)
  per letter vs Hoeffding \(c=0.0343\) (majorizes, as it must).
- Biased-adversary measure (O-share capped at \(1-\beta\)) — exact
  DP vs the Chernoff rate \(D(\gamma\|1-\beta)\). At
  \(\beta=0.37\) (barely supercritical) the exact measure at
  \(d=200\) is \(0.0456\), decaying at \(0.0154\) per letter while
  Chernoff is nearly vacuous (\(D=1.9\cdot 10^{-6}\)): the exact DP
  is far stronger than the bound near threshold.
  **COMPUTATIONALLY VERIFIED.**
- Exact tower binning
  \(\lfloor 8\{x^{3/2}\}\rfloor=\mathrm{isqrt}(64x^3)-8\,\mathrm{isqrt}(x^3)\)
  — integer-only. **EXACT.**
- Bracket-Hardy normal form of the tower observable (two-term
  Taylor, Paper B Lemma 7.2):
  \(\{z^{3/2}\}=\{v^{9/4}-\tfrac32 v^{3/4}\{v^{3/2}\}+o(1)\}\) —
  finite complexity; the polynomial analogue is Bergelson–Leibman.
  **OBSERVATION** (route-shaping, not a theorem here).

## Experiments

- Probe: `research.juggler_sequence.k3_rate_free`
- Artifact: `data/research/juggler/k3_rate_free/summary.json`
- Tests: `tests/research/juggler_sequence/test_k3_rate_free.py`

Science window: DP profiles to \(d=200\) (exact big-int counts);
tower census on the dyadic window \((10^6,2\cdot 10^6]\),
\(5\cdot 10^5\) odd starts, \(8^3\) joint bins, all exact. Tests use
\(d=40\) and a \(4\cdot 10^4\) window.

## Conjectures

`juggler_tower_rate_free_equidistribution` (ACTIVE): rate-free
fixed-depth equidistribution of the parity classes / the floor-power
tower. The quantitative records (Conjecture K in Paper B, Conjecture
V / HH) stay as they are, PARKED behind BB/GG/JJ.

## Counterexamples

None. The small-\(n\) contamination is a scope note, not a
counterexample: the tower census over \([5,2\cdot 10^6]\) shows a
\(6.4\sigma\) cell deviation driven by genuinely correlated small
\(n\) (equidistribution is asymptotic); on the dyadic window the
census is clean (max cell deviation \(0.145\) of expectation vs
extreme-value allowance \(0.161\); all \(512\) cells occupied;
OOOO-conditioned fifth-letter even share \(0.49835\pm 0.0060\)).

## Formalization

None new, and none needed for the claim tags: the certificate side
of both lemmas is already Lean (`power_bound_word`,
`J-power-envelope-contraction`); the measure side (limit order,
generating-function domination, Chernoff) is classical prose. The
lab's finite-itinerary Lean idiom does not cover natural-density
statements; packaging them would be machinery gravity.

## Results

Classification **K3_RATE_FREE_GREEN**.

- **Lemma A (EXACT — HUMAN PROOF, `J-rate-free-density-one`):**
  per-fixed-depth qualitative equidistribution implies density-one
  finite descent. Proposition J's inequality with \(N\to\infty\)
  taken before \(d\to\infty\); power savings is not consumed
  anywhere.
- **Lemma B (EXACT — HUMAN PROOF, same ledger row):** node-wise
  E-share \(\ge\beta>\beta_*=1-\log 2/\log 3\), rate-free, also
  suffices, by generating-function domination and Chernoff at
  \(\gamma=\log 2/\log 3\). The empirical split is \(0.5\); the
  required one is \(0.37\).
- **Species statement:** the BB/GG/JJ wall formally blocks rated
  methods only. The weakest sufficient kernel input is rate-free
  and lives in the ergodic (bracket-Hardy / nilmanifold)
  territory the toolkit never touched: brackets lift to
  nil-coordinates (Bergelson–Leibman, polynomial case), Hardy
  entries have an integer-part removal step (Frantzikinakis 2009),
  and nothing published covers the nested tower — the door is
  unbuilt, not walled.
- **Probe:** exact never-negative and biased-adversary profiles;
  dyadic tower census consistent with joint equidistribution;
  fifth-letter split \(0.49835\pm 0.0060\).

## Open questions

- The recorded falsifier for the ergodic route: does the
  floor-removal correction \(\tfrac32 v^{3/4}\{v^{3/2}\}\) re-enter
  the amplitude-product class inside any characteristic-factor
  argument (a would-be fourth layer of the wall), or does the
  nil-lift absorb it as it absorbs polynomial brackets? This is a
  literature-facing question (the Hardy-field extension of the
  Bergelson–Leibman bracket calculus) and is **not** opened as a
  laboratory branch.
- Exporting the pure amplitude-product model (Conjecture HH) as a
  standalone problem note remains the cheapest external move; the
  rate-free target gives it a second, weaker acceptable answer.

## Decision

**PROMOTE.** Two exact reduction lemmas enter the ledger
(`J-rate-free-density-one`) and permanently weaken what the K3 line
must produce: rate-free (or \(0.37\)-biased) fixed-depth statements
now suffice for density-one descent, and the three-layer wall does
not formally reach them. The quantitative K3/HH line stays PARKED;
no toolkit route is reopened; Paper B is untouched. Best next
question: does the Hardy-field bracket calculus exist — i.e. can
the nil-lift that absorbs polynomial brackets absorb
\(v^{3/4}\{v^{3/2}\}\), or does floor-removal self-similarity add a
fourth, ergodic layer to the wall?

## Publication assessment

Status: `STRUCTURAL`. The lemmas are short corollaries of recorded
results, valuable for re-aiming rather than novelty; the re-aimed
conjecture is a clean exportable question. No paper edit: Paper B is
frozen for submission, and the reduction can be cited from the
laboratory records if a revision is ever requested.

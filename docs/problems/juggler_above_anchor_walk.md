# Juggler above-anchor walk envelope (asymptotic descent, Phase-0)

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** Paper A, not a floor (\(N_0\)) campaign, not a finance reopen,
not a density census (Paper B certified density stays \(13/16\);
laboratory length-5 repair is \(7/8\)),
not a \(K_3\) attack, and not a claim that every positive integer
reaches 1. It does not reopen the parked escape-episode branch, the
closed survival-set branch, or the closed drift-first-passage branch.

## Problem

Can the Paper A §5 walk-charge layer (nonnegative exponent walk, hug
adversary, Ostrowski near-minima) constrain **open** trajectories —
hypothetical descent-free flights — rather than only hypothetical
cycles, and does the resulting slack-vs-defect ledger force eventual
descent?

## Exact statement

Write \(D(n)=\min\{k\ge 1: J^k(n)<n\}\) for the first-descent time
(the `HasFiniteStop` witness). The **Asymptotic Descent Conjecture**
(`juggler_asymptotic_descent`) is

\[
\exists N\ \forall n\ge N\ \exists k\ge 1:\ J^k(n)<n,
\]

i.e. \(D(n)<\infty\) for all large \(n\); with a finite check below
\(N\), strict integer descent and strong induction would give arrival
at \(1\) (the missing induction hypothesis of Paper A §6). The
quantitative form (`juggler_descent_time_log`) is
\(\sup_n D(n)/\log n<\infty\).

The negation of descent at every prefix is exactly `AboveAnchor`:
every realized state stays \(\ge n\). The porting question with
quantifiers: does `AboveAnchor n w` with \(2\le n\) force, for every
\(k\le|w|\),

\[
2^k \le 3^{\,\mathrm{oddCount}(w_{\le k})}
\qquad\text{and}\qquad
\mathrm{hugOdds}(k)\le \mathrm{oddCount}(w_{\le k})
\]

— the CycleMin walk hypotheses with no cycle? (Answer: yes; Lean.)

## Current literature

- Descent-certificate route named as the missing induction
  hypothesis — Paper A §6 (`docs/theory/juggler_finite_dynamics_note.md`);
  four consecutive expanding blocks from \(1999\) kill any uniform
  run bound (`J-four-block-persistent-expanding`, **EXACT — LEAN
  VERIFIED**).
- Certified descent density \(13/16\) in Paper B —
  **EXACT — HUMAN PROOF** (`J-four-step-descent-density`);
  laboratory length-5 repair \(7/8\) —
  **EXACT — HUMAN PROOF** (`J-five-step-descent-density`);
  \(57/64\) and \(29/32\) remain withdrawn **CONJECTURE**;
  density-one is conditional on all-depth
  equidistribution, parked behind the BB/GG/JJ \(K_3\) ladder.
- Uniform expanding tax — **REFUTED** (`J-expansion-slack-uniform-tax`);
  log-Lyapunov potential — **REFUTED** (`juggler_cycle_block_potential`);
  ambient-discrepancy-to-orbit transfer — **REFUTED/CLOSE**
  (parity discrepancy transfer branch).
- Episode-level descent laws on `AboveAnchor` prefixes — **PARK**
  (`ESCAPE_EPISODE_PARK`); survival-set mass — **CLOSE**.
- Walk layer for cycles: `cycleMin_prefix_pow_le`,
  `cycleMin_prefix_odds_ge_hug`, hug charge maximality
  (`J-cyclemin-hug-charge-max`) — **EXACT — LEAN VERIFIED**; the
  walk-charge kill gives period \(\ge 478245\) at the certified
  floor. Never previously applied to open trajectories.

Project relationship: **independent** as a porting question
(cycle walk layer → open `AboveAnchor` prefixes) and as a
descent-time record census; the conjectures themselves are
**PROJECT-SPECIFIC** formulations of the classical termination
question.

## Branch budget

```text
Mathematical target     does AboveAnchor force the nonnegative
                        exponent walk and hug domination, and does
                        the near-minimum slack-vs-defect ledger
                        force descent - unconditionally, or only
                        conditional on defect lower bounds?
Novelty hypothesis      the Section 5 walk layer constrains open
                        non-terminating orbits, not just cycles;
                        prior AboveAnchor branches never used it
Falsifier               an orbit family whose defect accumulation
                        at walk near-minima decays as fast as the
                        slack (zero-defect adversary realized); or
                        the porting lemma reparameterizes
                        trajectoryExponentGap
Existing machinery      AboveAnchor / ReturnBelow / FiniteProgress;
                        power_bound_contracts; hugOdds_least;
                        WalkTransport defect bounds; certified
                        Ostrowski q_j; certificate-harvest engine
Maximum Phase-0 scope   one porting-lemma writeup (Lean wrapper
                        only if trivial - it was), one probe:
                        D(n) census with record tracking plus
                        defect-vs-slack profiles on extremal
                        orbits; no Paper A edits, no N0 change
Promotion criterion     an unconditional descent-time theorem for
                        a nontrivial start class, or a conditional
                        envelope theorem strictly weaker than
                        orbit equidistribution
Stop criterion          the kill reduces exactly to per-visit
                        defect lower bounds equivalent to the
                        refuted/parked equidistribution transfer;
                        or reparameterization plus no new empirics
```

## Balanced-ternary formulation

Not BT-specific: the walk lives in the multiplicative exponents
\(3^a/2^k\), the same \(\log 2/\log 3\) Diophantine data as the cycle
finance layer. No balanced-ternary representation is claimed to bear
on the descent question.

## Why BT may be relevant

Only through the shared \(2\)–\(3\) multiplicative structure of the
laboratory (Ostrowski numeration of \(\log(3/2)/\log 3\)); no direct
representation claim.

## Candidate operations / invariants

- Exponent walk on an open prefix: \(u_k=a_k\log_2 3-k\),
  weight \(w_k=3^{a_k}/2^k\) — `AboveAnchor` forces \(u_k\ge 0\)
  (**EXACT — LEAN VERIFIED**, `aboveAnchor_prefix_pow_le`).
- Hug domination: \(\mathrm{hugOdds}(k)\le a_k\) on above-anchor
  prefixes (**EXACT — LEAN VERIFIED**,
  `aboveAnchor_prefix_odds_ge_hug`); odd density \(\ge\log 2/\log 3\)
  in every prefix of a hypothetical descent-free flight.
- Slack-vs-defect ledger (**OBSERVATION**): above the anchor,
  \(\delta_k=w_k\ln n-\ln x_k\ge 0\) (accumulated amplified floor
  defect) and \(\sigma_k=(w_k-1)\ln n\ge 0\) (walk slack); descent
  at \(k\) is exactly \(\delta_k>\sigma_k\). Gap descent:
  \(w_D<1\) (the word itself contracts; Lean
  `power_bound_contracts`). Defect descent: \(w_D\ge 1\) but floors
  push below the anchor.
- Descent-time records \(D(n)\) versus \(c\log n\) and
  \(\sqrt{n\log n}\) (**OBSERVATION**).

## Experiments

Runner: `python -m research.juggler_sequence.above_anchor_walk`
(probe `src/research/juggler_sequence/above_anchor_walk.py`).
Artifact: `data/research/juggler/above_anchor_walk/summary.json`.
Fast suite: `tests/research/juggler_sequence/test_above_anchor_walk.py`.

- Descent-time census on \([2,2\cdot 10^6]\) (`K_CAP` \(10^4\),
  `BIT_CAP` \(2\cdot 10^6\) bits): histogram of \(D\), record
  holders, per-dyadic-block maxima, and the exact gap/defect mode of
  every first descent (integer verdicts only).
- Walk profiles on the laboratories \(365, 501, 1517, 1999, 6187\)
  and the top record holders: per-step \(u_k\), defect
  \(\delta_k\), slack \(\sigma_k\), consumption ratio
  \(\rho_k=\delta_k/\sigma_k\), near-minimum visits
  (\(u_k<0.2\)), and the hug-domination margin
  \(\min_k(a_k-\mathrm{hugOdds}(k))\).

## Conjectures

- `conjectures/active/juggler_asymptotic_descent.json` — eventual
  descent for all sufficiently large starts (**CONJECTURE**).
- `conjectures/active/juggler_descent_time_log.json` —
  \(D(n)=O(\log n)\) (**CONJECTURE**).

## Counterexamples

None produced by this branch. The standing constraint from the
ledger: \(1999\to 5169\to 50093\to 193753\to 887471\) (four
consecutive expanding blocks) forbids uniform contracting-run
shortcuts; the profile here shows its orbit still descends at
\(D(1999)=26\) with min hug gap \(0\) — the orbit prefix touches the
hug bound exactly.

## Formalization

`formal/Problems/Juggler/AboveAnchorWalk.lean` (imported by the
laboratory barrel `Problems.Juggler`, not by `Problems.JugglerPaper`):

- `aboveAnchor_prefix_pow_le` — `AboveAnchor n w` with \(2\le n\)
  forces \(2^k\le 3^{\mathrm{oddCount}(w_{\le k})}\) for every
  \(k\le|w|\); the proof composes `power_bound_contracts` with the
  anchor hypothesis. Since the September 2026 hygiene pass the
  lemma lives in `CycleCore.lean` next to `AboveAnchor` itself,
  and `cycleMin_prefix_pow_le` is its one-line cycle corollary.
- `aboveAnchor_prefix_odds_ge_hug`, `aboveAnchor_odds_ge_hug` —
  composition with `hugOdds_least`: above-anchor prefixes dominate
  the exact hug word in odd count.

No `sorry`; full `lake build` clean. Ledger row
`J-above-anchor-hug-domination` (**EXACT — LEAN VERIFIED**).

## Results

- **Porting lemma (EXACT — LEAN VERIFIED):** the §5 discrete walk
  layer holds verbatim on open above-anchor prefixes; the hug
  adversary prices descent-free flight, not only cycles. A
  hypothetical non-terminating orbit carries odd density
  \(\ge\log 2/\log 3\approx 0.631\) in every prefix.
- **Gap descents dominate (COMPUTATIONALLY VERIFIED):** on
  \([2,2\cdot 10^6]\) every start descends below itself and every
  one of the \(1999999\) first descents is a gap descent — the
  parity word itself goes exponent-negative (\(3^{a_D}<2^D\));
  **zero** defect descents were observed. Floors never push an
  orbit below its anchor while the walk is still nonnegative, at
  these scales. Max \(D=257\) at \(n=1122603\); the six
  high-flyers \(48443,275485,412027,463157,1245741,1267909\)
  (peaks to \(6.5\cdot 10^6\) bits) resolve in the exact gmpy2
  retry pass with \(D\le 213\).
- **Defects are idle (OBSERVATION):** on the laboratory and record
  orbits the defect consumes at most a fraction
  \(\rho\le 3\cdot 10^{-3}\) of the walk slack at the tightest
  near-minimum visits (max \(0.003\) at \(501\); the record orbits
  \(34175, 78901, 1122603\) climb to \(u\sim 10\)–\(16\) and show
  \(\rho\le 10^{-4}\)); the zero-defect adversary is effectively
  realized by actual orbits at laboratory scales. An unconditional
  envelope kill would need defect lower bounds that empirics do not
  support at small heights.
- **Descent-time scaling (OBSERVATION):** record values of
  \(D(n)/\ln n\) grow slowly through the records — \(13.3\) at
  \(n=193\), \(16.2\) at \(13325\), \(22.4\) at \(78901\), then
  \(18.4\) at the final record \(1122603\) — consistent with
  \(O(\log n)\) up to a slowly varying factor and inconclusive on
  strict boundedness; decisively below the \(\sqrt{n\log n}\)
  envelope scale, whose ratio falls from \(2.75\) to \(0.065\)
  across the records.
- **Hug tightness (OBSERVATION):** record orbits approach the hug
  bound (min gap \(0\) occurs, e.g. at \(1999\)); the Lean bound is
  attained, not slack.

## Open questions

- Can any mechanism weaker than per-visit floor-defect lower bounds
  (equivalently, orbit equidistribution of \(\{x^{3/2}\}\) at
  near-minimum states — the parked \(K_3\)/JJ frontier) convert the
  envelope into an unconditional descent theorem?
- Is there a proof of \(D(n)=O(f(n))\) for any \(f(n)=o(n)\) on any
  cofinite class?

## Decision

**PROMOTE** the porting lemma into the platform
(`J-above-anchor-hug-domination`, Lean-verified; the hug adversary
now prices open descent-free flight). **PARK** the asymptotic-descent
envelope program itself: the census shows every observed first
descent is a gap descent and defects consume \(O(10^{-3})\) of the
walk slack, so forcing descent through the envelope reduces exactly
to floor-defect lower bounds at near-minimum visits — the same
deterministic-equidistribution wall (BB/GG/JJ, refuted
ambient-transfer) that parks the density program. The binding
mechanism for actual descent is the parity of nested floor powers
(Paper B territory), not the analytic defect. No route within
laboratory machinery converts the Lean-verified combinatorial
constraint into eventual descent.

Best next question: does the hug-domination constraint (odd density
\(\ge\log 2/\log 3\) in **every** prefix of a descent-free flight)
contradict any provable upper bound on realized odd-run densities —
i.e. can Paper B's depth-\(\le 4\) equidistribution kill the extremal
hug-hugging flights the way parity killed short cycle leftovers?

## Publication assessment

Status: **EXPLORATORY**. The porting lemma is a clean structural
theorem (Lean-verified) worth a paragraph in any future termination
note; the census is negative knowledge pricing the envelope route.
Not a paper candidate on its own.

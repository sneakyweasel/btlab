# Juggler mechanical extremizer and limiting charge

Status: **ARCHIVED**

Refinement of
([juggler_cycle_walk_excursion.md](juggler_cycle_walk_excursion.md)).
Not a halt theorem, not a floor raise, not a uniform \(B/\theta\)
claim, and not a reopen of the closed Christoffel leftover-cell
slogan.

## Problem

Walk-excursion identified leftover DP maximizers with the ceiling
Christoffel word of slope \(o/L\). Is that itinerary prefix-minimal in
\(u_k\) among all admissible \(u\ge 0\) walks with the same
\((L,o)\), and does leftover charge-per-letter converge to the
irrational mechanical average of slope \(1/(1+\log_2(3/2))\)?

## Exact statement

**Prefix dominance fails off the critical slope (REFUTED).**
Ceiling Christoffel has \(a_k=\lceil k\,o/L\rceil\). Among
admissible walks, \(u_k\) is minimized by greedy \(E\)-at-first-legal
time, not by that formula. Witness \((L,o)=(4,3)\): Christoffel is
`OOOE` (\(a_3=3\)), greedy is `OOEO` (\(a_3=2\)). The same gap
appears on \(94/123\) feasible pairs with \(L\le 24\).

**Prefix dominance holds on short convergents
(COMPUTATIONALLY VERIFIED).** The \(29\) pairs where greedy equals
Christoffel are the monochrome words and the short near-convergents
of \(\rho=1/(1+\alpha)\): \((3,2)\), \((6,4)\), \((9,6)\),
\((11,7)\), \((19,12)\). It also holds at leftover
\(L=19,84,1054\).

**Seed leftovers match Christoffel charge; family offsets do not
(COMPUTATIONALLY VERIFIED).** At the certified reduced base,
Christoffel \(B\) equals the committed survey DP on
\(L=50508,101016,151524,176251\) (relative error \(<10^{-14}\)).
On the \(1054\)-family offsets, survey \(B\) exceeds Christoffel
\(B\) by up to \(1.50\cdot 10^{-3}\) (worst \(L=180467\)). The
certified maximizer is therefore the hugging itinerary, which coincides
with Christoffel only on the seeds.

**Mechanical average at this floor (COMPUTATIONALLY VERIFIED).**
A \(10^5\)-letter ceiling-Beatty stream of slope
\(\rho=\log 2/\log 3\) at the \(50508\) reduced base has
\(C_*=0.047947\). Seed leftover \(C\) is \(0.047946\)--\(0.047948\).
The survey plateau was this average, not a coincidence of 19 DPs.
The irrational walk is *not* confined to \([0,1)\): \(u\) reaches
\(1+\alpha\approx 1.585\).

**Uniform \(B/\theta<1\) at fixed \(N_0\) remains false.**
Christoffel-evaluated \(B/\theta=5.25\) at \(L=176251\). Do not
reopen Baker.

No cycle of any length — not claimed.

## Current literature

- Walk-excursion maximizer identification —
  **COMPUTATIONALLY VERIFIED**
  ([juggler_cycle_walk_excursion.md](juggler_cycle_walk_excursion.md))
- Coupled walk charge / certified survey —
  **EXACT — HUMAN PROOF** / **COMPUTATIONALLY VERIFIED**
  ([juggler_cycle_walk_charge.md](juggler_cycle_walk_charge.md))
- Christoffel leftover-cell reduction —
  **REFUTED** (`juggler_christoffel_one_parameter`)
- Beatty identification of leftover \(L\) —
  **KNOWN**
- Baker/Rhin transfer —
  **REFUTED** (`juggler_baker_kills_near_convergents`)
- Mechanical / Christoffel discrepancy —
  **KNOWN** (Borel–Laubie / Berstel–de Luca)
- Every start reaches 1 — not claimed

Project relationship: **extended** (tests the exchange lemma named
by walk-excursion; does not reopen leftover-cell rigidity).

## Branch budget

```text
Mathematical target     Among admissible u≥0 walks with fixed (L,o),
                        does the ceiling Christoffel word of slope
                        o/L prefix-minimize u_k? And does B/L along
                        leftovers converge to the charge of the
                        irrational mechanical word of slope
                        1/(1+log2(3/2)) at the same n'?
Novelty hypothesis      Prefix dominance is an exchange lemma
                        (E is taken at the first legal time). The
                        survey C≈0.04805 is then the ergodic average
                        of g(u) for that mechanical rotation, not a
                        plateau of 19 independent DPs. Not the
                        REFUTED leftover-cell slogan.
Falsifier               An admissible word with some a_k < a_k(Chr);
                        or leftover C(L,n') not approaching the long
                        mechanical average at the same n'.
Existing machinery      christoffel_bits / christoffel_word;
                        reconstruct_maximizer; charge_row / deficit_D;
                        committed survey.json; o_min_and_theta
Maximum Phase-0 scope   Prefix-min DP vs ceiling Christoffel on
                        L≤24; greedy-E vs Christoffel; Christoffel
                        charge vs survey B (O(L), no traceback);
                        one long mechanical prefix average at the
                        certified floor. No Lean, no Paper A, no N0
                        raise, no new leftover DP, no C_* proof
Promotion criterion     Prefix dominance holds on the census, survey
                        B equals Christoffel charge, and leftover C
                        matches the mechanical average to the same
                        three digits as the survey spread
Stop criterion          A prefix-dominance counterexample that also
                        beats Christoffel charge; or C does not
                        converge; or the claim is only KNOWN
                        mechanical-word discrepancy
```

## Balanced-ternary formulation

None required. The walk lives on the exponent lattice
\(\mu a-b\).

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Ceiling Christoffel \(a_k=\lceil k\,o/L\rceil\) prefix-minimizes
  \(u_k\) among admissible walks —
  **REFUTED** (`juggler_walk_christoffel_prefix`); witness
  \((4,3)\): `OOEO` vs `OOOE`
- Greedy \(E\)-when-legal equals Christoffel on leftover seeds —
  **COMPUTATIONALLY VERIFIED** at \(19,84,1054\) and survey seeds
- Mechanical average \(C_*\approx 0.047947\) at this floor —
  **COMPUTATIONALLY VERIFIED**
- Uniform \(B/\theta<1\) at fixed \(N_0\) —
  **REFUTED** (already; confirmed on Christoffel \(B\))
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_walk_mechanical`
- Artifacts: `data/research/juggler/cycle_walk_mechanical/summary.json`
- Tests: `tests/research/juggler_sequence/test_cycle_walk_mechanical.py`

No CLI. No new Lean. Paper A is unchanged. The certified
walk-charge DP is not edited.

## Conjectures

`juggler_walk_christoffel_prefix` — **REFUTED**. Ceiling
Christoffel does not prefix-minimize \(u_k\) among admissible
walks of a given \((L,o)\).

## Counterexamples

- \((L,o)=(4,3)\): Christoffel `OOOE`, greedy `OOEO`, \(a_3=2<3\).
- Survey offsets \(51562,76289,\ldots,180467\): certified walk \(B\)
  exceeds streamed Christoffel \(B\) by \(0.027\%\)--\(0.15\%\).

## Formalization

None. No `WalkMechanical.lean`, no `sorry`. Paper A is unchanged.
Not a halt theorem.

## Results

Classification **WALK_MECHANICAL_CLOSED**.

- Prefix-min / greedy \(=\) Christoffel on \(29/123\) feasible
  pairs with \(L\le 24\): monochrome plus
  \((3,2),(6,4),(9,6),(11,7),(19,12)\)
- Holds at leftover \(19,84,1054\)
- Survey seeds match Christoffel \(B\); family offsets do not
  (max relative gap \(1.50\cdot 10^{-3}\))
- Mechanical \(C_*=0.047947\) matches seed \(C\); \(u\) reaches
  \(1+\alpha\)
- Uniform \(B/\theta\) at floor \(26254995\) is false
  (\(B/\theta=5.25\) at \(176251\))

## Open questions

The charge maximizer is the greedy hugging itinerary, which equals
Christoffel only near the critical slope. A human exchange lemma
for that greedy word — not for ceiling Christoffel — is a
different statement. Do not raise \(N_0\) and do not claim a
uniform \(B/\theta\) gap.

## Decision

**CLOSE.** The proposed Christoffel prefix-dominance theorem is
false: greedy `OOEO` undercuts `OOOE` at \((4,3)\), and the
certified survey \(B\) exceeds Christoffel charge on every
non-seed leftover. What survives is negative knowledge plus a
sharper adversary (greedy \(E\)-when-legal) that coincides with
Christoffel on the seeds, where the mechanical average already
explains \(C\). That is not the Phase-0 promotion criterion, and
it is not a leftover-cell reopen.

Best next question: does greedy \(E\)-at-first-legal-time
prefix-minimize \(u_k\) among all admissible walks, and is that
enough for an explicit \(C_*(n')\)?

## Publication assessment

Status: `ARCHIVED`.

A finite, exact obstruction to the Christoffel-extremizer slogan
for the walk-charge relaxation. The mechanical average remains a
correct description of the *seed* leftover density. Not a paper
candidate and not a halt theorem.

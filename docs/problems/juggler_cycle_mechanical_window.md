# Juggler gap transfer, short-cycle reduction, and the mechanical window

Status: **CLOSE** (Phase 0 decided)

Two things in one dossier. First, the floor-free **gap transfer**
\(n\log n\cdot\min(\Lambda,1)\le 2L\) (Paper A Theorem 4.10, Lean
`cycleMin_gap_transfer`) and its Rhin instance, the **short-cycle
reduction** \(L^{14.3}>n\log n/915\) for every nontrivial cycle
(Corollary 4.11). Second, the Phase-0 question that reduction
leaves: on the band of integers where the prescribed-branch map
\(f_w\) has fixed points, does the realized parity word show any
structure a per-orbit estimate could use? Not a halt theorem, not
a floor raise, not a reopen of the REFUTED Baker transfer at
floors, and not a Paper A edit beyond the recorded Theorem 4.10 /
Corollary 4.11 / §6 paragraph.

## Problem

Every method of Paper A bounds one side of the single closure
equation \(\Lambda=o\log 3-L\log 2=\sum_i\delta_i/\log x_i\).
Along the convergents \(q_k\) of \(\log 2/\log 3\) the minimum a
survivor needs grows like \(n_{\max}(q_k)\asymp a_{k+1}q_k^2/\log^2 n\),
so no floor and no defect upper bound excludes all lengths. What
statement, if any, is floor-free, and what exactly remains?

## Exact statement

**Gap transfer (EXACT — LEAN VERIFIED, `cycleMin_gap_transfer`).**
For a cycle itinerary \(w\) of length \(L\) with \(o\) odd
letters based at a cycle minimum \(n\ge 2\),
\[
n\log n\cdot\min(o\log 3-L\log 2,\,1)\le 2L .
\]
Proof: Theorem 4.4 reads \(P(A-B)\le LA\) with \(A=3^o,B=2^L,P=n\log n\).
If \(A\le B\) the left side is nonpositive; if \(A\ge 2B\) then
\(P\le 2L\); if \(B<A<2B\) then
\(\Lambda=\log(A/B)\le (A-B)/B\) and \(P(A-B)/B\le LA/B\le 2L\).
Abstract form `cycleMin_length_of_gap`: \(\varepsilon\le\min(\Lambda,1)\)
implies \(n\log n\cdot\varepsilon\le 2L\).

**Short-cycle reduction (EXACT — HUMAN PROOF; Rhin is classical).**
Rhin's effective measure in the form of Simons–de Weger Lemma 12,
\(\Lambda>e^{-13.3(0.46057+\log L)}=e^{-6.1256}L^{-13.3}\) with
\(H=\max(L,o)=L\), gives for every nontrivial cycle
\(n\log n\le 2e^{6.1256}L^{14.3}<915\,L^{14.3}\). Hence there is no
cycle with \(L^{14.3}\le n\log n/915\), for all \(n\ge 2\) and
without a descent floor; the no-cycle problem is exactly the
exclusion of long cycles.

**Mechanical window (OBSERVATION / COMPUTATIONALLY VERIFIED).**
For a prescribed word \(w\), \(f_w\) is the composition of the
prescribed branches (odd branch \(\lfloor\sqrt{m^3}\rfloor\), even
branch \(\lfloor\sqrt m\rfloor\), parity ignored). It is monotone
with average slope \(1+\Lambda(1+\log m)\), so its integer fixed
points number about \(1/(\Lambda(1+\log m))\approx n/L\) and sit in
a band around the finance balance point; a cycle with word \(w\)
exists iff a member of the band realizes \(w\). Hug words:

| \(L\) | \(o\) | \(\Lambda\) | crossing | fixed points | predicted | span | depth mean | depth max | \(\log_2\) size |
|---|---|---|---|---|---|---|---|---|---|
| 19 | 12 | \(1.36\cdot 10^{-2}\) | 34 | 11 | 16.3 | 18 | 0.82 | 3 | 3.5 |
| 84 | 53 | \(2.09\cdot 10^{-3}\) | 397 | 55 | 68.6 | 249 | 1.18 | 11 | 5.8 |
| 1054 | 665 | \(4.37\cdot 10^{-5}\) | 77062 | 1689 | 1869.6 | 14931 | 1.03 | 8 | 10.7 |

The count follows the drift prediction (ratios \(0.68,0.80,0.90\));
the set is a band, not a run (span/count \(1.6,4.5,8.8\)). The
realized depth histogram at \(L=1054\) is
\(833,411,213,119,55,37,11,6,4\): a fair coin (mean \(1.03\),
maximum below \(\log_2\) of the count). The single depth-\(11\)
member at \(L=84\) (\(m=429\)) is a \(3\%\) coincidence on \(55\)
draws. No full realization (none can exist below the certified
floor).

## Current literature

- Cycle financing and the \(m\)-cycle squeeze — Simons–de Weger
  (`known`); Rhin's effective two-logarithm measure (`known`,
  `rhin-1987-pade-irrationality`). The transfer at *floors* is
  **REFUTED** ([juggler_cycle_gap_baker.md](juggler_cycle_gap_baker.md));
  the floor-free transfer here is the complementary statement and
  is `independent` of that refutation.
- Formal-versus-realized words and the absence of a within-cell
  cocycle — [juggler_cycle_mechanical_lift.md](juggler_cycle_mechanical_lift.md)
  (`reproduced`: the band members' realized words are unrelated
  to the prescribed word beyond a coin).
- Nested-floor-power parity equidistribution (Paper B) — averaged
  over starts, depth \(\le 7\); no per-orbit statement (`known`).

## Branch budget

```text
Mathematical target     For a survivor word w, does the realized parity depth on the
                        band of mechanical fixed points show any structure beyond a
                        fair coin (geometric(1/2) depths, max ≈ log2 of the count)?
Novelty hypothesis      Consecutive integers in a short band might carry a correlated
                        parity signal at depth 2–3 usable by a short-interval estimate
                        at depth growing with n.
Falsifier               Geometric depths within binomial noise and max ≈ log2(count)
                        at every certified length: per-orbit depth L is a computation,
                        not a theorem.
Existing machinery      hug_word, o_min_and_theta, exact isqrt map, mechanical-lift
                        dossier.
Maximum Phase-0 scope   Hug words at L in {19, 84, 1054}: bisection to the crossing,
                        exact scan of the band, count vs 1/(Λ(1+log m)), realized
                        depth histogram. No Lean beyond Theorem 4.10, no floor.
Promotion criterion     Depth excess over log2(count) growing with L, or a band
                        deviating from the finance balance prediction.
Stop criterion          Fair coin at all lengths → CLOSE (method wall).
```

## Balanced-ternary formulation

None. The objects are the linear form \(o\log 3-L\log 2\), the
finance inequality, and the prescribed-branch composition on
integers; balanced ternary plays no role.

## Why BT may be relevant

Not relevant here; recorded for the template.

## Candidate operations / invariants

- Gap transfer \(n\log n\cdot\min(\Lambda,1)\le 2L\) —
  **EXACT — LEAN VERIFIED** (`cycleMin_gap_transfer`).
- Abstract length bound from any \(\varepsilon\le\min(\Lambda,1)\) —
  **EXACT — LEAN VERIFIED** (`cycleMin_length_of_gap`).
- Rhin instance \(L^{14.3}>n\log n/915\) — **EXACT — HUMAN PROOF**.
- Mechanical band count \(\approx 1/(\Lambda(1+\log m))\) —
  **OBSERVATION** (three lengths).
- Realized depth on the band is a fair coin — **OBSERVATION**.
- Per-orbit parity at depth growing with \(n\) — no candidate;
  method wall (see Decision).

## Experiments

- Probe: `research.juggler_sequence.cycle_mechanical_window`
  (`python -m research.juggler_sequence.cycle_mechanical_window`,
  `--long` adds \(L=25781\); not run, pure-Python cost \(\sim 10^9\)
  integer square roots).
- Artifact: `data/research/juggler/cycle_mechanical_window/summary.json`
  (`classification`, per-length rows: crossing, band, predicted
  count, depth histogram, `full_realizations`).
- Tests: `tests/research/juggler_sequence/test_cycle_mechanical_window.py`.

## Conjectures

None opened. The band count law is an observation, not a
conjecture; the fair-coin reading is the null hypothesis.

## Counterexamples

None. The one apparent outlier (depth \(11\) at \(m=429\), \(L=84\))
is a coincidence at the expected rate and is reported in the
artifact.

## Formalization

`formal/Problems/Juggler/GapTransfer.lean`: `cycleMin_gap_transfer`,
`cycleMin_length_of_gap`. Imported by `Problems.JugglerPaper` and
`Problems.Juggler`. No `sorry`. Rhin's measure is a hypothesis of
`cycleMin_length_of_gap`, not a Lean theorem.

## Results

- Theorem 4.10 and Corollary 4.11 are printed in Paper A (§4, new
  subsection; Contribution 5; layer 8; Appendix A; reference [15];
  a §6 paragraph naming the open problem).
- At the certified floor \(3.5\cdot 10^8\) Corollary 4.11 forces
  only \(L\ge 4\), against \(780239\) from the table: the reduction
  is floor-free and toothless at floors, consistent with the REFUTED
  Baker transfer.
- The mechanical band has the predicted count and a fair-coin
  realized depth at \(L=19,84,1054\).

## Open questions

Exclusion of long cycles \(L^{14.3}>n\log n/915\). It is a
statement about the parity word of a specific orbit at depth
\(L\); no tool in the laboratory or the literature addresses it.

## Decision

`CLOSE`. The reduction is a reparameterization of finance plus a
classical input: it names the frontier but excludes nothing the
table did not. The Phase-0 experiment finds the null hypothesis:
the band is where finance says it is, and the parity word on it is
a fair coin. Per-orbit parity at depth growing with \(n\) has no
candidate mechanism — Paper B's estimates are averaged over starts
and stop near depth seven; short-interval versions would be
weaker, not deeper; the only exact per-orbit facts (unique odd
preimage, even fibres are intervals) are parity-blind. Do not
reopen as a short-interval Paper B, as a two-copy Sturmian
rigidity, or as a longer band scan. Best next question: none in
this laboratory — the sentence in Paper A §6 is the deliverable.

## Publication assessment

Status: `THEOREM` (Theorem 4.10 Lean; Corollary 4.11 human with a
classical input). The band experiment is `EXPLORATORY` supporting
material and is not a paper claim beyond the one §6 sentence.

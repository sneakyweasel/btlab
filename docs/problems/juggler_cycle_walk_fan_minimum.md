# Juggler fan-minimum law and the CF reduction

Status: **ACTIVE** (Phase 0 decided)

Successor of the walk-finance competition
([juggler_cycle_walk_competition.md](juggler_cycle_walk_competition.md)),
answering its best next question: is the mid-fan minimum of the
required improvement bounded away from \(1\) uniformly over fans?
Not a halt theorem, not a floor raise, not a uniform \(B/\theta\)
claim, and not new floor verification: everything here is exact
arithmetic on the already-certified competition artifact.

## Problem

The self-consistent schedule walks the dangerous fans
\(L_k=q+kQ\) (dangerous convergent \(q\) of
\(\theta_{\rm rot}=\log(3/2)/\log 3\), positive convergent step
\(Q\), partial quotient \(a\) members). The per-level required
improvement dips to \(1.0735\) mid-fan on the \(55\)-fan. Is that
minimum a structural constant, or a function of the continued
fraction that a subsequence of fans can drive to \(1\)?

## Exact statement

**Balance law (first-order human derivation, instance
COMPUTATIONALLY VERIFIED).** At a common floor the DK envelope
factor cancels, so the required improvement across one fan step is

\[
R_k=\frac{\theta_k}{\theta_{k+1}}\cdot\frac{L_{k+1}}{L_k},
\qquad
\ln R_k\approx\frac{1}{A-k}+\frac{1}{B+k},
\]

with \(\varepsilon_k=\varepsilon-k\eta\)
(\(\varepsilon=-\ln(1-\theta(q))/\ln 3\), \(\eta=\|Qx\|\)),
\(A=\varepsilon/\eta\) (within \(1\) of the partial quotient at the
dangerous position) and \(B=q/Q\in(0,1)\). The sum is minimized at
the balance point \(k^*=(A-B)/2\), where both terms equal
\(2/(A+B)\):

\[
\boxed{\;\ln R_{\min}\approx\frac{4}{A+B}\;}
\]

**Instance (COMPUTATIONALLY VERIFIED, from the certified
competition artifact).**
Fan A (\(q=176251\), \(Q=301994\), \(a_{14}=55\)):
\(A=55.811\), \(B=0.5836\), \(k^*=27.61\); predicted
\(R_{\min}=1.0735\), exact \(1.0735\), schedule-measured
\(1.07353\); predicted and measured minimizer both
\(L=8632083=176251+28\cdot 301994\).
Fan B (\(q=16785921\), \(Q=17087915\), \(a_{16}=4\)):
\(A=4.284\), \(B=0.9823\); predicted \(R_{\min}=2.137\), exact and
measured \(2.163\) (inside the second-order band \((4/(A+B))^2\));
minimizer \(50961751\) matched.

**Reduction (the answer to the question).** \(R_{\min}\) over the
fan closed by quotient \(a\) satisfies
\(e^{4/(a+2)}\le R_{\min}\lesssim e^{4/a}\). Hence the fan minima
approach \(1\) along a subsequence **iff the partial quotients of
\(\log 2/\log 3\) at the dangerous positions are unbounded**.
Boundedness of the continued-fraction quotients of
\(\log 2/\log 3\) is a classical **OPEN** problem: generically
(Gauss–Kuzmin) the quotients are unbounded, and \(23\) and \(55\)
already occur, but no proof is known either way. The laboratory
competition program terminates at this reduction.

**Coming fans (prediction table).** Certified: \(a_{14}=55\)
(\(R_{\min}\in[1.073,1.075]\)), \(a_{16}=4\)
(\([1.95,2.72]\)). Observed at 90-digit precision, not certified:
\(a_{18}=1\) (\([3.79,54.6]\) — a single-step jump), \(a_{20}=15\)
(\([1.27,1.31]\)), \(a_{22}=9\) (\([1.44,1.56]\)), \(a_{24}=5\)
(\([1.77,2.23]\)).

No cycle of any length — not claimed. No new period bound.

## Current literature

- Walk-finance competition (break-even law, 61-level schedule) —
  **COMPUTATIONALLY VERIFIED**
  ([juggler_cycle_walk_competition.md](juggler_cycle_walk_competition.md))
- Gauss–Kuzmin statistics of partial quotients — **KNOWN**
- Boundedness of the CF quotients of \(\log 2/\log 3\) — **OPEN**
  (no effective result; not the Baker route, which stays REFUTED)
- Every start reaches 1 — not claimed

Project relationship: **extended** (the capstone of the Paper A §5
walk program: its asymptotic frontier is a named open Diophantine
problem).

## Branch budget

```text
Mathematical target     Is the mid-fan minimum of the required improvement
                        bounded away from 1 uniformly over dangerous fans,
                        or driven to 1 along a subsequence?
Novelty hypothesis      The balance formula ln R_min = 4/(A+B), A ~ the
                        dangerous-position partial quotient, B = q/Q: the
                        fan minimum is a one-line function of the CF of
                        log 2/log 3, so sharpness <=> unbounded quotients
Falsifier               Schedule minima deviate from exp(4/(A+B)) beyond
                        the second-order band, or k* misses the observed
                        minimizer
Existing machinery      cycle_walk_competition summary (exact theta per fan
                        row, 61 schedule levels), certified quotients
                        through a16 = 4
Maximum Phase-0 scope   One probe reading the stored summary (no new
                        certification, no floor work), dossier, conjecture,
                        tests, journal
Promotion criterion     Formula matches both fans' measured minima and
                        minimizers; the reduction statement survives
Stop criterion          Formula fails on a fan, or reparameterization of
                        the competition law
```

## Balanced-ternary formulation

None required.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Exact conversion \(\varepsilon=-\ln(1-\theta)/\ln 3\) —
  **EXACT — HUMAN PROOF** (one line)
- Balance law \(\ln R_{\min}\approx 4/(A+B)\), minimizer
  \(k^*=(A-B)/2\) — first-order human derivation; instance
  **COMPUTATIONALLY VERIFIED** on both certified fans
- Reduction: fan sharpness \(\iff\) unbounded dangerous-position
  quotients — **CONJECTURE**-level equivalence resting on the
  verified law; the quotient question itself is **OPEN**
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_walk_fan_minimum`
- Artifacts: `data/research/juggler/cycle_walk_fan_minimum/summary.json`
- Tests: `tests/research/juggler_sequence/test_cycle_walk_fan_minimum.py`

No CLI, no Lean, no new big-int certification, no floor work.

## Conjectures

`juggler_walk_fan_minimum_law` — **PROVED** 20 September 2026 (exact
form; what follows is the asymptotic reading it replaced):
along every dangerous fan, \(\ln R_{\min}=4/(A+B)+O((A+B)^{-2})\),
hence the schedule's required-improvement infimum over all fans is
\(1\) iff the dangerous-position partial quotients of
\(\log 2/\log 3\) are unbounded. Instances verified on the two
certified fans.

## Counterexamples

None. Fan B's \(1.2\%\) deviation from the first-order value sits
inside the declared second-order band.

## Formalization

None. No new Lean, no `sorry`.

## Results

Classification **WALK_FAN_MINIMUM_GREEN**.

- Fan A: \(R_{\min}\) predicted \(1.0735\) vs measured \(1.07353\)
  (error \(4\cdot 10^{-4}\)), minimizer \(8632083\) predicted and
  observed
- Fan B: predicted \(2.137\) vs measured \(2.163\), minimizer
  \(50961751\) predicted and observed
- The competition's mystery constant \(1.0735\) is
  \(e^{4/(A+B)}\) with \(A+B=56.39\) — nothing but the certified
  quotient \(55\)
- Future fans: the observed (uncertified) quotient \(15\) at
  \(a_{20}\) predicts a fan minimum near \(1.29\); a future
  quotient \(a\) yields \(e^{4/(a+2)}\le R_{\min}\lesssim e^{4/a}\)
- The dichotomy frontier is now a named open problem: unboundedness
  of the CF quotients of \(\log 2/\log 3\)

## Open questions

None actionable in the laboratory. The successor question —
are the partial quotients of \(\log 2/\log 3\) unbounded — is a
classical open Diophantine problem; no finite computation decides
it, and the Baker-type effective routes are REFUTED for this
application. Do not reopen.

## Decision

**PROMOTE.** The balance law is verified on both certified fans
with the minimizers matched exactly, it explains the competition's
measured \(1.0735\) in closed form, and it reduces the program's
asymptotic frontier to a named open problem. The walk-competition
program is complete: further laboratory work on this frontier
cannot progress without new mathematics on the continued fraction
of \(\log 2/\log 3\), so no successor branch is opened.

## Publication assessment

The closing paragraph of the Paper A successor's synthesis section:
the finance/walk competition's per-level slack is
\(\exp(4/(a+B))\) at the dangerous quotient \(a\), so the method is
asymptotically sharp exactly when \(\log 2/\log 3\) has unbounded
partial quotients — an attractive, honest place to stop. Claim
tags: instances COMPUTATIONALLY VERIFIED; the asymptotic law and
the equivalence are CONJECTURE; the quotient question is OPEN.
Not a halt theorem.

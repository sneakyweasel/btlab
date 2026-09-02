# Juggler crude envelope by Riemann sums and occupancy

Status: **ACTIVE** (Phase 0 decided)

Refinement of
([juggler_cycle_walk_koksma.md](juggler_cycle_walk_koksma.md)).
Not a halt theorem, not a floor raise, not a uniform \(B/\theta\)
claim, and not a reopen of the REFUTED Koksma \(+1/L\) or
Christoffel slogans.

## Problem

Koksma \(+1/L\) failed on leftover offsets. Can one prove
\(C_L<1/(\ln 3\,\ln n')\) for leftover hug / IET words by a
method that is not Denjoy–Koksma at constant \(1\), making the
18 walk-charge kills DP-free?

## Exact statement

**Hitting \(\lvert\#I-L\mu(I)\rvert\le 1\) is false (REFUTED).**
Equal bins of width \(1/250\) on the IET \(\{k\theta\}\),
\(\theta=\log_2(3/2)/\log_2 3\), overfill the first bin. At
\(L=180467\) that bin has \(725\) points against
\(L/m=721.868\) (error \(3.13\)). High-precision confirmation
rules out float artefact. The excess sits at \(u=0\), the peak
of the charge density.

**Riemann + \(J\)-slack schema (EXACT — HUMAN PROOF).**
\(f(u)=n^{1-2^u}/2^u\) is decreasing on \([0,1+\alpha]\). Split
the circle into \(m\) equal bins. On bin \(i\), \(f\le f(i\Delta)\).
If every occupancy satisfies \(\lvert n_i-L/m\rvert\le h\), then

\[
C_L
\le\Bigl(1+\frac{hm}{L}\Bigr)\Bigl(C_*+\frac1m\Bigr)
=C_*+\frac1m+\frac{hm}{L}C_*+\frac hL.
\]

The left Riemann sum of a decreasing function overshoots the
integral by at most \(f(0)/m<1/m\). From
\(1/(1+x)^2\le 1-2x+3x^2\) one has
\(J\le 1-2/\ln n+6/(\ln n)^2\), hence

\[
\frac1{\ln 3\,\ln n}-C_*
\ge \frac{2}{\ln 3\,(\ln n)^2}-\frac{6}{\ln 3\,(\ln n)^3}.
\]

At \(m=250\), \(h=4\), \(L\ge 50508\), \(\ln n\ge 17\), the
binning excess is \(0.005139\) and the \(J\)-gap is at least
\(0.005188\). So the occupancy cap \(h\le 4\) implies
\(C_L<1/(\ln 3\,\ln n)\).

**Occupancy cap on the leftovers
(COMPUTATIONALLY VERIFIED).** On all 19 leftovers at
floor \(26254995\), equal-bin occupancy stays within \(4\)
(max overshoot \(3.35\)). Integer counts; not a charge sum.
Published Ostrowski/Schoissengeier bounds on \(N D_N^*\) are
too loose for the slack (partial quotients \(23\) and \(55\)).

**Eighteen kills, DP-free under the envelope
(COMPUTATIONALLY VERIFIED).** Substituting
\(B\le L/(n'(\ln n')^2\ln 3)\) into the \(6/5\) unroll recovers
the same 18 lengths (margin \(1.008\) at \(L=50508\)) and still
misses \(L=176251\) (margin \(0.143\)). Uniform \(B/\theta<1\)
at this floor stays false. Same trust boundary as Theorem 4.6:
exact inequality plus a guarded float comparison. The walk DP
is not used. Period bound unchanged: \(176251\).

No cycle of any length — not claimed.

## Current literature

- Koksma \(+1/L\) —
  **REFUTED**
  ([juggler_cycle_walk_koksma.md](juggler_cycle_walk_koksma.md))
- Hug exchange and \(C_*\) —
  **EXACT — HUMAN PROOF**
  ([juggler_cycle_walk_exchange.md](juggler_cycle_walk_exchange.md))
- Ostrowski / Schoissengeier discrepancy —
  **KNOWN** (too loose here)
- Rotation hitting \(\lvert\#I-L\mu\rvert\le 1\) —
  **REFUTED** (`juggler_walk_hitting_one`)
- Baker/Rhin transfer —
  **REFUTED** (`juggler_baker_kills_near_convergents`)
- Every start reaches 1 — not claimed

Project relationship: **extended** (a DP-free envelope for the
already certified 18 kills; not a leftover-cell reopen).

## Branch budget

```text
Mathematical target     Prove C_L < 1/(ln 3 ln n') for leftover
                        hug/IET words by interval hitting +
                        Riemann sums, not Denjoy-Koksma at 1/L
Novelty hypothesis      |#I - L mu(I)| <= 1 on each bin plus the
                        slack 1-J in the Laplace integral
                        beats the Riemann + 1/m error
Falsifier               Hitting deviation too large; or
                        (1+hm/L)(C_*+1/m) >= 1/(ln 3 ln n')
                        on a leftover; or the argument is
                        Koksma +1/L under a change of name
Existing machinery      c_star_integral, IET rotation, leftover
                        table, J-form of C_*
Maximum Phase-0 scope   Hitting census on leftover L with a
                        fixed m; binning bound vs crude B;
                        analytic J-upper at L>=50508, ln n>=17.
                        No Lean, no Paper A, no N0, no new DP
Promotion criterion     Written human schema whose numeric
                        hypotheses hold on the 19 leftovers
                        and recover the 18 kills
Stop criterion          Binning bound fails; or this is only
                        the already-recorded 19-row observation
                        of C_hug < B
```

## Balanced-ternary formulation

None required. The walk lives on the exponent lattice
\(\mu a-b\).

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- \(\lvert\#I-L\mu(I)\rvert\le 1\) for equal IET bins —
  **REFUTED** (`juggler_walk_hitting_one`)
- \(C_L\le(1+hm/L)(C_*+1/m)\) given occupancy \(\le h\) —
  **EXACT — HUMAN PROOF**
- \(J\le 1-2/\ln n+6/(\ln n)^2\) —
  **EXACT — HUMAN PROOF**
- Occupancy \(\le 4\) on the 19 leftovers —
  **COMPUTATIONALLY VERIFIED**
- \(C_L<1/(\ln 3\,\ln n')\) on those leftovers, 18 DP-free
  kills — **COMPUTATIONALLY VERIFIED**
- Uniform \(B/\theta<1\) at fixed \(N_0\) —
  **REFUTED** (already)
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_walk_envelope`
- Artifacts: `data/research/juggler/cycle_walk_envelope/summary.json`
- Tests: `tests/research/juggler_sequence/test_cycle_walk_envelope.py`

No CLI. No new Lean. Paper A is unchanged. The certified
walk-charge DP is not edited.

## Conjectures

`juggler_walk_hitting_one` — **REFUTED**. Equal-bin IET
occupancy need not stay within \(1\) of \(L/m\).

`juggler_walk_crude_envelope` — **ACTIVE**. Occupancy \(\le 4\)
plus the Riemann/\(J\) schema gives \(C_L<1/(\ln 3\,\ln n')\)
on leftover hug itineraries at this floor.

## Counterexamples

- Hitting \(\le 1\): \(L=180467\), first bin \(725\) vs
  \(721.868\).
- Off-lattice check: \(L=60000\) has overshoot exactly \(4\).

## Formalization

None. No `WalkEnvelope.lean`, no `sorry`. Paper A is unchanged.
Not a halt theorem.

## Results

Classification **WALK_ENVELOPE_GREEN**.

- Hitting \(\le 1\) fails; leftover occupancy cap \(4\)
  (max overshoot \(3.35\))
- Analytic \(m=250\), \(h=4\), \(L=50508\), \(\ln n=17\):
  excess \(0.005139 < 0.005188\)
- All 19 leftovers satisfy the binning bound
- Envelope kills \(18/19\); margins \(1.008\) at \(50508\),
  \(0.143\) at \(176251\)
- Period bound unchanged

## Open questions

A human occupancy bound that replaces the 19-row cap
(first-bin / three-gap / a sharp Ostrowski constant), so the
envelope is not a finite census. Do not raise \(N_0\) and do
not claim a uniform \(B/\theta\) gap.

## Decision

**PROMOTE.** The proposed hitting-\(\le 1\) lemma is false, but
that is not the stop criterion: the Riemann + \(J\)-slack
schema is a human inequality, the occupancy cap \(h\le 4\) is
an exact 19-row integer census (not a charge DP), and together
they put \(C_L\) under \(1/(\ln 3\,\ln n')\) and recover the
18 kills without `walk_budget`. This is not Koksma \(+1/L\)
and not a restatement of “we saw \(C_{\mathrm{hug}}<B\)”.
The envelope is not yet a theorem for every \(L\ge 50508\).

Best next question: a human occupancy bound that replaces the
19-row cap \(h\le 4\), so the crude envelope is DP-free and
census-free?

## Publication assessment

Status: `THEOREM`.

A human comparison plus a finite occupancy certificate that
retires the walk DP for the 18 kills at this floor. Not a
paper candidate until the occupancy cap is human. Not a halt
theorem.

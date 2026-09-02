# Juggler ordered floor-error transport

Status: **ARCHIVED**

Reviewer follow-up of the arithmetic seam stack
([juggler_global_defect.md](juggler_global_defect.md),
[juggler_defect_lower_bound.md](juggler_defect_lower_bound.md),
[juggler_cycle_cluster_amplify.md](juggler_cycle_cluster_amplify.md),
[juggler_cycle_defect_congruence.md](juggler_cycle_defect_congruence.md),
[juggler_cycle_peak_valley_composition.md](juggler_cycle_peak_valley_composition.md)),
not a reopen of those branches and not a new paper. Total defect
and first-defect Amplify already exist. This phase asks whether
keeping every local remainder, transporting it by its position
in the itinerary, and splitting the vector at the \(O\mid E\) seam
produces a one-sided constraint the scalar \(\Delta\) cannot see.

Not a halt theorem, not a leftover-killer, not a finance reopen,
and not a claim that every positive integer reaches 1.

## Problem

Do not look at total defect. Track how each floor error is
amplified according to its position in the itinerary and split the
vector at the peak/valley seam. Does a climb-half, a descent-half,
or a single position obstruct a cycle without summing to
\(\Delta\)?

## Exact statement

**The recurrence already transports every remainder
(KNOWN / EXACT — LEAN VERIFIED).**
An even step is \(D\mapsto D+\mathrm{powGap}(T^2,\rho,2^k)\).
An odd step is
\(D\mapsto\mathrm{powGap}(T^2,\rho,2^k)+\mathrm{powGap}(x^{2^k},D,3)\).
The scalar is `accumulatedDefect`.

**Per-letter attribution unrolls that recurrence
(KNOWN / REPARAMETERIZATION).**
At letter \(i\) insert \(c_i=\mathrm{powGap}(T(x_i)^2,\rho_i,2^i)\)
and set \(e_i\) to `amplifyDefect` of \(c_i\) through the suffix,
later remainders dropped. Then
\[
\Delta_w(n)=\sum_i e_i+X.
\]
The sum plus the cross term is the global defect, not a new
object.

**Cross terms are the odd-step cubics
(KNOWN / REPARAMETERIZATION).**
\(X=0\) when no two positive chunks share a later odd
(\(\mathtt{OE}\), \(\mathtt{OOE}\), and \(\mathtt{OOOEE}\) at
\(25\) where the first remainder vanishes). \(X>0\) when they
do (\(\mathtt{OOEOOE}\) at \(365\); leftover shape at \(429\)).
That mixing is already `accumulateOdd`.

**First-defect Amplify is one coordinate
(KNOWN).**
If \(j=\mathrm{firstDefect}\), then \(e_j=\mathrm{Amplify}\).
Keeping later letters only adds more nonnegative coordinates.

**Formal position weights are suffix exponents
(KNOWN / REPARAMETERIZATION).**
The state-free factor is \(W_i=3^{\#O(w[i+1:])}\). On the
length-11 leftover this is
\((729,243,243,81,27,27,9,3,3,1,1)\). That is the closed
exponent budget read backwards, not a new position law.

**No seam-half beats \(G\) on an expanding itinerary
(COMPUTATIONALLY VERIFIED).**
On expanding \(\mathtt{OOE}\) at \(365\), \(1517\), and
\(1000057\), both halves and every single \(e_i\) stay below
\(G=n^9-n^8\). At \(365\), \(E_O/G\approx 2.8\cdot 10^{-4}\)
and Amplify\(/G\approx 2.7\cdot 10^{-4}\). On leftover shape
at \(429\), \(E_O/G\approx 0.045\), \(E_E/G\approx 0.70\),
\(\max e_i/G\approx 0.27\). The descent half is larger; it
still misses \(G\). Contracting \(\mathtt{OE}\) and
\(\mathtt{OOOEE}\) have \(G<0\) and \(T_w<n\), which is
`power_bound_contracts`.

No cycle of any length — not claimed.

## Current literature

- Global defect \(n^{3^o}=T_w(n)^{2^L}+\Delta\) —
  **EXACT — LEAN VERIFIED**
  (`global_defect_identity`)
- First-defect Amplify —
  **EXACT — LEAN VERIFIED**
  (`amplifyDefect`); leftover-killer **REFUTED**
  ([juggler_amplify_surplus.md](juggler_amplify_surplus.md),
  [juggler_cycle_cluster_amplify.md](juggler_cycle_cluster_amplify.md))
- Cycle finance —
  **EXACT — LEAN VERIFIED**
  (`cycleMin_finance`)
- Floor-defect / congruence accumulation —
  **CLOSE** / **REPARAMETERIZATION**
  ([juggler_cycle_defect_congruence.md](juggler_cycle_defect_congruence.md))
- Peak–valley interval composition —
  **CLOSE** / **REPARAMETERIZATION**
  ([juggler_cycle_peak_valley_composition.md](juggler_cycle_peak_valley_composition.md))
- Cumulative floor-loss \(\rho\)-product —
  **CLOSE** / **REFUTED**
  ([juggler_cumulative_floor_loss.md](juggler_cumulative_floor_loss.md))
- Defect correlation —
  **CLOSE**
  ([juggler_cycle_defect_correlation.md](juggler_cycle_defect_correlation.md))
- Cycle-wide exponent product —
  **CLOSE** / **REPARAMETERIZATION**
  ([juggler_cycle_exponent_budget.md](juggler_cycle_exponent_budget.md))
- Collatz-style financing —
  **known** (`simons-de-weger-2005-collatz-m-cycles`)
- Every start reaches 1 — not claimed

Project relationship: **refuted** as a new one-sided obstruction;
the ordered vector is a **REPARAMETERIZATION** of
`accumulatedDefect` plus the known Amplify gap.

## Branch budget

```text
Mathematical target     Does position-weighted, seam-split
                        transport of local floor errors give a
                        one-sided or ordered constraint that is
                        not scalar Δ, first-defect Amplify,
                        finance, or the closed congruence /
                        interval attacks?
Novelty hypothesis      An error's suffix lift depends on where
                        it sits in the itinerary; climb-half vs
                        descent-half can obstruct a cycle
                        without summing to Δ
Falsifier               attributed chunks + cross terms = Δ;
                        no seam-half beats G except by T_w < n;
                        first-order weights are suffix 3^{o'};
                        coupling is defect_correlation or
                        remainder_balance
Existing machinery      accumulatedDefect / accumulateOdd / Even;
                        amplifyDefect / firstDefect; formal_surplus;
                        circuits(); global_defect_identity;
                        cycleMin_finance; defect_congruence CLOSE;
                        peak_valley CLOSE; cluster_amplify CLOSE;
                        cumulative_floor_loss CLOSE
Maximum Phase-0 scope   exact per-letter attribution + O|E split
                        on OE, OOE, OOOEE, OOEOOE, L11 leftover
                        at 13 / 25 / 365 / 1517; compare halves
                        to G and to first-defect Amplify; record X.
                        No Lean, no finance reopen, no Paper A
Promotion criterion     a seam-half or single-position transport
                        exceeds G while first-defect Amplify does
                        not, and the reason is not T_w < n; or an
                        ordered climb/descent law that is not Δ
Stop criterion          vector sums to Δ; halves never beat G
                        except by contraction; weights are suffix
                        exponents; X is accumulateOdd cubics
```

## Closed-bridge gates

Do not reopen finance, first-defect Amplify, cluster Amplify,
defect congruence, peak–valley composition, cumulative floor
loss, or the exponent budget.

- **CLOSE** if \(\sum e_i+X=\Delta\).
- **CLOSE** if no seam-half or single \(e_i\) exceeds \(G\)
  except on contracting itineraries where \(T_w<n\).
- **CLOSE** if \(W_i=3^{\#O(\mathrm{suffix})}\).
- **CLOSE** if \(X\) is the odd-step cubic cross.
- **CLOSE** if first-defect Amplify is the first positive \(e_j\).
- **PROMOTE** only if a seam-half or single position beats \(G\)
  while Amplify does not, and the reason is not \(T_w<n\).

Do **not** raise \(N_0\). Do **not** open \(L=55293\). Do
**not** reintroduce finance. Do **not** edit Paper A. Do
**not** add Lean.

## Explicitly out of Phase-0

A \(K=11\) proof, a linearized \(\sum\rho_i W_i\) bound,
Fourier / residues / \(Q\)-sections, a branch-and-bound engine,
ledger row, new Lean, CLI, visualization, Paper A edit, a
congruence census, a peak–valley reopen.

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Per-letter transport \(e_i\) —
  **REPARAMETERIZATION** of `amplifyDefect` at every index
- Seam split \(E_O,E_E\) —
  **REPARAMETERIZATION** of grouping those coordinates
- Cross term \(X=\Delta-\sum e_i\) —
  **KNOWN** / **REPARAMETERIZATION** of `accumulateOdd`
- Formal weights \(W_i=3^{\#O(\mathrm{suffix})}\) —
  **REPARAMETERIZATION** of the closed exponent budget
- Expanding halves below \(G\) —
  **KNOWN** (the Amplify gap, now on every coordinate)
- Ordered leftover-killer —
  **REFUTED** (`juggler_cycle_error_transport`)
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_error_transport`
- Dataset: `data/research/juggler/cycle_finance/error_transport/summary.json`
- Tests: `tests/research/juggler_sequence/test_cycle_error_transport.py`
- Window: \(\mathtt{OE}\) at \(13\); \(\mathtt{OOOEE}\) at \(25\);
  \(\mathtt{OOE}\) at \(365\), \(1517\), \(1000057\);
  \(\mathtt{OOEOOE}\) at \(365\); leftover
  \(\mathtt{OOEOOEOOEOE}\) at first realized \(429\). Fast
  suite only. No CLI. No new Lean. No \(N_0\) raise.

## Conjectures

`juggler_cycle_error_transport` — **REFUTED**.

## Counterexamples

- \(13\xrightarrow{\mathtt{OE}}6\): \(\sum e_i=81+820=901=\Delta\),
  \(X=0\). Falsifier of a residual that is not the global defect.
- \(365\xrightarrow{\mathtt{OOE}}763\): \(E_O/G\approx 2.8\cdot 10^{-4}\),
  Amplify\(/G\approx 2.7\cdot 10^{-4}\), \(X=0\). Falsifier of a
  seam-half that beats \(G\) on an expanding itinerary.
- \(1517\xrightarrow{\mathtt{OOE}}3789\) and
  \(1000057\xrightarrow{\mathtt{OOE}}5623773\): same one-sided
  miss. Falsifier of a scale where the vector catches up.
- \(25\xrightarrow{\mathtt{OOOEE}}15\): first remainder vanishes,
  \(X=0\), \(T<n\). Falsifier of a contracting kill that is not
  `power_bound_contracts`.
- \(365\xrightarrow{\mathtt{OOEOOE}}1749\): \(X>0\) and
  \(E_O/G\approx 0.0046\). Falsifier of a cross term that is
  not the odd-step cubic, and of a two-block half that beats
  \(G\).
- \(429\xrightarrow{\mathtt{OOEOOEOOEOE}}646\):
  \(W=(729,243,243,81,27,27,9,3,3,1,1)\), \(E_E/G\approx 0.70\),
  \(\max e_i/G\approx 0.27\). Falsifier of leftover-shaped
  position weights that are not suffix \(3^{o'}\), and of a
  descent half that exceeds \(G\).

## Formalization

None added. The recurrence is already `accumulatedDefect`.
The suffix lift is already `amplifyDefect`. The first
coordinate is already `firstDefect`. Paper A is unchanged.
Do not add `ErrorTransport.lean`.

## Results

- **Unrolling** — **KNOWN** / **REPARAMETERIZATION**
  (`error_transport/summary.json`): \(\sum e_i+X=\Delta\) on
  every Phase-0 word.
- **Seam halves** — **COMPUTATIONALLY VERIFIED**: no half and
  no single \(e_i\) exceeds \(G\) on an expanding start.
- **Weights** — **REPARAMETERIZATION** of suffix \(3^{o'}\).
- **Cross terms** — **REPARAMETERIZATION** of `accumulateOdd`.
- **Amplify** — **KNOWN**: \(e_j\) at the first positive
  remainder.
- **No new cyclic obstruction.**

## Open questions

None from ordered floor-error transport. Do not reopen
Amplify, finance, defect congruence, peak–valley composition,
or the exponent budget. Do not build a linearized
\(\sum\rho_i W_i\) leftover-killer.

## Decision

**CLOSE**. The reviewer is right that the interesting
arithmetic is ordered, not the total defect. Unrolling the
existing lift produces a vector whose sum plus the cubic
cross is \(\Delta\), whose first positive coordinate is
Amplify, and whose formal weights are suffix \(3^{o'}\).
Seam halves stay below \(G\) on every expanding Phase-0
itinerary, including leftover shape at \(429\). Contracting
words die by \(T_w<n\). That is useful negative knowledge;
it is not a new invariant. No Paper A edit, no ledger row,
no new Lean, no \(N_0\) raise, no finance reopen.

Best next question: none from ordered floor-error transport.

## Publication assessment

Status: `ARCHIVED`. Laboratory negative knowledge on
position-weighted seam-split error transport; not a second
manuscript and not a Paper A edit.

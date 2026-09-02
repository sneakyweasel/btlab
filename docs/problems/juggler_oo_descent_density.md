# Juggler odd-to-odd descent density

Status: **ARCHIVED**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1. It does not reopen discrepancy
transfer, \(\theta\)-state, the 2-adic bridge, residual quotients, or
cycle leftovers.

## Problem

Does any fixed finite certificate family cover almost all odd-to-odd
starts, or is leftover density bounded away from \(0\)?

## Exact statement

Let
\[
\mathrm{OO}=\{n\ge 3:\ n\text{ odd},\ J(n)\text{ odd}\},\qquad
\mathrm{FP}=\{n\ge 2:\ \text{some realized finite itinerary has }J^{|w|}(n)<n\text{ or image }1\}.
\]
`FP` is Lean `FiniteProgress`. The Terras analogue is
\[
\frac{\#(\mathrm{OO}\cap[1,N]\cap\mathrm{FP})}{\#(\mathrm{OO}\cap[1,N])}\to 1
\qquad(N\to\infty).
\]
Phase 0 does not prove that limit. It asks whether any *fixed* finite
family — the contracting itineraries `OOOEE` and `OOEOE`, or first return
in \(\le K\) steps for a fixed \(K\in\{5,10,20,40\}\) — has leftover
\(o(|\mathrm{OO}|)\) as \(N\) runs through \(\{10^4,10^5,10^6\}\).

This is not Corollary 5.2 (density of the complementary short-certificate
class). It is not almost-all arrival at \(1\). A realizing `OOOEE` already
has `FiniteProgress` by `floorPower_oooee_of_follows`; the missing object
is the size of that realizing set inside \(\mathrm{OO}\).

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Terras–Everett almost-all Collatz stopping times — **known**, not a
  theorem about \(J\). Residue-class cylinders do not copy: realizing
  sets need not be intervals, and `odd_preimage_unique` makes odd fibers
  singletons.
- Automatic `E` / `OE` coverage and `unresolved_is_odd_odd` —
  **EXACT — LEAN VERIFIED**.
- \(\lvert\mathrm{OO}(N)-N/4\rvert\ll N^{5/6}\) —
  **EXACT — HUMAN PROOF**. Density of the complementary class, not of
  `FP` on \(\mathrm{OO}\).
- Image-discrepancy transfer —
  **REFUTED** in the tested form. Do not reopen.
- Math-note Proposition 4.4, horizon-\(20\) first return —
  **OBSERVATION**. The \(K=20\) row of this census must reproduce it.
- `power_bound_contracts` / `floorPower_oooee_of_follows` —
  **EXACT — LEAN VERIFIED**. Conditional on a realized itinerary.
- Negative log-log drift —
  **OBSERVATION** / **PARK**. Not a density theorem.

Project relationship: **extended**. The leftover after the short-certificate
density corollary. Totality remains unclaimed.

## Branch budget

```text
Mathematical target     Does any fixed finite certificate family
                        cover almost all of OO, or is leftover
                        density bounded away from 0?
Novelty hypothesis      Either a named contracting itinerary (OOOEE,
                        OOEOE, or a short finite list) has
                        leftover o(|OO|), or a fixed horizon K
                        does; or every fixed family has a
                        positive-density leftover, which kills
                        the Terras cylinder-sum copy
Falsifier               Leftover fraction for every tested fixed
                        family is stable and bounded away from 0;
                        or a density claim is only a rewrite of
                        Corollary 5.2 / Prop 4.5
Existing machinery      FiniteProgress; unresolved_is_odd_odd;
                        power_bound_contracts; wordOOOEE;
                        |OO(N)-N/4| ≪ N^{5/6}; Prop 4.5 table;
                        odd_preimage_unique; REFUTED image transfer
Maximum Phase-0 scope   One CPU probe: densities inside OO for
                        OOOEE, OOEOE, and first-return horizons
                        5, 10, 20, 40, at N in {10^4, 10^5, 10^6}.
                        No Lean, no CUDA, no halt, no length-7
                        cycle work, no discrepancy-transfer reopen
Promotion criterion     A proveable positive-density contracting
                        subclass of OO, or a human-proof that
                        leftover of a named family is o(|OO|)
Stop criterion          Every fixed family has a stable leftover
                        fraction > 0 (CLOSE that attack); or the
                        census only restates Prop 4.5 (CLOSE as
                        reparameterization); machinery gravity
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required. The 2-adic / BT bridge is closed.

## Candidate operations / invariants

- `OO` has density \(1/4\) —
  **EXACT — HUMAN PROOF** (Corollary 5.2); not the target
- realized `OOOEE` implies `FiniteProgress` —
  **EXACT — LEAN VERIFIED**
- leftover of `OOOEE` / `OOEOE` / horizon \(K\) inside `OO` is
  \(o(|\mathrm{OO}|)\) — the Phase-0 question
- almost-all `FiniteProgress` on `OO` — not claimed
- almost-all `ReachesOne` — not claimed
- image-discrepancy transfer — stays **REFUTED**
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.oo_descent_density`
- Records: [juggler_oo_descent_density.md](../research/juggler_oo_descent_density.md),
  [juggler_oo_descent_density.json](../research/juggler_oo_descent_density.json)
- Tests: `tests/research/juggler_sequence/test_oo_descent_density.py`
- The Research Engine control layer is not modified.
- No Lean file. No CUDA. No cycle engine.

## Conjectures

None opened. A leftover plateau is not entered as a conjecture that
almost-all descent fails.

## Counterexamples

- “`OOOEE` covers almost all of \(\mathrm{OO}\)” — leftover rate
  \(0.875\) at \(N=10^6\), stable from \(N=10^4\).
- “The union `OOOEE` \(\cup\) `OOEOE` covers almost all of
  \(\mathrm{OO}\)” — leftover rate \(0.750\) at \(N=10^6\).
- “A fixed horizon \(20\) has leftover \(o(|\mathrm{OO}|)\)” —
  leftover \(26{,}243\) of \(249{,}926\) at \(N=10^6\), rate
  \(0.105\), reproducing Proposition 4.4.
- “A fixed horizon \(40\) has leftover \(o(|\mathrm{OO}|)\)” —
  leftover rate \(0.0239\) at \(N=10^6\), already \(0.0244\) at
  \(N=10^4\).

## Formalization

None added. Existing names used as witnesses only:

- `FiniteProgress` / `unresolved_is_odd_odd`
- `wordOOOEE` / `floorPower_oooee_of_follows`
- `odd_preimage_unique`

`Progress` and `Envelope` are not rewritten. No `sorry`. No halt
theorem. No `FiniteProgress` search tactic. No `no_cycle_itinerary_length_seven`.

## Results

Classification **FIXED_FAMILY_POSITIVE_LEFTOVER**.

See [juggler_oo_descent_density.md](../research/juggler_oo_descent_density.md).
Inside \(\mathrm{OO}\) at \(N=10^6\) (\(\#\mathrm{OO}=249{,}926\)):

- realize `OOOEE`: rate \(0.125\), leftover \(0.875\)
- realize `OOEOE`: rate \(0.125\), leftover \(0.875\)
- word union: rate \(0.250\), leftover \(0.750\)
- first return \(\le 5\): leftover \(0.500\)
- first return \(\le 10\): leftover \(0.250\)
- first return \(\le 20\): leftover \(0.105\) (Proposition 4.4 reproduced)
- first return \(\le 40\): leftover \(0.0239\), already \(0.0244\) at
  \(N=10^4\)

No tested leftover series goes to \(0\). The \(K=20\) row is a
reproduction, not a new observation. The new split is that the shortest
contracting OO-words cover only a quarter of \(\mathrm{OO}\) together,
and that lengthening the fixed horizon from \(20\) to \(40\) leaves a
stable two-percent leftover.

## Open questions

Is there a measure on unbounded Juggler words, weaker than residue
classes, on which contracting itineraries cover almost every OO start?
Do not start that branch here. Do not fish horizons past \(K=40\).

## Decision

**CLOSE**. Every tested fixed family has a stable leftover fraction
bounded away from \(0\). That kills the Terras-style finite-cylinder
copy on \(\mathrm{OO}\). The almost-all `FiniteProgress` question
remains, but it is unbounded-length and has no 2-adic measure. This
census is not a rewrite of Corollary 5.2: that corollary counts the
complementary short-certificate class, not leftover inside \(\mathrm{OO}\).

Best next question: is there a measure on unbounded Juggler words,
weaker than residue classes, on which contracting itineraries cover almost
every OO start?

## Publication assessment

Status: `ARCHIVED`.

A negative density gate: finite itinerary lists and fixed horizons do not
give almost-all descent on \(\mathrm{OO}\). Not a paper theorem and
not a Juggler totality result.

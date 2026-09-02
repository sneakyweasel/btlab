# Juggler global sum-\(\rho\) / word-statistics

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1.

## Problem

After the residual-future CLOSE, the leftover object C is a global
bound on accumulated local floor remainders in
\((n,\text{word statistics})\). Does the *naive* path sum of the
existing \(\rho\) admit such a bound, or is it irreducibly
state-dependent?

Do not invent a new \(\rho\). Do not reopen residual quotients or
PE-factor grammar.

## Exact statement

The existing local remainder is

\[
\rho(x)=
\begin{cases}
x-T(x)^2 & x\text{ even},\\
x^3-T(x)^2 & x\text{ odd}.
\end{cases}
\]

This is `local_defect` / Lean `branchDefect`. For a realized itinerary
\(w\) of length \(k\),

\[
\mathrm{Rho}(w,n)=\sum_{i=0}^{k-1}\rho(x_i)
\]

is Lean `pathDefectSum`. It is **not** the weighted global defect

\[
\Delta_w(n)=n^{3^{\#O(w)}}-T_w(n)^{2^k}.
\]

Phase-0 asks whether any of H1–H4 holds on a stated window, whether
the known path identity is the only telescope, and whether every
useful comparison reduces to \(\Delta\) or \(T_w(n)<n\).

This says nothing about totality.

## Current literature

- Local remainders — **EXACT — LEAN VERIFIED** (`localDefectEven` /
  `Odd`, `branchDefect`).
- Naive path sum `pathDefectSum` and
  `pathPows = pathNextSquares + pathDefectSum` —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.Cycles`.
- Weighted \(\Delta\) recurrence, composition, \(\Delta=0\) rigidity —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.GlobalDefect`.
  Promoted; not reopened as a new object.
- First-defect Amplify — **EXACT — LEAN VERIFIED**. Does not beat
  surplus on expanding `OOE`.
- \(R=\Delta/S\) and forced residual drift —
  **CLOSE** / **REFUTED** as an independent attack
  (`juggler_normalized_defect.md`).
- \(\Delta>\) surplus on expanding mixed prefixes —
  **REFUTED** (equivalent to \(T_w(n)<n\)).
- Residual future-quotient — **CLOSE** as `FUTURE_QUOTIENT_REPACK`.
- PE-factor / word language — **CLOSE** as
  `JUGGLER_LANGUAGE_IS_KNOWN_GRAMMAR`.

Project relationship: **extended** (object C after the residual-state
CLOSE). Totality remains unclaimed.

## Branch budget

```text
Mathematical target     Does pathDefectSum admit an itinerary-statistics
                        bound in (n, k, o, runs) that is not a
                        rewrite of Δ or T_w(n)<n?
Novelty hypothesis      H1–H3 survive, or a new telescope A(x)-A(T(x))
                        controls the sum, or Δ vs Rho is a useful
                        non-circular contraction law.
Falsifier               H1–H3 fail by small exact pairs; the only
                        telescope is the known pathPows identity;
                        H4 reduces to T<n; same (k,o) Rho is
                        state-dependent.
Existing machinery      local_defect, pathDefectSum, globalDefect,
                        powGap, envelope slack, itinerary_word
Maximum Phase-0 scope   n<=4000 itineraries, k<=20 with a bit cap;
                        HARD_PROBES + known PE starts; H1–H4;
                        no GPU, no new atlas table, no Lean, no
                        first-return induction.
Promotion criterion     A bound that is not Δ, not T<n, not 2^k>3^o,
                        and not the known path identity.
Stop criterion          RHO_COMPLEX; another scalar; residual
                        quotient; PE-factor; halt; GPU census.
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- \(\rho=\) `local_defect` — **EXACT — LEAN VERIFIED** (existing)
- \(\mathrm{Rho}=\) `pathDefectSum` — **EXACT — LEAN VERIFIED**
  (existing; not a new \(\rho\))
- \(\mathrm{Rho}(uv,n)=\mathrm{Rho}(u,n)+\mathrm{Rho}(v,T_u(n))\) —
  definition / existing additivity
- \(\mathrm{Rho}=\sum x_i^{e_i}-\sum T(x_i)^2\) —
  **EXACT — LEAN VERIFIED**
- H1 \(\mathrm{Rho}\le F(k,o)\) —
  **REFUTED** (`E` at \(4\) vs \(3968\))
- H2 \(\mathrm{Rho}\le k(2n+1)\) or \(k(2n^3+1)\) —
  **REFUTED** (`OOO` at \(3\) and \(25\))
- H3 run signature determines Rho —
  **REFUTED** (same `E` pair)
- H4 \(\mathrm{Rho}\) vs surplus as a new contraction law —
  **REPARAMETERIZATION** of \(T_w(n)<n\)
- new \(A(x)-A(T(x))\) telescope —
  **REFUTED** for the existing potentials
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.sum_rho`
- Records: [juggler_sum_rho.md](../research/juggler_sum_rho.md),
  [juggler_sum_rho.json](../research/juggler_sum_rho.json)
- Dataset: `data/research/juggler/sum_rho/`
- Tests: `tests/research/juggler_sequence/test_sum_rho.py`

No new census. No `RHO_RECORD` atlas table in Phase-0.

## Conjectures

None opened.

## Counterexamples

- H1 “\(\mathrm{Rho}\le F(k,o)\)”: word `E`, \(n=4\) has \(\mathrm{Rho}=0\);
  \(n=3968\) has \(\mathrm{Rho}=124\).
- H3 “run signature determines Rho”: the same pair; one-letter `E`
  is a single even run.
- H2 “\(\mathrm{Rho}\le k(2n+1)\)”: `OOO` at \(n=3\),
  \(\mathrm{Rho}=41>21\).
- H2 “\(\mathrm{Rho}\le k(2n^3+1)\)”: `OOO` at \(n=25\),
  \(\mathrm{Rho}=97493>93753\).
- Same itinerary, different \(n\): `OOE` has \(\mathrm{Rho}=39\) at \(5\)
  and \(\mathrm{Rho}=6023969\) at \(775\).
- H4 “\(\mathrm{Rho}>|3^o-2^k|\) forces contraction”: both
  directions fail; the surplus comparison reduces to \(T_w(n)<n\).
- New state potential \(A(x)-A(T(x))\): none of \(x\), \(x^2\),
  \(x^3\), \(\rho(x)\) telescopes. The only identity is the existing
  `pathPows = pathNextSquares + pathDefectSum`.

## Formalization

None added. Existing `pathDefectSum` / `globalDefect` stay unchanged.
No `sorry`.

## Results

Classification **RHO_COMPLEX**, with secondary **RHO_COUNTEREXAMPLE**
and **RHO_REPACK**.

On itinerary prefixes \(n\le 4000\), \(k\le 20\) (bit cap \(256\))
plus `HARD_PROBES` and PE starts \(365,1999\), there are \(79553\)
realized \((n,w)\) rows.

- \(\mathrm{Rho}\) is the existing `pathDefectSum`. Composition is
  exact additivity. The path identity holds. \(\Delta\ge\mathrm{Rho}\)
  on the short identity window; length one gives equality.
- H1 fails at \(124\) of \(142\) \((k,o)\) groups. Smallest split:
  `E` at \(4\) versus \(3968\).
- H3 fails at \(1969\) of \(2573\) run-signature groups, same first
  pair.
- H2 scale envelopes fail at `OOO`.
- H4 is the circular rewrite \(\Delta>\mathrm{surplus}\iff T<n\).
  \(\mathrm{Rho}>\Delta\) never occurs on the short \(\Delta\) window.
- No new telescope.

No GPU search, no `RHO_RECORD` table, no Lean, no first-return
induction.

## Open questions

None opened. Do not invent another scalar aggregate. Residual
quotients and PE-factor grammar stay closed.

## Decision

**CLOSE** the sum-\(\rho\) word-statistics attack as `RHO_COMPLEX`.
Accumulated naive remainders stay state-dependent after aggregation.
Every proposed bound has a small exact counterexample, and the only
exact composition/telescope laws were already in
`pathDefectSum` / `globalDefect`. Do not add Lean. Do not claim
termination.

Best next question: none from this branch. Do not start another
scalar energy.

## Publication assessment

Status: `EXPLORATORY`. A negative object-C census, not a paper
candidate and not a Juggler totality result.

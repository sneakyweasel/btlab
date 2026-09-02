# Juggler survival-set inverse mass

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a reopen of
survivor-phase histograms, prefix cylinders, excursion transfer,
backward-geometry rank, preimage cylinders, or the Terras program,
not a new atlas language tag, not an ergodic theorem, not Paper A,
and not a claim that every positive integer reaches 1.

Individual long survivors look generic. This phase measures a
different object: the population \(B_k(N;X)\) of all integers in
a window that stay at least \(N\) for \(k\) steps, and whether
that set contracts under inverse iteration in a way that is not
already even-step `FiniteProgress`.

## Problem

For a fixed anchor \(N\), does the set of integers whose first
\(k\) iterates remain at least \(N\) undergo a genuine global
contraction under repeated Juggler preimages, and can that
contraction be strengthened from a density statement to an
arithmetic statement that excludes a single infinite survivor?

## Exact statement

\[
B_k(N)=\{n\ge N:T^j(n)\ge N\text{ for all }0\le j\le k\},
\qquad
B_k(N;X)=B_k(N)\cap[N,X].
\]

The recursion \(B_{k+1}(N)=[N,\infty)\cap T^{-1}(B_k(N))\) is
exact on unbounded sets. Windowed counts use a forward
\(\tau_N\) census, because \(T(n)\) may leave \([N,X]\).

Phase 0 computes \(S_k=|B_k(N;X)|\), ratios
\(R_k=S_{k+1}/S_k\), densities \(S_k/(X-N+1)\), even/odd
inverse mass, and a few weights \(x^{-\theta}\) on several
anchors and scaled windows.

A density decay is not emptiness. \(\mu(B_\infty)=0\) does not
imply \(B_\infty=\varnothing\). Absence under a bound is
`NOT OBSERVED WITHIN SEARCH BOUND`. This is not a halt theorem.

## Current literature

- Even starts contract —
  **EXACT — LEAN VERIFIED** (`even_itinerary_contracts`)
- Odd-to-even two-step descent —
  **EXACT — LEAN VERIFIED**
- Progress coverage leftover is odd-to-odd —
  **PROMOTE**
  ([juggler_progress_coverage.md](juggler_progress_coverage.md))
- Repeated inversion adds no extra rank —
  **CLOSE**
  ([juggler_backward_geometry.md](juggler_backward_geometry.md))
- One-word cylinders —
  **CLOSE** as `ANCHOR_CYLINDER_CLOSED`
- Survivor rounding phase —
  **CLOSE** as `SURVIVOR_PHASE_CLOSED`
- Excursion transfer —
  **CLOSE** as `EXCURSION_TRANSFER_CLOSED`
- Stopping-time prefix / OEIS A007320 — **known**; totality
  is not claimed
- Cube cell without a square cell — a **separate** leftover
- Every start reaches 1 — not claimed

Project relationship: **extended**. The designated
population-level diagnostic after the local/mesoscopic closes.

## Branch budget

```text
Mathematical target     For several N and scaled X, does
                        S_{k+1}/S_k admit a stable rho<1
                        (or a weighted mu) that is not the
                        even leak, and that can become an
                        arithmetic emptiness statement?
Novelty hypothesis      The survivor population cannot
                        sustain itself under T^{-1} even
                        though individuals look generic.
Falsifier               R_k -> 1 or exceeds 1 after scaling;
                        density grows with X; only even
                        FiniteProgress leaks; weights fail;
                        core stays macroscopic.
Existing machinery      floor_power; even_preimage; pred_odd;
                        even_itinerary_contracts; progress
                        coverage; stopping_times
Maximum Phase-0 scope   Forward tau_N census; several N;
                        X,2X,4X; even/odd inverse mass;
                        three weights; no Lean, no invariant
                        measure, no Terras reopen.
Promotion criterion     Uniform rho<1, or a finite core,
                        not equivalent to even contraction.
Stop criterion          Scale artefact; only density; only
                        the even leak; no route to emptiness.
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- \(B_{k+1}=[N,\infty)\cap T^{-1}(B_k)\) —
  **KNOWN** as set algebra
- Even leak \(n<N^2\Rightarrow T(n)<N\) —
  **EXACT — LEAN VERIFIED** (`even_itinerary_contracts`);
  this is exactly \(S_0-S_1\) at every tested \((N,X)\)
- Uniform \(\rho<1\) inverse contraction —
  **REFUTED** at the Phase-0 windows (\(R_k\) after the
  first step is not bounded by a stable \(\rho<0.95\);
  late \(R\) rises toward \(1\) as \(X\) grows)
- Finite survivor core —
  **REFUTED** as a window-independent statement:
  \(|B_{40}(2;X)|\) grows with \(X\)
- Density of \(B_k\) as \(X\) scales —
  **OBSERVATION**: \(S_k/X\) increases with \(X\) at
  many depths (finite-window decay is not asymptotic)
- Global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.survival_set`
- Records: [juggler_survival_set.md](../research/juggler_survival_set.md),
  [juggler_survival_set.json](../research/juggler_survival_set.json)
- Dataset: `data/research/juggler/survival_sets/`
- Tests: `tests/research/juggler_sequence/test_survival_set.py`

Science window: anchors \(2,3,5,10,50,100,1000\); windows
\(5\cdot 10^5,10^6,2\cdot 10^6,4\cdot 10^6\); \(k\le 40\).
Tests use \(X\le 160\), \(k\le 12\). No CLI. No Lean.

## Conjectures

None opened.

## Counterexamples

- “\(S_1=S_0\cdot\rho\) for a new \(\rho\).” False:
  \(S_0-S_1\) equals the even count in \([N,\min(X,N^2))\),
  already `even_itinerary_contracts`.
- “\(R_k\le\rho<1\) uniformly in \(k\) and \(X\).” False:
  late ratios sit near \(0.91\)–\(0.93\) and rise with
  \(X\) (e.g. \(N=2\): \(0.913\to 0.924\)).
- “\(S_k/X\) is nonincreasing in \(X\).” False: density
  grows with \(X\) at many depths for every tested \(N\).
- “\(B_{40}(N;X)\) is a finite core independent of \(X\).”
  False: \(|B_{40}(2;4\cdot 10^6)|=183380\), about
  \(4.5\) times \(|B_{40}(2;5\cdot 10^5)|\).
- “Windowed \(P([N,X])\) is odd-dominated.” False:
  \(P_E\sim X/2\) and \(P_O\sim X^{2/3}\).

## Formalization

None added. Existing `even_itinerary_contracts` and even/odd
cells already contain the identities. No `SurvivalSet.lean`.
No `sorry`. Paper A is unchanged.

## Results

Classification **SURVIVAL_SET_CLOSED**.

Science window: anchors \(2,3,5,10,50,100,1000\), windows
\(5\cdot 10^5\)–\(4\cdot 10^6\), \(k\le 40\)
(`COMPUTATIONALLY VERIFIED` as a bounded observation;
density is not emptiness):

- \(S_1=S_0-\#\{\text{evens }n\in[N,X]:n<N^2\}\) at every
  pair. The first leak is `even_itinerary_contracts`.
- No uniform \(\rho<1\). Late \(R_k\) is \(0.91\)–\(0.93\)
  and increases with \(X\).
- \(S_k/X\) grows with \(X\) at many \(k\) (Falsifier A
  for a window-free exponential).
- Windowed inverse mass of \([N,X]\): even branch
  \(\sim X/2\), odd branch \(\sim X^{2/3}\). The even
  preimages live near scale \(X^2\) and only the slice
  \(n\ge N^2\) stays in the window.
- \(|B_{40}(2;4\cdot 10^6)|=183380\). The depth-\(40\)
  set scales up, not down to a finite core.

This is the even-leak reparameterization and the
scale-artefact falsifier. User PARK labels “only density
/ generic branching / no route to emptiness” are this
close.

## Open questions

None from windowed inverse mass at this scope. Do not
upgrade \(S_k/X\to 0\) to \(B_\infty=\varnothing\). Do
not add `SurvivalSet.lean`. The leftover residual is
still the cube cell without a square cell.

## Decision

**CLOSE**. The only exact first-step contraction is the
already-proved even cut \(n<N^2\). Later ratios are not
a stable \(\rho<1\). Densities grow when the window
grows. A density statement cannot be promoted to
arithmetic emptiness. A branch whose new statements are
`KNOWN` or `REPARAMETERIZATION` is a close.

Best next question: none from survival-set inverse mass.
The leftover hole is still a cube cell without a square
cell.

## Publication assessment

Status: `EXPLORATORY`. A bounded population census, not a paper
candidate and not a Juggler totality result.

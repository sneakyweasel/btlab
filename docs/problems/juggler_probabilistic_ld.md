# Juggler exact paths versus 2025 large-deviation geometry

Status: **EXPLORATORY**

Standalone comparison of exact Juggler trajectories with the
Prasad–Prasad 2025 juggler-like random-walk / large-deviation model.
It is **not** a Research Engine control-layer experiment, not a
reproduction of the paper, and not a claim that every positive
integer reaches 1.

The previous drift census `juggler_probabilistic` remains
`STATISTICAL_ONLY` / `PARK`. This dossier is the geometry-comparison
phase of the same literature object, not a reopen of any closed
Atlas branch.

## Problem

Do the hardest exact Juggler trajectories follow the large-deviation
optimizer of the 2025 random-walk model, and do the deviations have
deterministic arithmetic structure?

## Exact statement

Write `J` for the even/odd floor-power map. For an exact trajectory
`x_0=n`, `x_{i+1}=J(x_i)`, set `L_i=log log x_i` when defined,
`Z_i=L_i/log n`, `t_i=i/log n`. From the M0 model derive
`p^*=3/4`, `a^*=(3/4)log 3-log 2`, `ρ^*=1`, `γ=1/I_Ber(log 2/log 3)`.
On `n<=4000` exact first-return walks, stored records, and selected
`n<=10^5` leftovers, compare observed `(t,Z)`, pre-peak slope,
odd frequency, duration tail, and increment law with those
predictors. Exceptional membership uses the a priori cuts
`max|Z-Z_model|>0.20` or `|p_O(pre-peak)-3/4|>0.25` on paths with
at least 8 pre-peak steps.

A model tail is not `H<∞`. Agreement is not a theorem.

## Current literature

- Prasad–Prasad 2025 (`prasad-prasad-2025-juggler-like`) —
  random-walk / large-deviation estimates for juggler-like maps.
  **known**, reconstructed in
  [juggler_probabilistic_model.md](../research/juggler_probabilistic_model.md).
  Not a theorem on exact `J`.
- Previous laboratory census
  [juggler_probabilistic.md](../research/juggler_probabilistic.md) —
  **OBSERVATION** of negative mixed-parity drift; **PARK** as
  `STATISTICAL_ONLY`.
- OEIS A007320 (`oeis-A007320`) — step counts. **known**.
- `power_bound_contracts`, `floorPower_odd_ge` —
  **EXACT — LEAN VERIFIED**.
- PE / residual-future / summed-rho / realization-set /
  landing-image / finite-itinerary `N_w` / first-return laws /
  adversarial paths / information-complexity / backward cells /
  acceleration / floor-boundary / 2-adic bridge / cell-hut —
  **CLOSE** or **PARK**. Do not reopen.

Project relationship: **independent** exact-versus-model comparison.
Totality remains unclaimed.

## Branch budget

```text
Mathematical target     Do exact hardest Juggler paths follow the
                        2025 LD optimizer, and where does exact
                        arithmetic disagree?
Novelty hypothesis      Extremals realize (or systematically miss)
                        (p*, a*, ρ*, γ); deviations have an exact
                        source
Falsifier               Records stay far from the optimizer as log n
                        grows, or exceptions are only long O-runs
Existing machinery      floor_power, first-return walks, stored
                        records, previous increment census
Maximum Phase-0 scope   model reconstruction; n<=4000 exact paths;
                        selected n<=1e5 + stored records; no CUDA
Promotion criterion     Precise agreement plus a named exact
                        constraint on the LD-dangerous regime
Stop criterion          MODEL_ONLY / MODEL_REFUTED with no new exact
                        family; machinery gravity; halt claim
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required. The 2-adic / BT bridge is closed.

## Candidate operations / invariants

- `L = log log x` as a new energy —
  not used; diagnostic / chart coordinate only
- M0 iid parity —
  **MODEL ASSUMPTION**
- `(p*, a*, ρ*, γ)` as exact J limits —
  not assumed; compared
- Exceptional set has a new residue / word family —
  tested; not promoted
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.probabilistic_ld`
- Model:
  [juggler_probabilistic_model.md](../research/juggler_probabilistic_model.md)
- Records:
  [juggler_probabilistic_vs_exact.md](../research/juggler_probabilistic_vs_exact.md),
  [juggler_probabilistic_vs_exact.json](../research/juggler_probabilistic_vs_exact.json)
- Dataset: `data/research/juggler/probabilistic/` (`ld_files` in the
  manifest)
- Tests: `tests/research/juggler_sequence/test_probabilistic_ld.py`

No GPU. No new Lean file. No automaton.

## Conjectures

None opened.

## Counterexamples

- `P(O)=1/2` as a trajectory law: orbit-induced frequencies are
  measured separately on ordinary, hard, and record ensembles.
- Even starts as LD witnesses: `H(n)=1` exactly (`LEAN-CERTIFIED`
  even contraction).
- Finite-n `Z_peak → 1`: the predictor `1 + log log n / log n` is
  an asymptotic cartoon on this window.

## Formalization

None added. Existing Envelope / Dynamics lemmas stay as they are.
No `sorry`.

## Results

Classification **MODEL_ONLY**.

The random-walk model describes bulk log-log increments, near-iid ordinary parity, and (on the longest delay records) pre-peak odd frequency near p*=3/4. It does not give a stable ascent slope a*, the duration-tail rate is about 2.6 I0 on this window, and the exceptional set is the expanding odd prefix already visible in the itinerary. Descriptive, not proof-producing.

## Open questions

None from this branch as an automatic sequel. Do not reopen closed
symbolic-compression branches. Do not launch CUDA Phase 2.

## Decision

**CLOSE**. The random-walk model describes bulk log-log increments, near-iid ordinary parity, and (on the longest delay records) pre-peak odd frequency near p*=3/4. It does not give a stable ascent slope a*, the duration-tail rate is about 2.6 I0 on this window, and the exceptional set is the expanding odd prefix already visible in the itinerary. Descriptive, not proof-producing. Do not claim termination.

Best next question: none from this branch.

## Publication assessment

Status: `EXPLORATORY`. An exact-versus-model comparison of trajectory
geometry, not a paper candidate and not a Juggler totality result.

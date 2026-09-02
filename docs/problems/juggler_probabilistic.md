# Juggler probabilistic drift and large-deviation frontier

Status: **EXPLORATORY**

Standalone statistical layer on the exact Juggler floor-power map. It
is **not** a Research Engine control-layer experiment, not a reopen of
any closed symbolic-compression branch, and not a claim that every
positive integer reaches 1.

## Problem

Does the exact Juggler map possess a robust large-scale statistical
law for the diagnostic coordinate `L = log log x`, and do the
finite trajectories that violate a baseline stochastic model have
an exact arithmetic description that could support a later
statistical-plus-exact constraint?

## Exact statement

For `x >= 2` write `J` for the even/odd floor-power map. For
`x >= 16` and `J(x) >= 3` define the diagnostic

    ΔL(x) = log log J(x) − log log x.

`ΔL` is not the dynamics. Phase 0 asks, on `n <= 4000` exact
first-return walks and `n <= 10^5` one-step / leftover-aware walks:

1. whether `E[ΔL]` is negative under mixed-parity ensembles (uniform,
   log-uniform, orbit-induced); odd-only one-step is tautologically
   the `O` increment;
2. whether short history or the listed moduli change that sign;
3. whether `P(H(n) >= k)` admits a reproducible descriptive tail,
   where `H(n)` is the observed first-return-below length;
4. whether the starts with large `H` have a named arithmetic
   structure that is not “a long initial odd run”.

A window tail is not `H < ∞`. Negative drift is not termination.

## Current literature

- OEIS A007320 (`oeis-A007320`) — computational step counts. **known**.
- Tao, almost all Collatz orbits (`tao-2019-almost-all-collatz`) —
  Collatz logarithmic-density theorem. **known**, not imported.
- Prasad–Prasad 2025 juggler-like random-walk preprint
  (`prasad-prasad-2025-juggler-like`) — literature context only.
  **known**, not a theorem on exact `J`.
- Phase-12 parity-drift block lemmas (`OOOEE`, `EE`) —
  **EXACT — LEAN VERIFIED** as conditional word laws, not a
  statistical law.
- `power_bound_contracts`, `floorPower_odd_ge` —
  **EXACT — LEAN VERIFIED**.
- PE / residual-future / residual projections / summed-rho /
  realization-set / landing-image / finite-itinerary `N_w` / first-return
  structural laws / adversarial paths / information-complexity /
  backward cells / acceleration / floor-boundary / 2-adic bridge —
  **CLOSE**. Do not reopen.

Project relationship: **independent** statistical reading of exact
`J`. Totality remains unclaimed.

## Branch budget

```text
Mathematical target     Does exact J have a robust large-scale
                        log-log drift, and do model-violating finite
                        paths have exact arithmetic structure?
Novelty hypothesis      A Juggler-specific increment law, not a
                        copied Collatz random walk, plus a named
                        exceptional set
Falsifier               Drift sign depends on the ensemble; exceptions
                        are only long O-runs; no stable tail
Existing machinery      floor_power, _walk_returns, first-return
                        records, power_bound_contracts, Phase-12
                        conceptual log-log costs
Maximum Phase-0 scope   n<=4000 exact walks; n<=1e5 one-step and
                        leftover-aware H; M0–M4 comparison; CPU only
Promotion criterion     A named measure with a usable exceptional
                        arithmetic family, or a precise tail that
                        is not a window histogram
Stop criterion          STATISTICAL_ONLY / MODEL_DEPENDENT /
                        PROBABILISTIC_COMPLEX; closed-branch reopen;
                        halt claim; another scalar invariant
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required. The 2-adic / BT bridge is closed.

## Candidate operations / invariants

- `L = log log x` as the dynamics —
  not used; diagnostic only
- `ΔL = branch_term + floor_error` —
  **OBSERVATION** of the floating rewrite; `J` remains exact
- `P(O)=1/2` as a law —
  **REFUTED** as a dynamical assumption; it is a uniform counting identity
- Odd-only one-step drift —
  tautologically `μ_O ≈ log(3/2)`; not a competing `μ_∞`
- Negative large-scale mixed-parity drift —
  **OBSERVATION** on the stated windows
- Exceptional starts form a named arithmetic family —
  **REFUTED** as Phase-0 promotion: they are odd starts with long
  initial `O`-runs
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.probabilistic`
- Records: [juggler_probabilistic.md](../research/juggler_probabilistic.md),
  [juggler_probabilistic.json](../research/juggler_probabilistic.json)
- Dataset: `data/research/juggler/probabilistic/`
- Tests: `tests/research/juggler_sequence/test_probabilistic.py`

No GPU. No new Lean file. No automaton.

## Conjectures

None opened.

## Counterexamples

- `P(O)=P(E)=1/2` as a trajectory law: orbit-induced `P(O)` is measured,
  not assumed.
- Odd-uniform one-step negative drift: every odd start is an `O` step.
- `H<=10` for every `n<=4000`: `n=193` has `H=70`.
- Model `M0` equals exact `H`: even starts have exact `H=1`; the
  additive `L` model does not see that identity.

## Formalization

None added. Existing Envelope / Dynamics lemmas stay as they are.
No `sorry`.

## Results

Classification **STATISTICAL_ONLY**.

Large-scale log-log drift is negative and robust across the named ensembles, and the increment law approaches the branch terms at large bit length. The deterministic exceptional set is odd starts with long initial O-runs: the expanding branch, not a new exact family. The stochastic model does not yield a usable pointwise constraint. Typical contraction is not universal contraction.

## Open questions

None from this branch as an automatic sequel. A later theorem would
need a named measure and a genuine tail inequality. Do not reopen
closed symbolic-compression branches.

## Decision

**PARK**. Large-scale log-log drift is negative and robust across the named ensembles, and the increment law approaches the branch terms at large bit length. The deterministic exceptional set is odd starts with long initial O-runs: the expanding branch, not a new exact family. The stochastic model does not yield a usable pointwise constraint. Typical contraction is not universal contraction. Do not claim termination.

Best next question: none from this branch.

## Publication assessment

Status: `EXPLORATORY`. A statistical census of the exact increment
and the typical-versus-pointwise gap, not a paper candidate and not
a Juggler totality result.

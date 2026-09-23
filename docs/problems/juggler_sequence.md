# Frozen Engine campaign: even/odd floor-power map

Status: **EXPLORATORY**

This is the sixth mathematical campaign on frozen Research Engine v2.3
and the first wildcard after the frontier list. It does **not** claim
that every positive integer reaches 1. The adapter is a thin
one-variable spec with `affine_system=None`. There is no radical
attack and no new flood attack.

CLI is not required. Tests invoke `ResearchLoop` and
`StrategyPlanner` in-process.

## Problem

On the stored even/odd floor-power map, does frozen v2.3 diagnose a
regime distinct from residue-affine control and from divisor-sum
iteration, without a new radical attack and without claiming that
every positive seed reaches 1?

## Exact statement

On the stored packet `juggler` (positive integers, dummy control,
identity observation, seed \(13\)), with

\[
T(n)=\lfloor\sqrt{n}\rfloor\quad(n\text{ even}),\qquad
T(n)=\lfloor n^{3/2}\rfloor\quad(n\text{ odd}),
\]

does frozen v2.3 recover a class obstruction relevant to reaching 1,
or only a finite seed closure plus a missing affine cover?

Computational budget (stored packet): 16 planner steps / 32 residual
states; successor undefined when \(n<1\) or the bit length exceeds 512.

## Current literature

- OEIS A007320 (`oeis-A007320`): number of steps for \(n\) to reach 1.
  Computational table. **COMPUTATIONAL**.
- Laboratory aliquot campaign: divisor-sum is outside affine control
  with truncated factorization. **KNOWN**. Comparison cluster, not
  the same map.

Project relationship: **engine diagnosis**. No new number-theory
theorem is claimed.

## Branch budget

```text
Mathematical target     Does frozen v2.3 diagnose the floor-power map
                        as distinct from residue-affine control and
                        from divisor-sum, without a radical attack
                        and without a halt theorem on Z>0?
Novelty hypothesis      A nonlinear integer fingerprint that is not
                        aliquot truncation and not a 5x/4 strip.
Falsifier               Affine cover; new radical attack; seed-13
                        halt billed as a Z-theorem; this is aliquot
                        or the 5x/4 strip.
Existing machinery      One-variable dummy-control spec pattern
                        (SigmaMinusNSpec); unmodified ResearchLoop;
                        StrategyPlanner TERMINATION.
Maximum Phase-0 scope   Thin packet seed 13; prefix probes; live
                        loop; smallest exact Lean identities.
Promotion criterion     An exact class obstruction to reaching 1
                        that is not the definition.
Stop criterion          All KNOWN/REPARAMETERIZATION; new attack;
                        universal halt claim.
```

## Balanced-ternary formulation

None.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- \(T(1)=1\). **EXACT — LEAN VERIFIED** (`floorPower_one`). **KNOWN**.
- \(T(13)=46\). **EXACT — LEAN VERIFIED**. **KNOWN**.
- \(13\mapsto 46\mapsto 6\mapsto 2\mapsto 1\) in four steps.
  **EXACT — LEAN VERIFIED**. **KNOWN**. Not a \(\mathbb Z_{>0}\) theorem.
- Odd \(3\) grows (\(T(3)=5\)). **OBSERVATION**. **REFUTED** as
  global descent.
- No complete piecewise-affine cover on the sample window.
  **OBSERVATION** (`INCONCLUSIVE`). **KNOWN** (floor powers).
- Exact residual closure of the packet seed has size 5.
  **EXACT** (engine `SUPPORTED`). Horizon artefact of seed 13.

## Experiments

- `tests/research/juggler_sequence/test_juggler_sequence.py`
- Runner: `research.juggler_sequence.runner.run_campaign`
- Scout (never imported by spec/adapter/planner):
  `research.juggler_sequence.scout`

## Conjectures

None opened. Whether every positive integer reaches 1 remains
literature-open and is not restated as a project conjecture.

## Counterexamples

- “The map is residue-affine.” **REFUTED**: `affine_system is None`;
  odd branch is a floor power; census `INCONCLUSIVE`.
- “Seed 13 reaching 1 is a theorem on all positive integers.”
  **REFUTED**.
- “The successor is \(\sigma(n)-n\).” **REFUTED**: \(T(13)=46\),
  not \(1\).
- “The successor is the \(5x/4\) strip.” **REFUTED**: \(T(8)=2\),
  not \(10\).
- “Every positive \(n\) decreases.” **REFUTED** at \(n=3\).
- “Progress requires a new radical attack.” **REFUTED**: exact I/O
  is the definition; the frozen stack diagnoses the regime.

## Formalization

Live Lean is `formal/Problems/Juggler/` (barrel
`formal/Problems/Juggler.lean`). Identities `floorPower_one`,
`floorPower_thirteen_step`, `floorPower_thirteen_reaches_one`. The
old `Problems.Engine.FloorPower` stack was deleted in the
layer rewrite. No `sorry`. No ledger row (KNOWN).

## Results

See sections A–L below.

## Open questions

Whether every positive integer reaches 1. A four-step orbit of seed
13 is not that theorem.

## Decision

**CLOSE**. Frozen v2.3 recovered the packet-seed finite closure and
refused a piecewise-affine cover. The identities are elementary.
The fingerprint (`FINITE_SEED_CLOSURE`) is distinct from aliquot
factorization truncation, which answers the board's failure-learning
question without a new attack. All surviving statements are `KNOWN`.
Laboratory decision `CLOSE`. Engine `ResearchDecision` may still be
`CONTINUE`.

Best next question: the unmodified leftover pick on the board after
this ingest. What exact obstruction, if any, can frozen v2.3 produce
there without new attacks? Do not add a radical attack.

## Publication assessment

Status: `EXPLORATORY`. No paper candidate.

---

### A. Blind target specification

What the engine received (`FloorPowerSpec` / `juggler`):

- state space positive integers;
- dummy singleton control;
- identity observation;
- seed \(13\);
- successor the two stored floor formulas;
- budget 16 planner steps / 32 residual states.

No named conjecture or open-problem status in `spec.py` /
`adapter.py` / `planner.py`. Scout is not imported there.

### B. Diagnosis

Memory-free `StrategyPlanner` with goal `TERMINATION` selected
`global_inductive` and returned no attack results (no ranking-function
attack on the frozen stack).

Live `ResearchLoop` on the stored packet:

- `RegimeFingerprint`: `INTEGER_1D`, `SINGLETON`,
  `FINITE_CONTRACTING`, `FINITE_SEED_CLOSURE`, `EXACT_CLOSURE`,
  piecewise-affine `UNCERTAIN`, affine control `UNOBSERVED`.
- `ResearchDecision`: **CONTINUE** — new structural regime with an
  exact certificate (the seed-13 closure). That certificate is not a
  map theorem.

Planner output with empty `ResearchMemory()` was identical to the
memory-free run.

### C. Existing attack results

| Attack | Status |
|--------|--------|
| reconnaissance | OBSERVATION |
| piecewise_affine | INCONCLUSIVE; no complete cover |
| closure | SUPPORTED; size 5 |
| functional | REFUTED |
| separation | SUPPORTED |
| quotient | SUPPORTED |
| parameter_domain / control_word / vector_affine / matrix_word | INAPPLICABLE |

### D. Class analysis

Even integers contract by integer square root (when \(n>1\)). Odd
integers can grow. \(\{1\}\) is a fixed point. Seed 13 enters that
fixed point in four steps. No residue class was found that forces
all orbits to 1.

### E. Scout / blind comparison

| Candidate | Scout | Blind | Classification |
|-----------|-------|-------|----------------|
| seed 13 reaches 1 | yes | independently | **KNOWN** |
| \(T(1)=1\) | yes | independently | **KNOWN** |
| no affine cover | yes | independently | **KNOWN** |
| universal halt | open | not obtained | not yield |
| distinct from aliquot truncation | hypothesized | yes on this seed | **OBSERVATION** |

### F. Invariants and quotients

| Candidate | Status |
|-----------|--------|
| \(T(1)=1\) | **PROVED** / **LEAN_CERTIFIED** |
| seed-13 four-step orbit | **PROVED** / **LEAN_CERTIFIED** |
| residue-affine cover | **not obtained** |
| halt on all positive integers | **not obtained** |

### G. Mathematical yield

```text
known_rediscoveries:     seed-13 orbit; missing affine cover
new_exact_results:       floorPower_one / thirteen_step / thirteen_reaches_one
new_invariants:          none
new_obstructions:        none
new_counterexamples:     T(3)=5; T(8)=2 vs 5x/4; T(13)=46 vs sigma-13
new_conjectures:         none
new_formalizations:      Problems.Engine.FloorPower
potentially_new_mathematics: none
unresolved_questions:    whether every positive integer reaches 1
engineering_changes:     0
representation_novelty:  MEDIUM
mathematical_novelty:    NONE
```

Classification: `KNOWN_REDISCOVERY` plus a `DISTINCT_REGIME`
fingerprint versus aliquot. Not `POTENTIALLY_NEW_THEOREM`.

### H. Failure-memory update

`REPRESENTATION` (no affine cover). Not `GLOBAL_REASONING`: halt on
\(\mathbb Z_{>0}\) is out of scope. Grey loot ids
`juggler:loot:mismatch`, `:seed13`, `:cluster`.

### I. Prior-art reconciliation

OEIS A007320 records step counts to 1. It does not supply a class
obstruction this campaign missed. The laboratory identities are the
packet-seed orbit.

### J. Lean

`Problems.Engine.FloorPower`. Strongest exact theorem:
`floorPower_thirteen_reaches_one`. No `sorry`.

### K. ResearchLoop / StrategyPlanner

Memory ingest did not change flood-planner output. Blind
`StrategyPlanner(TERMINATION)` selected `global_inductive` with
empty results. Next leftover target is selected automatically (no
override). Do not start that leftover in this branch.

### L. Final decision

```text
CLOSE
```

Engine `ResearchDecision` was `CONTINUE`. Laboratory and campaign
close because the finite orbit is KNOWN, there is no affine cover,
and no class forces all seeds to 1. Do not add a radical attack. Do
not claim totality. Do not start the next target automatically.

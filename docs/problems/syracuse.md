# Accelerated odd-only map (Syracuse engine stress test)

Status: **EXPLORATORY**

This module does **not** claim a proof or disproof of the Collatz conjecture.
It is a Research Engine v2 diagnosis benchmark. It does not reopen the parked
application [collatz.md](collatz.md) or the archived shortcut test
[collatz_finite_descent.md](collatz_finite_descent.md).

CLI `btlab research analyze|attack|reproduce|report syracuse`.

## Problem

Can v2 diagnose the structural language of the accelerated odd-only map

\[
S(n)=\frac{3n+1}{2^{v_2(3n+1)}}
\]

on positive odd integers without being told 2-adic structure, and without
claiming a Collatz solution?

## Exact statement

On \(\mathbb{Z}_{>0}^{\mathrm{odd}}\), with dummy control and identity
observation, can v2 discover the latent family \(2^k y=3x+1\) from exact
I/O and certify the arithmetic domain of each parameter without being
told \(v_2\), and without claiming a Collatz solution? Window agreement
is not a map theorem on all odd positives.

## Current literature

- Accelerated \(T\) well-defined on positive odds: ledger `C-T-welldefined`,
  Lean `acceleratedT`. **KNOWN** (engine rediscovery of the definition).
- Parked four-coordinate dictionary: [collatz.md](collatz.md),
  [collatz_mathematics.md](../collatz_mathematics.md). **KNOWN**. The
  novelty hypothesis that BT observables of the realizer \(R\) are
  independent of \(R\) is **REFUTED** (`H_BT_independence`). Do not re-test.
- Shortcut map engine test: [collatz_finite_descent.md](collatz_finite_descent.md)
  **CLOSE**. Different map (parity controls, even states).
- `lagarias-2010-3x+1-survey`: survey of the \(3x+1\) problem. **KNOWN**.
- `terras-1976-stopping-time`: stopping-time density. **KNOWN** heuristic /
  density, not a global proof.
- `tao-2019-almost-all-collatz`: almost all orbits attain almost bounded
  values (logarithmic density). **KNOWN** theorem; not global convergence.
- Cycle-exclusion preprints in `literature/` (`lebel-2026` and related):
  **working paper / unverified claim** unless independently Lean-checked
  here. Not treated as established mathematics.
- Computational verification of the conjecture on large finite ranges is
  **computationally verified range**, never a proof.

Project relationship: engine diagnosis / **engine rediscovery** of
well-definedness and \(S(1)=1\). No new Collatz theorem is claimed.

## Branch budget

```text
Mathematical target     Can v2 diagnose S without Collatz hints, and
                        certify an exact constraint or a precise engine
                        boundary?
Novelty hypothesis      A noncontracting / mixed-magnitude regime with
                        hidden branching, or ENGINE_LIMITATION if v2
                        cannot name the partition.
Falsifier               Adapter seeds v2, residues, cycles, or Lyapunov;
                        imports research.collatz; or a census is billed
                        as a Collatz proof.
Existing machinery      Diagnosis loop; AttackPlanner; Accelerated.lean.
Maximum Phase-0 scope   One integer adapter; generic attacks; Lean of an
                        exact identity the loop actually has.
Promotion criterion     A new reusable exact control language, or a
                        precise engine boundary that justifies later work.
Stop criterion          Machinery gravity; Collatz-solution language;
                        only KNOWN reparameterizations.
```

## Balanced-ternary formulation

None. The adapter uses ordinary integer arithmetic.

## Why BT may be relevant

It is not required. The laboratory question is whether the upgraded
engine loop, which saturated the scalar digit-fold family, recognizes a
genuinely different integer map.

## Candidate operations / invariants

- \(S\) well-defined on positive odds. **EXACT — LEAN VERIFIED**
  (`acceleratedT` / `syracuseS`). **KNOWN**.
- \(S\) preserves oddness. **EXACT — LEAN VERIFIED** (`syracuseS_odd`).
  **KNOWN**.
- \(S(1)=1\). **EXACT — LEAN VERIFIED** (`syracuseS_one`). **KNOWN**
  elementary.
- \(V(n)=n\) strictly decreases. **REFUTED** (\(S(1)=1\), \(S(3)=5\)).
- Odd box \([1,15]\) invariant. **REFUTED** (\(S(11)=17\)).
- \(S(n)<n\) for odd \(n\ge 3\). **REFUTED** (\(S(3)=5\)).
- \(S^2=S\). **REFUTED**.
- Integer \(n\) is a finite residual. **PARKED** (BFS hits the cap).
  Bounded census, not infinitude.
- Sample-supported family \(2^k y = 3x+1\) with several observed \(k\).
  **OBSERVATION**. **KNOWN** as `acceleratedT_mul`.
- Maximal-divisibility conjunction for that family. **OBSERVATION** of
  the map on a window; the integer iff is **EXACT — LEAN VERIFIED** and
  **KNOWN** (`mul_pow_eq_iff_padicValInt`). Presentation \(k=v_2(3x+1)\)
  only after the conjunction is certified. Not a global map theorem.

Do not re-test REFUTED ids `W_commutes_T`, `H_BT_independence`,
`n_star_le_n`, `C-shortcut-one-step-lyapunov`.

## Experiments

- `btlab research analyze|attack|reproduce|report syracuse`
- Adapter tests: `tests/research/syracuse/test_syracuse.py`
- Records: `data/research/collatz/syracuse/`
- Seed 27, state cap 16: closure **INCONCLUSIVE** by design (the seed
  trajectory is longer than the cap). Seed 1 is a finite fixed point and
  is not the benchmark seed.

## Conjectures

None opened. The Collatz conjecture is not a conjecture of this branch.

## Counterexamples

- One-step Lyapunov \(V(n)=n\): \(n=1\) (\(S(1)=1\)).
- Universal contraction for odd \(n\ge 3\): \(n=3\) (\(S(3)=5\)).
- Interval \([1,15]\cap 2\mathbb{Z}+1\): \(S(11)=17\).
- Idempotence: \(S(S(3))=1\neq 5\).

## Formalization

`formal/Problems/Collatz/Syracuse.lean` aliases `acceleratedT`, proves
`syracuseS_one`, specializes the Engine iff as
`syracuseS_parameter_iff`, and applies generic composition as
`syracuse_compose_two`. Thin obstruction instances:
`syracuse_len_one_cycle_dvd`, `syracuse_last_step_remainder`,
`syracuse_cycle_abs_obstruction`. Generic lemmas:
`formal/Problems/Engine/ParameterDomain.lean`,
`formal/Problems/Engine/ControlWord.lean`,
`formal/Problems/Engine/ControlObstruction.lean`. No `sorry`. No ledger row.

## Results

### A. End-to-end pipeline

```text
Diagnosis
  → PiecewiseAffineCensus
  → ParameterDomain
  → ControlWord
  → ControlObstruction
  → Certification
```

Hint-free adapter. No injected \(v_2\), branch table, or affine formula.
Planner order: reconnaissance, piecewise_affine, parameter_domain,
control_word, control_obstruction, then existing attacks. `AttackContext.affine` stays unset.

### B. Syracuse discovery trace

`piecewise_affine` is `OBSERVATION` / `BOUNDED` / `PARAMETERIZED_CENSUS`.
Sample-supported family \(2^k y = 3x+1\) (\(p=3\), \(r=1\), `base=2`)
with observed \(k\in\{1,2,3,4,6\}\) on 32 odd samples (window plus seed
orbit; coverage 1.0; unresolved empty). Status remains
`SUPPORTED_BY_SAMPLES` until domain certification. Not a global branch
theorem. \(k=5\) is absent from this window (first odd witness \(x=53\)
lies outside).

### C. Candidate domains

For each observed \(k\), mere divisibility \(2^k\mid(3x+1)\) is
`NECESSARY_ONLY` / `SAMPLE_SUPPORTED` (higher \(k\) also satisfy it).
Maximal conjunction \(2^k\mid(3x+1)\land 2^{k+1}\nmid(3x+1)\) is
`EXACT` / `LEAN_CERTIFIED` for the **relation**, with presentation
\(k=v_2(3x+1)\) only after that. Overlap 0. Predicate count 5.
Counterexample queries 1994. Globality:
`relation_certified_map_empirical`. Domain completeness:
`window_complete`. Parameter completeness: complete on labeled samples,
not an enumeration of every \(k\in\mathbb{N}\).

### D. Falsification

Failed hypotheses (adapter probes and domain trap):

- \(V(n)=n\) decreases: \(S(1)=1\), \(S(3)=5\).
- Odd box \([1,15]\) invariant: \(S(11)=17\).
- Finite affine table exhausts \(S\): refused (`PARAMETERIZED_CENSUS`).
- Mere \(2^k\mid(3x+1)\) selects parameter \(k\): `NECESSARY_ONLY` on
  every observed \(k\).
- Maximal predicates overlapping: overlap 0 on the falsification window.

No sufficiency counterexample survived for the maximal conjunction.

### E. Exact certificate

`AffineFamilyCertificate` (generic, not a Syracuse-only type):

- family: \(2^k y=3x+1\), observed \(k=(1,2,3,4,6)\)
- domain: maximal divisibility, presentation \(k=v_2(3x+1)\)
- direction: `EXACT` (both necessity and sufficiency of the relation)
- evidence: `LEAN_CERTIFIED` for the integer iff
- soundness: certified (relation)
- completeness / branch validity: window / empirical for the **map**
- Lean: `Problems.Engine.mul_pow_eq_iff_padicValInt`

This is not \(S\) proved on all odd positives, not cycle exclusion, and
not boundedness.

### F. Synthetic genericity

Same pipeline, no Syracuse references in attack sources.

| Target | Family discovery | Parameter | Domain | Soundness | Completeness | Certificate |
|--------|------------------|-----------|--------|-----------|--------------|-------------|
| A congruence | `FINITE_CENSUS` coverage 1 | residues mod 3 | window-exact congruence | window | finite | `COUNTEREXAMPLE_SURVIVED` |
| B sign | `FINITE_CENSUS` coverage 1 | sign | window-exact sign | window | finite | `COUNTEREXAMPLE_SURVIVED` |
| C nested | `FINITE_CENSUS` coverage 1 | four congruences | window-exact | window | finite | `COUNTEREXAMPLE_SURVIVED` |
| D power-clear | `PARAMETERIZED` \(2^k y=x+1\) | \(k=0..5\) | maximal | certified relation | partial (one unresolved) | `LEAN_CERTIFIED` |
| odd-prime \(v_3\) | `PARAMETERIZED` base 3 | \(k=0..3\) | maximal | certified relation | partial | `LEAN_CERTIFIED` |
| mixed residue | `PARAMETERIZED` coverage 0.825 | \(k=0..5\) | mixed then maximal | certified relation | partial | `LEAN_CERTIFIED` |

Trap B (same map D): \(2^k\mid q\) is `NECESSARY_ONLY`. Odd-prime C shows
the machinery is not secretly base 2.

Digit-fold cores remain `SATURATED`. WeightDrift stays excluded.
SignedP0's secondary mod-3 census does not reopen that family.

### G. Lean

Generic: `Problems.Engine.mul_pow_eq_iff_padicValInt`,
`padicValInt_eq_of_mul_pow`, `last_step_remainder`,
`cycle_abs_obstruction`, `dvd_constant_of_dvd_remainder`. Syracuse specialization:
`syracuseS_parameter_iff`, `syracuse_last_step_remainder`,
`syracuse_cycle_abs_obstruction`, `syracuse_dvd_constant_of_dvd_remainder`. Map identity
`acceleratedT_mul` / `syracuseS_mul` already existed. No `sorry`. No
ledger row (KNOWN). The census is not retagged `EXACT — LEAN VERIFIED`.

### H. ResearchLoop

Fingerprint: `INTEGER_1D`, `SINGLETON`, `MIXED_MAGNITUDE`,
`UNBOUNDED_SAMPLE`, piecewise `PARAMETERIZED`, latent `PARAMETERIZED`,
domain `EXACT`, control-word algebra `EXPLOITABLE`, obstruction
`RECURSIVE_INVARIANT`. Nearest digit-fold
record: **HIGH** delta. Core mismatch with the saturated family.
Coverage exercised: finite-closure attempt, contraction, growth,
infinite reachable trajectories, valuation dynamics, modular
restrictions (sampled), quotient, separation, latent piecewise-affine
control, parameter-domain certification, control-word composition,
cycle obstruction, control-obstruction calculus, symbolic multi-step
obstruction, recursive remainder invariant. Inapplicable: branching controls, affine
modular/spectral/block, reverse. Not tested: deferred `symbolic_control`
attack, recursive digit semantics.

Engine `ResearchDecision`:

```text
CONTINUE
```

Reason: latent parameterized family recovered, domain certified,
control-word algebra exploitable, and a recursive remainder invariant
is proved; map globality on \(\mathbb{Z}\) remains
empirical. Prompt vocabulary:
**PARTIALLY_CERTIFIED** (relation exact; map empirical; observed \(k\)
sample-bounded). Not `ENGINE_LIMITATION`. The last-\(0\) elimination
\(D\mid C\Rightarrow D\mid 12\) is **KNOWN** arithmetic, not a Collatz theorem.

### I. ComplexityProfile

Unchanged schema. Seed 27: `control_count=1`,
`max_separation_depth=1`, `closure_status=INCONCLUSIVE`; reachable count
unset (cap). Domain-certification costs are not profile fields; they live
on `AttackResult.evidence` (`predicate_count=5`, `queries=1994`,
`overlap=0`, `census_kind`, `coverage`). The profile cannot express
proof-synthesis cost; that limitation is documented rather than forked.

### J. Prior art

| Class | Item |
|-------|------|
| KNOWN MATHEMATICS | `acceleratedT_mul`; padic valuation iff; composed clearing / cycle equations; Tao density; Terras heuristics |
| ENGINE REDISCOVERY | family \(2^k y=3x+1\), maximal domain, and multi-step composition from I/O; mixed magnitude |
| NEW FORMALIZATION | Engine `mul_pow_eq_iff_padicValInt`, `compose_two_affine`, `last_step_remainder`, `dvd_constant_of_dvd_remainder`; thin `syracuseS_parameter_iff`, `syracuse_compose_two`, `syracuse_last_step_remainder`, `syracuse_dvd_constant_of_dvd_remainder` |
| NEW GENERIC ENGINE CAPABILITY | census plus domain certificates plus control-word composition plus symbolic class obstruction plus recursive remainder invariants |
| POTENTIALLY NEW MATHEMATICS | none claimed |

### K. Branch decision

```text
CONTINUE
```

Dossier mapping: `PARK`. Exact reconstructed latent control is **KNOWN**
clearing. Control-word composition is exploitable; recursive remainder
invariants obstruct an infinite last-\(0\) class with
\(\lvert D\rvert\le\lvert C\rvert\). Modular, reverse, block,
and spectral stay inapplicable in the same pass (no `AffineSystem`
injection). Do not reopen `research.collatz`. The remaining generic
question is higher-length remainder recurrences that are not a
fixed-last constant — not a Collatz solver.

## Open questions

Can a higher-length remainder recurrence yield an invariant that is not
a fixed-last constant, still without injecting an `AffineSystem`
and still without claiming convergence?

## Decision

`PARK`. v2 has crossed observe → infer → certify → compose → constrain
→ obstruct, including a recursive remainder identity for \(m=2\) when
magnitude domination fails. The identities are **KNOWN** arithmetic
rediscovered generically. Map globality, cycles, and boundedness are
not proved. Do not auto-continue. Do not escalate to Collatz.

Best next question: can a higher-length remainder recurrence yield an
invariant that is not a fixed-last constant?

## Publication assessment

Status: `EXPLORATORY`. Not a `PAPER_CANDIDATE` as a Collatz contribution.
The value is the generic reconstruction / certification / composition /
obstruction pipeline.



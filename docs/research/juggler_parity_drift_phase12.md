# Juggler parity-drift Phase-12 falsifier

Status: **PHASE_12_JUGGLER_PARITY_DRIFT_FALSIFIER**

This is not a termination attack, not a divergence theorem, and not a
parity-frequency theorem. Depth is at most `k=5`. Fixed parity itineraries only.
The exact surrogate is `T^k(n)<n` or the floor-power inequalities, never a
floating-point log-log comparison.

## Branch budget

```text
Mathematical target     Can fixed parity blocks be certified as contractive
                        for an exact log-log energy surrogate?
Novelty hypothesis      Mixed odd/even blocks may contract even though odd
                        steps expand, via additive log-log costs.
Falsifier               A realizing frozen OOOEE state with T^5(n)>=n, or
                        a one-step power-bound failure.
Existing machinery      FloorPower, two k=2 lemmas, WINDOW+orbit 13.
Maximum Phase-12 scope  Three pre-ranked words/bounds, depth<=5.
Promotion criterion     Exact non-definitional block inequality with Lean path.
Stop criterion          arbitrary words, k>5, frequency theorem, new energy family.
```

## Metadata

- engine_control_version: `0.2.7`
- source_engine: `v2.3`
- experimental_status: `PHASE_12_JUGGLER_PARITY_DRIFT_FALSIFIER`
- target: `juggler_sequence`
- max depth: `5`
- classification: **PARITY_DRIFT_GREEN_LOOT**
- lean: `PROVED`
- loot: `PARITY_DRIFT_GREEN_LOOT`
- decision reason: OOOEE is exactly contractive and Lean-proved as a conditional block law

Candidate 1 survival is a definitional restatement, not new loot.
Candidate 3 (`EE`) is the shortest negative-drift word; even contraction
is not new loot. `DEFAULT_ATTACK_ORDER` is unchanged.

## Energy model

- Conceptual: conceptual E(n)=log log n; odd +log(3/2), even -log 2
- Exact surrogate: T^k(n)<n for block contraction; T(n)^2<=n^3 (odd) and T(n)^2<=n (even) for one-step increments. No floating-point verdicts.

## Pre-ranked words

| Word | Length | Exact negative | Allowed | C3 |
| --- | --- | --- | --- | --- |
| `EE` | 2 | `True` | `True` | `True` |
| `OEE` | 3 | `True` | `True` | `False` |
| `OOOE` | 4 | `False` | `True` | `False` |
| `OOOEE` | 5 | `True` | `True` | `False` |
| `OOOEEE` | 6 | `True` | `False` | `False` |

Thresholds: odd one-step `n>=3`, even/OOOEE `n>=2`. n>=2 is the exact obstruction n^5<=1 in the OOOEE power chain; n=1 is the odd fixed point; odd expansion uses the existing n>=3 lemma

## Exceptional state

log-log energy is undefined/awkward at 1; T(1)=1. Not a termination theorem.

## Candidate 1: `one_step_increment_bounds` (survived)

- Statement: For odd n>=3, T(n)^2 <= n^3 and T(n)>n. For even n>=2, T(n)^2 <= n and T(n)<n. These are the exact power surrogates of the additive log-log increments.
- Domain: odd n>=3 or even n>=2
- Word: `O|E`
- Idealized drift: odd +log(3/2), even -log 2 (heuristic only)
- Motivation: Ask whether fixed additive branch costs exist as exact inequalities. The power bounds are the floor-power definitions; the signs are the one-step expansion/contraction of the exact surrogate T.
- Checked: 40
- Loot-eligible: `False`

- Note: survived, but the inequality is the floor-power definition or even-branch contraction already implied by T(n)<n. Not new compositional loot.

## Candidate 2: `oooee_conditional_contraction` (survived)

- Statement: If a trajectory follows the parity itinerary OOOEE starting at n>=2, then T^5(n)<n. Conditional on the branch word; not a claim that every orbit contains OOOEE.
- Domain: n>=2 whose five successive branch parities are OOOEE
- Word: `OOOEE`
- Idealized drift: 3^3 < 2^{2+3} (exact negative)
- Motivation: OOOEE is the first mixed block whose idealized drift is negative: 3^3=27 < 2^5=32. Exact surrogate T^5(n)<n.
- Checked: 3
- Loot-eligible: `True`

## Candidate 3: `shortest_negative_block` (survived)

- Statement: If a trajectory follows the parity itinerary EE starting at n>=2, then T^2(n)<n. Selected as the shortest frozen-list word with exact negative idealized drift and depth<=5.
- Domain: n>=2 whose successive branch parities are EE
- Word: `EE`
- Idealized drift: 3^0 < 2^{2+0} (exact negative)
- Motivation: Among EE, OEE, OOOE, OOOEE, OOOEEE, the shortest negative-drift word of depth<=5 is EE. Do not optimize over arbitrary words.
- Checked: 12
- Loot-eligible: `False`

- Note: survived, but the inequality is the floor-power definition or even-branch contraction already implied by T(n)<n. Not new compositional loot.

## Decision

**PARITY_DRIFT_GREEN_LOOT**

OOOEE is exactly contractive and Lean-proved as a conditional block law.

Loot: `PARITY_DRIFT_GREEN_LOOT`. Lean: `PROVED`.
Scope: `LOCAL_BRANCH_LAW`. Not `GLOBAL_TERMINATION`. Level C is out of scope.
`parity_drift_block` is not a production attack.

## Best next question

Do not infer that every orbit contains OOOEE. That is Level C.
The raised proposal is `parity_drift_block` as a target-specific
conditional-block attack, not a halt theorem.

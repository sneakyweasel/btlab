# Juggler prefix-OOO extra scale

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1. It does not reopen the internal-E
bootstrap branch.

## Problem

Do prefix-`OOO` extra scale, or an `OOOOEE` `CycleMin` rotation, exclude
`CycleItinerary` on the two parked leftovers `OOOEOE` and `OOOOEE`?

## Exact statement

On a `CycleMin n` of `OOOEOE` write \(z=T^3(n)\) and
\(y=\lfloor\sqrt{z}\rfloor\). Existing facts give

\[
z\ge(n+1)^2,\qquad
y^2\le z<(y+1)^2,\qquad
y\ge n,\qquad
T(y)<(n+1)^2.
\]

If \(y=n\), then \(n^2\le z<(n+1)^2\) contradicts the `OOO` threshold.
If \(y\ge n+1\), extra scale would mean \(y\ge(n+1)^{4/3}\) strongly
enough that \(T(y)\ge(n+1)^2\). Decide whether `LowerPowerBound` on
`OOO` supplies that uniformly, or only eventually.

`CycleMin` orientations of `OOOOEE` are the six rotations. Starts `E`
and `OE` are already forbidden. A last letter `O` is the last-odd cell
\(n^2\le x^3<(n+1)^2\) against \(x\ge n\).

This says nothing about cycles as `CycleItinerary` ending in `O`. It does
not exclude every length-6 E-terminating word. Do not prove totality.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Internal-E bootstrap —
  **EXACT — LEAN VERIFIED**. `OOOEOE` and `OOOOEE` remain.
- `ooo_suffix_threshold` for \(q\ge 3\) —
  **EXACT — LEAN VERIFIED**.
- Last-even and last-odd cells —
  **EXACT — LEAN VERIFIED**.
- `succ_sq_le_cube` —
  **EXACT — LEAN VERIFIED**.

Project relationship: **extended**. The parked leftover of
`juggler_cycle_internal_e`. Totality remains unclaimed.

## Branch budget

```text
Mathematical target     Do prefix-OOO extra scale, or an OOOOEE CycleMin
                        rotation, exclude CycleItinerary on OOOEOE and OOOOEE?
Novelty hypothesis      T^3(n) ≥ (n+1)^2 plus the even cell of y forces
                        T(y) ≥ (n+1)^2; OOOOEE dies by rotation
Falsifier               y=n is the OOO threshold; leftover is envelope
                        slack; or only a window search
Existing machinery      CycleMin, cycleMin_even_ge_sq, last-even/odd
                        cells, ooo_suffix_threshold, LowerPowerBound,
                        cycleMin_not_odd_even / not_start_even
Maximum Phase-0 scope   Two words only. Exact cell/threshold identities.
                        Lean iff a reusable inequality is proved.
Promotion criterion     Lean exclusion of CycleItinerary on one or both words,
                        or a named extra-scale lemma that is not a rewrite
                        of ooo_suffix_threshold
Stop criterion          Both leftovers are KNOWN/REPARAMETERIZATION;
                        Q0 census; cycle engine; length-6 theorem; halt
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- `y=n` after prefix `OOO` and an internal `E` —
  **EXACT — LEAN VERIFIED**, and a **REPARAMETERIZATION** of
  `ooo_suffix_threshold` plus the even cell
- `CycleMin` cannot end in `O` —
  **EXACT — LEAN VERIFIED**, and a **REPARAMETERIZATION** of
  `cycle_last_odd_interval` plus `succ_sq_le_cube`
- `LowerPowerBound` extra scale from \(n=3\) —
  **REFUTED**
- `OOOOEE` reduces to `CycleMin OOOOEE` —
  **EXACT — HUMAN PROOF** (rotation inventory)
- `CycleItinerary` on `OOOEOE` or `OOOOEE` is impossible — not claimed
- no length-6 E-terminating cycle — not claimed
- cycles ending in `O` as `CycleItinerary` are impossible — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_ooo_scale`
- Records: [juggler_cycle_ooo_scale.md](../research/juggler_cycle_ooo_scale.md),
  [juggler_cycle_ooo_scale.json](../research/juggler_cycle_ooo_scale.json)
- Tests: `tests/research/juggler_sequence/test_cycle_ooo_scale.py`
- The Research Engine control layer is not modified.
- No cycle-state search. No length 7. No O-terminating programme.

## Conjectures

None opened.

## Counterexamples

None to the `y=n` contradiction or to `cycleMin_not_end_odd`. The
stronger claims that fail:

- “`LowerPowerBound` on `OOO` forces \(T(y)\ge(n+1)^2\) from \(n=3\)” —
  the integer comparison fails at \(n=3\) and \(n=5\).
- “`OOOOEE` is excluded by rotation” — the only remaining `CycleMin`
  orientation is `OOOOEE` itself.
- “`y=n` is extra scale” — it is the existing `OOO` threshold.

## Formalization

`formal/Problems/Juggler/Cycles.lean`, a small extension. Added:

- `cycleMin_not_end_odd`
- `wordOOOEOE` / `wordOOOEOE_split`
- `cycleMin_prefix_ooo_even_sqrt_ne`
- `no_cycleMin_ooooeoe_of_sqrt_eq`

`FloorPower`, `Progress`, and `Minimal` are not rewritten. No `sorry`.
No halt theorem. No `no_juggler_cycle`. No `CycleSearch`. No
`no_cycle_itinerary_ooooeoe` / `no_cycle_itinerary_ooooee`. No
`no_cycle_itinerary_length_six`. No `PowerBoundEq` attack. No `PowerHeight`.
No ledger row.

## Results

See [juggler_cycle_ooo_scale.md](../research/juggler_cycle_ooo_scale.md).
Classification **OOO_SCALE_THRESHOLD_ONLY**.

The `y=n` landing is the `OOO` threshold. `CycleMin` cannot end in
`O`. `LowerPowerBound` on `OOO` has `D=2^{38}` and first forced
overshoot at `n=109`; it is not uniform from `n=3`. Neither leftover
`CycleItinerary` is excluded.

## Open questions

Whether every positive integer reaches 1. Extra scale on these two
words is not a new uniform law. Do not open length 7. Do not start
an O-terminating `CycleItinerary` programme.

## Decision

**CLOSE**. The `y=n` identity is `ooo_suffix_threshold` against the
even cell. `cycleMin_not_end_odd` is the last-odd cell plus
`succ_sq_le_cube`. `LowerPowerBound` extra scale is not uniform from
\(n=3\). `OOOOEE` reduces to itself as a `CycleMin` and is not
excluded. A branch whose surviving statements are `KNOWN` or
`REPARAMETERIZATION` is a `CLOSE`. Do not launch Phase 1.

Best next question: write the structure paper (Atlas +
`FiniteProgress` leftover + cycle stack + \(N^{5/6}\)).

A later branch, [juggler_leftover_cycles](juggler_leftover_cycles.md),
excludes both leftover `CycleItinerary`s by a finite evaluation below
\(256\) plus the tail \(n^{81}>2^{130}(n+1)^{64}\). That is not this
branch's uniform-from-\(3\) attack; the `CLOSE` here is unchanged.

## Publication assessment

Status: `ARCHIVED`.

Named corollaries of existing cells, not a paper distinction and not
a Juggler totality result.

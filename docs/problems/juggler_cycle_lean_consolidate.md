# Juggler cycle Lean leftover merge

Status: **STRUCTURAL**

Packaging of theorems that already survived. It is **not** a Research
Engine control-layer experiment and not a claim that every positive
integer reaches 1. It is not a length-8 census, not a new leftover
family, and not a halt theorem.

## Problem

The leftover programme is already one argument: a prefix cell versus
a tail, with two-even, bunched, and first-E as instances, and gapped
`CycleItinerary` as rotation of `CycleMin`. The Lean files were not.

## Exact statement

There is one shared comparison

```text
n^{3^a} ≤ 2^{denomBits a} * z^{2^a}
z < Z
2^{denomBits a} * Z^{2^a} < n^{3^a}
```

recorded as `leftover_prefix_preimage`. Two-even is the instance
`Z = (n+1)^4`. Bunched uses `Z ∈ {(n+1)^8, (n+1)^6, (n+1)^4}` or a
tight last-odd cell. First-E is the same comparison started at
`y = T_{O^a E}(n)` on a `CycleMin`. Gapped `CycleItinerary` is
`exists_cycleMin` plus rotation onto an already-excluded `CycleMin`
class, not a cell instance.

The small-cycle census remains length `≤ 7` only. Existing theorem
names stay. There is no `no_cycle_itinerary_length_eight`, no
`no_cycle_itinerary_bunched`, and no `no_juggler_cycle`.

## Current literature

All instances were already **EXACT — LEAN VERIFIED**:

- two-even leftovers (`no_cycle_itinerary_two_even_ee`, `_eoe`);
- seven bunched last-cluster families;
- first-E gapped `CycleMin`s;
- gapped `CycleItinerary` by rotation;
- named length-6/7 leftovers and the length-`≤7` census.

Project relationship: **reparameterization** of file layout, not of
the mathematics.

## Branch budget

```text
Mathematical target     One leftover-cell-versus-tail lemma, with
                        two-even, bunched, and first-E as instances;
                        gapped CycleItinerary as rotation of CycleMin;
                        census still length ≤7 only
Novelty hypothesis      none — packaging of theorems that already
                        survived
Falsifier               a new family, a length-8 assembler, or
                        no_juggler_cycle
Existing machinery      Cycles, leftover/bunched modules, census
Maximum Phase-0 scope   split the cycle kernel; extract the cell
                        schema; merge infinite leftovers; keep
                        eval tables; update barrels/tests
Promotion criterion     lake build Problems.Juggler and
                        Problems.JugglerPaper; same exclusions;
                        census still ≤7
Stop criterion          new math; halt language; Paper A rewrite
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- `leftover_prefix_preimage` is the shared contradiction.
- `CycleCore` holds `CycleItinerary`, `CycleMin`, `rotateItinerary`, and
  last-even cells.
- `CycleExtrema` holds peak/defect math, off the leftover path.
- `SmallCycleCensus` imports `CycleCore` and `LeftoverShort` only.

## Experiments

None. This branch is Lean packaging.

## Conjectures

None.

## Counterexamples

None. Packaging does not reopen refuted leftover attacks.

## Formalization

- `formal/Problems/Juggler/CycleCore.lean`
- `formal/Problems/Juggler/CycleExtrema.lean`
- `formal/Problems/Juggler/Cycles.lean` (barrel)
- `formal/Problems/Juggler/LeftoverPreimage.lean`
- `formal/Problems/Juggler/LeftoverShort.lean`
- `formal/Problems/Juggler/LeftoverFamilies.lean`
- eval satellites and `BunchedTight.lean` unchanged
- `formal/Problems/Juggler/SmallCycleCensus.lean` still only
  `no_cycle_itinerary_length_le_six` / `_seven`

No `sorry`. Paper A was not edited.

## Results

`leftover_prefix_preimage` is the shared lemma. Two-even, EEE, EOEE,
EOOEE, EEOE, EOEOE, EOOOEE, and EOOEOE `_of_ge` proofs are
instances. First-E and gapped `CycleItinerary` live in the same module
as sections. `ooooooeee` is the `a = 6` EEE instance, not a second
proof in `LeftoverShort`. Census still stops at length 7.

## Open questions

Length 8 remains open as a census. Four-even leftovers remain as
already recorded (`PARK` / `CLOSE`), not as a Lean merge.

## Decision

**PROMOTE** as packaging. The leftover programme is one lemma plus
instances; the files now say that. Same exclusions, same census
bound, no Paper A theorem numbers, no new ledger rows.

Best next question: stop. Rotation and internal-E on the
thirty length-11 leftovers are now `CLOSE`
([length-11 non-pullback](juggler_length11_nonpullback.md)).
That question was already recorded; this packaging branch did
not open it.

## Publication assessment

Status: `STRUCTURAL`.

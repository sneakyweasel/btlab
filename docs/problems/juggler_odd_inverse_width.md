# Juggler odd-inverse width (fan-follower integer hits)

Status: **CLOSE** (the width law is elementary; uniqueness is
`odd_preimage_unique`; the boxed infinite-hit slogan is a quantifier
reversal of a realized odd step)

Not a halt theorem, not a divergence exclusion, not a reopen of
cycle inverse-width, hug-cylinder \(C_L\), odd towers, or
fan-concat. Not a Paper A edit and not a forward parity census.

## Problem

The odd inverse interval has real width \(\Delta x\sim\tfrac23 y^{-1/3}\).
Does uniqueness-plus-shrinking turn an infinite fan-follower into a
new Diophantine demand — infinitely many exact integer hits of
shrinking nonlinear inverse intervals — or is that the recorded
odd-cell and hug-flow law?

## Exact statement

**Width (EXACT — HUMAN PROOF).** The odd fibre of \(y\) sits in
\([y^{2/3},(y+1)^{2/3})\). The mean-value theorem gives
\(\Delta x=\tfrac23\xi^{-1/3}\) for some \(\xi\in(y,y+1)\).

**Uniqueness is not eventual (EXACT — HUMAN PROOF / EXACT — LEAN
VERIFIED).** \(\Delta x<1\) for every \(y\ge 1\): set \(t=y^{1/3}\ge 1\),
then \(2t<3t^2+3\) because \(3t^2-2t+3\) has discriminant \(-32<0\).
The lattice statement is stronger and already Lean: an odd floor
cell contains at most one integer (`odd_preimage_unique`, Paper A
Lemma 3.1). Occupancy is the cube test of `J-odd-pred-empty-cube`.

**Forward hits are tautological (COMPUTATIONALLY VERIFIED on the
named odds; EXACT as a restatement).** If \(x\) is odd and
\(y=T(x)\), then \(x\in I_y\) and \(y\) is Type 2. Named witnesses
\(x\in\{3,37,365,761\}\). An infinite fan-follower, going forward,
therefore produces infinitely many exact hits by construction.

**Backward flow is not starved (OBSERVATION, existing artifact).**
Hug/fan words are `OE`/`OOE`, not long O-runs. Net backward flow
is already positive: `OE` \(+5\lambda/12\) bits, `OOE`
\(+7\lambda/24\) bits. Formal odd-end launch already occurs on
17/44 existing 19-endpoints; realized glue is still zero.

No cycle of any length — not claimed. No divergent orbit — not
claimed.

## Current literature

- Odd cell uniqueness — **EXACT — LEAN VERIFIED**
  (`odd_preimage_unique`, Paper A Lemma 3.1)
- Type 0/1/2 emptiness — **EXACT — HUMAN PROOF**
  (`J-odd-pred-empty-cube`); **PARK** as a forward law
  ([juggler_empty_odd_preimage.md](juggler_empty_odd_preimage.md))
- Inverse-tube width as a leftover-killer — **REFUTED**
  ([juggler_cycle_inverse_width.md](juggler_cycle_inverse_width.md));
  occupied hull of width \(0.221<1\)
- Hug-cylinder O-pullback and positive `OE`/`OOE` flow — **PARK**
  ([juggler_hug_cylinder_construction.md](juggler_hug_cylinder_construction.md))
- Fan-block glue — **PARK**
  ([juggler_flight_fan_concat.md](juggler_flight_fan_concat.md));
  17/44 odd 19-endpoints, zero \(19\to 19\)
- Odd-chain minimality — **CLOSE**
  ([juggler_odd_chain_minimality.md](juggler_odd_chain_minimality.md))
- Odd-landing sets — **CLOSE**; Lean comment: not a
  shrinking-interval calculus

Project relationship: **refuted** as a new obstruction;
**reparameterization** of the recorded cell/flow facts.

## Branch budget

```text
Mathematical target     Is Δx ~ (2/3) y^{-1/3} a new concatenability
                        obstruction for infinite fan-following, or
                        the recorded odd-cell / hug-flow law?
Novelty hypothesis      uniqueness plus shrinking width makes an
                        infinite fan-follower a rigid infinite
                        sequence of exact integer hits, stricter
                        than a forward parity census
Falsifier               width < 1 for all y ≥ 1; uniqueness is
                        odd_preimage_unique; every odd x makes T(x)
                        Type 2; hug/fan words interleave E so net
                        backward flow is already positive
Existing machinery      odd_preimage_unique (Preimages.lean);
                        J-odd-pred-empty-cube; empty_odd_cell
                        Types 0/1/2; hug-cylinder O-pullback
                        ~ (1/3) X^{-1/3} with OE/OOE net positive;
                        cycle_inverse_width REFUTED; fan-concat PARK
Maximum Phase-0 scope   exact width table on a log grid; Type 0/1/2
                        shares vs (2/3)y^{-1/3}; elementary width<1;
                        read existing hug-flow / fan-concat artifacts;
                        no new n-window, no Lean, no Paper A
Promotion criterion     a hit law that is not odd_preimage_unique, not
                        Type 2-from-odd, and not the priced O-pullback
Stop criterion          statements are KNOWN or REPARAMETERIZATION
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Real odd-inverse width \(\tfrac23 y^{-1/3}\) —
  **KNOWN** calculus; MVT ratio \(\to 1\) on \(y=10^k\)
- \(\Delta x<1\) for large \(y\) only —
  **false**; true for every \(y\ge 1\)
- Unique odd predecessor —
  **EXACT — LEAN VERIFIED** (`odd_preimage_unique`)
- Occupied share \(\sim\tfrac23 y^{-1/3}\) —
  **OBSERVATION** on 80-point decade windows and on
  \(y\le 4000\) (Type 0 share \(0.937\))
- Odd step produces Type 2 —
  **KNOWN** (empty-odd-preimage); confirmed on
  \(\{3,37,365,761\}\)
- Infinite exact hits starve a fan-follower —
  **REFUTED** (`juggler_odd_inverse_width`)
- Zero backward branching on hug/fan words —
  **false**; E-regeneration keeps net `OE`/`OOE` flow positive
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.odd_inverse_width`
- Artifact:
  `data/research/juggler/odd_inverse_width/summary.json`
- Tests:
  `tests/research/juggler_sequence/test_odd_inverse_width.py`

Power grid \(y=10^k\) for \(k=0,\ldots,12\); finite width check
\(y\le 10^5\); 80 consecutive \(y\) at each of
\(10^2,\ldots,10^6\); ambient Types on \(y\le 4000\); named odd
hits \(\{3,37,365,761\}\). Hug-flow and fan-concat artifacts are
read, not rerun. No CLI. No Lean. No \(n_{\max}\) raise.

## Conjectures

- `juggler_odd_inverse_width` — **REFUTED**.

## Counterexamples

- “Width \(<1\) only for large \(y\)” — \(y=1\) already has
  width \(2^{2/3}-1\approx 0.587<1\).
- “Width \(<1\) empties the cell” — \(9\xrightarrow{\mathrm{OOE}}11\)
  occupies a hull of width \(0.221\) (archived inverse-width
  falsifier); \(y=1\) is occupied.
- “An infinite O-using orbit needs a new hit law” — every odd
  \(x\) makes \(T(x)\) Type 2 with occupant \(x\).
- “Zero backward branching starves hug/fan words” — existing
  hug-flow ledger is net positive per `OE`/`OOE` block; 17/44
  19-endpoints are already odd.

## Formalization

None new. `odd_preimage_unique` stays in `Preimages.lean`. No
`OddInverseWidth.lean`. Paper A is unchanged. No `sorry`.

## Results

Classification **ODD_INVERSE_WIDTH_REPARAMETERIZATION**.

- Power-grid widths match \(\tfrac23 y^{-1/3}\) (ratio
  \(0.881\) at \(y=1\), then \(1-O(1/y)\)); occupant count is
  \(0\) or \(1\); no multi occupancy.
- Elementary certificate and the scan \(y\le 10^5\) both give
  width \(<1\) universally. Maximum width is at \(y=1\).
- Decade occupied shares sit next to the local prediction
  (\(0.125\) vs \(0.128\) at \(10^2\); \(0.025\) vs \(0.031\)
  at \(10^4\)). Ambient Type 0 share on \(y\le 4000\) is
  \(0.937\), with Type 1 and Type 2 equal (\(126\) each).
- Named odd steps are Type 2 self-preimages.
- Hug-flow artifact still reports `HUG_FLOW_CONFIRMED` and
  positive `OE`/`OOE` bits; fan-concat still has \(17/44\)
  odd 19-endpoints and zero glue.

## Open questions

None from inverse width. Do not reopen cycle inverse-width,
hug-cylinder \(C_L\), odd towers, or a new \(n\)-window for
fan-concat. The fan-follower stays a coherent surviving
failure mode; this door does not kill it and does not
construct it.

## Decision

**CLOSE.** The width formula is the known MVT expansion of
the odd cell. Uniqueness holds for every \(y\ge 1\) and is
already Lean. The boxed infinite-hit slogan, read forward, is
the definition of a realized odd letter; read backward, it is
the priced O-pullback whose net `OE`/`OOE` flow is positive.
Every Phase-0 statement is `KNOWN` or `REPARAMETERIZATION`.
That is the stop criterion. Best next question: none from
this door; the fan-follower is not owed another cell census.

## Publication assessment

Status: `EXPLORATORY`. A calibration and a slogan refutation.
Not a paper candidate. No Paper A/B edit. No flight-note rewrite.

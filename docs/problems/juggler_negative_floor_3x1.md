# The 3x-1 verification floor

Status: **PROMOTE** (the floor is supplied; the mirror's period bound
becomes a statement)

Standalone computational phase on the Collatz bridge. Not a halt theorem
for either map, not a Juggler cycle exclusion, and not a change to
\(N_0\).

## Problem

`J-negative-cycle-finance-is-the-juggler-mirror` gave a conditional
table. Its missing input was a verification floor for the \(3x-1\) map,
which the laboratory searched for and did not find in the literature, and
which the journal named as the branch's best next question. Supply it.

## Exact statement

Let \(g(y)=y/2\) for even \(y\) and \((3y-1)/2\) for odd \(y\) on
\(\mathbb Z_{>0}\); its cycles are \(1\), the triple \(5,7,10\), and the
eleven-element cycle at \(17\). Verify that every \(1\le y<2^{38}\)
reaches one of those three. Then read the kernel-checked
`neg_cycle_finance`, \(2(|x|-1)(3^o-2^K)\le (K-o)3^o\) at a negative
cycle's least \(|x|\), at that floor, and report the least period a
fourth cycle could have.

## Current literature

- `hercher-2023-collatz-m-cycles`, `eliahou-1993-collatz-cycle-lengths` and the
  positive-side period bounds. **known**; the positive side is
  reproduced, not extended, by
  [collatz_finance_mirror](juggler_collatz_finance_mirror.md).
- No published verification floor for \(3x-1\) was found by the
  recorded search — OEIS text records, Roosendaal's index, Lagarias's
  bibliography, Chamberland section 6.1 — which is not the same as none
  existing. **independent**: the floor here is the laboratory's own
  computation.
- `neg_cycle_finance`, `neg_cycle_word_is_juggler_shape` in
  `Problems/Juggler/CollatzBridge.lean`. **EXACT — LEAN VERIFIED**; the
  implication from floor to period is theirs, and only the floor is
  empirical.

Project relationship: **independent**.

## Branch budget

```text
Mathematical target     Supply a verification floor for 3x-1 and convert the
                        conditional mirror table into an unconditional period
                        bound for a fourth negative cycle.
Novelty hypothesis      The floor is reachable by an ordinary descent verifier
                        and no published one exists to import.
Falsifier               A fourth cycle inside the range, or a start that does
                        not descend within the step cap.
Already killed by?      No. The finance mirror is PROMOTE and explicitly asks
                        for this input; nothing in negative_knowledge.md forbids
                        a verification floor, and this is not N_0, not Baker,
                        and not a local attack.
Existing machinery      negative_cycle_survivors, lambda_juggler,
                        three_gap_walk, neg_cycle_finance.
Maximum Phase-0 scope   One C verifier, chunked, archived beside the summary;
                        a Python reference on a small window; the bound read off
                        the laboratory's own finance walk.
Promotion criterion     A clean certificate tiling an interval to a stated floor,
                        agreeing with an independent reference rule.
Stop criterion          Any failure or any new cycle in range.
```

## Balanced-ternary formulation

None required. Integer arithmetic on \(\mathbb Z_{>0}\).

## Why BT may be relevant

It is not.

## Candidate operations / invariants

- ascending-induction descent verification of \(g\) —
  **COMPUTATIONALLY VERIFIED** to \(2^{40}\)
- the descent rule agrees with full iteration to a cycle element —
  **COMPUTATIONALLY VERIFIED** on \(y<300000\)
- floor \(\Rightarrow\) period bound through `neg_cycle_finance` —
  **EXACT — LEAN VERIFIED**

## Experiments

`python -m research.juggler_sequence.negative_floor_3x1` writes
`data/research/juggler/negative_floor_3x1/summary.json`,
`chunks.json`, and
[juggler_negative_floor_3x1.md](../research/juggler_negative_floor_3x1.md).
The verifier source is archived as `verify_3x1.c` beside them and the
probe can recompile and re-run it on any window. The committed
certificate is 8 chunks of \(2^{35}\) tiling \([3,2^{38})\).

## Conjectures

None.

## Counterexamples

None. Zero failures, zero new cycles, greatest step count 544 against a
cap of 4000 — so no orbit in range came within an order of magnitude of
the cap, which is what would flag a cycle whose least element exceeds the
start being tested.

## Formalization

No new Lean module. The implication is already `neg_cycle_finance`; a
verification floor is not a Lean object.

## Results

- **Every \(1\le y<2^{38}=274877906944\) reaches \(1\), \(5\) or
  \(17\).** 549755813864 odd starts, 16 disjoint chunks, 0 failures, 0 new
  cycles, greatest step count 544, greatest excursion
  \(2.61\cdot10^{23}\) in an `unsigned __int128` state, so the width
  mattered — the excursion leaves 64 bits — and overflow was never near.
- **A fourth cycle of the \(3x-1\) shortcut map has period at least
  \(9538065\)**, with \(6017849\) odd steps. Equivalently a fourth
  negative cycle of shortcut \(3x+1\), whose word is a Paper A CycleMin
  shape letter for letter. At \(10^{11}\) the number is \(1988215\); at
  \(2^{40}\), which is about 45 further core-minutes, it would be
  \(9538065\).
- The two verification rules agree: descent and full iteration give the
  same verdict on every odd \(y<300000\).

## Open questions

Pushing the floor. \(2^{40}\) is minutes; \(2^{60}\) and \(2^{68}\) —
the latter giving the \(72448885240\) of the conditional table — need
sieved GPU verification and are a separate project.

## Decision

**PROMOTE**. The branch does exactly what the journal asked: the table
entry becomes a statement. The floor is a computation and is labelled as
one; the implication it feeds is kernel-checked. Nothing about the
Juggler moves — this is a Collatz-side input that the Juggler's own
finance inequality converts.

Best next question: the \(2^{40}\) floor, then a sieved verifier.

## Publication assessment

Status: `STRUCTURAL`. A computational certificate plus a one-line
implication; it belongs with the finance mirror, not in a manuscript of
its own.

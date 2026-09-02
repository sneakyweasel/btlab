# Juggler first-intersection \(E^r\) block

Status: **ARCHIVED**

Directed follow-up of
[juggler_cycle_intersection_taxonomy.md](juggler_cycle_intersection_taxonomy.md),
not a reopen of the eight-case table, the OE corridor, or the
cyclic seam, and not a new paper. After peak intersection collapsed
to the archived \(\mathtt{OE}\) slice, this phase asks whether the
remaining even channel, parameterized by the length \(r\) of the
common even suffix, produces a two-sided envelope that is not
trailing-evens or the expanding-prefix test.

Not a halt theorem, not a finance leftover-killer, not a corridor
reopen, and not a claim that every cycle has a distinguished
entry valley.

## Problem

Determinism pushes an odd-run first meeting to its peak and an
even-run first meeting to the next valley. The leftover invariant
is the length \(r\) of the common \(E^r\) block. Does
\(\mathtt{O}\,E^r\,\mathtt{O}\) then empty for \(r\ge 2\), or is
that comparison already on the ledger?

## Exact statement

**Odd-run interiors push to the peak
(KNOWN / EXACT — LEAN VERIFIED).**
A first meeting strictly inside an odd run is not first:
`odd_preimage_unique` / `oddLanding_preimage_unique`. The future after
the unique odd parent is shared, so the canonical cut is the peak.

**Even-run interiors push to the next valley, keeping \(r\)
(KNOWN).**
After the first shared even state the two trajectories coincide, so
the remaining even letters are a common suffix of length \(r\). The
object is the block \(\mathtt{O}\,E^r\,\mathtt{O}\), not a free
interior point.

**The exact integer envelope
(KNOWN / REPARAMETERIZATION).**
Nested floor-square-root is the interval
\[
v^{2^r}\le p<(v+1)^{2^r}.
\]
The unique odd parent of \(p\) sits in the outer cube cell
\[
v^{2^{r+1}}\le u^3<(v+1)^{2^{r+1}}.
\]
This is `cycle_trailing_evens_lt` plus `odd_preimage_unique`.

**Type I at \(r=1\) is the archived corridor
(KNOWN / REPARAMETERIZATION).**
For \(v=n\),
\[
n^4\le u^3<(n+1)^4,
\]
and last-even-not-square makes the left inequality strict. That is
`corridor_bounds`. Do not reopen it.

**A first block \(\mathtt{O}^{a_0}E^r\) is CycleMin-possible only
if it expands
(KNOWN / REPARAMETERIZATION).**
The climb envelope \(p^{2^{a_0}}\le n^{3^{a_0}}\) and the scale
barrier \(p\ge n^{2^r}\) combine to
\[
2^{a_0+r}\le 3^{a_0}.
\]
So \(a_0\in\{2,3\}\) forbids \(r\ge 2\); \(a_0=4\) allows \(r=2\);
\(a_0=5\) forbids \(r=3\); \(a_0=6\) allows \(r=3\). This is
`power_bound_word` plus `even_run_scale_barrier`.

**Last-run \(r\ge 2\) is occupied
(KNOWN / COMPUTATIONALLY VERIFIED).**
Trailing \(\mathtt{EE}\) has count \(n(n^2+n+1)\). Trailing
\(\mathtt{EEE}\) is realized. The even channel is not a thin
corridor and is not empty.

**A short climb can realize \(r\ge 2\) only by leaving the
CycleMin tube
(COMPUTATIONALLY VERIFIED).**
On \([13,2001)\), \(252\) OO-launches have first even-run length
\(\ge 2\). The first is \(25\xrightarrow{\mathtt{OOOEE}}15\),
which fails \(2^{5}\le 3^{3}\) and drops below the start. The first
CycleMin-shaped \(r=2\) is \(115\) (\(a_0=5\), valley \(8165\)).
Local \(r\ge 2\) occurs; it does not empty.

No cycle of any length — not claimed.

## Current literature

- Unique odd cell —
  **EXACT — LEAN VERIFIED**
  (`odd_preimage_unique`, `oddLanding_preimage_unique`)
- Trailing-evens cell \(T_v(n)<(n+1)^{2^r}\) —
  **EXACT — LEAN VERIFIED**
  (`cycle_trailing_evens_lt`)
- Even-run scale barrier —
  **EXACT — LEAN VERIFIED**
  (`even_run_scale_barrier`)
- Word power envelope —
  **EXACT — LEAN VERIFIED**
  (`power_bound_word`)
- Isolated-E last run \(\mathtt{OE}\); trailing \(\mathtt{EE}\)
  of size \(n(n^2+n+1)\) —
  **CLOSE** / not a leftover-killer
  ([juggler_cycle_entry_corridor.md](juggler_cycle_entry_corridor.md))
- First-intersection taxonomy —
  **CLOSE** / **REPARAMETERIZATION**
  ([juggler_cycle_intersection_taxonomy.md](juggler_cycle_intersection_taxonomy.md))
- Collatz-style financing —
  **known** (`simons-de-weger-2005-collatz-m-cycles`)
- Every start reaches 1 — not claimed

Project relationship: **refuted** as an \(E^r\) leftover
obstruction; the envelopes are **REPARAMETERIZATION**s of
trailing-evens and the expanding-prefix test.

## Branch budget

```text
Mathematical target     Can a CycleMin initial climb meet the cycle
                        across an E^r block for r>=2, after odd
                        interiors push to the peak and r=1 is the
                        archived OE seam?
Novelty hypothesis      the r-parameter of the common even suffix
                        gives a two-sided O E^r O envelope that is
                        not trailing-evens / the expanding-prefix
                        test / the OE corridor
Falsifier               r=1 recovers n^4 <= u^3 < (n+1)^4; first-run
                        r vs a0 is 2^{a0+r} <= 3^{a0}; last-run
                        r>=2 is the occupied EE/EEE family
Existing machinery      odd_preimage_unique; cycle_trailing_evens_lt;
                        even_run_scale_barrier; power_bound_word;
                        ee_entry_count; corridor_bounds; eee_witness
Maximum Phase-0 scope   exact O E^r O cells; r=1 corridor recovery;
                        a0/r compatibility; last-run occupancy; a
                        cheap realized first-run window. No Lean,
                        no finance, no census engine
Promotion criterion     an r>=2 emptiness or bound that is not an
                        archived cell
Stop criterion          the comparison is expansion plus
                        trailing-evens, and r>=2 stays occupied
```

## Closed-bridge gates

Do not reopen the entry corridor, the cyclic seam, or the
eight-case intersection table. Do not reopen peak finance.

- **CLOSE** if \(r=1\) recovers the archived OE corridor.
- **CLOSE** if the first-run cap is \(2^{a_0+r}\le 3^{a_0}\).
- **CLOSE** if last-run \(r\ge 2\) is the occupied EE/EEE family.
- **CLOSE** if a short OO climb realizes \(r\ge 2\) only by
  dropping below \(n\).
- **PROMOTE** only if an \(E^r\) type empties, or a bound appears,
  that is not an archived cell.

Do **not** raise \(N_0\). Do **not** open \(L=55293\). Do **not**
reintroduce finance. Do **not** edit Paper A. Do **not** rebuild
the backward corridor tree. Do **not** reopen the eight-case
census.

## Explicitly out of Phase-0

A \(K=11\) proof, defect amplification, Fourier / residues /
\(Q\)-sections, a branch-and-bound engine, ledger row, new Lean,
CLI, visualization, Paper A edit, an even-preimage leftover-killer.

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Odd-interior push to peak —
  **KNOWN** (`odd_preimage_unique`)
- Even-interior push to valley + \(r\) —
  **KNOWN** (determinism)
- \(\mathtt{O}\,E^r\,\mathtt{O}\) envelope —
  **REPARAMETERIZATION** of `cycle_trailing_evens_lt`
- \(r=1\) corridor —
  **KNOWN** / **REPARAMETERIZATION** of `corridor_bounds`
- First-run cap \(2^{a_0+r}\le 3^{a_0}\) —
  **REPARAMETERIZATION** of `power_bound_word` plus
  `even_run_scale_barrier`
- Last-run \(r\ge 2\) —
  **KNOWN**; count \(n(n^2+n+1)\); \(\mathtt{EEE}\) realized
- \(E^r\) leftover-killer —
  **REFUTED** (`juggler_cycle_e_block`)
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_e_block`
- Dataset: `data/research/juggler/cycle_finance/e_block/summary.json`
- Tests: `tests/research/juggler_sequence/test_cycle_e_block.py`
- Window: \(n=10^6+1\) envelopes and last-run occupancy; first-run
  pairs \(a_0\le 8\), \(r\le 6\); realized OO-launches on odds in
  \([13,2001)\). Fast suite only. No CLI. No new Lean.

## Conjectures

`juggler_cycle_e_block` — **REFUTED**.

## Counterexamples

- \(r=1\) outer cell is \(n^4\le u^3<(n+1)^4\). Falsifier of a new
  peak-intersection envelope.
- \(2^{a_0+r}\le 3^{a_0}\) is the expanding-prefix test. Falsifier
  of a new first-run scale law. Pairs \((2,2)\) and \((3,2)\) fail;
  \((4,2)\) and \((6,3)\) hold.
- \(25\xrightarrow{\mathtt{OOOEE}}15\). Falsifier of “a short climb
  cannot realize \(r=2\)”: it can, by leaving the \(\ge n\) tube.
- \(n(n^2+n+1)\) even-even preimages and a trailing-\(\mathtt{EEE}\)
  witness. Falsifier of empty last-run \(r\ge 2\).
- \(115\) with \(a_0=5\), \(r=2\), valley \(8165\). Falsifier of
  empty CycleMin-shaped first-run \(r\ge 2\).

## Formalization

None added. The uniqueness lemma is already
`odd_preimage_unique`. The even cell is already
`cycle_trailing_evens_lt`. The first-run cap is already
`power_bound_word` plus `even_run_scale_barrier`. Paper A is
unchanged. Do not add `EBlock.lean`.

## Results

- **Three canonical types** — **KNOWN**: peak \(\mathtt{O}|E\),
  valley \(\mathtt{E}|O\), even block \(E^r\). Odd interiors
  disappear.
- **\(r=1\)** — **REPARAMETERIZATION** of the archived OE
  corridor (`e_block/summary.json`: `r1_corridor.matches_outer`).
- **First-run cap** — **REPARAMETERIZATION**:
  `2^{a0+r} <= 3^{a0}`.
- **Last-run \(r\ge 2\)** — **COMPUTATIONALLY VERIFIED** /
  **KNOWN**: EE count \(n(n^2+n+1)\); EEE realized.
- **Realized window** — **COMPUTATIONALLY VERIFIED**. \(502\)
  OO-launches; \(252\) have \(r\ge 2\); \(41\) of those are
  CycleMin-shaped; first contracting witness \(25\); first shaped
  witness \(115\).
- **No new cyclic obstruction.**

## Open questions

None from the \(E^r\) block. Bidirectional sliding of a first
intersection to either boundary is a separate closed branch
([juggler_cycle_seam_sliding.md](juggler_cycle_seam_sliding.md)).
Do not reopen the entry corridor, the cyclic seam, or the
first-intersection taxonomy. Do not open an even-preimage
leftover-killer from this classification.

## Decision

**CLOSE**. Determinism really does shrink the table to three
types, and \(r=1\) is the archived corridor. The new-looking
\(r\ge 2\) comparison is the expanding-prefix test on a first
block and the trailing-evens cell on a last block. Last-run
\(r\ge 2\) is occupied by an enormous fibre; CycleMin-shaped
first-run \(r\ge 2\) occurs (witness \(115\)). The hope that
\(r\ge 2\) can be eliminated, leaving only \(\mathtt{OE}\), is
false. That is useful negative knowledge; it is not a new
invariant. No Paper A edit, no ledger row, no new Lean, no
\(N_0\) raise, no finance reopen.

Best next question: none from the first-intersection \(E^r\)
block.

## Publication assessment

Status: `ARCHIVED`. Laboratory negative knowledge on an \(r\)
parameterization of the even channel; not a second manuscript
and not a Paper A edit.

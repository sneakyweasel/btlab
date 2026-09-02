# Juggler first-intersection taxonomy

Status: **ARCHIVED**

Refinement of
[juggler_cycle_cyclic_seam.md](juggler_cycle_cyclic_seam.md),
[juggler_cycle_entry_corridor.md](juggler_cycle_entry_corridor.md),
and [juggler_cycle_extremal_composition.md](juggler_cycle_extremal_composition.md),
not a reopen of those branches and not a new paper. After the
CycleMin \(2{+}2\) seam closed, this phase asks whether the useful
object is the **first intersection** \(x\) of a forward trajectory
from \(n\) with a hypothetical cycle, classified by valley / odd
ascent / peak / even descent.

Not a halt theorem, not a finance leftover-killer, not a corridor
reopen, not a peak-finance reopen, and not a claim that every
cycle has a distinguished entry valley.

## Problem

A cycle has valleys, odd ascents, peaks, and even descents. If
\(x\) is the first shared point of an “initial climb” from \(n\)
with a cycle through \(x\), does the local shape at \(x\) impose
a two-sided envelope that is not an archived cell?

## Exact statement

**If \(n\) lies on the cycle, the first intersection is \(n\)
(KNOWN / REPARAMETERIZATION).**
CycleMin normalisation already cuts at the minimum. The letters
touching \(n\) are exactly
\[
\mathtt{OE}\mid n\mid\mathtt{OO}
\qquad\text{or}\qquad
\mathtt{EE}\mid n\mid\mathtt{OO}.
\]
Launch through a peak is impossible (`cycleMin_not_odd_even`).
Return through \(O\) is impossible (`cycleMin_not_end_odd`). Later
points on the same orbit are cut-points, not first intersections.
That is the closed cyclic-seam window.

**Odd-to-odd first meeting is impossible
(KNOWN / EXACT — LEAN VERIFIED).**
Every value has at most one odd parent
(`odd_preimage_unique`, `oddLanding_preimage_unique`). Two trajectories
that both arrive by \(O\) already agreed at that unique parent, so
the meeting was not first. Interior \(\mathtt{OO}\) and a
climb-created peak (\(\mathtt{OE}\) with both arrivals odd) are
not first-intersection types.

**Peak two-sided scale is archived
(KNOWN / REPARAMETERIZATION).**
On a CycleMin orbit the first peak after \(n\) is the first-even /
canonical \(\mathtt{OE}^r\) package. Peak finance is the top-ascent
envelope. Composing min + first-even + top cell + peak is
`COMPOSITION_REPACKAGING`. The comparison
\(F_{\mathrm{climb}}(x)\le x\le D_{\mathrm{cycle}}(x)\) is that
program again.

**The only bulk distinct-parent channel is even-to-even
(KNOWN).**
Genuine first meetings require two distinct parents: odd+even or
even+even. The even-even two-step fibre of odd \(n\) has count
\(n(n^2+n+1)\). That is the trailing-\(\mathtt{EE}\) cell that
already closed the entry corridor. There is no thin
\(n^{4/3}\) slice on this channel.

The eight-row local-word table collapses to four geometric
positions, then the two odd-arrival rows die, and the CycleMin
cut collapses to the archived \(2{+}2\) window. What remains is
the already-named even tree.

No cycle of any length — not claimed.

## Current literature

- Unique odd cell —
  **EXACT — LEAN VERIFIED**
  (`odd_preimage_unique`, `oddLanding_preimage_unique`)
- CycleMin starts \(\mathtt{OO}\), cannot start \(\mathtt{OE}\),
  cannot end odd —
  **EXACT — LEAN VERIFIED**
- Isolated-E last run \(\mathtt{OE}\); trailing \(\mathtt{EE}\)
  of size \(n(n^2+n+1)\) —
  **CLOSE** / not a leftover-killer
  ([juggler_cycle_entry_corridor.md](juggler_cycle_entry_corridor.md))
- \(2{+}2\) window \(\{\mathtt{OE}\mid\mathtt{OO},\mathtt{EE}\mid\mathtt{OO}\}\) —
  **CLOSE** / **REPARAMETERIZATION**
  ([juggler_cycle_cyclic_seam.md](juggler_cycle_cyclic_seam.md))
- Canonical peak descent; peak finance = top ascent —
  **EXACT — LEAN VERIFIED** / **REPARAMETERIZATION**
  ([juggler_cycle_peak_descent.md](juggler_cycle_peak_descent.md))
- Extremal composition —
  **CLOSE** / `COMPOSITION_REPACKAGING`
  ([juggler_cycle_extremal_composition.md](juggler_cycle_extremal_composition.md))
- Collatz-style financing —
  **known** (`simons-de-weger-2005-collatz-m-cycles`)
- Every start reaches 1 — not claimed

Project relationship: **refuted** as a first-intersection leftover
obstruction; the odd-odd collapse is a **REPARAMETERIZATION** of
`odd_preimage_unique`; the CycleMin cut is the archived seam.

## Branch budget

```text
Mathematical target     Can two trajectories first meet at a point
                        whose both parents are odd, or does a
                        valley / odd-ascent / peak / even-descent
                        taxonomy produce a two-sided envelope that
                        is not odd_preimage_unique / the CycleMin 2+2
                        seam / peak-finance / trailing-EE count?
Novelty hypothesis      first-intersection geometry is finer than
                        the CycleMin seam and the archived corridor
Falsifier               odd_preimage_unique; first intersection of a
                        CycleMin orbit is n; peak scale is
                        COMPOSITION_REPACKAGING; EE is n(n^2+n+1)
Existing machinery      odd_preimage_unique; oddLanding_preimage_unique;
                        cycleMin_starts_two_odds; cycleMin_not_odd_even;
                        cycleMin_not_end_odd; exists_cycleMin_last_odd_run;
                        cycle_peak_finance; ee_entry_count
Maximum Phase-0 scope   record the collapse against existing lemmas;
                        unique-odd-parent check on a fast window.
                        No probe, no census, no Lean, no finance
Promotion criterion     a first-intersection constraint that is not
                        unique-odd-parent or an archived cell
Stop criterion          the table reduces to EE plus archived seams
```

## Closed-bridge gates

Do not reopen the entry corridor or the cyclic seam. Do not
reopen peak finance.

- **CLOSE** if a CycleMin first intersection is \(n\) and the
  \(2{+}2\) window is the archived pair.
- **CLOSE** if odd+odd first meeting is `odd_preimage_unique`.
- **CLOSE** if a climb-created peak is the unique odd parent.
- **CLOSE** if peak two-sided scale is peak finance /
  extremal composition.
- **CLOSE** if the remaining distinct-parent channel is the
  archived EE count.
- **PROMOTE** only if a first-intersection type empties, or a
  bound appears, that is not an archived cell.

Do **not** raise \(N_0\). Do **not** open \(L=55293\). Do **not**
reintroduce finance. Do **not** edit Paper A. Do **not** rebuild
the backward corridor tree. Do **not** open an eight-case census.

## Explicitly out of Phase-0

A \(K=11\) proof, defect amplification, Fourier / residues /
\(Q\)-sections, a branch-and-bound engine, ledger row, new Lean,
CLI, visualization, Paper A edit, an even-preimage leftover-killer.

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- CycleMin first intersection is \(n\) —
  **KNOWN** / **REPARAMETERIZATION** of the \(2{+}2\) seam
- Odd+odd first meeting —
  **KNOWN** empty (`odd_preimage_unique`)
- Climb-created peak as first meeting —
  **KNOWN** empty (`oddLanding_preimage_unique`)
- Peak two-sided envelope \(F\le x\le D\) —
  **REPARAMETERIZATION** of `cycle_peak_finance` /
  extremal composition
- Even+even first meeting —
  **KNOWN**; count \(n(n^2+n+1)\)
- First-intersection leftover-killer —
  **REFUTED** (`juggler_cycle_intersection_taxonomy`)
- No cycle of any length — not claimed

## Experiments

- Probe: none. Phase-0 is the existing uniqueness window in
  `tests/research/juggler_sequence/test_odd_landing_sets.py`
  plus the record test
  `tests/research/juggler_sequence/test_cycle_intersection_taxonomy.py`.
- Dataset: none. No census.
- Window: odd starts in \([1,2001)\); uniqueness already holds
  on \([1,401)\) in the odd-landing suite. Fast suite only.
  No CLI. No new Lean.

## Conjectures

`juggler_cycle_intersection_taxonomy` — **REFUTED**.

## Counterexamples

- A CycleMin orbit first meets itself at \(n\). Falsifier of a
  free first-intersection cut at a later valley or peak.
- `odd_preimage_unique`: two odd parents of the same image cannot
  exist. Falsifier of interior \(\mathtt{OO}\) and of a
  climb-created peak as first intersections.
- Peak finance equals the top-ascent envelope. Falsifier of
  \(F_{\mathrm{climb}}(x)\le x\le D_{\mathrm{cycle}}(x)\) as a
  new gap.
- \(n(n^2+n+1)\) even-even two-step preimages. Falsifier of a
  thin first-intersection corridor on the remaining channel.

## Formalization

None added. The uniqueness lemma is already
`odd_preimage_unique` / `oddLanding_preimage_unique`. The CycleMin
cut is already `cycleMin_starts_two_odds` plus
`exists_cycleMin_last_odd_run`. Paper A is unchanged. Do not
add `IntersectionTaxonomy.lean`.

## Results

- **CycleMin cut** — **KNOWN** / **REPARAMETERIZATION**: first
  intersection is \(n\); window \(\{\mathtt{OE}\mid\mathtt{OO},\mathtt{EE}\mid\mathtt{OO}\}\).
- **Odd+odd** — **EXACT — LEAN VERIFIED**: empty
  (`oddLanding_preimage_unique`).
- **Peak scale** — **REPARAMETERIZATION** of peak finance /
  `COMPOSITION_REPACKAGING`.
- **EE channel** — **KNOWN**: \(n(n^2+n+1)\).
- **No new cyclic obstruction.**

## Open questions

None from the first-intersection taxonomy. The directed \(E^r\)
follow-up
([juggler_cycle_e_block.md](juggler_cycle_e_block.md))
is also closed: the even channel parameterized by \(r\) is
trailing-evens plus the expanding-prefix test. Do not reopen the
entry corridor or the cyclic seam. Do not open an even-preimage
leftover-killer from this classification. Homogeneous-run sliding
is a separate closed branch
([juggler_cycle_seam_sliding.md](juggler_cycle_seam_sliding.md)).

## Decision

**CLOSE**. The four-position language is a restatement of run
form. If \(n\) is on the cycle, the first intersection is the
archived CycleMin seam. If \(n\) is a transient, odd-to-odd and
climb-created-peak meetings die on `odd_preimage_unique`. The
photogenic peak comparison is extremal composition under a new
name. The only bulk distinct-parent channel is the even tree
already measured as \(n(n^2+n+1)\). That is useful negative
knowledge; it is not a new invariant. No Paper A edit, no
ledger row, no new Lean, no \(N_0\) raise, no finance reopen,
no eight-case census.

Best next question: none from the first-intersection taxonomy.

## Publication assessment

Status: `ARCHIVED`. Laboratory negative knowledge on a
first-intersection refinement; not a second manuscript and
not a Paper A edit.

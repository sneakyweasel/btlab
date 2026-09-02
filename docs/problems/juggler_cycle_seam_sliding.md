# Juggler cyclic seam sliding

Status: **ARCHIVED**

Refinement of
[juggler_cycle_e_block.md](juggler_cycle_e_block.md)
and
[juggler_cycle_intersection_taxonomy.md](juggler_cycle_intersection_taxonomy.md),
not a reopen of those branches and not a new paper. The \(E^r\)
block already pushes odd interiors to the peak and even interiors
*forward* to the next valley. This phase asks the stronger
claim: that an interior cut may be **slid either way**, so
\(E\mid EEE\), \(EE\mid EE\), \(EEE\mid E\) are one cyclic
geometry and one may choose whichever boundary gives the
stronger inequality.

Not a halt theorem, not a finance leftover-killer, not a corridor
reopen, and not a claim that a first intersection can be moved
numerically.

## Problem

An \(E^r\) block applies the same map at every letter. If an
initial climb first meets a cycle inside that block, does the
intersection cut slide to the peak or the valley without changing
the cyclic word class, and does choosing the stronger boundary
then impose an inequality that is not cyclic rotation or the
trailing-evens cell?

## Exact statement

**Combinatorial sliding is cyclic rotation
(KNOWN / EXACT — LEAN VERIFIED).**
If \(w\) is a cycle itinerary and the cut sits \(k\) letters into a
homogeneous run, `rotateItinerary w k` is the same necklace
(`cycleItinerary_rotateItinerary`). Sliding through a leading even run is
`rotateItinerary_even_run`. The interior cuts
\[
E\mid EEE,\qquad EE\mid EE,\qquad EEE\mid E
\]
are therefore one cyclic word class. There is no intrinsic
combinatorial entry location inside \(E^r\).

**A first intersection does not slide backward
(EXACT — HUMAN PROOF).**
The \(E^r\) block already allows only the *forward* push to
the next valley. Bidirectional sliding is stronger, and false.
If the climb first meets the descent
\(P\xrightarrow{E}x_1\xrightarrow{E}\cdots\xrightarrow{E}V\)
at an interior \(x_i\), then \(P\) was not visited. From \(x_i\)
onward the trajectories share a tail, so the valley lies on that
tail, but it is not the first shared point. The two
“canonical descriptions”
\[
\text{climb}\to P\xrightarrow{E^r}V
\qquad\text{and}\qquad
\text{climb}\to V\to O\to P\xrightarrow{E^{r-1}}V'
\]
are the two parity-change seams \(\mathtt{OE}\) and \(\mathtt{EO}\),
not two views of one first intersection.

**Peak / valley transfer is the trailing-evens cell
(KNOWN / REPARAMETERIZATION).**
On a cycle itinerary that ends \(E^r\),
`cycle_trailing_evens_lt` is \(P<(n+1)^{2^r}\). The slogan
\(P\approx V^{2^r}\) is that two-sided cell. Taking \(2^r\)-th
roots does not add a bound. On a minimal non-terminating orbit
the matching lower cell is `even_run_scale_barrier`.

**Odd interiors are not first meetings
(KNOWN / EXACT — LEAN VERIFIED).**
`odd_preimage_unique` already closed interior \(\mathtt{OO}\). Sliding
an \(O^r\) cut is vacuous for first intersections.

**Run length is the archived even-count
(KNOWN).**
A nontrivial cycle has at least four evens
(`no_cycle_itinerary_even_count_le_three`). How long one homogeneous
block can be is that count plus `cycle_trailing_evens_lt` at
each \(r\), not a sliding consequence.

No cycle of any length — not claimed.

## Current literature

- Cyclic shift of a cycle itinerary —
  **EXACT — LEAN VERIFIED**
  (`rotateItinerary`, `cycleItinerary_rotateItinerary`, `rotateItinerary_even_run`)
- Trailing-evens cell \(T_v(n)<(n+1)^{2^r}\) —
  **EXACT — LEAN VERIFIED**
  (`cycle_trailing_evens_lt`)
- Even-run scale barrier —
  **EXACT — LEAN VERIFIED**
  (`even_run_scale_barrier`)
- Unique odd parent —
  **EXACT — LEAN VERIFIED**
  (`odd_preimage_unique`, `oddLanding_preimage_unique`)
- Even-count \(\le 3\) impossible —
  **EXACT — LEAN VERIFIED**
  (`no_cycle_itinerary_even_count_le_three`)
- \(2{+}2\) window \(\{\mathtt{OE}\mid\mathtt{OO},\mathtt{EE}\mid\mathtt{OO}\}\) —
  **CLOSE** / **REPARAMETERIZATION**
  ([juggler_cycle_cyclic_seam.md](juggler_cycle_cyclic_seam.md))
- First-intersection taxonomy —
  **CLOSE** / **REFUTED**
  ([juggler_cycle_intersection_taxonomy.md](juggler_cycle_intersection_taxonomy.md))
- First-intersection \(E^r\) block, one-way push —
  **CLOSE** / **REFUTED**
  ([juggler_cycle_e_block.md](juggler_cycle_e_block.md))
- \(r=4\) trailing cell already sharp —
  **CLOSE** / **REFUTED**
  ([juggler_e4_tight_pullback.md](juggler_e4_tight_pullback.md))
- Collatz-style financing —
  **known** (`simons-de-weger-2005-collatz-m-cycles`)
- Every start reaches 1 — not claimed

Project relationship: **refuted** as a sliding leftover
obstruction; combinatorial sliding is a **REPARAMETERIZATION** of
`cycleItinerary_rotateItinerary`; peak / valley transfer is
`cycle_trailing_evens_lt`.

## Branch budget

```text
Mathematical target     Does sliding a first-intersection cut through
                        a homogeneous E^r (or O^r) run produce a
                        two-sided envelope, or a restriction on r,
                        that is not rotateItinerary / cycle_trailing_evens_lt /
                        even_run_scale_barrier / odd_preimage_unique /
                        the archived OE/EO cells?
Novelty hypothesis      interior E-cuts collapse, so only EO and OE
                        plus run length remain, and choosing the peak
                        or valley boundary yields a stronger inequality
Falsifier               combinatorial sliding is rotateItinerary; a first
                        intersection cannot slide backward to the peak;
                        P ~ V^{2^r} is trailing-evens; O interiors are
                        not first meetings; max E^r is even-count
Existing machinery      cycleItinerary_rotateItinerary, rotateItinerary_even_run,
                        cycle_trailing_evens_lt, even_run_scale_barrier,
                        odd_preimage_unique, no_cycle_itinerary_even_count_le_three,
                        closed cyclic-seam / intersection-taxonomy /
                        E^r block
Maximum Phase-0 scope   three-way split (word / trajectory / scale);
                        one backward-slide witness; necklace identity
                        for E|EEE / EE|EE / EEE|E; scale check against
                        trailing-evens. No finance, no Lean, no census
Promotion criterion     a first-intersection constraint or a bound on r
                        that is not an archived rotation or cell
Stop criterion          sliding is cyclic rotation; first intersection
                        cannot move backward; peak/valley transfer is
                        trailing-evens; EO/OE reduction is the closed
                        taxonomy
```

## Closed-bridge gates

Do not reopen the entry corridor, the cyclic seam, the
first-intersection taxonomy, or the \(E^r\) block. Do not
reopen \(r=4\) pullback.

- **CLOSE** if interior \(E\)-cuts are `rotateItinerary` of one necklace.
- **CLOSE** if a first intersection interior to \(E^r\) cannot be
  slid to the peak and is not first at the valley.
- **CLOSE** if \(P<(V+1)^{2^r}\) is `cycle_trailing_evens_lt`.
- **CLOSE** if \(O^r\) interiors are `odd_preimage_unique`.
- **CLOSE** if “how long can \(E^r\) be” is even-count plus the
  trailing cell.
- **PROMOTE** only if a sliding type empties, or a bound appears,
  that is not an archived rotation or cell.

Do **not** raise \(N_0\). Do **not** open \(L=55293\). Do **not**
reintroduce finance. Do **not** edit Paper A. Do **not** rebuild
the backward corridor tree. Do **not** open an \(E^r\)-length
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

- Interior \(E\)-cuts of one necklace —
  **KNOWN** / **REPARAMETERIZATION** of `cycleItinerary_rotateItinerary`
- First-intersection backward slide —
  **REFUTED**; witness \(102\to 10\leftarrow 100\), first meet \(10\)
- Forward slide to the valley —
  **KNOWN**; shared tail, not first
- Peak / valley transfer \(P<(V+1)^{2^r}\) —
  **REPARAMETERIZATION** of `cycle_trailing_evens_lt`
- \(O^r\) interiors as first meetings —
  **KNOWN** empty (`odd_preimage_unique`)
- Canonical seams \(\{\mathtt{EO},\mathtt{OE}\}\) —
  **REPARAMETERIZATION** of the closed intersection taxonomy
- Homogeneous-run leftover-killer —
  **REFUTED** (`juggler_cycle_seam_sliding`)
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_seam_sliding`
- Dataset: `data/research/juggler/cycle_finance/seam_sliding/summary.json`
- Tests: `tests/research/juggler_sequence/test_cycle_seam_sliding.py`
- Window: necklace identity at \(r=4\); backward-slide at
  \(100\xrightarrow{E^2}3\) and \(10000\xrightarrow{E^3}3\);
  trailing-cell check at those peaks. Fast suite only. No CLI.
  No new Lean.

## Conjectures

`juggler_cycle_seam_sliding` — **REFUTED**.

## Counterexamples

- \(E\mid EEE\), \(EE\mid EE\), \(EEE\mid E\) are rotations of
  \(\mathtt{OOEEEE}\). Falsifier of distinct interior cut types.
- \(100\xrightarrow{E}10\xrightarrow{E}3\) versus
  \(102\xrightarrow{E}10\xrightarrow{E}3\): first intersection is
  \(10\), not \(100\) or \(3\). Falsifier of first-intersection
  sliding to either boundary.
- \(100<4^4\) and \(10000<4^8\). Falsifier of \(P\approx V^{2^r}\)
  as a new cell.
- Unique odd parent. Falsifier of \(O^r\) first-intersection
  sliding.

## Formalization

None added. Combinatorial sliding is already
`cycleItinerary_rotateItinerary` / `rotateItinerary_even_run`. The cell is
already `cycle_trailing_evens_lt`. Paper A is unchanged. Do not
add `SeamSliding.lean`.

## Results

- **Necklace** — **KNOWN** / **REPARAMETERIZATION**
  (`seam_sliding/summary.json`): interior \(E\)-cuts are one
  class.
- **First intersection** — **EXACT — HUMAN PROOF**: backward
  slide fails; forward slide is a later shared point.
- **Scale** — **REPARAMETERIZATION** of
  `cycle_trailing_evens_lt`.
- **No new cyclic obstruction.**

## Open questions

None from cyclic seam sliding. Do not reopen the first-intersection
taxonomy, the \(E^r\) block, or the entry corridor. Do not open an
\(E^r\)-length leftover-killer from the boundary choice.

## Decision

**CLOSE**. Homogeneous \(E^r\) is dynamically uniform for the
*word*: interior cuts slide by `rotateItinerary`. It is not uniform
for a *first intersection*: the \(E^r\) block already permits
only the forward push to the valley, and sliding backward to
the peak is false. The numerical transfer \(P\approx V^{2^r}\)
is the trailing-evens cell. Reducing to \(\mathtt{EO}\) and
\(\mathtt{OE}\) plus run length is the closed taxonomy under a
cleaner name.
That is useful compression of the language; it is not a new
invariant. No Paper A edit, no ledger row, no new Lean, no
\(N_0\) raise, no finance reopen, no \(E^r\) census.

Best next question: none from cyclic seam sliding.

## Publication assessment

Status: `ARCHIVED`. Laboratory negative knowledge on sliding a
homogeneous-run cut; not a second manuscript and not a Paper A
edit.

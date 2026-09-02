# Juggler CycleMin cyclic seam types

Status: **ARCHIVED**

Refinement of
[juggler_cycle_entry_corridor.md](juggler_cycle_entry_corridor.md),
not a reopen of that branch and not a new paper. After the
OE-privileged corridor closed, this phase asks a different
question: classify the **local parity itinerary on both sides** of a
CycleMin \(n\), instead of asking for the last valley before \(n\).

Not a halt theorem, not a finance leftover-killer, not an
inverse-width reopen, not a floor raise, and not a claim that
the orbit must return through the isolated \(\mathtt{OE}\) cell.

## Problem

A cycle can be written starting at any vertex. CycleMin
normalization still cuts the itinerary at the minimum state \(n\).
The first iterate \(T(n)\) is then fixed, but the incoming letter
need not be the isolated-\(\mathtt{OE}\) seam. Which local words
\[
\cdots\,w_{-}\,n\,w_{+}
\]
are possible, and what inequality does each type impose?

## Exact statement

**Return through \(O\) is impossible (KNOWN / EXACT — LEAN VERIFIED).**
The last letter cannot be odd (`cycleMin_not_end_odd`). The odd
return cell \(n^2\le x^3<(n+1)^2\) lives at scale \(n^{2/3}<n\), so
it fails the \(\ge n\) tube. At \(n=10^6+1\), \(13\), and \(101\)
there is no odd predecessor \(\ge n\).

**Launch is \(\mathtt{OO}\) (KNOWN / EXACT — LEAN VERIFIED).**
The minimum is odd, so the itinerary cannot start \(E\) or \(\mathtt{OE}\)
(`cycleMin_starts_two_odds`). There is no freedom to “enter at a
peak” as the first letter after the CycleMin cut: \(x_1=T(n)\) is
odd and the next letter is again \(O\).

**The \(2{+}2\) window has exactly two legal types
(EXACT — LEAN VERIFIED / REPARAMETERIZATION).**
`exists_cycleMin_last_odd_run` says the itinerary ends \(O^aE\) with
\(a\le 1\). Together with the forced prefix \(\mathtt{OO}\), the
letters touching \(n\) are
\[
\mathtt{OE}\mid n\mid\mathtt{OO}
\qquad\text{or}\qquad
\mathtt{EE}\mid n\mid\mathtt{OO}.
\]
The first is isolated last \(E\); the second is a trailing even
run of length at least two. No third \(2{+}2\) type exists.

**Each type uses an archived cell (KNOWN).**
Type \(\mathtt{OE}\mid\mathtt{OO}\): last peak in \((n^2,(n+1)^2)\),
last valley in \(n^4<v^3<(n+1)^4\). Type \(\mathtt{EE}\mid\mathtt{OO}\):
the same last-even cell, plus `cycle_trailing_evens_lt` at
\(r\ge 2\) (previous even of scale \(n^4\)). Both launches use
`oo_suffix_threshold`: \(T^2(n)\ge(n+1)^2\).

**The \(3{+}3\) window only lengthens those two families
(COMPUTATIONALLY VERIFIED).**
Legal extensions are \(\mathtt{EOE}\mid\mathtt{OO}\{E,O\}\),
\(\mathtt{OEE}\mid\mathtt{OO}\{E,O\}\), and
\(\mathtt{EEE}\mid\mathtt{OO}\{E,O\}\). Left \(\mathtt{OOE}\) is the
archived last-run comparison. The right third letter is the
parity of \(T^2(n)\): both \(\mathtt{OOE}\) and \(\mathtt{OOO}\)
occur among OO-realizers in \([13,2001)\). Trailing \(\mathtt{EEE}\)
is realized. An \(\mathtt{OEE}\) search is optional occupancy of
the same EE family (last odd at scale \(n^{8/3}\), not
\(n^{4/3}\)).

**Both legal \(2{+}2\) types are occupied
(COMPUTATIONALLY VERIFIED).**
At \(n=10^6+1\) there are \(33\) CycleMin-legal \(\mathtt{OE}\)
entries and \(n(n^2+n+1)\) even-even two-step preimages. The floor
representative itself starts \(\mathtt{OE}\), so it is not a
CycleMin launch; that does not add a type.

No cycle of any length — not claimed.

## Current literature

- Starts \(\mathtt{OO}\), ends \(E\), cannot end odd —
  **EXACT — LEAN VERIFIED**
  (`cycleMin_starts_two_odds`, `cycleMin_getLast_even`,
  `cycleMin_not_end_odd`)
- Last odd-run length \(0\) or \(1\) —
  **EXACT — LEAN VERIFIED**
  (`exists_cycleMin_last_odd_run`)
- Last-even and trailing-evens cells —
  **EXACT — LEAN VERIFIED**
  (`cycle_last_even_interval`, `cycle_trailing_evens_lt`)
- Isolated-E last run \(\mathtt{OE}\); trailing \(\mathtt{EE}\)
  of size \(n(n^2+n+1)\) —
  **CLOSE** / not a leftover-killer
  ([juggler_cycle_entry_corridor.md](juggler_cycle_entry_corridor.md))
- Entry tax / cyclic-valley leftover-killers —
  **CLOSE**
- Collatz-style financing —
  **known** (`simons-de-weger-2005-collatz-m-cycles`)
- Every start reaches 1 — not claimed

Project relationship: **refuted** as a new seam inequality; the
two-type list is a **REPARAMETERIZATION** of the existing Lean
first/last-letter lemmas.

## Branch budget

```text
Mathematical target     Do the letters touching a CycleMin n form
                        only a small finite set of seam types, and
                        does any type impose an inequality that is
                        not last-even / oo_suffix / trailing-evens /
                        start-OO / no-end-O?
Novelty hypothesis      a 2-sided taxonomy replaces the OE-privileged
                        corridor with a useful local invariant
Falsifier               the 2+2 window is {OE|OO, EE|OO}; both cells
                        are archived and occupied; longer windows only
                        lengthen E^r or O^{a0}
Existing machinery      cycleMin_starts_two_odds, cycleMin_not_end_odd,
                        exists_cycleMin_last_odd_run, last-even,
                        trailing-evens, ee_entry_count
Maximum Phase-0 scope   classify 2+2 and 3+3 windows; occupancy of
                        legal/forbidden types; launch OOE/OOO split
                        on OO-realizers. No finance, no corridor tree
Promotion criterion     a new inequality or a type that empties for a
                        non-archived reason
Stop criterion          the list is the existing Lean first/last
                        letters; both legal types use archived cells
```

## Closed-bridge gates

Do not reopen the entry-corridor leftover-killer. Do not treat
return-\(O\) as open.

- **CLOSE** if the \(2{+}2\) window is exactly
  \(\{\mathtt{OE}\mid\mathtt{OO},\mathtt{EE}\mid\mathtt{OO}\}\)
  and both cells are archived and occupied.
- **CLOSE** if return-\(O\) and launch-\(\mathtt{OE}\) are the
  existing Lean lemmas.
- **CLOSE** if \(3{+}3\) only lengthens \(E^r\) or splits
  \(T^2(n)\) parity.
- **PROMOTE** only if a type empties, or a bound appears, that is
  not an archived cell.

Do **not** raise \(N_0\). Do **not** open \(L=55293\). Do **not**
reintroduce finance. Do **not** edit Paper A. Do **not** rebuild
the backward corridor tree.

## Explicitly out of Phase-0

A \(K=11\) proof, defect amplification, Fourier / residues /
\(Q\)-sections, a branch-and-bound engine, ledger row, new Lean,
CLI, visualization, Paper A edit.

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- \(2{+}2\) seam \(\{\mathtt{OE}\mid\mathtt{OO},\mathtt{EE}\mid\mathtt{OO}\}\) —
  **EXACT — LEAN VERIFIED** / **REPARAMETERIZATION**
- Return \(O\) —
  **KNOWN** empty under CycleMin (`cycleMin_not_end_odd`)
- Launch \(\mathtt{OE}\) —
  **KNOWN** empty (`cycleMin_not_odd_even`)
- Type occupancy —
  **COMPUTATIONALLY VERIFIED**; \(33\) OE valleys and
  \(n(n^2+n+1)\) EE chains
- Launch split \(\mathtt{OOE}\) vs \(\mathtt{OOO}\) —
  **COMPUTATIONALLY VERIFIED**; both occur
- New seam inequality —
  **REFUTED** (`juggler_cycle_cyclic_seam`)
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_cyclic_seam`
- Dataset: `data/research/juggler/cycle_finance/cyclic_seam/summary.json`
- Tests: `tests/research/juggler_sequence/test_cycle_cyclic_seam.py`
- Window: \(n=10^6+1\) occupancy; launch split on odds in
  \([13,2001)\); one \(\mathtt{EEE}\) witness; bounded
  \(\mathtt{OEE}\) search. Fast suite only. No CLI. No new Lean.

## Conjectures

`juggler_cycle_cyclic_seam` — **REFUTED**.

## Counterexamples

- Return \(O\) has no predecessor \(\ge n\). Falsifier of a third
  incoming letter.
- \(33\) OE valleys and \(n(n^2+n+1)\) EE chains. Falsifier of a
  missing legal type or an empty legal type.
- First \(\mathtt{OOE}\) and first \(\mathtt{OOO}\) launches in
  \([13,2001)\). Falsifier of a forced third launch letter.
- All listed inequalities are `cycleMin_starts_two_odds` /
  `cycleMin_not_end_odd` / last-even / trailing-evens /
  `oo_suffix_threshold`. Falsifier of a new cell.

## Formalization

None added. The two-type list is already
`cycleMin_starts_two_odds` plus `exists_cycleMin_last_odd_run` in
`EvenCountThree.lean`. Paper A is unchanged. Do not add
`CyclicSeam.lean`.

## Results

- **Two types** — **EXACT — LEAN VERIFIED** /
  **REPARAMETERIZATION** (`cyclic_seam/summary.json`):
  `legal=['EE|OO','OE|OO']`.
- **Occupancy** — **COMPUTATIONALLY VERIFIED**. OE \(33\); EE
  \(n(n^2+n+1)\); return-\(O\) empty; left \(\mathtt{OOE}\) empty.
- **Launch split** — both \(\mathtt{OOE}\) and \(\mathtt{OOO}\)
  occur.
- **No new inequality.**

## Open questions

None from the cyclic-seam classification. Do not reopen the
entry corridor. Do not open a finance charge on the
\(n^{8/3}\) last-odd of \(\mathtt{OEE}\). Do not open a
first-intersection taxonomy
([juggler_cycle_intersection_taxonomy.md](juggler_cycle_intersection_taxonomy.md)).

## Decision

**CLOSE**. Cutting a genuine cycle at its minimum does **not**
force the isolated \(\mathtt{OE}\) seam, and it also does not
allow return through \(O\) or launch through \(\mathtt{OE}\). The
local word around \(n\) is exactly one of two archived types:
\(\mathtt{OE}\mid\mathtt{OO}\) or \(\mathtt{EE}\mid\mathtt{OO}\).
Longer windows only lengthen the trailing even run or record the
parity of \(T^2(n)\). That is a useful distinction from the closed
corridor branch; it is not a new invariant. No Paper A edit, no
ledger row, no new Lean, no \(N_0\) raise, no finance reopen.

Best next question: none from the CycleMin cyclic seam.

## Publication assessment

Status: `ARCHIVED`. Laboratory negative knowledge on a 2-sided
seam taxonomy; not a second manuscript and not a Paper A edit.

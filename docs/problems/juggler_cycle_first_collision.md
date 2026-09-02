# Juggler first exact collision

Status: **ARCHIVED**

Directed follow-up of the closed first-intersection stack
([juggler_cycle_intersection_taxonomy.md](juggler_cycle_intersection_taxonomy.md),
[juggler_cycle_cyclic_seam.md](juggler_cycle_cyclic_seam.md),
[juggler_cycle_entry_corridor.md](juggler_cycle_entry_corridor.md),
[juggler_cycle_seam_sliding.md](juggler_cycle_seam_sliding.md)),
not a reopen of those branches and not a new paper. The previous
programme studied the geometry of the first meeting point \(x\).
This phase studies the inverse fork \(c\to x\leftarrow t\).

Not a halt theorem, not a leftover-killer, not a finance reopen,
not a twin-flight reopen, and not a claim that every positive
integer reaches 1.

## Problem

Let \(x\) be the first point at which an initial trajectory meets
a hypothetical CycleMin cycle. Let \(c\) be the cyclic predecessor
and \(t\) the transient predecessor:

\[
J(c)=J(t)=x,\qquad c\ne t.
\]

Classify \((c,t)\in E/O\times E/O\). What restrictions does
CycleMin impose on the **pair** \((c,t)\), not on \(x\) alone?

## Exact statement

**Collision Factorization (EXACT — HUMAN PROOF /
REPARAMETERIZATION).**
A cycle \(C\) is forward-invariant. If \(t\in C\) then every
iterate of \(t\) lies on \(C\). Hence a forward trajectory that
arrives at \(x\in C\) through \(t\) first meets \(C\) at \(x\) if
and only if \(t\notin C\). There is no extra ancestor condition.
A cycle has exactly one in-edge at \(x\), so the pair is exactly
the unique cyclic parent together with any other parent.

**CycleMin acts only on which parent can be cyclic
(KNOWN / REPARAMETERIZATION).**

| Where \(x\) sits | Cyclic parent \(c\) | Transient \(t\) |
|---|---|---|
| CycleMin valley \(x=n\) | even, last-even cell | any other parent |
| Interior, cycle arrives \(O\) | the unique odd parent, and it must be \(\ge n\) | every even parent |
| Interior, cycle arrives \(E\) | one even parent | other evens, and the odd parent if occupied |

**The four types (KNOWN / REPARAMETERIZATION).**
\((O,O)\) is empty by `odd_preimage_unique`. At \(x=n\), \((O,E)\)
and \((O,O)\) are empty by `cycleMin_not_end_odd` (the odd cell
of \(n\) sits at scale \(n^{2/3}<n\)). Remaining types:

- valley \((E,O)\): occupancy is odd-cell Type 2; \(t<n\) is
  automatically off-cycle;
- valley \((E,E)\): any two distinct evens in \([n^2,(n+1)^2)\);
- interior \((O,E)\): forced if the cycle arrives by \(O\);
- interior \((E,O)\) / \((E,E)\): cycle arrives by \(E\).

**The square-interval pairing is two independent cells
(REPARAMETERIZATION).**
If \(c\) is even then \(c\in[x^2,(x+1)^2)\). If \(t\) is odd then
\(t^3\in[x^2,(x+1)^2)\). The offset \(t^3-x^2\) is the archived
cube-gap of the odd cell. An odd cube sits at distance \(1\) from
the nearest even in the interval. Even-even gaps are the even
widths \(2,4,\ldots,2(\lvert\mathrm{Pred}_E\rvert-1)\) of an
arithmetic progression of difference \(2\).

No cycle of any length — not claimed.

## Current literature

- Unique odd cell —
  **EXACT — LEAN VERIFIED**
  (`odd_preimage_unique`, `oddLanding_preimage_unique`)
- CycleMin cannot end odd —
  **EXACT — LEAN VERIFIED**
  (`cycleMin_not_end_odd`)
- Even / odd floor cells —
  **EXACT — LEAN VERIFIED**
  (`even_preimage_iff`, `odd_preimage_iff`)
- Empty-odd-cell Type 0/1/2 —
  **KNOWN**
  ([juggler_empty_odd_preimage.md](juggler_empty_odd_preimage.md))
- First-intersection taxonomy —
  **CLOSE** / **REPARAMETERIZATION**
  ([juggler_cycle_intersection_taxonomy.md](juggler_cycle_intersection_taxonomy.md))
- Cyclic seam \(2{+}2\) window —
  **CLOSE**
  ([juggler_cycle_cyclic_seam.md](juggler_cycle_cyclic_seam.md))
- Entry corridor (predecessors \(\ge n\)) —
  **CLOSE**
  ([juggler_cycle_entry_corridor.md](juggler_cycle_entry_corridor.md))
- Seam sliding; witness \(100\to 10\leftarrow 102\) —
  **CLOSE**
  ([juggler_cycle_seam_sliding.md](juggler_cycle_seam_sliding.md))
- Adjacent-seam propagation —
  **CLOSE**
  ([juggler_cycle_seam_propagate.md](juggler_cycle_seam_propagate.md))
- General first-collision / ancestry —
  **CLOSE**
  ([juggler_first_collision.md](juggler_first_collision.md));
  distinct last parents, not CycleMin roles
- Seam ancestry graph —
  **CLOSE**
  ([juggler_cycle_seam_ancestry.md](juggler_cycle_seam_ancestry.md))
- Twin-flight / `high_merge` —
  **CLOSE** / **PARK**; different objects
- Collatz-style financing —
  **known** (`simons-de-weger-2005-collatz-m-cycles`)
- Every start reaches 1 — not claimed

Project relationship: **refuted** as a joint leftover
obstruction; Collision Factorization is a
**REPARAMETERIZATION** of forward invariance plus the unique
cyclic in-edge; mixed placement is the archived cube-gap.

## Branch budget

```text
Mathematical target     What restrictions does CycleMin impose on
                        the pair (c,t) with J(c)=J(t)=x, c!=t,
                        c on the cycle, t the transient parent,
                        and x the first meeting — not on x alone?
Novelty hypothesis      the collision is jointly constrained
                        (forbidden type, order/gap/residue of
                        (c,t) or (c,t^3) in the square interval)
                        in a way that is not Pred cells,
                        odd_preimage_unique, or the cyclic-parent type
Falsifier               Collision Factorization: first iff t not
                        on the cycle; CycleMin constrains only
                        which parent can be cyclic; (c,t) is then
                        any other parent
Existing machinery      even_preimage / odd_preimage_integers / odd_preimage;
                        cycleMin_not_end_odd; odd_preimage_unique;
                        even_predecessors; empty-odd-preimage Type 0/1/2;
                        closed seam stack
Maximum Phase-0 scope   4-type x {x=n, x interior} lemma table;
                        Pred occupancy at n=10^6+1 and odd x in
                        [13,2001); one joint observable in the
                        square interval; 2-3 named merge witnesses
                        as calibration. No Lean, no finance, no CLI
Promotion criterion     a pair type or a relation on (c,t) that
                        both cells allow, with a legal cyclic
                        parent, and that fails for a reason not
                        on the archived list
Stop criterion          factorization holds; mixed placement is
                        generic; (E,E) gaps are free;
                        every empty type is odd_preimage_unique or
                        cycleMin_not_end_odd
```

## Closed-bridge gates

Do not reopen the entry corridor, the cyclic seam, the
first-intersection taxonomy, the \(E^r\) block, seam sliding,
seam propagate, the general first-collision / ancestry branch,
the seam ancestry graph, the exponent budget, cyclic block
transfer, peak–valley composition, finance, twin-flight,
high-merge, backward-geometry rank, or the empty-odd-preimage
forward law.

- **CLOSE** if factorization holds: first \(\Leftrightarrow t\notin C\);
  CycleMin constrains only the cyclic-parent type.
- **CLOSE** if every empty type is `odd_preimage_unique` or
  `cycleMin_not_end_odd`.
- **CLOSE** if mixed \((c,t^3)\) placement is generic in the
  square interval and \((E,E)\) gaps are free.
- **CLOSE** if “odd feeder from below into \(n\)” is only
  empty-odd-preimage occupancy.
- **PROMOTE** only if a joint emptiness or residue/order/gap
  law survives those gates.

Do **not** raise \(N_0\). Do **not** open \(L=55293\). Do
**not** reintroduce finance. Do **not** edit Paper A. Do
**not** claim termination. Do **not** add Lean.

## Explicitly out of Phase-0

A \(K=11\) proof, defect amplification, Fourier / residues /
\(Q\)-sections, a branch-and-bound engine, ledger row, new Lean,
CLI, visualization, Paper A edit, a leftover-killer census, a
halt theorem, a twin-flight merge census.

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Collision Factorization first \(\Leftrightarrow t\notin C\) —
  **EXACT — HUMAN PROOF** / **REPARAMETERIZATION** of
  forward invariance
- Valley \((O,\ast)\) —
  **KNOWN** empty (`cycleMin_not_end_odd`)
- \((O,O)\) anywhere —
  **KNOWN** empty (`odd_preimage_unique`)
- Valley \((E,O)\) occupancy —
  **REPARAMETERIZATION** of odd-cell Type 2
- Square-interval offset \(t^3-x^2\) —
  **REPARAMETERIZATION** of the archived cube-gap
- Even-even gaps —
  **REPARAMETERIZATION** of \(\mathrm{Pred}_E\) as an
  arithmetic progression of difference \(2\)
- First-collision leftover-killer —
  **REFUTED** (`juggler_cycle_first_collision`)
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_first_collision`
- Dataset: `data/research/juggler/cycle_finance/cycle_first_collision/summary.json`
- Tests: `tests/research/juggler_sequence/test_cycle_first_collision.py`
- Window: lemma table; valley occupancy at \(n=10^6+1\);
  odd starts in \([13,2001)\); square-interval joint observable
  on Type-2 images; \((E,E)\) gaps at \(x=10\) and by formula
  at the floor; named forks \(100\to 10\leftarrow 102\) and
  \(365/501\) at \(763\). Fast suite only. No CLI. No new Lean.

## Conjectures

`juggler_cycle_first_collision` — **REFUTED**.

## Counterexamples

- Collision Factorization: first meeting at \(x\) iff \(t\notin C\).
  Falsifier of an extra ancestor condition on the pair.
- `odd_return_ge_n` is empty at \(n=10^6+1\), \(13\), and
  \(125\). Falsifier of valley \((O,\ast)\).
- `odd_preimage_unique` on odd starts in \([1,2001)\). Falsifier of
  \((O,O)\).
- Valley \((E,O)\) is Type 0 at \(n=10^6+1\) and occupied at
  \(25\to 125\). Falsifier of a pair law beyond empty-odd-preimage
  occupancy.
- Offset \(t^3-x^2\) equals the cube-gap on all \(994\) Type-2
  images of odd starts in \([13,2001)\); nearest-even gap is
  \(1\). Falsifier of a mixed residue lock.
- At \(x=10\), eleven evens \(100,\ldots,120\) have gaps
  \(2,4,\ldots,20\). Falsifier of a restricted \((E,E)\) gap.
- \(100\to 10\leftarrow 102\) and \(365/501\) at \(763\) via
  \(582276\) and \(582916\) are \((E,E)\). Calibration, not
  CycleMin.

## Formalization

None added. Uniqueness is already `odd_preimage_unique` /
`oddLanding_preimage_unique`. Valley return is already
`cycleMin_not_end_odd`. Floor cells are already `even_preimage_iff`
/ `odd_preimage_iff`. Paper A is unchanged. Do not add
`FirstCollision.lean`.

## Results

- **Factorization** — **EXACT — HUMAN PROOF** /
  **REPARAMETERIZATION**: first \(\Leftrightarrow t\notin C\);
  CycleMin constrains only the cyclic-parent type
  (`cycle_first_collision/summary.json`).
- **Valley occupancy** — **COMPUTATIONALLY VERIFIED**:
  \(\lvert\mathrm{Pred}_E\rvert=n=10^6+1\); odd-cell Type 0;
  \((E,E)\) count \(n(n-1)/2\); \((O,\ast)\) empty.
- **Type-2 odd witness** — **COMPUTATIONALLY VERIFIED**:
  \(25\to 125\), \(t<x\), \(\lvert\mathrm{Pred}_E\rvert=125\);
  \(502\) odd Type-2 images in the window.
- **Joint observable** — **REPARAMETERIZATION**: offset equals
  the cube-gap; nearest-even gap \(1\); both parent types on
  every odd start in \([13,2001)\).
- **Calibration** — **COMPUTATIONALLY VERIFIED**: both named
  forks are \((E,E)\); \(763\) has empty odd cell.
- **No new cyclic obstruction.**

## Open questions

None from the first exact collision. Do not reopen the
first-intersection taxonomy, the general first-collision
branch, the entry corridor, the cyclic seam, seam sliding, or
twin-flight. Do not build a pair-census engine. Do not claim
termination.

## Decision

**CLOSE**. Collision Factorization holds: a first meeting is
exactly an off-cycle parent of a cycle point. CycleMin
constrains only which parent can be cyclic — even at the
valley, the unique odd parent on an odd arrival — and the
transient is then any other parent. Every empty type is
`odd_preimage_unique` or `cycleMin_not_end_odd`. Mixed placement
of \((c,t^3)\) in the square interval is the archived cube-gap.
Even-even gaps are free in \(\mathrm{Pred}_E\). The odd feeder
from below is empty-odd-preimage occupancy, not a new pair law.
That is useful negative knowledge; it is not a new invariant.
No Paper A edit, no ledger row, no new Lean, no \(N_0\) raise,
no finance reopen, no twin-flight census.

Best next question: none from this pair.

## Publication assessment

Status: `ARCHIVED`. Laboratory negative knowledge on the
geometry of a first-collision pair; not a second manuscript
and not a Paper A edit.

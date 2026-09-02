# Juggler cycle-lift ancestry drop

Status: **ARCHIVED**

Directed follow-up of the closed
[first exact collision](juggler_cycle_first_collision.md)
and the closed
[seam ancestry graph](juggler_cycle_seam_ancestry.md),
not a reopen of those branches and not a new paper. The
parent-fibre census throws away the integer parent, the
ancestry depth, and the period. This phase keeps that triple
and asks whether the cycle-lift equation produces a drop
below the CycleMin minimum.

Not a halt theorem, not a leftover-killer, not a finance
reopen, and not a claim that every positive integer reaches 1.

## Problem

An off-cycle parent \(t\) of a cycle point and the cyclic
parent \(c\) satisfy

\[
c=T^L(t),\qquad T(t)=T(c),\qquad t\ne c.
\]

Does CycleMin force \(T^L(t)<n\)? If it does, the lift
identity \(T^L(t)=c\ge n\) is contradicted and the
initial-cycle intersection is empty.

## Exact statement

**Lift identity (EXACT — HUMAN PROOF /
REPARAMETERIZATION).**
If \(T(t)=T(c)\) then \(T^k(t)=T^k(c)\) for every
\(k\ge 1\). If also \(T^L(c)=c\), then \(T^L(t)=c\).
There is no extra parent-identity condition. On images
\(x\in[1,200]\) every multi-parent fibre has identical
futures through \(12\) steps.

**CycleMin forbids the drop (EXACT — HUMAN PROOF).**
Every cycle point is \(\ge n\), so \(c\ge n\) and
\(T^L(t)=c\ge n\). The hoped-for inequality \(T^L(t)<n\)
is the opposite of the lift.

**The sink is the only known cycle
(COMPUTATIONALLY VERIFIED).**
\(n=1\), \(L=1\), \(c=1\), \(t=2\): \(T(2)=1\not<1\).
Depth-\(2\) grandparents \(\{4,6,8\}\) satisfy
\(T^{2}(s)=1\not<1\).

**Valley last-even scale (KNOWN /
REPARAMETERIZATION).**
If the first meeting is the CycleMin valley, the cyclic
parent sits in the last-even cell \([n^2,(n+1)^2)\). Every
off-cycle even parent of \(n\) therefore lands at a point
\(\ge n^2\) after one circuit. Checked at \(n=13,25,10^6+1\).

**Odd feeders start below \(n\) and land at scale \(n^2\)
(COMPUTATIONALLY VERIFIED / REPARAMETERIZATION).**
Type-2 witness \(25\to 125\): \(t<x\) but \(T(t)=x\). If
\(125\) were a valley, the circuit image would be an even
in \([125^2,126^2)\). The only parents that start below the
image are sent *up*, not down.

**Parent identity is forgotten after one step
(KNOWN / REPARAMETERIZATION).**
The even cell has a constant next state
(`preimage_same_next_state`, `first_even_freeze`). An odd
parent, if present, joins the same point. After one step
the future does not depend on \(t\). Ancestry depth only
shifts the index: \(T^{d}(s)=x\) implies
\(T^{d+L-1}(s)=c\).

**Eventual descent is not a circuit drop
(KNOWN).**
The ordinary fork \(100\to 10\leftarrow 102\) shares a
future and later reaches \(1\). That is termination of a
transient, not \(T^L(t)<n\) on a period-\(L\) cycle.

No cycle of any length — not claimed.

## Current literature

- Unique odd cell —
  **EXACT — LEAN VERIFIED**
  (`odd_preimage_unique`, `oddLanding_preimage_unique`)
- Even cell constant next state —
  **EXACT — LEAN VERIFIED**
  (`even_preimage_iff`, `preimage_same_next_state`,
  `first_even_freeze`)
- CycleMin cannot end odd —
  **EXACT — LEAN VERIFIED**
  (`cycleMin_not_end_odd`)
- Last-even cell \([n^2,(n+1)^2)\) —
  **EXACT — LEAN VERIFIED**
  (`cycle_last_even_interval`)
- Collision Factorization, first \(\Leftrightarrow t\notin C\) —
  **CLOSE** / **REPARAMETERIZATION**
  ([juggler_cycle_first_collision.md](juggler_cycle_first_collision.md))
- Parent-type / phase ancestry graph —
  **CLOSE** / **REPARAMETERIZATION**
  ([juggler_cycle_seam_ancestry.md](juggler_cycle_seam_ancestry.md))
- General first-collision / ancestry —
  **CLOSE**
  ([juggler_first_collision.md](juggler_first_collision.md))
- First-intersection taxonomy —
  **CLOSE**
  ([juggler_cycle_intersection_taxonomy.md](juggler_cycle_intersection_taxonomy.md))
- Entry corridor; trailing \(\mathtt{EE}\) count
  \(n(n^2+n+1)\) —
  **CLOSE**
  ([juggler_cycle_entry_corridor.md](juggler_cycle_entry_corridor.md))
- Collatz-style financing —
  **known** (`simons-de-weger-2005-collatz-m-cycles`)
- Every start reaches 1 — not claimed

Project relationship: **refuted** as a circuit-drop
obstruction; the lift equation is a **REPARAMETERIZATION**
of determinism plus periodicity; the even-fibre future is
`preimage_same_next_state`.

## Branch budget

```text
Mathematical target     Does CycleMin force T^L(t) < n for
                        every off-cycle parent t of a cycle
                        point, i.e. T(t)=T(c), t!=c,
                        T^L(c)=c?
Novelty hypothesis      parent identity + ancestry depth +
                        period give a drop below the minimum
                        that kills initial-cycle intersection
Falsifier               lift identity T^L(t)=c together with
                        CycleMin c>=n; sink 2->1; valley
                        last-even scale n^2; identity
                        forgotten after one step
Existing machinery      floor_power; even_preimage /
                        odd_preimage_unique; cycleMin_not_end_odd;
                        cycle_last_even_interval;
                        preimage_same_next_state;
                        first_even_freeze; Collision
                        Factorization
Maximum Phase-0 scope   prove the lift identity; calibrate
                        the sink and depth-2 grandparents;
                        check futures on fibres x<201;
                        last-even scale at 13, 25, 10^6+1;
                        Type-2 25->125; named fork 100/102.
                        No Lean, no finance, no CLI, no
                        Paper A
Promotion criterion     a drop T^{d+L-1}(s) < n that is not
                        the lift identity and not
                        termination
Stop criterion          T^L(t)=c>=n at every depth; parent
                        identity forgotten after one step;
                        the drop is the opposite inequality
```

## Closed-bridge gates

Do not reopen first-collision, the seam ancestry graph,
the first-intersection taxonomy, the entry corridor, the
cyclic seam, seam sliding, seam propagate, twin-flight,
or finance.

- **CLOSE** if \(T^L(t)=c\ge n\).
- **CLOSE** if the sink \(2\to 1\) fails the drop.
- **CLOSE** if the valley circuit image sits in the
  last-even cell of scale \(n^2\).
- **CLOSE** if parent identity is forgotten after one
  step (`preimage_same_next_state`).
- **CLOSE** if ancestry depth only shifts the index.
- **PROMOTE** only if a circuit drop below \(n\) survives
  those identities and is not termination.

Do **not** raise \(N_0\). Do **not** open \(L=55293\). Do
**not** reintroduce finance. Do **not** edit Paper A. Do
**not** claim termination. Do **not** add Lean.

## Explicitly out of Phase-0

A leftover-itinerary attack, a \(K=11\) proof, defect
amplification, Fourier / residues / \(Q\)-sections, a
branch-and-bound engine, ledger theorem row, new Lean,
CLI, visualization, Paper A edit, a halt theorem, a
predecessor BFS.

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Lift identity \(T^L(t)=c\) —
  **EXACT — HUMAN PROOF** / **REPARAMETERIZATION** of
  determinism plus periodicity
- CycleMin drop \(T^L(t)<n\) —
  **REFUTED** (opposite of \(c\ge n\))
- Sink \(2\to 1\) —
  **KNOWN**; \(T(2)=1\not<1\)
- Valley last-even scale \(n^2\) —
  **KNOWN** (`cycle_last_even_interval`)
- Parent-identity erasure —
  **KNOWN** (`preimage_same_next_state`)
- Ancestry-depth shift —
  **REPARAMETERIZATION** of the same identity
- Cycle-lift leftover-killer —
  **REFUTED** (`juggler_cycle_lift_ancestry`)
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_lift_ancestry`
- Dataset: `data/research/juggler/cycle_finance/cycle_lift_ancestry/summary.json`
- Tests: `tests/research/juggler_sequence/test_cycle_lift_ancestry.py`
- Window: lift identity on \(x\in[1,200]\), horizon \(12\);
  sink \(1\) with \(t=2\) and grandparents \(\{4,6,8\}\);
  last-even scale at \(13\), \(25\), \(10^6+1\); Type-2
  \(25\to 125\); fork \(100,102\to 10\); depth-\(2\) scan
  on \(x<40\). Fast suite only. No CLI. No new Lean.

## Conjectures

`juggler_cycle_lift_ancestry` — **REFUTED**.

## Counterexamples

- Lift identity: \(T(t)=T(c)\) and \(T^L(c)=c\) imply
  \(T^L(t)=c\). Falsifier of an independent circuit map.
- Sink: \(T(2)=1\not<1\). Depth-\(2\): \(T^2(4)=T^2(6)=T^2(8)=1\).
  Falsifier of the drop on the only known cycle.
- Last-even cell \([n^2,(n+1)^2)\) at \(n=13,25,10^6+1\).
  Falsifier of a valley circuit image below \(n\).
- Type-2 \(25\to 125\): \(t<x\) but \(T(t)=x\); a valley
  circuit would land at scale \(125^2\). Falsifier of
  “small feeders drop”.
- Futures agree on every multi-parent fibre \(x\in[1,200]\)
  and on \(100,102\to 10\). Falsifier of surviving parent
  identity. Eventual descent of that fork is termination,
  not a circuit drop.

## Formalization

None added. The even-fibre future is already
`preimage_same_next_state` / `first_even_freeze`. The last-even
cell is already `cycle_last_even_interval`. Valley return
is already `cycleMin_not_end_odd`. Paper A is unchanged.
Do not add `CycleLiftAncestry.lean`.

## Results

- **Lift identity** — **EXACT — HUMAN PROOF** /
  **REPARAMETERIZATION**: \(T^L(t)=c\)
  (`cycle_lift_ancestry/summary.json`).
- **Drop** — **REFUTED**: CycleMin forces \(c\ge n\).
- **Sink** — **COMPUTATIONALLY VERIFIED**: \(T(2)=1\);
  depth-\(2\) grandparents land on \(1\).
- **Valley scale** — **KNOWN**: last-even \(\ge n^2\).
- **Type-2** — **COMPUTATIONALLY VERIFIED**: \(25<125\),
  circuit scale \(n^2\) if \(125\) were a valley.
- **Parent identity** — **KNOWN**: forgotten after one
  step; depth only shifts the index.
- **No new cyclic obstruction.**

## Open questions

None from the cycle-lift drop. Do not reopen first-collision,
seam ancestry, or the entry corridor. Do not treat eventual
descent of a transient as a circuit inequality. Do not claim
termination.

## Decision

**CLOSE**. The boxed equation is a genuine cycle-lift, and
it does use the information the fibre census throws away.
The information does not survive: after one step every
parent of the same image has the same future, and after
one circuit that future is the cyclic parent \(c\ge n\).
CycleMin therefore forces the opposite of a drop below
\(n\). The only known cycle already fails the drop. Odd
feeders that start below the image land at last-even scale
\(n^2\). Ancestry depth only relabels the same identity.
That is useful negative knowledge; it is not a new
invariant. No Paper A edit, no ledger row, no new Lean,
no \(N_0\) raise, no finance reopen.

Best next question: none from this lift drop.

## Publication assessment

Status: `ARCHIVED`. Laboratory negative knowledge on a
CycleMin circuit-drop of off-cycle parents; not a second
manuscript and not a Paper A edit.

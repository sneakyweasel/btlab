# Juggler first-collision / ancestry classification

Status: **ARCHIVED**

Standalone application phase on the Juggler floor-power map. It is
**not** a reopen of the closed first-intersection / cyclic-seam /
entry-corridor / seam-sliding / seam-propagate stack, not twin-flight,
not a predecessor BFS, not a leftover-killer, not Paper A, and not a
claim that every positive integer reaches 1.

The closed first-intersection taxonomy asked for the first shared
point of a climb **with a cycle**. This phase asks the general
cross-word question: when do two realizing words first meet?

## Problem

Characterize
\[
T_u(n)=T_v(m)=x
\]
with no earlier shared state, starting from the four last-letter
parent types \(\mathtt{EE}\), \(\mathtt{EO}\), \(\mathtt{OE}\),
\(\mathtt{OO}\).

## Exact statement

Write \(n=n_0\xrightarrow{u_1}\cdots\xrightarrow{u_{|u|}}n_{|u|}=T_u(n)\)
for a realizing word. A **first collision** is \(n\neq m\), both
words nonempty and realizing, \(T_u(n)=T_v(m)=x\), and
\[
\{n_0,\ldots,n_{|u|-1}\}\cap\{m_0,\ldots,m_{|v|-1}\}=\emptyset.
\]
The **parent type** is the ordered pair
\((u_{|u|},v_{|v|})\in\{E,O\}^2\). The last parents are
\(n_{|u|-1}\) and \(m_{|v|-1}\). Meetings at the known sink
\(\{1,2\}\) are excluded from the occupancy table, as in
twin-flight; the sink exception is recorded separately.

**First collision iff distinct last parents
(KNOWN / REPARAMETERIZATION), off the sink.**
A deterministic map that shares any earlier state \(y\neq x\)
shares the tail from \(y\), hence the same last parent. Equal last
parents already met at that parent. On itinerary pairs with
\(1\le|u|,|v|\le 3\) and starts \(\le 400\), excluding meetings at
\(\{1,2\}\), the iff holds on \(9375\) meetings (\(5642\) first,
\(3733\) same-parent).

**\(\mathtt{OO}\) is empty (KNOWN / EXACT — LEAN VERIFIED).**
At most one odd parent (`odd_preimage_unique`,
`oddLanding_preimage_unique`). Two odd arrivals already agreed at
that parent, so the meeting is not first. One-step \(\mathtt{OO}\)
count is \(0\) on every \(x\in[3,400]\).

**\(\mathtt{OE}\) / \(\mathtt{EO}\) are the mixed cell
(KNOWN / REPARAMETERIZATION).**
The odd side is the unique odd parent if it exists; the even side
is \(\mathrm{Pred}_E(x)\). Ordered one-step counts on
\(x\in[3,400]\) are \(4288\) each, matching
\(|\mathrm{Pred}_O|\cdot|\mathrm{Pred}_E|\). Witness
\(5\xrightarrow{O}11\leftarrow_{E}122\).

**\(\mathtt{EE}\) is distinct even-cell pairs
(KNOWN / REPARAMETERIZATION).**
Ordered one-step count \(21413594\) on \(x\in[3,400]\), matching
\(P(P-1)\) for \(P=|\mathrm{Pred}_E(x)|\). Fibres match
`even_preimage`. Witness \(100\to 10\leftarrow 102\). Same last parent
is not first: \(16\xrightarrow{EE}2\leftarrow_{EE}18\) share \(4\).
The two-step count \(n(n^2+n+1)\) stays archived with the entry
corridor.

**Sink overshoot is the known \(2\to 1\) loop
(KNOWN).**
Including meetings at \(\{1,2\}\) breaks the iff:
\(4\xrightarrow{EEO}1\leftarrow_{E}2\) has distinct last parents
\(1\) and \(2\) but already shared \(2\). One word walked past the
first meeting along \(2\to 1\to 1\). That is not a new seam.

No cycle of any length — not claimed.

## Current literature

- Floor-power map — **KNOWN** (`oeis-A094683`,
  `pickover-1991-computers-imagination`)
- Unique odd cell —
  **EXACT — LEAN VERIFIED**
  (`odd_preimage_unique`, `oddLanding_preimage_unique`)
- Even square cell —
  **EXACT — LEAN VERIFIED** (`even_preimage_iff`)
- First-intersection taxonomy —
  **CLOSE** / **REPARAMETERIZATION**
  ([juggler_cycle_intersection_taxonomy.md](juggler_cycle_intersection_taxonomy.md))
- CycleMin \(2{+}2\) seam \(\{\mathtt{OE}\mid\mathtt{OO},\mathtt{EE}\mid\mathtt{OO}\}\) —
  **CLOSE**
  ([juggler_cycle_cyclic_seam.md](juggler_cycle_cyclic_seam.md))
- Trailing-\(\mathtt{EE}\) count \(n(n^2+n+1)\) —
  **CLOSE**
  ([juggler_cycle_entry_corridor.md](juggler_cycle_entry_corridor.md))
- Seam sliding witness \(100\to 10\leftarrow 102\) —
  **CLOSE**
  ([juggler_cycle_seam_sliding.md](juggler_cycle_seam_sliding.md))
- Twin-flight sink convention —
  **CLOSE**
  ([juggler_twin_flight.md](juggler_twin_flight.md))
- Backward predecessor geometry —
  **CLOSE** as `BACKWARD_COMPLEX`
  ([juggler_backward_geometry.md](juggler_backward_geometry.md))
- Every start reaches 1 — not claimed

Project relationship: **independent**, then **refuted** as a new
seam. The four-type table is a **REPARAMETERIZATION** of the
one-step cells plus shared-tail determinism.

## Branch budget

```text
Mathematical target     For nonempty itinerarys u,v, when is
                        T_u(n)=T_v(m)=x a first collision,
                        and what do the four last-letter
                        types EE, EO, OE, OO force?
Novelty hypothesis      parent type plus the first-collision
                        cut is a new seam: some type empties
                        or thins in a way that is not the
                        one-step cells
Falsifier               first collision iff last parents
                        differ; OO empty by odd_preimage_unique;
                        OE/EO = unique odd parent x even cell;
                        EE = distinct even-cell pairs
Existing machinery      pred_even / pred_odd
                        (backward_geometry.py);
                        even_preimage / odd_preimage_integers
                        (floor_cells.py); follows_itinerary /
                        image_after (compensated_contraction.py);
                        odd_preimage_unique; ee_entry_count
Maximum Phase-0 scope   define first collision; one-step
                        parent census on x <= 400; check
                        first_collision <=> distinct last
                        parents on |u|,|v| <= 3 samples;
                        one witness per occupied type.
                        No Lean, no finance, no CLI, no
                        |u|>=4 census, no Pred BFS
Promotion criterion     a fibre, emptiness, or word-pair
                        restriction that is not odd uniqueness,
                        the even cell, determinism, trailing-EE,
                        twin-flight, or NC inversion
Stop criterion          the four-type table is the cell law
                        plus "deterministic maps share tails";
                        or machinery gravity
```

## Closed-bridge gates

Do not reopen the first-intersection taxonomy, the cyclic seam,
the entry corridor, seam sliding, or seam propagate. Do not
reopen twin-flight or backward geometry.

- **CLOSE** if first collision iff distinct last parents.
- **CLOSE** if OO is `odd_preimage_unique`.
- **CLOSE** if OE/EO is the unique odd parent times the even cell.
- **CLOSE** if EE is distinct even-cell pairs (two-step count
  \(n(n^2+n+1)\) stays archived; do not reopen the corridor).
- **PROMOTE** only if a type empties or thins for a reason that
  is not a cell or shared-tail determinism.

Do **not** raise \(N_0\). Do **not** treat this as a leftover-killer.
Do **not** reintroduce finance. Do **not** edit Paper A. Do **not**
rebuild a predecessor BFS. Do **not** open a \(|u|\ge 4\) census.

## Explicitly out of Phase-0

A leftover-itinerary attack, finance, \(N_0\) raise, ledger row, new
Lean, CLI, visualization, Paper A edit, a collision graph, a
length-4 ancestry engine.

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- First collision iff distinct last parents —
  **KNOWN** / **REPARAMETERIZATION** of determinism, off
  \(\{1,2\}\)
- \(\mathtt{OO}\) first meeting —
  **KNOWN** empty (`odd_preimage_unique`)
- \(\mathtt{OE}\) / \(\mathtt{EO}\) —
  **KNOWN**; unique odd parent times \(\mathrm{Pred}_E(x)\)
- \(\mathtt{EE}\) —
  **KNOWN**; distinct even-cell pairs
- Sink overshoot \(4\xrightarrow{EEO}1\leftarrow_{E}2\) —
  **KNOWN**; the \(2\to 1\) loop
- First-collision new seam —
  **REFUTED** (`juggler_first_collision`)
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.first_collision`
- Dataset: `data/research/juggler/first_collision/`
- Tests: `tests/research/juggler_sequence/test_first_collision.py`

One-step census on \(x\le 400\), sink \(\{1,2\}\) excluded;
itinerary pairs with \(1\le|u|,|v|\le 3\) and starts \(\le 400\);
witnesses \(100,102\to 10\), \(5,122\to 11\), same-parent
\(16,18\to 2\), sink overshoot \(4,2\to 1\). No CLI. No Lean.

## Conjectures

`juggler_first_collision` — **REFUTED**.

## Counterexamples

- `odd_preimage_unique`: two odd parents of the same image cannot
  exist. Falsifier of \(\mathtt{OO}\) as a first-collision type.
- One-step fibres equal `even_preimage` / `odd_preimage_integers` on
  \(x\le 400\). Falsifier of a thinner OE/EO or EE channel.
- Itinerary iff on \(9375\) non-sink meetings. Falsifier of a
  first-collision cut that is not distinct last parents.
- \(4\xrightarrow{EEO}1\leftarrow_{E}2\): distinct last parents
  after the orbits already joined. Falsifier of the iff on the
  sink; not a new type, the known loop.

## Formalization

None added. The uniqueness lemma is already
`odd_preimage_unique` / `oddLanding_preimage_unique`. The even cell
is already `even_preimage_iff`. Paper A is unchanged. Do not add
`FirstCollision.lean`.

## Results

Classification **FIRST_COLLISION_CLOSED**.

- **Iff** — **KNOWN** / **REPARAMETERIZATION**: off \(\{1,2\}\),
  first collision iff last parents differ.
- **\(\mathtt{OO}\)** — **EXACT — LEAN VERIFIED**: empty
  (`odd_preimage_unique`).
- **\(\mathtt{OE}\) / \(\mathtt{EO}\)** — **KNOWN**: \(4288\)
  one-step pairs each on \(x\in[3,400]\).
- **\(\mathtt{EE}\)** — **KNOWN**: \(21413594\) ordered distinct
  even-parent pairs on the same window.
- **Sink** — **KNOWN**: overshoot along \(2\to 1\to 1\).
- **No new seam.**

## Open questions

None from first-collision / ancestry. Do not open a length-4
census. Do not add `FirstCollision.lean`. Do not reopen the
cycle first-intersection stack.

## Decision

**CLOSE**. The four parent types are the one-step cells. First
collision is distinct last parents, except on the known sink
loop where a longer word can walk past the first meeting.
That is useful negative knowledge; it is not a new invariant.
No Paper A edit, no ledger row, no new Lean, no \(N_0\) raise,
no finance reopen, no leftover-killer.

Best next question: none from first-collision / ancestry.

## Publication assessment

Status: `ARCHIVED`. Laboratory negative knowledge on a
cross-word first-collision refinement; not a second manuscript
and not a Paper A edit.

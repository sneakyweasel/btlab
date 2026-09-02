# Juggler square-seam cycle lemma

Status: **EXPLORATORY**

Standalone structural check of isolated perfect-square states as
algebraic junctions on a hypothetical cycle. It is **not** a
reopen of exact-floor impact, not a cyclic-seam word-cut, not a
leftover-killer, and not a claim that every positive integer
reaches 1.

## Problem

If a nontrivial cycle contains an isolated square, what exact
two-sided constraints do the odd seam \(s^2\to s^3\) and the
isolated even seam \(k^2\to k\) impose on the incoming parent and
the outgoing arc?

## Exact statement

Split the map. Do not write \(J(s^2)=s^3\) for every square.

- **Odd isolated seam.** \(s\) odd and not a square, \(x=s^2\).
  Then \(J(x)=s^3\) exactly, local defect \(0\), next letter \(O\).
  Isolated because \(s^3\) is a square iff \(s\) is.
- **Even isolated seam.** \(k\) even and not a square, \(x=k^2\).
  Then \(J(x)=k\) exactly, local defect \(0\), next letter \(E\).

An incoming parent \(y\) of the square is either an even cell
occupant or the unique odd-cell occupant. An outgoing arc starts
at the exact image. Phase 0 asks whether those two arcs, coupled
through the same integer \(s\) or \(k\), yield a word factor, a
strictly stronger finance identity, or a Diophantine restriction
that is not `even_cell_iff`, `odd_cell_unique`, CycleMin
square-scale, or a vanishing local in the global-defect identity.
This says nothing about totality.

Consecutive exact steps are the existing monochrome tower and are
out of scope.

## Current literature

- Exact iff square —
  **EXACT — LEAN VERIFIED** (`localDefect*_eq_zero_iff`).
- Image of an odd square is the cube —
  **EXACT — LEAN VERIFIED** (`floorPower_odd_sq_eq_cube_iff_square`,
  `isSquare_pow_three_iff`).
- Even / odd parents —
  **EXACT — LEAN VERIFIED** (`even_cell_iff`, `odd_cell_unique`).
- CycleMin is odd; even states \(\ge n^2\); last even is the
  cell \([n^2,(n+1)^2)\), not the point \(n^2\) —
  **EXACT — LEAN VERIFIED** / last-even square **REFUTED**
  (`J-cyclemin-short-even-not-square`).
- Even tower \(2^{2^{r-1}}\) reaches 1 —
  **EXACT — LEAN VERIFIED** (`even_tower_to_one`).
- Certified floor \(N_0=162849448\) —
  every \(n\le N_0\) reaches 1, so no square \(\le N_0\) can sit
  on a nontrivial cycle. That is the floor, not a seam theorem.
- Exact-floor impact —
  **CLOSE** ([juggler_exact_floor_impact.md](juggler_exact_floor_impact.md)).
- Cyclic seam types —
  **CLOSE** / archived
  ([juggler_cycle_cyclic_seam.md](juggler_cycle_cyclic_seam.md)).
  Those are word cuts at CycleMin, not square states.

Project relationship: **reproduced** the cell and CycleMin
package; **refuted** as a new cycle-junction law.

## Branch budget

```text
Mathematical target     If a nontrivial cycle contains an isolated
                        square, what exact two-sided constraints do
                        the odd seam s^2 -> s^3 and the even seam
                        k^2 -> k impose on the incoming parent and
                        the outgoing arc?
Novelty hypothesis      The zero-defect junction couples W- and W+
                        through one integer s (or k) and yields a
                        word factor, a strictly stronger finance
                        identity, or a Diophantine restriction on s
                        that is not even_cell_iff / odd_cell_unique /
                        CycleMin square-scale / global defect
Falsifier               Both seams rewrite as the existing cells plus
                        localDefect=0; local word is *OO (odd) or
                        *EE (even) by parity of the image; a zero
                        crumb saves O(1/x) and does not move any
                        leftover; short W+/- closure is a cell
                        composition or the small-cycle census
Existing machinery      localDefect*_eq_zero_iff, even_cell_iff,
                        odd_cell_unique, cycleMin_even_ge_sq,
                        cycle_last_even_interval, cycleMin_start_odd,
                        even_tower_to_one, cycleMin_finance,
                        isSquare_pow_three_iff
Maximum Phase-0 scope   Write both local identities; check odd-parent
                        occupancy and even-interval width on s,k <= 200;
                        algebra for CycleMin = odd square; one-crumb
                        finance saving vs leftover scale; short
                        |W+/-| <= 3 closure only as a cell check.
                        No orbit census, no leftover campaign
Promotion criterion     A constraint on s or on the two arcs that is
                        not a cell, CycleMin lemma, or d_i=0 in the
                        global-defect identity
Stop criterion          All three slogans reduce to KNOWN /
                        REPARAMETERIZATION; any GPU atlas, Paper A,
                        N0, DK, or cyclic-seam reopen
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Isolated odd seam \(s^2\to s^3\), crumb 0, increment
  \(\log_2(3/2)\) —
  **EXACT — LEAN VERIFIED** (existing one-step odd equality)
- Isolated even seam \(k^2\to k\), crumb 0, increment \(-1\) —
  **EXACT — LEAN VERIFIED** (existing one-step even equality)
- Local word `*OO` / `*EE` is a new CycleMin obstruction —
  **REFUTED**; `*OO` is the CycleMin launch; incoming types are
  the archived cyclic-seam pair \(\mathtt{OE}\mid n\mid\mathtt{OO}\)
  and \(\mathtt{EE}\mid n\mid\mathtt{OO}\)
- CycleMin \(=\) odd square adds a scale law beyond \(d_0=0\) —
  **REFUTED**; OO suffix and last-even cell are the standard
  identities with \(n=s^2\)
- One vanishing crumb is a leftover-mover —
  **REFUTED**; odd save \(5.77\cdot 10^{-13}\) at the first odd
  square above \(N_0\); even save \(\le 7.37\cdot 10^{-9}\) under
  `cycleMin_even_ge_sq`
- Short \(W_\pm\) closure is a new Diophantine on \(s\) —
  **REFUTED**; \(|W_\pm|\le 3\) through an isolated square is a
  period \(\le 7\) cycle, already excluded, and none occur on
  roots \(\le 30\)
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.square_seam`
- Artifact:
  `data/research/juggler/square_seam/summary.json`
- Note: [juggler_square_seam.md](../research/juggler_square_seam.md)
- Tests:
  `tests/research/juggler_sequence/test_square_seam.py`

Odd/even identities and parent cells on roots \(\le 200\).
CycleMin-is-square algebra on those odd roots. Finance saving
at the first isolated roots with square \(>N_0\). Short
\(|W_\pm|\le 3\) closure on roots \(\le 30\). No GPU. No atlas
recensus. No Lean. No \(N_0\) raise. No leftover campaign.

## Conjectures

None opened. Computational observations are not conjectures.

## Counterexamples

- “\(J(s^2)=s^3\) for every square” — even isolated witness
  \(36\to 6\), \(100\to 10\).
- “Odd entrance is a new thin-cell law” — it is
  `odd_cell_unique`; 5 of 93 isolated odd roots \(\le 200\) have
  an odd parent, never more than one. Even width is \(2q+1\).
- “Square CycleMin tightens the last-even cell” — the cell is
  \([n^2,(n+1)^2)=[s^4,(s^2+1)^2)\), the standard even cell of
  image \(n\).
- “A short two-sided word around the seam can close” — 0 hits
  for \(|W_\pm|\le 3\) on isolated roots \(\le 30\).

## Formalization

None new. Cells, defect, CycleMin, and `even_tower_to_one` stay
where they are. No `SquareSeam.lean`. Paper A is unchanged. No
`sorry`.

## Results

Classification **SQUARE_SEAM_REPARAMETERIZATION**.

- Identities: every isolated odd root \(s\le 200\) has
  \(J(s^2)=s^3\), crumb 0, local word `*OO`; every isolated even
  root \(k\le 200\) has \(J(k^2)=k\), crumb 0, local word `*EE`.
  Fixtures \(9\to 27\), \(36\to 6\), \(100\to 10\).
- Entrance: odd parents unique (5 occupied of 93); even width
  \(2q+1\).
- CycleMin \(=s^2\): OO suffix and last-even cell hold with no
  extra scale. The only new arithmetic is \(d_0=0\).
- Finance: not a leftover mover. Odd save \(5.77\cdot 10^{-13}\)
  at \(s_0=12763\); even save under CycleMin \(\le 7.37\cdot 10^{-9}\).
  Relative \(1/L\) at \(25781\) is \(3.88\cdot 10^{-5}\).
- Short closure: 0 odd hits, 0 even hits.

## Open questions

None from the square-seam junction. Do not reopen cyclic seams,
exact-floor impact, leftover finance, walk coboundary, or DK at
\(L=478245\). Do not raise \(N_0\).

## Decision

**CLOSE.** An isolated square on a cycle is a zero-defect step
whose incoming parent is an ordinary cell and whose outgoing
letter is forced by the parity of the image. The local words
`*OO` and `*EE` are CycleMin launch / even-to-even, not new
factors. One vanishing crumb is a global-defect special case and
does not move leftovers. Short two-sided closure is a short
cycle, already excluded. Every Phase-0 statement is `KNOWN` or
`REPARAMETERIZATION`. That is the stop criterion. Best next
question: none from this door; do not start another square-state
cycle census.

## Publication assessment

Status: `EXPLORATORY`. A negative structural reading of exact
square junctions. Not a paper candidate. No Paper A/B edit.

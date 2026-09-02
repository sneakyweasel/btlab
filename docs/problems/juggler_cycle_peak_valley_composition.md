# Juggler peak–valley interval composition

Status: **ARCHIVED**

Reviewer follow-up of the excursion necklace and the local
seam cells, not a reopen of
[juggler_cycle_seam_sliding.md](juggler_cycle_seam_sliding.md),
[juggler_cycle_e_block.md](juggler_cycle_e_block.md),
[juggler_cycle_exponent_budget.md](juggler_cycle_exponent_budget.md),
[juggler_cycle_closure.md](juggler_cycle_closure.md), or
[juggler_cycle_extremal_composition.md](juggler_cycle_extremal_composition.md),
and not a new paper. The local cells
\(V^{2^r}\le P<(V+1)^{2^r}\) and the iterated odd climb already
exist. This phase asks whether composing them around the whole
necklace forces \(P_1>P_1\) or \(P_1<P_1\) without identifying a
dangerous seam.

Not a halt theorem, not a finance leftover-killer, and not a
claim that every cycle itinerary is impossible.

## Problem

For each block
\[
P_i\xrightarrow{E^{r_i}}V_i\xrightarrow{O^{a_{i+1}}}P_{i+1},
\]
the even tower and the odd climb are exact. After one necklace,
\(P_1\mapsto P_2\mapsto\cdots\mapsto P_1\). Does that composite
interval map sit strictly off the diagonal, for a reason that is
not the itinerary envelope or an archived cell?

## Exact statement

**Exact cells compose to \(T_w\)
(KNOWN / REPARAMETERIZATION).**
The even tower \(V^{2^r}\le P<(V+1)^{2^r}\) fixes
\(V=\operatorname{isqrt}^{r}(P)\). The odd climb is iterated
`floor_power`. The composite around the necklace is the Juggler
word map. A cycle satisfies \(T_w(P)=P\), so the exact composite
cannot be \(P>P\) or \(P<P\).

**The naive exponent map is an envelope
(KNOWN / OBSERVATION).**
The slogan \(P'=\lfloor V^{3^a/2^a}\rfloor\) is the real-power
cell, not the nested climb. At \(365\), the exact first peak is
\(582276\) and \(\lfloor 365^{9/4}\rfloor=582316\); the exact
\(\mathtt{OOE}\) landing is \(763=\lfloor 365^{9/8}\rfloor\).

**One-sided composition is the itinerary envelope
(KNOWN / REPARAMETERIZATION).**
Composing \(P<(V+1)^{2^r}\) with \(P'\le V^{3^a/2^a}\) yields
\(P'\le P^{3^o/2^L}\). The block product is identically
\(3^o/2^L\). That is `power_bound_word` and the closed
exponent budget. Strict \(P'<P\) iff \(3^o<2^L\)
(`power_bound_contracts`): \(\mathtt{OE}\) is \(3/4\),
\(\mathtt{OOOEE}\) is \(27/32\). Leftover-shaped
\(\mathtt{OOEOOEOOEOE}\) is \(2187/2048>1\).

**Real slack intervals follow the exponent sign
(OBSERVATION / REPARAMETERIZATION).**
Widening \(V>P^{1/2^r}-1\) and composing the real odd climb
sits entirely below \(P\) on \(\mathtt{OOOEE}\) at the peak
\(52214\), and entirely above \(P\) on the length-11 leftover
shape at \(10^3\) and \(10^6\). That sign is \(3^o\lessgtr 2^L\),
not a new cell. Nested floors can sit below the real lower
bound; they are finance / the global defect.

**Expanding necklaces occur
(KNOWN / EXACT — LEAN VERIFIED).**
\(365\xrightarrow{\mathtt{OOE}}763\xrightarrow{\mathtt{OOE}}1749\)
(`two_block_ooe_365`). The composite is \(P'>P\), which is
expansion, not a cycle contradiction.

**Leftover interval hulls already meet
(KNOWN / REFUTED as a leftover-killer).**
The mechanical \(\mathtt{OOE}/\mathtt{OE}\) interval at
\(L=25781\) is \([986891,25482877]\) and meets the start
([juggler_cycle_closure.md](juggler_cycle_closure.md)). Do not
recompute it.

The odd fixed point \(n=1\) is not a peak–valley necklace: it
has no even letter.

No cycle of any length — not claimed.

## Current literature

- One-sided word envelope —
  **EXACT — LEAN VERIFIED**
  (`power_bound_word`, `power_bound_contracts`)
- Trailing-evens cell \(P<(V+1)^{2^r}\) —
  **EXACT — LEAN VERIFIED**
  (`cycle_trailing_evens_lt`)
- Even tower \(V^{2^r}\le P<(V+1)^{2^r}\) —
  **KNOWN**
  (`even_tower_bounds`)
- Formal expansion \(2^L<3^o\) —
  **EXACT — LEAN VERIFIED**
  (`cycle_itinerary_formally_expanding`)
- Global defect —
  **EXACT — LEAN VERIFIED**
  (`global_defect_identity`)
- Two expanding \(\mathtt{OOE}\) blocks —
  **EXACT — LEAN VERIFIED**
  (`two_block_ooe_365`)
- Cycle-wide exponent product —
  **CLOSE** / **REPARAMETERIZATION**
  ([juggler_cycle_exponent_budget.md](juggler_cycle_exponent_budget.md))
- Exact floor closure leftover-killer —
  **CLOSE** / **REFUTED**
  ([juggler_cycle_closure.md](juggler_cycle_closure.md))
- Extremal composition around one cycle —
  **CLOSE** / **REPARAMETERIZATION**
  ([juggler_cycle_extremal_composition.md](juggler_cycle_extremal_composition.md))
- Homogeneous-run sliding —
  **CLOSE** / **REPARAMETERIZATION**
  ([juggler_cycle_seam_sliding.md](juggler_cycle_seam_sliding.md))
- First-intersection \(E^r\) block —
  **CLOSE** / **REFUTED**
  ([juggler_cycle_e_block.md](juggler_cycle_e_block.md))
- Collatz-style financing —
  **known** (`simons-de-weger-2005-collatz-m-cycles`)
- Every start reaches 1 — not claimed

Project relationship: **refuted** as a necklace-level
\(P>P\)/\(P<P\) termination route; exact composition is
\(T_w\); the real sign is the closed exponent budget.

## Branch budget

```text
Mathematical target     Does composing the exact peak–valley cells
                        P --E^r--> V --O^a--> P' around a necklace
                        force P>P or P<P, without identifying a
                        dangerous seam, for a reason that is not
                        power_bound / trailing-evens / the closed
                        exponent budget / cycle_closure?
Novelty hypothesis      the unit of proof becoming the whole
                        necklace yields a global inconsistency the
                        local cells do not
Falsifier               exact cells compose to T_w (a cycle has
                        P=P); one-sided composition is 3^o/2^L;
                        leftover itineraries expand; slack sign is the
                        exponent gap; mechanical hulls meet
Existing machinery      even_tower_bounds; cycle_trailing_evens_lt;
                        power_bound_word; power_bound_contracts;
                        circuits(); two_block_ooe_365; exponent
                        budget CLOSE; cycle_closure CLOSE
Maximum Phase-0 scope   block parser; exponent identity; exact vs
                        one-sided vs slack composition on OE,
                        OOOEE, OOE^2, L=11 leftover; cite the
                        mechanical meeting. No Lean, no finance,
                        no Paper A, no leftover census
Promotion criterion     a necklace-level P>P or P<P that is not
                        the exponent gap or an archived cell
Stop criterion          composition is T_w or power_bound;
                        leftover real intervals follow 3^o>2^L
```

## Closed-bridge gates

Do not reopen seam sliding, the \(E^r\) block, the exponent
budget, cycle closure, or extremal composition.

- **CLOSE** if exact cells compose to \(T_w\).
- **CLOSE** if the one-sided product is \(3^o/2^L\).
- **CLOSE** if leftover-shaped words have \(3^o>2^L\).
- **CLOSE** if real slack intervals sit above \(P\) exactly
  when the itinerary expands and below \(P\) exactly when it
  contracts.
- **CLOSE** if the leftover hull meeting is the closed
  cycle-closure record.
- **PROMOTE** only if a necklace emptiness appears that is
  not the exponent gap or an archived cell.

Do **not** raise \(N_0\). Do **not** open \(L=55293\). Do
**not** reintroduce finance. Do **not** edit Paper A. Do
**not** add Lean.

## Explicitly out of Phase-0

A \(K=11\) proof, defect amplification, Fourier / residues /
\(Q\)-sections, a branch-and-bound engine, ledger row, new Lean,
CLI, visualization, Paper A edit, an even-preimage leftover-killer.

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Exact peak–valley composite —
  **REPARAMETERIZATION** of \(T_w\)
- Block exponent product —
  **REPARAMETERIZATION** of `power_bound_word` / the closed
  exponent budget
- Contracting real interval on \(\mathtt{OOOEE}\) —
  **REPARAMETERIZATION** of `power_bound_contracts`
- Expanding real interval on leftover shape \(2187/2048\) —
  **REPARAMETERIZATION** of formal expansion
- \(365\to 1749\) —
  **KNOWN** (`two_block_ooe_365`)
- Mechanical meeting at \(L=25781\) —
  **KNOWN** / cycle-closure **REFUTED** leftover-killer
- Necklace \(P>P\) or \(P<P\) termination —
  **REFUTED** (`juggler_cycle_peak_valley_composition`)
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_peak_valley_composition`
- Dataset: `data/research/juggler/cycle_finance/peak_valley_composition/summary.json`
- Tests: `tests/research/juggler_sequence/test_cycle_peak_valley_composition.py`
- Window: identities at \(7/\mathtt{OE}\), \(25/\mathtt{OOOEE}\),
  \(365/\mathtt{OOE}\) and \(\mathtt{OOEOOE}\); slack at leftover
  peaks \(10^3,10^6\); naive versus exact at \(365\). Fast suite
  only. No CLI. No new Lean.

## Conjectures

`juggler_cycle_peak_valley_composition` — **REFUTED**.

## Counterexamples

- Exact cells compose to \(T_w\): \(25\xrightarrow{\mathtt{OOOEE}}15\),
  \(365\xrightarrow{\mathtt{OOEOOE}}1749\). Falsifier of a
  multi-valued interval map that a cycle would miss.
- Block product is \(3^o/2^L\): \(\mathtt{OOOEE}\) is \(27/32\),
  leftover \(\mathtt{OOEOOEOOEOE}\) is \(2187/2048\). Falsifier of
  a new one-sided necklace bound.
- Real slack on \(\mathtt{OOOEE}\) at peak \(52214\) is
  \([7591,9564]\subset(-\infty,52214)\). Falsifier of a
  contracting inequality that is not the exponent gap.
- Real slack on the length-11 leftover at \(10^6\) is
  \([2.537\cdot 10^6,2.554\cdot 10^6]\subset(10^6,\infty)\).
  Falsifier of leftover \(P'<P\).
- \(365\to 1749\). Falsifier of a universal \(P'<P\) necklace.
- Mechanical interval \([986891,25482877]\) at \(L=25781\) meets
  the start. Falsifier of leftover emptiness by composed cells.

## Formalization

None added. The envelope is already `power_bound_word`. The
even cell is already `cycle_trailing_evens_lt`. The expanding
witness is already `two_block_ooe_365`. Paper A is unchanged.
Do not add `PeakValleyComposition.lean`.

## Results

- **Functional** — **KNOWN** / **REPARAMETERIZATION**
  (`peak_valley_composition/summary.json`): valley composite
  equals `follow_word`; peak composite equals the rotated
  spelling.
- **Exponent** — **REPARAMETERIZATION** of `power_bound_word`
  and the closed exponent budget.
- **Sign** — **OBSERVATION**: real slack sits below \(P\) on
  contracting itineraries and above \(P\) on expanding itineraries.
- **No new cyclic obstruction.**

## Open questions

None from peak–valley interval composition. Do not reopen the
exponent budget, cycle closure, seam sliding, or the \(E^r\)
block. Do not open a leftover-killer from the real slack sign.

## Decision

**CLOSE**. The reviewer is right that the local cells already
exist and that the necklace is the natural unit. Composing the
*exact* cells does not produce \(P>P\) or \(P<P\): they are
\(T_w\), and a cycle would satisfy \(T_w(P)=P\). Composing the
*relaxed* cells reproduces the exponent gap
\(3^o\lessgtr 2^L\), which is `power_bound_word` and the closed
exponent budget. Leftover hulls already meet. That is useful
compression of the reviewer slogan; it is not a new invariant.
No Paper A edit, no ledger row, no new Lean, no \(N_0\) raise,
no finance reopen.

Best next question: none from peak–valley interval composition.

## Publication assessment

Status: `ARCHIVED`. Laboratory negative knowledge on composing
the excursion-necklace cells; not a second manuscript and not a
Paper A edit.

# Juggler word-order exact-map invariant

Status: **ARCHIVED**

Directed follow-up of
[juggler_cycle_exponent_budget.md](juggler_cycle_exponent_budget.md)
and [juggler_cycle_word_functional.md](juggler_cycle_word_functional.md),
not a reopen of those branches and not a new paper. Attack #1 showed
that the block product is \((o,L)\)-only. This phase asks whether
the *exact* ordered map \(T_w\) yields a cycle-usable quantity that
sees letter order and is not already \(D_w\), a named cell, or
cheap-\(\mathtt{OOE}\) adjacency.

Not a halt theorem, not a leftover-killer, and not a claim that
every cycle itinerary is impossible.

## Problem

Two words with the same exponent budget \(3^o/2^L\) need not have
the same exact map. Does that order-dependence produce a cyclic
obstruction that finance and the envelope cannot see?

## Exact statement

**The slogan is true and already used
(KNOWN).**
The exact map is the ordered composition of
\(\lfloor x^{3/2}\rfloor\) and \(\lfloor\sqrt{x}\rfloor\). Same
\((o,L)\) does not fix \(T_w\).

**A start realizes one itinerary
(KNOWN / EXACT — HUMAN PROOF).**
The parity of each state is unique, so each \(n\) follows exactly
one word of each length. Distinct same-length words have disjoint
`follows` domains. There is no common start at which to compare
\(T_w(n)\) and \(T_{w'}(n)\).

**CycleItinerary endpoints forget the itinerary
(KNOWN / EXACT — HUMAN PROOF).**
On a `CycleItinerary`, \(T_w(n)=n\), so
\[
\Delta_w(n)=n^{3^o}-n^{2^L},\qquad
\frac{T_w(n)}{n^{3^o/2^L}}=n^{1-P_L}.
\]
Both are functions of \((n,o,L)\) only
(`global_defect_identity` plus `image_eq_start_defectRatio`).
Any cycle invariant built from the endpoint and the budget
forgets the order.

**\(D_w\) already sees order
(KNOWN / REPARAMETERIZATION).**
\(\mathrm{lowerDenom}(w)=4^{S(w)}\) with
\(S=\sum_i 2^i\,3^{\#O(w[i+1:])}\). Through length \(8\), all
\(12\) pairs of distinct expanding necklaces with the same
\((o,L)\) have different \(S\). That is the closed word-functional
branch, not a new \(Q\).

**Named cells already see order
(KNOWN / EXACT — LEAN VERIFIED).**
\(\mathtt{OOE}\), \(\mathtt{OEO}\), and \(\mathtt{EOO}\) share
\((o,L)=(2,3)\) and budget \(9/8\). They are one necklace,
excluded by different cells / rotation, not by the budget.

**Cheap-\(\mathtt{OOE}\) adjacency already sees order
(KNOWN).**
\(\mathtt{OOOEE}\) and \(\mathtt{OOEOE}\) share
\((o,L)=(3,5)\) and budget \(27/32\). The second word contains
the archived cheap-\(\mathtt{OOE}\) then \(\mathtt{OE}\) factor.

**No unarchived pair (COMPUTATIONALLY VERIFIED).**
Expanding itineraries of length \(\le 8\): \(105\) words, \(17\)
budgets, \(12\) distinct-necklace pairs, \(0\) unarchived.
CycleMin-oriented subset: \(18\) words, the same \(12\) pairs,
all `lowerDenom`. Every pair has empty common domain on
\([2,2001)\).

No cycle of any length — not claimed.

## Current literature

- Block product \(\prod\rho_i=3^o/2^L\) —
  **CLOSE** / **REPARAMETERIZATION**
  ([juggler_cycle_exponent_budget.md](juggler_cycle_exponent_budget.md))
- Slack-weight functional \(S(w)\) / \(D_w=4^{S(w)}\) —
  **CLOSE** / **REPARAMETERIZATION**
  ([juggler_cycle_word_functional.md](juggler_cycle_word_functional.md))
- \(\mathtt{OOE}\) / \(\mathtt{OEO}\) / \(\mathtt{EOO}\) exclusions —
  **EXACT — LEAN VERIFIED**
  ([juggler_cycle_arith.md](juggler_cycle_arith.md))
- Cheap \(\mathtt{OOE}\) cannot feed \(\mathtt{OE}\) —
  **EXACT — HUMAN PROOF**
  ([juggler_cycle_ordered_excursion.md](juggler_cycle_ordered_excursion.md))
- Exact cells compose to \(T_w\) —
  **CLOSE** / **REPARAMETERIZATION**
  ([juggler_cycle_peak_valley_composition.md](juggler_cycle_peak_valley_composition.md))
- Cyclic remainder balance —
  **EXACT — LEAN VERIFIED**
  ([juggler_cycle_rounding.md](juggler_cycle_rounding.md))
- Prefix expansion \(3^{o_k}\ge 2^k\) —
  **CLOSE**
  ([juggler_cycle_prefix_feasibility.md](juggler_cycle_prefix_feasibility.md))
- Global defect on a cycle —
  **EXACT — LEAN VERIFIED**
  (`global_defect_identity`; `image_eq_start_defectRatio`)
- Collatz-style financing —
  **known** (`simons-de-weger-2005-collatz-m-cycles`)
- Every start reaches 1 — not claimed

Project relationship: **refuted** as a new cyclic invariant; the
slogan is **KNOWN** and every cycle-usable compression is
**REPARAMETERIZATION** of an archived tag.

## Branch budget

```text
Mathematical target     For CycleMin-legal words with the same
                        exponent budget (o,L), is there a
                        cycle-usable Q of the exact ordered map T_w
                        that is not a function of (o,L) alone and
                        is not already D_w / S(w), a named cell,
                        cheap-OOE adjacency, peak–valley / T_w,
                        cyclic rounding, or prefix expansion?
Novelty hypothesis      two words with 3^o/2^L equal have different
                        exact compositions, so some intermediate
                        exact quantity could forbid a cycle that
                        finance and the exponent budget cannot see
Falsifier               every same-(o,L) distinction is a rotation,
                        D_w / S(w), a named cell (OE / OOE / EOO),
                        cheap-OOE→OE, or the cycle-endpoint collapse
                        Δ = n^{3^o}−n^{2^L}
Existing machinery      cycle_itinerary_functional (S, necklaces, D_w=4^S);
                        lower_denom; follows_itinerary; floor_power;
                        no_cycle_itinerary_ooe / oeo / eoo; ordered
                        excursion; peak-valley composition; global
                        defect; cycle_rounding
Maximum Phase-0 scope   human-proof endpoint collapse; (o,L)-grouped
                        census k≤8; explicit pairs OOE/OEO/EOO and
                        OOOEE/OOEOE; tag each distinction. No Lean,
                        no finance, no N0, no L=25781
Promotion criterion     an unarchived identity or systematic
                        inequality relating T_w and T_{w'} for
                        distinct necklaces with the same (o,L)
Stop criterion          the slogan is KNOWN and every cycle-usable
                        compression is archived
```

## Closed-bridge gates

Do not treat \(D_w\), named cells, or cheap-\(\mathtt{OOE}\)
adjacency as the find. Do not reopen the exponent budget, the
word-functional leftover-killer, finance, or peak–valley
composition.

- **CLOSE** if CycleItinerary \(\Delta\) and \(T/n^P\) are \((o,L)\)-only.
- **CLOSE** if a start follows at most one word of each length.
- **CLOSE** if every same-budget necklace pair through length \(8\)
  is `rotation` / `lowerDenom` / `named_cell` / `adjacency`.
- **CLOSE** if \(\mathtt{OOE}/\mathtt{OEO}/\mathtt{EOO}\) are
  named cells on one necklace.
- **CLOSE** if \(\mathtt{OOOEE}\) versus \(\mathtt{OOEOE}\) is
  archived adjacency.
- **PROMOTE** only if a pair produces an unarchived relation
  between \(T_w\) and \(T_{w'}\).

Do **not** raise \(N_0\). Do **not** open \(L=25781\). Do
**not** reintroduce finance. Do **not** edit Paper A. Do
**not** add Lean.

## Explicitly out of Phase-0

A leftover census, Fourier / residues / \(Q\)-sections, a
branch-and-bound engine, new Lean, CLI, visualization, Paper A
edit, a finance floor raise, a Halbeisen-style reopen of
\(S(w)\).

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Exact map \(T_w\) depends on letter order —
  **KNOWN**
- Unique itinerary of each length —
  **EXACT — HUMAN PROOF**
- CycleItinerary \(\Delta=n^{3^o}-n^{2^L}\) —
  **REPARAMETERIZATION** of `global_defect_identity`
- CycleItinerary \(T/n^P=n^{1-P}\) —
  **REPARAMETERIZATION** of `image_eq_start_defectRatio`
- Same \((o,L)\), different \(S\) —
  **KNOWN** (`cycle_itinerary_functional`)
- \(\mathtt{OOE}/\mathtt{OEO}/\mathtt{EOO}\) —
  **KNOWN** (named cells / rotation)
- \(\mathtt{OOOEE}\) versus \(\mathtt{OOEOE}\) —
  **KNOWN** (cheap-\(\mathtt{OOE}\) adjacency)
- Word-order leftover-killer —
  **REFUTED** (`juggler_cycle_itinerary_order`)
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_itinerary_order`
- Dataset: `data/research/juggler/cycle_finance/word_order/summary.json`
- Tests: `tests/research/juggler_sequence/test_cycle_itinerary_order.py`
- Window: expanding itineraries \(k\le 8\); common-follows scan on
  \([2,2001)\); itinerary uniqueness on \(n<64\), \(k\le 6\).
  Fast suite only. No CLI. No new Lean. No \(N_0\) raise.

## Conjectures

`juggler_cycle_itinerary_order` — **REFUTED**.

## Counterexamples

- \(\Delta=n^{3^o}-n^{2^L}\) and \(T/n^P=n^{1-P}\) on a
  `CycleItinerary`. Falsifier of an endpoint quantity that sees order.
- A start follows exactly one word of each length. Falsifier of
  a same-\(n\) comparison of two same-length maps.
- All \(12\) distinct expanding necklaces with the same
  \((o,L)\) through length \(8\) have different \(S\). Falsifier
  of a new \(n\)-independent \(Q\).
- \(\mathtt{OOE}/\mathtt{OEO}/\mathtt{EOO}\) share budget
  \(9/8\) and are excluded by cells. Falsifier of “the budget
  is the map”.
- \(\mathtt{OOOEE}\) versus \(\mathtt{OOEOE}\) is cheap-\(\mathtt{OOE}\)
  then \(\mathtt{OE}\). Falsifier of an unarchived contracting pair.

## Formalization

None added. The endpoint identities are already
`global_defect_identity` and `image_eq_start_defectRatio`.
The short-word exclusions are already `no_cycle_itinerary_ooe` /
`oeo` / `eoo`. Paper A is unchanged. Do not add
`WordOrder.lean`.

## Results

- **Endpoint collapse** — **KNOWN** /
  **REPARAMETERIZATION** (`word_order/summary.json`).
- **Unique itinerary** — **EXACT — HUMAN PROOF** /
  **COMPUTATIONALLY VERIFIED**.
- **Necklace census** — **COMPUTATIONALLY VERIFIED**:
  `unarchived=0` on \(12\) pairs.
- **Canonical cells** — **KNOWN**.
- **No new cyclic obstruction.**

## Open questions

None from an itinerary-order exact-map invariant. Do not reopen
\(D_w\), named cells, or cheap-\(\mathtt{OOE}\) adjacency as
the find. Do not start a same-\(n\) comparison of same-length
words.

## Decision

**CLOSE**. The slogan is true: same \((o,L)\) does not fix
\(T_w\). On a cycle the endpoint quantities collapse to
\((n,o,L)\). Distinct same-length words have disjoint domains,
so there is no common start at which a new exact-map \(Q\)
could be read. Every same-budget necklace distinction through
length \(8\) is `lowerDenom`. The canonical triple is one
necklace of named cells. \(\mathtt{OOOEE}\) versus
\(\mathtt{OOEOE}\) is archived adjacency. This is Attack #1’s
complement — the exact map sees order, and every cycle-usable
compression of that fact is already in the platform. No
Paper A edit, no ledger row in the theorem ledger, no new Lean,
no \(N_0\) raise, no leftover-killer census.

Best next question: none from an itinerary-order exact-map invariant.

## Publication assessment

Status: `ARCHIVED`. Laboratory negative knowledge on an
order-sensitive rewrite of the exponent budget; not a second
manuscript and not a Paper A edit.

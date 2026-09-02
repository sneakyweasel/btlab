# Juggler cycle-wide block exponent budget

Status: **ARCHIVED**

Directed follow-up of
[juggler_cycle_e_block.md](juggler_cycle_e_block.md)
and [juggler_cycle_finance.md](juggler_cycle_finance.md),
not a reopen of finance, not a leftover-killer, and not a new
paper. After the first-block test \(2^{a_0+r}\le 3^{a_0}\) closed
as the expanding-prefix comparison, this phase asks whether the
cycle-wide product of those block exponents is a stronger
closure obstruction.

Not a halt theorem, not a floor raise, and not a claim that
every cycle itinerary is impossible.

## Problem

A CycleMin word is a concatenation of blocks
\(O^{a_i}E^{r_i}\). Ignoring floors, block \(i\) scales as
\(x\mapsto x^{\rho_i}\) with \(\rho_i=3^{a_i}/2^{a_i+r_i}\). Does
\(\prod_i\rho_i\approx 1\), together with local CycleMin
constraints, give an exponent separation that exact integer
return cannot realize — and that is not formal expansion or
finance?

## Exact statement

**The product is the itinerary ratio
(KNOWN / REPARAMETERIZATION).**
Write \(A=\sum a_i\) and \(R=\sum r_i\). Then
\[
\prod_i\rho_i
=\prod_i\frac{3^{a_i}}{2^{a_i+r_i}}
=\frac{3^A}{2^{A+R}}
=\frac{3^o}{2^L}
\]
identically. The block split does not appear.

**The signed sum is partition-independent
(KNOWN / REPARAMETERIZATION).**
\[
\sum_i\bigl(a_i\log 3-(a_i+r_i)\log 2\bigr)
=o\log 3-L\log 2.
\]
Local CycleMin constraints on a first block change one summand
and force the others to compensate. They do not change the
total.

**Exact equality is impossible
(KNOWN).**
\(3^A=2^{A+R}\) never holds for \(L\ge 1\): the two sides have
distinct prime factors. That is already why every nonempty
cycle itinerary is strictly expanding,
\(2^L<3^o\) (`cycle_itinerary_formally_expanding`).

**Exact integer return is the defect identity
(KNOWN / EXACT — LEAN VERIFIED).**
On a realized itinerary, \(n^{3^o}=T_w(n)^{2^L}+\Delta_w(n)\). A
cycle has \(T_w(n)=n\), so
\[
\Delta_w(n)=n^{3^o}-n^{2^L}=n^{2^L}(n^{3^o-2^L}-1).
\]
That is `global_defect_identity` plus
`image_eq_start_defectRatio`. The integer dynamics *do*
realize the exponent budget: they realize it as a positive
defect, not as \(3^A=2^{A+R}\).

**Floors on that defect are finance
(KNOWN / EXACT — LEAN VERIFIED).**
The relative gap \(\theta=1-2^L/3^o\) is charged against
\(O(L/(n\log n))\) cell errors:
\[
n\log n\cdot(3^o-2^L)\le L\cdot 3^o
\]
(`cycleMin_finance`). Near-convergents of \(\log 2/\log 3\)
make \(\theta\) tiny and are the leftover lengths. Baker-type
gap lower bounds cannot beat the exact gap
([juggler_cycle_gap_baker.md](juggler_cycle_gap_baker.md)).

**An expanding first block on a leftover forces later
contraction (KNOWN).**
The first-block test \(2^{a_0+r}\le 3^{a_0}\) makes
\(\rho_1\ge 1\). On a leftover, \(3^o/2^L=1+\theta\) with
\(\theta\) tiny, so
\[
\prod_{i\ge 2}\rho_i=\frac{3^o/2^L}{\rho_1}<1.
\]
At \(L=19\) (\(o=12\)), \(\mathtt{OOE}\) has \(\rho=9/8\) and
the rest is \(59049/65536\). At \(L=84\) (\(o=53\)) the same
split has rest \(<1\). That compensation is \(m\)-finance /
height packing, not a new sign law.

No cycle of any length — not claimed.

## Current literature

- Formal expansion \(2^L<3^o\) —
  **EXACT — LEAN VERIFIED**
  (`cycle_itinerary_formally_expanding`)
- Global defect \(n^{3^o}=T_w(n)^{2^L}+\Delta\) —
  **EXACT — LEAN VERIFIED**
  (`global_defect_identity`)
- Return burns the surplus, \(1+q=n^{3^o-2^L}\) —
  **EXACT — LEAN VERIFIED**
  (`image_eq_start_defectRatio`)
- Cycle finance —
  **EXACT — LEAN VERIFIED**
  (`cycleMin_finance`;
  [juggler_cycle_finance.md](juggler_cycle_finance.md))
- First-block expanding test —
  **REPARAMETERIZATION**
  ([juggler_cycle_e_block.md](juggler_cycle_e_block.md))
- Baker / Rhin on \(\lvert 3^o-2^L\rvert\) —
  **CLOSE** / **REFUTED**
  ([juggler_cycle_gap_baker.md](juggler_cycle_gap_baker.md))
- Near-tight leftover rigidity —
  **CLOSE** / **REFUTED**
  ([juggler_cycle_near_tight.md](juggler_cycle_near_tight.md))
- Cyclic word functional —
  **CLOSE** / **REPARAMETERIZATION** of `lowerDenom`
  ([juggler_cycle_word_functional.md](juggler_cycle_word_functional.md))
- Collatz-style financing —
  **known** (`simons-de-weger-2005-collatz-m-cycles`)
- Every start reaches 1 — not claimed

Project relationship: **refuted** as a new exponent
separation; the budget is a **REPARAMETERIZATION** of
\(3^o/2^L\) and finance.

## Branch budget

```text
Mathematical target     Does the cycle-wide product of block
                        exponents give a closure obstruction
                        that is not 3^o>2^L / cycleMin_finance /
                        global defect / leftover near-convergents?
Novelty hypothesis      local CycleMin block constraints make
                        the signed exponent sum incompatible
                        with exact integer return
Falsifier               ∏ ρ_i = 3^o/2^L identically; the signed
                        sum ignores the partition; floors are
                        finance; leftovers have tiny θ
Existing machinery      cycle_itinerary_formally_expanding;
                        cycleMin_finance;
                        image_eq_start_defectRatio;
                        global_defect_identity;
                        first-block 2^{a0+r}<=3^{a0}
Maximum Phase-0 scope   product/sum identities; leftover
                        compensation after an expanding first
                        block; 3^A≠2^{A+R}. No finance reopen,
                        no Lean, no N0
Promotion criterion     a sign/gap obstruction that is not
                        formal expansion or finance
Stop criterion          the budget is 3^o/2^L and the floors
                        are finance
```

## Closed-bridge gates

Do not reopen finance, Baker, near-tightness, or the \(E^r\)
block leftover-killer.

- **CLOSE** if \(\prod\rho_i=3^o/2^L\) identically.
- **CLOSE** if the signed sum is \(o\log 3-L\log 2\).
- **CLOSE** if \(3^A=2^{A+R}\) is unique factorization, already
  used by `cycle_itinerary_formally_expanding`.
- **CLOSE** if exact return is `global_defect_identity` /
  `image_eq_start_defectRatio` and the floors are
  `cycleMin_finance`.
- **CLOSE** if an expanding first block on a leftover only
  forces later contraction.
- **PROMOTE** only if a sign or gap appears that is not
  formal expansion or finance.

Do **not** raise \(N_0\). Do **not** open \(L=55293\). Do
**not** reintroduce a leftover-killer census. Do **not** edit
Paper A. Do **not** add Lean.

## Explicitly out of Phase-0

A \(K=11\) proof, defect amplification, Fourier / residues /
\(Q\)-sections, a branch-and-bound engine, ledger row, new Lean,
CLI, visualization, Paper A edit, a finance floor raise.

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Block product \(\prod\rho_i=3^o/2^L\) —
  **KNOWN** / **REPARAMETERIZATION**
- Signed sum \(o\log 3-L\log 2\) —
  **KNOWN** / **REPARAMETERIZATION**
- \(3^A\neq 2^{A+R}\) —
  **KNOWN** (`cycle_itinerary_formally_expanding`)
- Exact return defect —
  **EXACT — LEAN VERIFIED** (`global_defect_identity`)
- Floors —
  **EXACT — LEAN VERIFIED** (`cycleMin_finance`)
- First-block compensation on leftovers —
  **KNOWN**
- Cycle-wide exponent leftover-killer —
  **REFUTED** (`juggler_cycle_exponent_budget`)
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_exponent_budget`
- Dataset: `data/research/juggler/cycle_finance/exponent_budget/summary.json`
- Tests: `tests/research/juggler_sequence/test_cycle_exponent_budget.py`
- Window: algebraic identities on one three-block word; leftover
  lengths \(19\) and \(84\) with an \(\mathtt{OOE}\) first block.
  Fast suite only. No CLI. No new Lean. No \(N_0\) raise.

## Conjectures

`juggler_cycle_exponent_budget` — **REFUTED**.

## Counterexamples

- \(\prod\rho_i=3^A/2^{A+R}\) on
  \((2,1)+(3,2)+(7,4)\) and on the single block \((12,7)\).
  Falsifier of a partition-dependent budget.
- \(3^{12}\neq 2^{19}\) and \(3^{53}\neq 2^{84}\). Falsifier of
  a new impossibility: this is unique factorization.
- \(L=19\): \(\mathtt{OOE}\) has \(\rho=9/8\), the rest is
  \(59049/65536<1\). Falsifier of a global sign that forbids
  later contraction.
- Exact return is \(\Delta=n^{3^o}-n^{2^L}\). Falsifier of
  “the integer dynamics cannot realize the exponent budget”.

## Formalization

None added. Formal expansion is already
`cycle_itinerary_formally_expanding`. The defect identity is already
`global_defect_identity`. The floors are already
`cycleMin_finance`. Paper A is unchanged. Do not add
`ExponentBudget.lean`.

## Results

- **Product identity** — **KNOWN** /
  **REPARAMETERIZATION** (`exponent_budget/summary.json`).
- **Signed-sum identity** — **KNOWN** /
  **REPARAMETERIZATION**.
- **Equality** — **KNOWN** impossible.
- **Leftover compensation** — **COMPUTATIONALLY VERIFIED**
  at \(L=19,84\): expanding \(\mathtt{OOE}\) forces rest \(<1\).
- **No new cyclic obstruction.**

## Open questions

None from the exponent budget. The Lyapunov rewrite \(L\mapsto\rho L\)
is
[juggler_cycle_block_potential.md](juggler_cycle_block_potential.md).
The cyclic interval-transfer follow-up
([juggler_cycle_block_transfer.md](juggler_cycle_block_transfer.md))
is closed. Do not reopen finance, Baker, near-tightness, or the
\(E^r\) first-block leftover-killer. Do not open a run-length
automaton.

## Decision

**CLOSE**. The cycle-wide exponent is \(3^o/2^L\). It does not
see the block decomposition, so it is not stronger than the
first-block prefix test: that test constrains one factor, and
the leftover product then forces the other factors to
contract. Exact equality never holds, which is already the
expanding-word lemma. Exact integer return holds by a positive
defect, and the size of that defect is finance. The slogan
that this is closer to a termination theorem is the finance
programme under a new name. No Paper A edit, no ledger row,
no new Lean, no \(N_0\) raise, no leftover-killer census.

Best next question: none from the cycle-wide exponent budget.

## Publication assessment

Status: `ARCHIVED`. Laboratory negative knowledge on a
block-factor rewrite of \(3^o/2^L\); not a second manuscript
and not a Paper A edit.

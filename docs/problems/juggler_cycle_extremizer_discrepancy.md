# Juggler 25781 finance-extremizer discrepancy

Status: **ARCHIVED**

Refinement of
[juggler_cycle_almost_search.md](juggler_cycle_almost_search.md) and
[juggler_cycle_finance_cell_bridge.md](juggler_cycle_finance_cell_bridge.md),
not a new paper. After the finance-to-cell bridge closed, this
phase asks whether the first 1–3 realized excursions of the
\(L=25781\) finance-extremal necklace deviate from its defect-free
envelope by an exact discrepancy \(X\) that is **not** an archived
cell and that can be charged in the length-only defect sum at the
published floor \(N_0=10^6\).

Not a halt theorem, not a floor raise, not a reopen of empty-`OOE`
/ \(243<256\) / shared-`OOE`-prefix death, not Phase 2 at
\(L=55293\), and not a \(1054k\) family census.

## Problem

The packed word at \((L,o)=(25781,16266)\) is uniquely
finance-optimal (\(6751\) `OOE` + \(2764\) `OE`) and is not a
long realized itinerary. Is there a floor-independent arithmetic
deviation, visible in the first three excursions versus the
abstract envelope, that is new and large enough to kill \(25781\)
already at \(n=10^6+1\)?

## Exact statement

**First discrepancy is the shared `OOE` prefix (COMPUTATIONALLY
VERIFIED).**
On every odd start in \([10^6+1,10^6+2001]\) the packed word
dies before its first mechanical `OE` (letter index \(9\),
block \(3\)). The modal tag is `shared_ooe_prefix` on all
\(1001\) starts. This is the closed cell-bridge object, not a
new \(K=2/3/4\) lemma.

**Realized blocks hit the integer envelope (COMPUTATIONALLY
VERIFIED).**
\(197\) starts complete one prescribed `OOE` and \(23\) complete
two; none complete three. On all \(243\) realized excursions
the integer envelope equals the landing (`deficit` \(=0\),
`ooe_cell` \(w^8\le v^9\)). The first \(a=2\) start
\(n=1000057\) gives
\(1000057\xrightarrow{\mathrm{OOE}}5623773\xrightarrow{\mathrm{OOE}}39244721\),
then the third `OOE` fails. Cheap-`OOE` and \(F_2(v)>v\) hold
on those realized rows; they are the archived scale facts, not
a new charge.

**\(\Delta_{\mathrm{fin}}\) does not predict \(d_{\mathrm{closure}}\)
(COMPUTATIONALLY VERIFIED).**
Five words with the same `OOE` prefix and
\(\Delta_{\mathrm{fin}}\) spanning \(7.2\cdot10^{-5}\) have
identical follow statistics (max \(6\), mean \(2.0169\)).
Prefix-changed controls (`OE` front, `OOOE` front) move the
histogram by \(O(1)\) letter. This is the measurement
cell_bridge did not make, and it is uncorrelated.

**No charge kills \(25781\) at \(N_0=10^6\) (COMPUTATIONALLY
VERIFIED).**
The observed relative envelope tax is \(0\).
`parity_excludes` and `budget_excludes` remain false at
\(n=10^6+1\).

A deeper follow-death census is not a theorem.
Follow depth \(\le 11\) is already
**COMPUTATIONALLY VERIFIED** in
[juggler_cycle_almost_search.md](juggler_cycle_almost_search.md)
and is not recensed as a result.

No cycle of any length — not claimed.

## Current literature

- Finance-to-cell bridge —
  **CLOSE** / **REFUTED**
  ([juggler_cycle_finance_cell_bridge.md](juggler_cycle_finance_cell_bridge.md)).
  Terminal \((2,1)\) is realized; canonical and bunched-`OOE`
  follow histograms are identical; empty \((2,2,1)\) is
  \(243<256\).
- Almost-cycle search, prescribed-word follow \(\le 11\) —
  **CLOSE**
  ([juggler_cycle_almost_search.md](juggler_cycle_almost_search.md))
- `OOE` cell \(w^8\le v^9\); cheap-`OOE` adjacency;
  two-block persistence \(243<256\) —
  **EXACT — HUMAN PROOF** /
  leftover-killer **REFUTED**
  ([juggler_cycle_ordered_excursion.md](juggler_cycle_ordered_excursion.md))
- Run-type packing, \(99\) leftovers —
  **EXACT — HUMAN PROOF** /
  **COMPUTATIONALLY VERIFIED**
  ([juggler_cycle_budget_opt.md](juggler_cycle_budget_opt.md))
- Descent floor \(N_0=26254995\) kills \(25781\) computationally —
  **COMPUTATIONALLY VERIFIED**
  ([juggler_descent_floor.md](juggler_descent_floor.md)).
  This phase does not re-exclude by search and does not raise
  \(N_0\).
- Collatz-style financing —
  **known** (`simons-de-weger-2005-collatz-m-cycles`)
- Every start reaches 1 — not claimed

Project relationship: **refuted** as a floor-independent leftover
charge; every recorded \(X\) is the shared `OOE` prefix or the
existing `ooe_cell` / `power_bound_word` envelope.

## Branch budget

```text
Mathematical target     Is there an exact discrepancy X, visible in
                        the first 1–3 realized excursions of the
                        25781 finance-extremal necklace versus its
                        envelope, that is not F2 / 243<256 / the
                        shared OOE prefix, and that charges the
                        defect sum enough to kill 25781 at N0=10^6?
Novelty hypothesis      Near-extremal finance forces a universal
                        early arithmetic deviation (not an empty
                        terminal cell) that is covariant on 1054k
Falsifier               Every recorded X is F2, 243<256, shared
                        OOE prefix, or a rewrite of power_bound_word
Existing machinery      distinguished_words / follow_word
                        (cycle_almost_search.py); excursion_map,
                        ooe_cell_holds (cycle_ordered_excursion.py);
                        budget_rhs / run_type_counts
                        (cycle_budget_opt.py); cell_bridge CLOSE
Maximum Phase-0 scope   One table on the canonical word plus a
                        tiny graded-slack follow sample. No N0
                        raise, no 1054 family, no 55293, no tall
                        seeds, no Lean, no Paper A edit
Promotion criterion     A reusable X that is not an archived cell
                        and that strictly lowers n_max(25781)
                        below 10^6, or a clean K=2/3/4 lemma
Stop criterion          X is archived, or Δ_fin and d_closure are
                        uncorrelated on the graded sample
```

## Closed-bridge gates

Classify \(X\) before any follow-up. Do not reopen the boxed
hybrid

> finance-extremal local configuration \(\Rightarrow\) empty odd
> predecessor cell

already **REFUTED** as `juggler_cycle_finance_cell_bridge`.

- **CLOSE** if \(X\) is `ooe_cell` \(w^8\le v^9\), \(F_2(v)>v\),
  \(243<256\), cheap-`OOE` adjacency, or “shared `OOE` prefix
  dies.” Record as negative knowledge. Do not open \(K=11\),
  \(1054k\), or \(L=55293\).
- **CLOSE** if \(d_{\mathrm{closure}}\) is independent of
  \(\Delta_{\mathrm{fin}}\) on the graded sample (predicted by
  the identical bunched/canonical histograms).
- **PROMOTE** only if \(X\) is a new exact inequality that,
  charged in the length-only sum at \(n=10^6+1\), makes
  `parity_excludes` / `budget_excludes` kill \(25781\).

Do **not** raise \(N_0\). Do **not** mix in the
\(7{,}110{,}201\)-class tall seeds. Keep those as a separate
height database.

## Explicitly out of Phase-0

\(1054\)-family covariance, \(L=50508\) / \(55293\), a \(K=11\)
proof, Fourier / residues / \(Q\)-sections / more generic finance
constants, ledger row, Lean, Paper A edit. Those open only if
Phase-0 produces a non-archived \(X\).

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- First three realized \(F_a(v)\) versus the defect-free
  envelope \(v\mapsto v^{3^a/2^{a+1}}\) —
  **COMPUTATIONALLY VERIFIED**; deficit \(0\) on every
  realized block
- Prefix finance deficit versus the packed envelope at the same
  scale —
  **OBSERVATION**; numerical residue \(\sim10^{-20}\), not a tax
- \(\Delta_{\mathrm{fin}}=S_{\max}-S(w)\) versus
  \(d_{\mathrm{closure}}\) on a graded two-type sample —
  **COMPUTATIONALLY VERIFIED**; uncorrelated on the same-`OOE`
  prefix (the measurement cell_bridge did not make)
- `ooe_cell` / \(F_2(v)>v\) / \(243<256\) / cheap-`OOE` /
  shared `OOE` prefix / `power_bound_word` —
  **KNOWN** archived cells (both CLOSE gates fired)
- Floor-independent leftover-killer at \(L=25781\) —
  **REFUTED** (`juggler_cycle_extremizer_discrepancy`)
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_extremizer_discrepancy`
- Dataset: `data/research/juggler/cycle_finance/extremizer_discrepancy/summary.json`
- Tests: `tests/research/juggler_sequence/test_cycle_extremizer_discrepancy.py`
- Window: odd starts in \([10^6+1,10^6+2000]\); first three
  excursions of the packed word; graded-slack follow on eight
  two-type words at the same \((L,o)\). Fast suite only. No CLI.
  No Lean. No \(N_0\) raise.

## Conjectures

`juggler_cycle_extremizer_discrepancy` — **REFUTED**.

## Counterexamples

- All \(1001\) odds in \([10^6+1,10^6+2001]\) have first
  \(X=\) `shared_ooe_prefix` (first `OE` at letter \(9\)).
- On \(243\) realized `OOE` blocks, \(\mathrm{env}-F=0\) and
  `ooe_cell` holds. Witness: \(1000057\to 5623773\to 39244721\).
- Five same-`OOE`-prefix words with
  \(\Delta_{\mathrm{fin}}\) up to \(7.2\cdot10^{-5}\) have
  identical \(d_{\mathrm{closure}}\) (max \(6\), mean
  \(2.0169\)). Falsifier of a finance-slack law.

## Formalization

None. No `ExtremizerDiscrepancy.lean`. Paper A is unchanged.
Do not formalize the sample table.

## Results

- **Shared-prefix death** — **COMPUTATIONALLY VERIFIED**
  (`extremizer_discrepancy/summary.json`):
  `modal_x=shared_ooe_prefix`, `all_archived=true`,
  completed-block counts \(781/197/23/0\).
- **Envelope comparison** — **COMPUTATIONALLY VERIFIED**.
  Mean relative deficit \(0\) on \(243\) realized rows.
- **Graded slack** — **COMPUTATIONALLY VERIFIED**.
  `uncorrelated=true`; same-prefix mean span \(0\), max span
  \(0\), \(\Delta_{\mathrm{fin}}\) span \(7.2\cdot10^{-5}\).
- **Charge** — does not kill \(25781\) at the published floor.
- **No new leftover-killer.**

## Open questions

None from the extremizer discrepancy. Do not open \(K=11\),
the \(1054k\) family, or \(L=55293\). The
\(7{,}110{,}201\)-class tall seeds stay with the parked height
database.

## Decision

**CLOSE**. The first invariant discrepancy of the \(25781\)
finance-extremal necklace versus its envelope is the already
archived shared-`OOE` prefix. When a prescribed `OOE` is
realized, the landing equals the integer \(9/8\)-envelope and
`ooe_cell` holds; there is nothing to charge. The graded sample
that cell_bridge omitted shows \(d_{\mathrm{closure}}\)
independent of \(\Delta_{\mathrm{fin}}\) on every itinerary that
keeps the `OOE` prefix. Both stop-gates fire. No Paper A edit,
no ledger row, no Lean, no \(N_0\) raise.

Best next question: none from the 25781 extremizer discrepancy.

## Publication assessment

Status: `ARCHIVED`. Laboratory negative knowledge on a
finance refinement; not a second manuscript and not a
Paper A edit.

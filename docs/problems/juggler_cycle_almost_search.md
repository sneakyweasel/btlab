# Juggler exact almost-cycle search

Status: **ARCHIVED**

Refinement of
[juggler_cycle_finance.md](juggler_cycle_finance.md) and
[juggler_cycle_budget_opt.md](juggler_cycle_budget_opt.md),
not a new paper. After the itinerary-independent leftover-killers
closed at the exponent envelope, this phase asks whether a
large exact search for
\(E_L(n,w)=\lvert T_w(n)-n\rvert/n\) on the finance-surviving
frontier produces a cycle, an unusually close almost-cycle, or
a reusable terminal failure. Phase 1 is \(L=25781\) only.
Not a halt theorem, not a leftover-itinerary census, not a
\(2^L\) enumeration, and not a floor-extension campaign.

## Problem

The 99 run-type survivors are not killed by any
word-independent statistic. Does an exact search over
structurally admissible \(O/E\) words and \(n\ge 10^6+1\)
reach integer closure, or get close enough that the first
failure is a common arithmetic configuration?

## Exact statement

**Distinguished itinerary (COMPUTATIONALLY VERIFIED).**
For \((L,o)=(25781,16266)\) the extremal path \(o_k=r(k)\),
the ceiling Christoffel word of slope \(o/L\), and the
packed `OOE`/`OE` Beatty interleaving are the same word.
It is two-type (\(6751\) copies of `OOE`, \(2764\) of `OE`),
starts `OO`, ends `E`, and is prefix-expanding.

**No length-\(25781\) CycleMin return (COMPUTATIONALLY
VERIFIED, packed-legal bit budget).**
Every odd \(n\in[2\cdot10^6+1,\,n_{\max}^{\mathrm{run}}]\)
with \(n_{\max}^{\mathrm{run}}(25781)=19010076\) either
drops below \(n\) in at most \(257\) steps or exceeds
\(16384\) bits while still `AboveAnchor`. Among the
\(8505038\) odds, \(8497557\) drop, \(7481\) hit the bit
cap, \(0\) survive \(25781\) steps, and \(0\) realize
\(E_L\). The hardest packed-legal seed is \(n=6127057\)
(\(257\) steps, \(13739\) bits, \(162\) odds). This is not
a floor certificate: the \(7481\) high peaks were not all
walked to first passage.

**Prescribed-word follow (COMPUTATIONALLY VERIFIED).**
On \([10^6+1,10^6+20001]\) the distinguished word has
maximum follow depth \(11\) and mean depth \(2.03\). Zero
complete followers. The \(24\) longest first-passage seeds
have maximum follow depth \(8\).

**Exact backward (COMPUTATIONALLY VERIFIED).**
Run-length inversion uses the \(O(y^{1/3})\) `OE`-compatible
preimage, not the even cell of width \(2y\). On \(96\)
endpoints (log grid plus realized `OE`/`OOE` landings) the
beam dies at an empty `OOE` preimage after at most two of
\(9515\) blocks. Meet-in-the-middle at \(n=10^6+1\) fails
the same way. This is the existing \(F_2\) cell, not a
terminal failure after a near-return.

**Envelope scale (EXACT — HUMAN PROOF / OBSERVATION).**
If an itinerary with \(\theta=3^o/2^L-1\) completed, the
defect-free return error would be
\(E_{\mathrm{env}}=n^\theta-1=\mathrm{expm1}(\theta\ln n)\),
equal to \(3.52\cdot10^{-4}\) at \(n=10^6+1\). No completed
word tested that number.

No cycle of any length — not claimed. Phase 2
(\(L=55293\)) and Phase 3 (the remaining \(99\)) were not
opened.

## Current literature

- Run-type packing, \(99\) leftovers —
  **EXACT — HUMAN PROOF** /
  **COMPUTATIONALLY VERIFIED**
  ([juggler_cycle_budget_opt.md](juggler_cycle_budget_opt.md))
- Prefix expansion / Christoffel witnesses —
  **REFUTED** as leftover-killers
  ([juggler_cycle_prefix_feasibility.md](juggler_cycle_prefix_feasibility.md),
  [juggler_cycle_christoffel.md](juggler_cycle_christoffel.md))
- Pair-level, modular, conditioned, and ordered closure —
  **REFUTED** as leftover-killers; intervals reduce to the
  envelope
- `odd_preimage_unique` / `even_preimage_iff` / `F_a` —
  **EXACT — LEAN VERIFIED** / existing block maps
- Descent floor \(N_0=2\cdot10^6\) —
  **COMPUTATIONALLY VERIFIED**; max first-passage \(257\)
  steps at \(n=1122603\)
- Collatz-style financing —
  **known** (`simons-de-weger-2005-collatz-m-cycles`)
- Every start reaches 1 — not claimed

Project relationship: **refuted** as a near-closure
leftover-killer; the first failure is the existing empty
`OOE` cell and the existing first-passage scale.

## Branch budget

```text
Mathematical target     min E_L(n,w)=|T_w(n)-n|/n at L=25781
                        over finance-admissible words and
                        n>=10^6+1, exact arithmetic; does
                        near-closure share an obstruction?
Novelty hypothesis      word-independent leftover-killers
                        are closed; the obstruction appears
                        only at near-integer closure
Falsifier               no unusually close returns; or
                        near-returns are generic envelope;
                        or the tree stays exponential; or
                        the search only rediscovers the
                        power envelope and finance bounds
Existing machinery      CycleMin; AboveAnchor; run-type
                        finance; 99 survivors;
                        prefix_feasibility; exact cells;
                        odd_preimage_unique; F_a / Q;
                        power_bound_word; a0>=2; exact T
Maximum Phase-0 scope   L=25781 only; distinguished words
                        + run-length beam + exact backward
                        + CycleMin forward scan; no 2^L;
                        no Phase 2/3; no Lean; no floor
                        campaign on million-bit peaks
Promotion criterion     exact cycle; tiny E_L with a
                        repeated signature; a common exact
                        local failure after near-return;
                        or a theorem-extractable miss bound
Stop criterion          generic envelope; no closer-than-
                        random returns; exponential leftover
                        tree; or word-by-word failures
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- \(E_L(n,w)=\lvert T_w(n)-n\rvert/n\) —
  **OBSERVATION**; empty at \(L=25781\)
- \(E_{\mathrm{env}}=n^\theta-1\) —
  **EXACT — HUMAN PROOF** (defect-free envelope)
- `OE`-compatible preimage of width \(O(y^{1/3})\) —
  **EXACT — HUMAN PROOF** (\(y^4\le n^3<(y+1)^4\))
- Extremal \(=\) Christoffel \(=\) packed Beatty at
  \(L=25781\) —
  **COMPUTATIONALLY VERIFIED**
- Empty `OOE` run preimage —
  **REPARAMETERIZATION** of the existing \(F_2\) cell
- Near-closure leftover-killer —
  **REFUTED** (`juggler_cycle_almost_search`)
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_almost_search`
- Dataset: `data/research/juggler/cycle_finance/almost_search/summary.json`
- Tests: `tests/research/juggler_sequence/test_cycle_almost_search.py`
- Window: odds in \([2\cdot10^6+1,19010076]\);
  prescribed-word follow on \([10^6+1,10^6+20001]\);
  backward beam on \(96\) endpoints; \(64\)-sample
  high-peak rewalk to \(200000\) bits / \(400\) steps.
  Calibration at \(L=19\). Fast suite only. No CLI. No Lean.
  GPU was not used: closure is exact integer arithmetic.

## Conjectures

`juggler_cycle_almost_search` — **REFUTED**.

## Counterexamples

- No \(n\) in the packed-legal scan realizes \(T^{25781}(n)=n\)
  or even stays `AboveAnchor` for \(258\) steps. Falsifier:
  no unusually close return.
- Maximum follow depth of the distinguished word is \(11\).
  The itinerary is not a realized itinerary.
- All \(96\) exact backward attempts die at an empty `OOE`
  preimage after at most two blocks. This is the existing
  cell, not a near-closure signature.
- \(L=19\) calibration: closest completed AboveAnchor
  return error is \(4/53\approx0.0755\), larger than the
  envelope value \(0.035\) at \(n=13\).

## Formalization

None. No `CycleAlmostSearch.lean`. Paper A is unchanged.
Do not formalize the first-passage histogram.

## Results

- **One distinguished word** — **COMPUTATIONALLY VERIFIED**.
  Extremal, Christoffel, and packed Beatty coincide.
- **No \(E_L\)** — **COMPUTATIONALLY VERIFIED**
  (`almost_search/summary.json`): \(n_{\mathrm{at}\,L}=0\),
  \(\min E=\mathrm{null}\), max first-passage \(257\) at
  \(n=6127057\).
- **First failure** — empty `OOE` preimage (`fail_block`
  `2,1` on every backward endpoint). Existing \(F_2\).
- **High peaks** — \(7481\) seeds exceed \(16384\) bits.
  A \(64\)-sample: \(60\) drop by step \(154\), \(4\) still
  grow past \(200000\) bits. Not a floor certificate.

## Open questions

None from almost-cycle search. Phase 2 and Phase 3 are
not opened. The finance-to-cell bridge that asked whether
the early empty-`OOE` failure is a new hybrid theorem is
**CLOSE**
([juggler_cycle_finance_cell_bridge.md](juggler_cycle_finance_cell_bridge.md)).
The \(7481\) high-peak seeds belong to the already parked
floor-raise campaign, not to this branch.

## Decision

**CLOSE**. The search never produced a near-return. Every
packed-legal odd in the run-type window drops by step
\(257\) or explodes past a packed-legal bit size. The
unique distinguished word is not followed past depth
\(11\), and exact backward dies at the first `OOE` cell.
That is the closed pair-level / ordered-excursion object,
not a new obstruction that appears only at near-integer
closure. The envelope value \(3.52\cdot10^{-4}\) was never
tested against a completed word. Do not open Phase 2 or
Phase 3. No Paper A edit, no ledger row, no Lean.

Best next question: none from exact almost-cycle search.

## Publication assessment

Status: `ARCHIVED`. Laboratory negative knowledge on a
finance refinement; not a second manuscript and not a
Paper A edit.

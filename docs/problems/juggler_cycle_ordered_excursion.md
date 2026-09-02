# Juggler ordered excursion closure

Status: **ARCHIVED**

Refinement of
[juggler_cycle_budget_opt.md](juggler_cycle_budget_opt.md) and
[juggler_cycle_conditioned_closure.md](juggler_cycle_conditioned_closure.md),
not a new paper. It asks whether the exact ordered maps
\(v\overset{O^aE}{\to}w\overset{O^bE}{\to}z\) forbid a transition
that the aggregate \((L,o,e)\) packing cannot see.
Not a halt theorem, not a leftover-itinerary census, not a new finance
identity, not Fourier, not a \(Q\)-return, and not a residue /
\(p\)-adic system.

## Problem

Finance survival does not force a small class of run words. After
that negative result, does the exact integer landing of one
excursion constrain the next run's start and length?

## Exact statement

Write \(F_a(v)=T^{a+1}(v)\) when the first \(a\) states are odd
and \(T^a(v)\) is even. The peak is \(p=T^a(v)\) and the next
valley is \(w=\lfloor\sqrt p\rfloor\).

**OOE cell (EXACT — HUMAN PROOF).**
If \(a(v)=2\) and \(w=F_2(v)\), then \(w^8\le v^9\). This is the
existing exponent cell, not a tighter two-sided interval.

**Scale-conditioned \((2,1)\) (EXACT — HUMAN PROOF).**
If \(a(v)=2\) and \(v^{27}<n^{32}\), then \(w^3<n^4\), so
\(w<\mathtt{oe\_start\_min}(n)\). The next CycleMin-legal run
cannot be `OE`. At a CycleMin start this is the known cheap-`OOE`
adjacency.

**Two-block persistence (EXACT — HUMAN PROOF).**
If \(a(v)=2\), \(a(F_2(v))=2\), and \(v^{243}<n^{256}\), the
composed cell \(z^{64}\le v^{81}\) forces \(z^3<n^4\). Hence
\((2,2,1)\) is impossible at \(v=n\). The comparison is
\(81/64<4/3\), i.e. \(243<256\).

**Two-block correction (OBSERVATION).**
On the first \(a=2\) start \(v=1000057\) one has
\(F_2(F_2(v))=39244721\) against envelope \(39244728\). Relative
deficit \(1.8\cdot10^{-7}\). Floor loss does not constrain the
next run beyond the envelope.

**No leftover \((L,o)\) dies (COMPUTATIONALLY VERIFIED).**
Near \(n=10^6+1\), \((2,1)\) and \((2,2,1)\) are CycleMin-illegal,
but \((2,2)\) and \((2,2,2)\) occur, and \((2,2,1)\) becomes legal
at scale \(n^{9/8}\). A depth-\(3\) run from \(n\) lands above
\(\mathtt{oe\_start\_min}\). Unscaled pairs
\((1,1),(2,1),(1,2),(2,2),(2,3),(3,1)\) are realized at large
scale. The \(365/1517\) prefix \((2,2,2)\) still splits. Both
spotlight leftovers have \(\mathrm{OOE}/\mathrm{OE}\) equal to
\(\log(4/3)/\log(9/8)\) at the \(10^{-5}\) level; that is the
near-convergent identity, not a new obstruction.

**Exact landings do not create \(C_{a,b}\) (COMPUTATIONALLY VERIFIED).**
After three `OOE`, \(Q^3(365)=4447\) has next run \(2\) and
\(Q^3(1517)=33811\) has next run \(1\). Both sit in the same
justified band \([n^{4/3},n^{3/2})\), just below
\(n^{729/512}\) (deficits \(2\) and \(9\)). In a radius-\(400\)
window around each landing, nearby \(a=2\) starts realize next
runs including \(1\) and \(2\). Two-block sign
\(F_b(F_a(v))\lessgtr v\) matches \(\mathrm{sign}(\mu(a)\mu(b)-1)\)
with \(0\) flips on \([3,5000)\) and \([10^6+1,10^6+4002)\).
A contracting block does not force a large next run. Three-block
composition was not opened.

No cycle of any length — not claimed.

## Current literature

- Cheap `OOE` cannot feed `OE` —
  **KNOWN**
  ([juggler_cycle_budget_opt.md](juggler_cycle_budget_opt.md));
  leftover-killer **REFUTED**
  (`juggler_cycle_run_extremum_leftover_killer`)
- `power_bound_word`, OOE cell \(w^8\le v^9\) —
  **EXACT — LEAN VERIFIED**
- `oe_start_min`, `cycleMin_even_ge_sq` —
  **EXACT — HUMAN PROOF** / **EXACT — LEAN VERIFIED**
- Isolated-`OE` contracts —
  **EXACT — LEAN VERIFIED** (`oe_block_contracts`)
- Run-length pairs as a grammar —
  **REFUTED**
  ([juggler_block_map_q.md](juggler_block_map_q.md))
- Prefix \((2,2,2)\) determines the next run —
  **REFUTED** by \(365\) versus \(1517\)
- Pair-level interval closure —
  **CLOSE**
  ([juggler_cycle_closure.md](juggler_cycle_closure.md))
- Finance-conditioned exact closure —
  **CLOSE**
  ([juggler_cycle_conditioned_closure.md](juggler_cycle_conditioned_closure.md))
- Run-type finance, \(99\) leftovers —
  **EXACT — HUMAN PROOF** /
  **COMPUTATIONALLY VERIFIED**
  ([juggler_cycle_budget_opt.md](juggler_cycle_budget_opt.md))
- Collatz-style financing —
  **known** (`simons-de-weger-2005-collatz-m-cycles`)
- Every start reaches 1 — not claimed

Project relationship: **refuted** as a leftover-pair killer;
the two-block persistence is a **REPARAMETERIZATION** of the
OOE cell plus `oe_start_min`.

## Branch budget

```text
Mathematical target     Ordered block closure: exploit the actual
                        sequence of excursion types
                        O^{a0}E O^{a1}E ... O^{a_{e-1}}E
                        rather than only (L,o,e), while avoiding
                        enumeration of complete words.
Novelty hypothesis      A hypothetical cycle with a finance-surviving
                        (L,o) cannot choose its successive block
                        maps independently. Exact Juggler arithmetic
                        couples consecutive valleys/peaks strongly
                        enough that some ordered local transition
                        relation is impossible around the full cycle.
Falsifier               For L=25781 and 55293 there exists a large
                        structurally defined class of ordered run
                        sequences satisfying all known local constraints,
                        and every consecutive block pair admits exact
                        forward/backward integer compatibility. Or every
                        new constraint reduces to the existing
                        power envelope / run-type finance.
Existing machinery      CycleMin; AboveAnchor; run decomposition;
                        run-type finance (99 survivors);
                        first-run a0 >= 2;
                        isolated-OE bound;
                        OOE/OE finite-progress exclusions;
                        exact odd/even cells;
                        odd_preimage_unique;
                        even_preimage_iff;
                        EnvelopeState;
                        block_map Q;
                        exact floor composition
Maximum Phase-0 scope   Work on ordered block pairs/triples only:
                        (a,b), (a,b,c), and the corresponding exact
                        valley-to-valley maps.
                        Start with the finance-hardest survivors
                        L=25781 and 55293.
                        Derive a reusable relation between consecutive
                        valleys, peaks, and run lengths.
                        No complete-word enumeration;
                        no new finance identity;
                        no Fourier;
                        no Q-return-section theory;
                        no residue/p-adic system;
                        no terminal-cluster reopen.
Promotion criterion     A reusable ordered transition obstruction:
                        (v_i, a_i, v_{i+1}, a_{i+1})
                        cannot belong to a specified region,
                        or an exact two-/three-block inequality forces
                        a forbidden transition.
Stop criterion           Consecutive block relations remain feasible
                        over a broad product set; all constraints
                        collapse to exponent envelopes; the first
                        useful relation depends on the complete word;
                        or the analysis becomes another symbolic
                        automaton with no exact theorem.
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Exact excursion \(F_a(v)=T^{a+1}(v)\) —
  **REPARAMETERIZATION** of `floor_power` / `block_map`
- OOE cell \(w^8\le v^9\) —
  **KNOWN** (`power_bound_word`)
- Scale-conditioned \((2,1)\) —
  **REPARAMETERIZATION** of cheap-`OOE` adjacency
- Two-block \((2,2,1)\) at \(v=n\) —
  **EXACT — HUMAN PROOF** and **REPARAMETERIZATION** of the
  composed envelope \(81/64<4/3\)
- Two-block floor deficit —
  **OBSERVATION**; relative size \(<10^{-6}\)
- Valley spacing \(a\ge 3\Rightarrow F_3(v)\ge\mathtt{oe\_start}\)
  from \(n\) —
  **REPARAMETERIZATION** of \(\mu(3)=27/16>4/3\)
- Descent requires a large compensation peak —
  **REFUTED** (\(6187\): \(11189\to1087\to189\))
- Exact \((v,a)\) yields a reusable \(C_{a,b}\) —
  **REFUTED** (\(4447\) versus \(33811\) in the same
  \([n^{4/3},n^{3/2})\) band; local \(B_2\) overlaps)
- Two-block return sign is finer than \(\mu(a)\mu(b)\) —
  **REFUTED** (\(0\) sign flips in both sampled windows)
- Ordered leftover-killer —
  **REFUTED** (`juggler_cycle_ordered_excursion_leftover_killer`)
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_ordered_excursion`
- Dataset: `data/research/juggler/cycle_finance/ordered_excursion/summary.json`
- Tests: `tests/research/juggler_sequence/test_cycle_ordered_excursion.py`
- Window: first \(a=2\) start \(1000057\); pair census
  \([10^6+1,10^6+20001)\) and the \(n^{9/8}\) window of width
  \(8000\); controls \(365\) and \(1517\); spotlights
  \(L=25781\) and \(L=55293\); reopen landings \(4447\) and
  \(33811\) with local \(B_2\) radius \(400\) and two-block
  sign windows \([3,5000)\) and \([10^6+1,10^6+4002)\).
  Fast suite only. No CLI. No Lean.

## Conjectures

`juggler_cycle_ordered_excursion_leftover_killer` — **REFUTED**.

## Counterexamples

- Unscaled pairs \((1,1),(2,1),(2,2),(2,3),(3,1)\) are realized
  below \(20000\). Falsifier A.
- \((2,2,2)\) occurs \(36\) times in the near-\(n\) window;
  \((2,2,1)\) is CycleMin-legal \(36\) times at scale \(n^{9/8}\).
  Falsifier B.
- Two-block exact landing is \(7\) below the independent
  envelope. Falsifier D.
- Prefix \((2,2,2)\) has fourth run \(2\) at \(365\) and \(1\) at
  \(1517\). The scale law only says `OE` *may* start after three
  `OOE`, not that it must.
- The exact landings \(4447\) and \(33811\) share the justified
  band \([n^{4/3},n^{3/2})\) and sit just below
  \(n^{729/512}\), yet the next runs are \(2\) and \(1\).
  Local \(B_2\) around each is multi-valued. Falsifier A of the
  \((v,a)\) reopen.
- Two-block signs on \((a,b)\in\{1,2,3\}^2\) match the
  independent envelope \(\mu(a)\mu(b)\). Falsifier B.
- Descent \(11189\to1087\to189\) on \(6187\) has no compensating
  large peak.

## Formalization

None. No `CycleOrderedExcursion.lean`. Paper A is unchanged.
The OOE cell and `oe_start_min` are not re-proved.

## Results

- **Two-block persistence** — **EXACT — HUMAN PROOF**:
  \(v^{243}<n^{256}\) and two `OOE` runs force the next valley
  below `oe_start_min`. At \(v=n\) this is \(243<256\).
- **Two-block correction** — **OBSERVATION**
  (`ordered_excursion/summary.json`): relative deficit
  \(1.8\cdot10^{-7}\).
- **No leftover \((L,o)\) dies** — **COMPUTATIONALLY VERIFIED**:
  `emptied_count=0`. Both spotlights remain feasible at every
  tested ordered scale. The other \(97\) leftovers were not
  scanned: both spotlights already kill the slogan.
- **\(365/1517\) split** — **COMPUTATIONALLY VERIFIED**: the
  theorem lives at scale, not at the symbolic prefix.
- **Exact \((v,a)\) reopen** — **COMPUTATIONALLY VERIFIED**:
  retaining the integer valley still does not produce a
  region \(C_{a,b}\) or a two-block inequality beyond
  \(\mu(a)\mu(b)\). Artifact key `state_reopen`. No second
  leftover-killer.

## Open questions

None from ordered pair/triple closure. A kill would require a
complete word or a global climb-count that is not local. The
cyclic interval-transfer follow-up
([juggler_cycle_block_transfer.md](juggler_cycle_block_transfer.md))
is closed: \(F_{a,r}\) is this envelope, and outcome C is the
\(365/1517\) split. Do not open a run-length automaton.

## Decision

**CLOSE**. Consecutive block relations remain feasible over a
broad product set. The only exact transition lemmas are the
OOE cell composed once and twice; both reduce to
\(w^8\le v^9\) and \(81/64<4/3\). That is Falsifier A plus
Falsifier D. The 2026-08-31 reopen that keeps the exact
landing \(v\) (the named pair \(4447\) versus \(33811\)) is
the same object: same justified band, overlapping local
\(B_2\), and two-block signs identical to \(\mu(a)\mu(b)\).
Keep the two-block persistence as negative knowledge. No
second leftover-killer, no Paper A edit, no ledger row, no Lean.

Best next question: none from ordered excursion closure.

## Publication assessment

Status: `ARCHIVED`. Laboratory negative knowledge on a finance
refinement; not a second manuscript and not a Paper A edit.

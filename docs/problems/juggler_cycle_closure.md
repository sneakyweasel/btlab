# Juggler exact cycle-floor closure

Status: **ARCHIVED**

Refinement of
[juggler_cycle_budget_opt.md](juggler_cycle_budget_opt.md) and
[juggler_cyclic_feasibility.md](juggler_cyclic_feasibility.md),
not a new paper. It asks whether the exact coupled floor equations
around a hypothetical cycle empty a surviving \((L,o)\) in
\(\mathcal E_{\mathrm{run}}(10^6)\) without enumerating words.
Not a halt theorem, not a leftover-itinerary census, not a new finance
budget, not Fourier, not a \(Q\)-return, and not a residue /
\(p\)-adic system.

## Problem

Near-convergent exponent balance \(3^o\approx 2^L\) is only a
necessary aggregate. Can the integer/floor system

\[
x_{i+1}^2\le x_i^{e_i}<(x_{i+1}+1)^2,\qquad x_0=x_L=n
\]

fail for every admissible word of a leftover pair, in particular
\(L=25781\) and \(L=55293\)?

## Exact statement

**OE cell (EXACT — HUMAN PROOF).**
If \(x\xrightarrow{\mathrm{OE}}z\), then \(y=\lfloor x^{3/2}\rfloor\)
is even and \(z=\lfloor\sqrt y\rfloor\), hence

\[
z^4\le x^3<(z+1)^4.
\]

The image is a singleton. On \(400\) odd realisers the landing
equals \(\lfloor x^{3/4}\rfloor\). This is the exponent cell plus
evenness of \(T(x)\), not a strictly narrower two-sided interval.

**OOE landing (OBSERVATION).**
The exact image is a singleton at or one below
\(\lfloor x^{9/8}\rfloor\). Nested floors can sit *below* the naive
eighth-root cell. That is envelope slack, not a tighter feasible
set.

**Word-independent hull (EXACT — HUMAN PROOF).**
Using only \((L,o)\), the envelope gives
\(T_w(n)\le n^{3^o/2^L}=n^{P_L}\) and no itinerary-free positive lower
bound better than \(1\). On the finance window
\([N_0+1,n_{\max}^{\mathrm{par}}]\) the start interval meets the
envelope hull at both leftover lengths. First-odd and last-even
cells live at different indices and are the existing CycleMin
extrema, not a same-slot intersection.

**Order hull (COMPUTATIONALLY VERIFIED).**
An extreme `OE`-run after one `OOE` crashes below the start
(log-space). The union over orders therefore meets the start.
The mechanical `OOE`/`OE` necklace interval on \(L=25781\) is
\([986891,25482877]\) and meets \([10^6+1,26254995]\). On
\(L=55293\) that one necklace interval empties; this is not a
\((L,o)\) theorem.

**Cycle remainder (REPARAMETERIZATION).**
On a cycle, `global_defect_identity` is
\(n^{3^o}-n^{2^L}=\Delta=n^{2^L}(n^g-1)\) with
\(g=3^o-2^L\). Then \(\gcd(n,\Delta)=n^{2^L}\) is tautological.
No new divisibility.

**Odd inverse chain (REPARAMETERIZATION).**
A consecutive odd predecessor is unique or absent
(`odd_preimage_unique`). Empty cells appear immediately on the
sampled starts. This is not a new cyclic obstruction.

No cycle of any length — not claimed.

## Current literature

- Inverse-floor cells and `odd_preimage_unique` —
  **EXACT — LEAN VERIFIED** (`Preimages.lean`)
- Repeated mixed inversion —
  **CLOSE**
  ([juggler_backward_geometry.md](juggler_backward_geometry.md));
  composed bounds are nested cells
- Cyclic itinerary interval / \(\varphi\)-product —
  **CLOSE**
  ([juggler_cyclic_feasibility.md](juggler_cyclic_feasibility.md));
  leftover-shaped words stayed feasible at \(k\le 16\)
- Sequential odd-odd substitution —
  **CLOSE** as the OO envelope
  ([juggler_sequential_mordell.md](juggler_sequential_mordell.md))
- Global defect \(n^{3^o}=T_w(n)^{2^L}+\Delta\) —
  **EXACT — LEAN VERIFIED** (`global_defect_identity`)
- Run-type finance, \(99\) leftovers —
  **EXACT — HUMAN PROOF** /
  **COMPUTATIONALLY VERIFIED**
  ([juggler_cycle_budget_opt.md](juggler_cycle_budget_opt.md))
- First-even overshoot \(M\ge(n+1)^2\) —
  **EXACT — LEAN VERIFIED**
- Collatz-style financing —
  **known** (`simons-de-weger-2005-collatz-m-cycles`)
- Every start reaches 1 — not claimed

Project relationship: **refuted** as a leftover-pair killer;
local cells are **known**.

## Branch budget

```text
Mathematical target     Exact Diophantine closure for the 99 finance-surviving
                        period lengths: can a CycleMin word with the surviving
                        (L,o) actually satisfy T_w(n)=n?
Novelty hypothesis      Near-convergent exponent balance is only a necessary
                        aggregate condition. Exact floor closure imposes a
                        second, arithmetic compatibility condition on the
                        entire cyclic chain.
Falsifier               A surviving (L,o), especially L=25781 or 55293,
                        admits an exact cyclic integer solution; or every
                        interval remains feasible; or closure reduces to
                        3^o ≈ 2^L / the envelope; or killing requires the
                        complete word.
Existing machinery      CycleMin; AboveAnchor; exact odd/even floor cells;
                        floorPower; power_bound_word; cycleMin_finance;
                        run-type finance; first-even overshoot;
                        99 survivor set E_run(10^6)
Maximum Phase-0 scope   Exact closure equations for L=25781 and 55293;
                        symbolic elimination / interval propagation;
                        no brute-force orbit search, no Fourier,
                        no Q-sections, no new finance budget,
                        no residues/p-adics, no terminal-cluster reopen
Promotion criterion     An exact reusable closure obstruction that rules
                        out at least one surviving (L,o) without
                        enumerating candidate words.
Stop criterion          Closure equations reduce only to 3^o ≈ 2^L;
                        every interval remains feasible; solving requires
                        exact word enumeration; only numerical near-misses;
                        or the attack becomes another envelope/finance
                        reformulation.
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- OE exponent cell \(z^4\le x^3<(z+1)^4\) —
  **EXACT — HUMAN PROOF** (this dossier)
- OOE singleton with possible floor lag \(1\) —
  **OBSERVATION**
- Word-independent hull \(T\le n^{P_L}\) —
  **REPARAMETERIZATION** of `power_bound_word`
- First-even versus last-even cells —
  **REPARAMETERIZATION** of CycleMin extrema
- Cycle remainder \(n^{3^o}-n^{2^L}=\Delta\) —
  **REPARAMETERIZATION** of `global_defect_identity`
- Odd inverse uniqueness —
  **REPARAMETERIZATION** of `odd_preimage_unique`
- Exact closure empties a leftover \((L,o)\) —
  **REFUTED** (`juggler_cycle_closure_leftover_killer`)
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_closure`
- Dataset: `data/research/juggler/cycle_finance/cycle_closure/summary.json`
- Tests: `tests/research/juggler_sequence/test_cycle_closure.py`
- Window: \(L=25781\) and \(L=55293\) at \(n\in[10^6+1,n_{\max}^{\mathrm{par}}]\);
  block samples on `OE`/`OOE`/`OOOE`/`OOEOE`/`OOEOOE`. Fast suite
  only. No CLI. No Lean.

## Conjectures

`juggler_cycle_closure_leftover_killer` — **REFUTED**.

## Counterexamples

- Word-independent start-versus-envelope intersection is nonempty
  at both leftover lengths (envelope hi \(2.627\cdot 10^7\) versus
  \(n_{\mathrm{hi}}=2.625\cdot 10^7\) at \(L=25781\)).
- Mechanical necklace interval at \(L=25781\) is
  \([986891,25482877]\) and meets the finance window. Emptying one
  extreme order does not empty the union.
- First-odd image \(\sim n^{3/2}\) and last-even cell
  \([n^2,(n+1)^2)\) are disjoint and sit at different indices;
  the gap is first-even overshoot.
- \(\gcd(n,\Delta)=n^{2^L}\) does not constrain leftover \(n\).
- A long odd inverse chain hits an empty cell at once
  (`odd_preimage_unique`), not a new cyclic pattern.

## Formalization

None. No `CycleClosure.lean`. Paper A is unchanged.

## Results

- **OE cell = exponent cell** — **EXACT — HUMAN PROOF** /
  **COMPUTATIONALLY VERIFIED** (\(400\) samples, gap \(0\)).
- **No leftover \((L,o)\) dies** — **COMPUTATIONALLY VERIFIED**
  (`cycle_closure/summary.json`): `emptied_count=0`. Both
  word-independent hulls meet the start. \(L=25781\) mechanical
  interval meets. \(L=55293\) mechanical interval empties as a
  single necklace, not as a pair theorem.
- **Remainder** — **REPARAMETERIZATION** of
  `global_defect_identity`.
- **Odd chains** — **REPARAMETERIZATION** of `odd_preimage_unique`.

## Open questions

None from exact closure at the \((L,o)\) level. A kill would
require a complete itinerary, which Phase 0 forbids and which is not
a pair obstruction.

## Decision

**CLOSE**. Exact floor closure, once the itinerary is not fixed, is
the existing exponent envelope plus the existing cells. Local
OE/OOE images are singletons (the map is a function). Forward
hulls stay feasible on both spotlight leftovers. The cycle
identity is `global_defect_identity`. Odd inverses are
`odd_preimage_unique`. First versus last cells are CycleMin extrema
at different indices. Keep the OE cell lemma as negative
knowledge. No Paper A edit, no ledger row, no Lean.

Best next question: none from exact pair-level closure.

## Publication assessment

Status: `ARCHIVED`. Laboratory negative knowledge on a finance
refinement; not a second manuscript and not a Paper A edit.

# Juggler exact modular cycle closure

Status: **ARCHIVED**

Refinement of
[juggler_cycle_budget_opt.md](juggler_cycle_budget_opt.md) and
[juggler_cycle_closure.md](juggler_cycle_closure.md), not a new
paper. It asks whether the modular shadow of the exact square/cube
floor cells refuses to close on a surviving \((L,o)\) in
\(\mathcal E_{\mathrm{run}}(10^6)\) without enumerating words.
Not a halt theorem, not a leftover-itinerary census, not a new finance
budget, not Fourier, not a \(Q\)-return, not a 2-adic cylinder
reopen, and not a generic residue automaton.

## Problem

Pair-level interval closure is the exponent envelope. Formal
\(O/E\) feasibility is not integer realizability. Do the exact
cells

\[
y^2\le x^3<(y+1)^2\qquad\text{(odd)},\qquad
y^2\le x<(y+1)^2\qquad\text{(even)}
\]

impose a modular compatibility condition around a hypothetical
near-convergent cycle that finance and interval hulls cannot see?

## Exact statement

For a modulus \(m\) and a structural block \(W\), the relation
\(R_W(m)\subseteq(\mathbb Z/m\mathbb Z)^2\) contains \((x,y)\)
when the exact integer floor equations admit a realization
beginning at some integer \(\equiv x\) and ending at one
\(\equiv y\). Cycle-scale necessary form \(R_{\mathrm{nec}}\)
treats the defects \(\delta,\eta\) as free residues whenever
\(2Y+1>m\). Witness form \(R_{\mathrm{wit}}\) records exact
`floor_power` landings at \(n\ge N_0+1\).

**Cycle-scale \(R_{\mathrm{nec}}\) (EXACT — HUMAN PROOF).**
On a `CycleMin` with \(n\ge N_0+1\), every listed modulus
satisfies \(2Y+1>m\). Then \(\delta\) and \(\eta\) are free
residues, so the odd cell \(x^3=y^2+\delta\) and the even cell
\(x=y^2+\eta\) impose no restriction beyond the first-letter
parity of the source. The diagonal \(\Delta_m\) meets
\(R_{\mathrm{nec}}\) at every odd-compatible residue.

**Even-cell existence (EXACT — HUMAN PROOF).**
If \(Y\ge m\) and the source class has an even lift, the interval
\([Y^2,(Y+1)^2)\) is longer than \(m\), so every target residue
is realized. This is the existence half of `even_preimage_iff`, not a
new cell.

**No leftover \((L,o)\) dies (COMPUTATIONALLY VERIFIED).**
For \(L=25781\) and \(L=55293\), every listed \(m\in\{8,16,32,64,
3,9,27,81\}\) and every product \(2^a3^b\) through \(16\cdot 81\)
has a nonempty witness diagonal on the run-type class `OOE`/`OE`.
Shared self-loops exist; the increment gcd is \(1\); the run-type
counts return. Defect-width collapse does not occur. The other
\(97\) leftovers were not scanned: both spotlights already kill
the pair-level slogan.

No cycle of any length — not claimed.

## Current literature

- Inverse-floor cells, `odd_preimage_unique`, `even_preimage_iff` —
  **EXACT — LEAN VERIFIED** (`Preimages.lean`)
- Odd-odd remainder \(\rho\equiv y-1\pmod 8\) —
  **EXACT — LEAN VERIFIED** (`LandingValuation.lean`)
- Defect lower bounds mod \(4\) and \(8\) —
  **EXACT — LEAN VERIFIED** (`DefectLowerBound.lean`)
- `OOE` cylinder does not decide the next letter —
  **EXACT — LEAN VERIFIED** (`ooe_cylinder_both_next_parities`)
- Pair-level interval closure —
  **CLOSE**
  ([juggler_cycle_closure.md](juggler_cycle_closure.md));
  leftover-killer **REFUTED**
- 2-adic itinerary cylinders —
  **CLOSE**
  ([juggler_2adic_integer_bridge.md](juggler_2adic_integer_bridge.md))
- Peak \((\delta,\varepsilon)\) residue census —
  **CLOSE**
  ([juggler_cycle_diophantine.md](juggler_cycle_diophantine.md));
  residues collapse to odd/odd
- Run-type finance, \(99\) leftovers —
  **EXACT — HUMAN PROOF** /
  **COMPUTATIONALLY VERIFIED**
  ([juggler_cycle_budget_opt.md](juggler_cycle_budget_opt.md))
- Prefix expansion of leftovers —
  **CLOSE**
  ([juggler_cycle_prefix_feasibility.md](juggler_cycle_prefix_feasibility.md))
- Collatz-style financing —
  **known** (`simons-de-weger-2005-collatz-m-cycles`)
- Every start reaches 1 — not claimed

Project relationship: **refuted** as a leftover-pair killer; the
cycle-scale necessary relation is **known** first-letter parity.

## Branch budget

```text
Mathematical target     Modular closure of the exact square/cube floor
                        equations for the 99 finance-surviving (L,o) pairs
Novelty hypothesis      Exact floor cells impose modular compatibility
                        around a closed cycle that finance and interval
                        hulls cannot see
Falsifier               Every tested modulus admits a diagonal residue
                        realization; or the relation is only parity /
                        odd_preimage_unique / existing cells; or only a
                        complete word dies; or the useful modulus is a
                        large automaton / p-adic system
Existing machinery      CycleMin; Cells; odd_preimage_unique; even_preimage_iff;
                        LandingValuation mod-8; run-type finance;
                        prefix_feasibility; cycle_closure (CLOSED)
Maximum Phase-0 scope   Exact modular shadows of composed floor cells;
                        2^a, 3^b, then 2^a 3^b; L=25781 and 55293 first;
                        word-independent / structural-class only
Promotion criterion     Reusable modular closure: exact cells + run
                        structure ⇒ R_cycle(m) ∩ Δ_m = ∅
Stop criterion          Nonempty diagonal on all structural classes;
                        bookkeeping only; Level C only; huge automaton
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required. Powers of \(3\) enter only as the odd-step
cube, not as a trit encoding.

## Candidate operations / invariants

- Cycle-scale \(R_{\mathrm{nec}}\) is first-letter parity
  (defects free once \(2Y+1>m\)) —
  **EXACT — HUMAN PROOF** (this dossier)
- Even-cell existence at scale \(2Y+1\ge m\) is the full
  even-source relation —
  **EXACT — HUMAN PROOF** (this dossier)
- Block identities `OE`, `OOE`, `OOOE`, `OEE`, `OOEE` as
  relations, not functions —
  **REPARAMETERIZATION** of the exact cells
- CycleMin first-odd versus last-even residues —
  **REPARAMETERIZATION** of the existing overshoot
  (different indices)
- Additive increment of `OOE`/`OE` at the run-type counts —
  **COMPUTATIONALLY VERIFIED**; gcd \(1\), counts return
- Pair-level modular leftover-killer —
  **REFUTED** (`juggler_cycle_mod_closure_leftover_killer`)
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_mod_closure`
- Dataset: `data/research/juggler/cycle_finance/mod_closure/summary.json`
- Tests: `tests/research/juggler_sequence/test_cycle_mod_closure.py`
- Window: \(L=25781\) and \(L=55293\); moduli \(8,16,32,64\),
  \(3,9,27,81\), and products \(2^a3^b\) through \(16\cdot 81\).
  Fast suite only. No CLI. No Lean.

## Conjectures

`juggler_cycle_mod_closure_leftover_killer` — **REFUTED**.

## Counterexamples

- At cycle scale \(2Y+1>m\) for every listed modulus, so
  \(R_{\mathrm{nec}}\) is first-letter parity and
  \(\Delta_m\cap R_{\mathrm{nec}}\) contains every odd-compatible
  residue (Falsifier B).
- Mod \(8\): odd and even local \(R_{\mathrm{wit}}\) fill all
  \(32\) necessary pairs. `OE` has self-loops at \(1,3,5,7\);
  `OOE` at \(3,5,7\); three shared odd self-loops. Union return
  exists. Increment gcd \(1\).
- The same diagonal / counts-return pattern holds for every
  listed \(m\) on both \((25781,16266)\) and \((55293,34886)\).
- First-odd residue and last-even cell are different indices;
  the last-even interval of length \(2n+1\) covers \(\mathbb Z/m\mathbb Z\).
  This is the existing CycleMin overshoot.
- Defect-width collapse \(\delta<m\Rightarrow\delta=d\) needs
  \(m>2n\ge 2\cdot 10^6\), which is a large automaton
  (Falsifier D), not a Phase-0 modulus.

## Formalization

None. No `CycleModClosure.lean`. Paper A is unchanged. Existing
mod-\(8\) lemmas in `LandingValuation` and `DefectLowerBound`
are not re-proved.

## Results

- **Cycle-scale \(R_{\mathrm{nec}}\)** — **EXACT — HUMAN PROOF**:
  first-letter parity. Defects are free residues.
- **Even-cell existence** — **EXACT — HUMAN PROOF**: full
  even-source relation once \(Y\ge m\).
- **No leftover \((L,o)\) dies** — **COMPUTATIONALLY VERIFIED**
  (`mod_closure/summary.json`): `emptied_count=0`. Both
  spotlights have a witness diagonal, a nonempty necessary
  diagonal, increment gcd \(1\), and run-type count return on
  every listed \(m\). Mod \(8\) local witnesses fill \(R_{\mathrm{nec}}\).
  `OE`/`OOE`/`OOOE`/`OEE`/`OOEE` each have at least one self-loop
  mod \(8\). The other \(97\) leftovers were not scanned.
- **First versus last** — **REPARAMETERIZATION** of CycleMin
  overshoot.

## Open questions

None from low-order modular closure at the \((L,o)\) or run-type
level. A kill would require a complete word or a modulus larger
than the defect window, both out of Phase 0.

## Decision

**CLOSE**. At CycleMin scale the exact floor-cell shadow is
first-letter parity: defects are free residues, even cells fill,
and every listed modulus has a diagonal residue realization for
the `OOE`/`OE` class on both \(L=25781\) and \(L=55293\). This is
Falsifier A plus Falsifier B. Composition over `OE`/`OOE`/`OOOE`
does not go beyond the existing mod-\(8\) landing lemmas. Keep
the cycle-scale parity lemma as negative knowledge. No Paper A
edit, no ledger row, no Lean.

Best next question: none from low-order modular closure.

## Publication assessment

Status: `ARCHIVED`. Laboratory negative knowledge on a finance
refinement; not a second manuscript and not a Paper A edit.

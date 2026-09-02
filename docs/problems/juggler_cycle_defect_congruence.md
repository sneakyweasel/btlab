# Juggler floor-defect / congruence accumulation

Status: **ARCHIVED**

Directed follow-up of
[juggler_cycle_exponent_budget.md](juggler_cycle_exponent_budget.md)
and the already-closed remainder stack
([juggler_global_defect.md](juggler_global_defect.md),
[juggler_cycle_rounding.md](juggler_cycle_rounding.md),
[juggler_cycle_diophantine.md](juggler_cycle_diophantine.md),
[juggler_cycle_mod_closure.md](juggler_cycle_mod_closure.md),
[juggler_cycle_remainder_finance.md](juggler_cycle_remainder_finance.md)),
not a reopen of finance, not a leftover-killer, and not a new
paper. After the cycle-wide exponent product closed as
\(3^o/2^L\), the reviewer reserve asked whether the surviving
floor errors force an impossible congruence or fractional-part
combination.

Not a halt theorem, not a floor raise, and not a claim that
every cycle itinerary is impossible.

## Problem

Every odd step is \(p=\lfloor v^{3/2}\rfloor\) and every even
step is \(v=\lfloor\sqrt p\rfloor\). Each seam is therefore an
exact remainder cell. After the main power exponents cancel on a
cycle, do the residual inequalities require an impossible
combination of congruences or fractional parts — and is that
obstruction not the global defect, cyclic remainder balance,
cycle-scale modular freeness, or finance?

## Exact statement

**Each seam is an existing cell
(KNOWN / EXACT — LEAN VERIFIED).**
An odd state satisfies \(p^2\le v^3<(p+1)^2\). An even state
satisfies \(q^2\le p<(q+1)^2\). The remainders are
`localDefectOdd` / `localDefectEven`.

**Composition is the global defect
(KNOWN / EXACT — LEAN VERIFIED).**
The weighted lift of those remainders is \(\Delta_w(n)\), and
\[
n^{3^{\#O(w)}}=T_w(n)^{2^{|w|}}+\Delta_w(n)
\]
(`global_defect_identity`). This is not an additive sum
([juggler_sum_rho.md](juggler_sum_rho.md) already closed that
rewrite).

**A return leaves the surplus
(KNOWN / EXACT — LEAN VERIFIED).**
On a cycle, \(T_w(n)=n\), so
\[
\Delta_w(n)=n^{3^o}-n^{2^L}=n^{2^L}(n^{3^o-2^L}-1)
\]
(`image_eq_start_defectRatio`, Paper A Corollary 2.7). The main
exponents cancel into this positive integer. Its size is
`cycleMin_finance`. Near-convergents of \(\log 2/\log 3\) make
the relative gap tiny and are the leftover lengths.

**Cyclic remainder balance is an identity
(KNOWN / EXACT — LEAN VERIFIED).**
\[
\sum\rho+\sum_{\mathrm{even}}x(x-1)
=
\sum_{\mathrm{odd}}x^2(x-1)
\]
on a cycle (`cycle_remainder_balance`). Off cycle the same
identity has correction \(x_0^2-x_k^2\). All-zero remainders
are already impossible for \(n\ge 2\)
(`cycle_not_localsTight`). An identity plus a known rigidity
is not a new modular obstruction.

**The peak pair is envelope slack
(KNOWN / REPARAMETERIZATION).**
One odd-then-even pair is
\[
x^3-p^{4}=2\varepsilon p^2+\varepsilon^2+\delta
\]
(`peak_diophantine_slack`). Transient peaks occupy several
residues mod \(8\) and \(16\).

**Cycle-scale congruences are free
(KNOWN).**
Once \(2Y+1>m\), the defects \(\delta,\eta\) are free residues,
so the cells impose only first-letter parity
([juggler_cycle_mod_closure.md](juggler_cycle_mod_closure.md)).
At the published floor, every listed modulus has
\(2Y+1>m\). A kill would need a complete word or a modulus
larger than the defect window.

**Fractional parts are unrestricted
(KNOWN).**
Normalized cell position \(\mathrm{pos}=\rho/(2T+1)\) is the
usable fraction of \(\{v^{3/2}\}\). Finance-relevant `OOE`
starts reach \(\mathrm{pos}=0.9999737\)
([juggler_cycle_remainder_finance.md](juggler_cycle_remainder_finance.md)).

No cycle of any length — not claimed.

## Current literature

- Global defect \(n^{3^o}=T_w(n)^{2^L}+\Delta\) —
  **EXACT — LEAN VERIFIED**
  (`global_defect_identity`)
- Return burns the surplus, \(1+q=n^{3^o-2^L}\) —
  **EXACT — LEAN VERIFIED**
  (`image_eq_start_defectRatio`)
- Cyclic remainder balance and all-zero rigidity —
  **EXACT — LEAN VERIFIED**
  (`cycle_remainder_balance`, `cycle_not_localsTight`)
- Peak \((\delta,\varepsilon)\) slack —
  **CLOSE** / **REPARAMETERIZATION**
  ([juggler_cycle_diophantine.md](juggler_cycle_diophantine.md))
- Cycle-scale modular closure —
  **CLOSE** / **REFUTED** leftover-killer
  ([juggler_cycle_mod_closure.md](juggler_cycle_mod_closure.md))
- Finance-weighted remainder positions —
  **CLOSE** / **REFUTED** leftover-killer
  ([juggler_cycle_remainder_finance.md](juggler_cycle_remainder_finance.md))
- Naive path-sum of remainders —
  **CLOSE** / **REFUTED**
  ([juggler_sum_rho.md](juggler_sum_rho.md))
- Cycle-wide exponent product —
  **CLOSE** / **REPARAMETERIZATION**
  ([juggler_cycle_exponent_budget.md](juggler_cycle_exponent_budget.md))
- Cycle finance —
  **EXACT — LEAN VERIFIED**
  (`cycleMin_finance`)
- Collatz-style financing —
  **known** (`simons-de-weger-2005-collatz-m-cycles`)
- Every start reaches 1 — not claimed

Project relationship: **refuted** as a new congruence or
fractional-part obstruction; the residual after cancellation is
a **REPARAMETERIZATION** of the global defect, and its size is
finance.

## Branch budget

```text
Mathematical target     After composing the exact seam inequalities
                        around a cycle, do the residuals (once the
                        main 3^o vs 2^L powers cancel) force an
                        impossible congruence or fractional-part
                        combination that is not global defect /
                        cyclic remainder balance / mod-closure
                        freeness / cycleMin_finance?
Novelty hypothesis      Floor errors are the only surviving
                        obstruction and they are modularly or
                        fractional-part incompatible
Falsifier               The composed residual is Δ = n^{3^o}-n^{2^L};
                        cyclic balance is an identity; at cycle
                        scale defects are free residues; cell
                        positions are unrestricted
Existing machinery      global_defect_identity; cycle_remainder_balance;
                        cycle_not_localsTight; peak_diophantine_slack;
                        cycle_mod_closure R_nec; cycleMin_finance;
                        remainder_finance pos unrestricted
Maximum Phase-0 scope   Write the composed residual identity;
                        replay the four existing falsifiers on one
                        short word / leftover pair / near-top witness.
                        No new modulus census, no finance reopen, no Lean
Promotion criterion     A congruence or {frac} obstruction those
                        four objects do not already state
Stop criterion          The reserve attack is their composition
```

## Closed-bridge gates

Do not reopen finance, Baker, remainder finance, modular
closure, Diophantine peak pairs, or the exponent budget.

- **CLOSE** if composed seams are `global_defect_identity`.
- **CLOSE** if a return leaves \(n^{3^o}-n^{2^L}\).
- **CLOSE** if cyclic remainder balance is an identity.
- **CLOSE** if the peak pair is `peak_diophantine_slack`.
- **CLOSE** if cycle-scale defects are free residues.
- **CLOSE** if cell positions are unrestricted.
- **PROMOTE** only if a congruence or fractional-part
  obstruction appears that those objects do not already state.

Do **not** raise \(N_0\). Do **not** open \(L=55293\). Do
**not** reintroduce a leftover-killer census. Do **not** edit
Paper A. Do **not** add Lean.

## Explicitly out of Phase-0

A \(K=11\) proof, a new modulus census, Fourier / \(Q\)-sections,
a branch-and-bound engine, ledger row, new Lean, CLI,
visualization, Paper A edit, a finance floor raise.

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Seam cells \(p^2\le v^3<(p+1)^2\) and \(q^2\le p<(q+1)^2\) —
  **KNOWN** (`localDefectOdd` / `localDefectEven`)
- Composed residual \(\Delta_w(n)\) —
  **KNOWN** / **REPARAMETERIZATION** (`global_defect_identity`)
- Cycle leftover \(n^{3^o}-n^{2^L}\) —
  **KNOWN** (`image_eq_start_defectRatio`)
- Cyclic remainder balance —
  **KNOWN** (`cycle_remainder_balance`)
- Peak-pair slack —
  **KNOWN** / **REPARAMETERIZATION** (`peak_diophantine_slack`)
- Cycle-scale \(R_{\mathrm{nec}}\) —
  **KNOWN** (first-letter parity)
- Cell position \(\mathrm{pos}=\rho/(2T+1)\) —
  **KNOWN** (unrestricted)
- Floors on that leftover —
  **KNOWN** (`cycleMin_finance`)
- Composed-remainder leftover-killer —
  **REFUTED** (`juggler_cycle_defect_congruence`)
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_defect_congruence`
- Dataset: `data/research/juggler/cycle_finance/defect_congruence/summary.json`
- Tests: `tests/research/juggler_sequence/test_cycle_defect_congruence.py`
- Window: seam cells at \(13\); composed residual on \(365\)
  \(\mathtt{OOE}\); peak-pair slack at \(13\); path balance on
  that itinerary; first-step residues on \(\mathtt{OOE}\) starts
  in \([13,400)\); defect-width collapse on the archived moduli
  at \(n=10^6+1\); near-top witness \(1016445\); leftover gaps
  at \(L=19,84\). Fast suite only. No CLI. No new Lean. No
  \(N_0\) raise.

## Conjectures

`juggler_cycle_defect_congruence` — **REFUTED**.

## Counterexamples

- \(365\) follows \(\mathtt{OOE}\) and
  \(\Delta=\mathrm{envelope\ slack}\). Falsifier of a new
  composed residual.
- Cycle leftover \(n^{3^o}-n^{2^L}\). At \(L=19\) the gap is
  \(7153\); at \(L=84\) it is \(3^{53}-2^{84}\). Both are finance
  gaps, not moduli.
- Path balance on \(365\) \(\mathtt{OOE}\) equals
  \(\mathrm{start}^2-\mathrm{end}^2\). On a return the
  correction vanishes. Falsifier of a cyclic sum obstruction.
- Peak pair \(13\to 46\to 6\):
  \(13^3-6^4=2\cdot 10\cdot 46^2+10^2+81\). Falsifier of a
  sequential identity that is not envelope slack.
- First-step \(\mathtt{OOE}\) remainders on \([13,400)\) occupy
  several residues mod \(3,8,9,16\). Falsifier of one forbidden
  class.
- At \(n\ge 10^6+1\), every listed modulus has \(2Y+1>m\).
  Falsifier of a cycle-scale congruence.
- \(\mathtt{OOE}\)-legal \(n=1016445\) has
  \(\mathrm{pos}=0.9999737\). Falsifier of a forced fractional-
  part cut.

## Formalization

None added. The identity is already `global_defect_identity`.
The return leftover is already `image_eq_start_defectRatio`.
The cyclic sum is already `cycle_remainder_balance`. The floors
are already `cycleMin_finance`. Paper A is unchanged. Do not
add `DefectCongruence.lean`.

## Results

- **Composition identity** — **KNOWN** /
  **REPARAMETERIZATION** (`defect_congruence/summary.json`).
- **Cycle leftover** — **KNOWN** (`image_eq_start_defectRatio`).
- **Balance identity** — **KNOWN**.
- **Peak-pair slack** — **KNOWN** / **REPARAMETERIZATION**.
- **Residues not a single class** — **COMPUTATIONALLY VERIFIED**
  on \(\mathtt{OOE}\) starts in \([13,400)\).
- **Cycle-scale defects free** — **KNOWN** (replay of
  `defect_width_collapses`).
- **Cell positions unrestricted** — **KNOWN** (replay of
  \(n=1016445\)).
- **No new cyclic obstruction.**

## Open questions

None from composed floor-defect congruences. Do not reopen
finance, Baker, remainder finance, modular closure, Diophantine
peak pairs, or the exponent budget.

## Decision

**CLOSE**. After the main powers cancel, the residual is
\(\Delta=n^{3^o}-n^{2^L}\). That is the global defect on a
return, and its size is finance. The cyclic remainder sum is an
identity. At cycle scale the defects are free residues, and
finance-relevant cell positions sit at the top of their cells.
The slogan that floor errors are a surprisingly strong leftover
obstruction is the finance programme under a new name, plus four
already-closed remainder attacks. No Paper A edit, no ledger
row, no new Lean, no \(N_0\) raise, no leftover-killer census.

Best next question: none from floor-defect / congruence
accumulation.

## Publication assessment

Status: `ARCHIVED`. Laboratory negative knowledge on a reviewer
reserve; not a second manuscript and not a Paper A edit.

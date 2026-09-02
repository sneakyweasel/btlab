# Juggler strict block potential

Status: **ARCHIVED**

Directed follow-up of
[juggler_cycle_exponent_budget.md](juggler_cycle_exponent_budget.md),
not a reopen of that product, finance, or compensated
contraction, and not a new paper. Attack #1 wrote the block
scale as \(\rho=3^a/2^{a+r}\). This phase asks whether that
scale is a Lyapunov function: a state-only \(\Phi\) with
\(\Phi(J^{\mathrm{block}}(n))<\Phi(n)\) on every CycleMin-legal
block, or at one canonical event per block.

Not a halt theorem, not a leftover-killer, and not a claim that
every cycle itinerary is impossible.

## Problem

The formal block map is \(L\mapsto\rho L\) with \(L=\log n\).
Does a logarithmic potential, or a floor-corrected variant in
the same monotone class, strictly decrease on every legal
\(O^a E^r\) block and thereby forbid a cycle?

## Exact statement

**Logarithmic candidates are monotone
(KNOWN / EXACT — HUMAN PROOF).**
On integers \(n\ge 3\), both \(\log n\) and \(\log\log n\) are
strictly increasing. Therefore
\[
\Phi(T)<\Phi(n)\qquad\Longleftrightarrow\qquad T<n
\]
for \(\Phi\in\{\log,\log\log\}\). The “logarithmic Lyapunov” is
block contraction.

**CycleMin-legal first blocks never decrease \(L\)
(KNOWN).**
A first block is CycleMin-possible only if it expands
(\(2^{a_0+r}\le 3^{a_0}\)) and the valley stays \(\ge n\). By
that definition \(T\ge n\), so no increasing \(\Phi\) can drop.
Witness \(115\xrightarrow{\mathtt{O}^5E^2}8165\)
(\(\rho=243/128>1\)).

**Contracting blocks already decrease
(KNOWN / EXACT — LEAN VERIFIED).**
If \(3^a<2^{a+r}\) and \(n\ge 2\), then \(T<n\)
(`power_bound_contracts`). Floors make the inequality stronger,
not weaker. Witness \(25\xrightarrow{\mathtt{OOOEE}}15\)
(\(\rho=27/32<1\)).

**The floor-strict scale is the mixed envelope
(KNOWN / EXACT — LEAN VERIFIED).**
For a mixed itinerary,
\[
T^{2^{a+r}}<n^{3^a},
\]
i.e. \(L(T)<\rho L(n)\) (`power_bound_word_strict`). When
\(\rho>1\) this still allows \(L(T)>L(n)\). It is not a
Lyapunov inequality.

**A first-\(E\) event always decreases and does not kill
cycles (KNOWN).**
Every even step has \(T=\lfloor\sqrt{x}\rfloor<x\) for
\(x\ge 2\). So every increasing \(\Phi\) drops at the first
\(E\) of a block. The preceding odd run can raise \(\Phi\) by
more. The net sign is the sign of \(T-n\).

**A state-only potential cannot telescope
(KNOWN).**
On a cycle, \(T_w(n)=n\), so \(\Phi(n)=\Phi(n)\). Strict
decrease on every block of a closed orbit is impossible for
any \(\Phi\) of \(n\) alone. The formal product of the
\(\rho_i\) is \(3^o/2^L>1\); floors eat the surplus. That is
the exponent budget / finance.

No cycle of any length — not claimed.

## Current literature

- Word envelope \(T^{2^k}\le n^{3^o}\) —
  **EXACT — LEAN VERIFIED**
  (`power_bound_word`)
- Mixed words are strict —
  **EXACT — LEAN VERIFIED**
  (`power_bound_word_strict`)
- Formal contraction \(3^o<2^k\Rightarrow T<n\) —
  **EXACT — LEAN VERIFIED**
  (`power_bound_contracts`)
- Formal expansion on a cycle —
  **EXACT — LEAN VERIFIED**
  (`cycle_itinerary_formally_expanding`)
- Cycle finance —
  **EXACT — LEAN VERIFIED**
  (`cycleMin_finance`;
  [juggler_cycle_finance.md](juggler_cycle_finance.md))
- Block product \(\prod\rho_i=3^o/2^L\) —
  **CLOSE** / **REPARAMETERIZATION**
  ([juggler_cycle_exponent_budget.md](juggler_cycle_exponent_budget.md))
- Compensated contraction is not uniform —
  **EXACT — LEAN VERIFIED** as a local certificate,
  not a Lyapunov
  ([juggler_compensated_contraction.md](juggler_compensated_contraction.md))
- \(L=\log\log x\) is a diagnostic, not the map —
  **KNOWN**
  ([juggler_probabilistic.md](juggler_probabilistic.md))
- Collatz-style financing —
  **known** (`simons-de-weger-2005-collatz-m-cycles`)
- Every start reaches 1 — not claimed

Project relationship: **refuted** as a new Lyapunov; the
candidates are **REPARAMETERIZATION**s of contraction and
the mixed envelope.

## Branch budget

```text
Mathematical target     Does a state-only Φ (log n, log log n, or a
                        floor-corrected log) strictly decrease on
                        every CycleMin-legal O^a E^r block, or at
                        one canonical event per block, in a way that
                        is not T<n / power_bound_contracts /
                        power_bound_word_strict / the exponent budget?
Novelty hypothesis      floors turn L ↦ ρ L into a strict Lyapunov
                        even on expanding first blocks
Falsifier               log and log log are monotone, so Φ(T)<Φ(n)
                        iff T<n; CycleMin-legal first blocks have
                        valley ≥ n; 115→8165 increases L; a state-only
                        Φ cannot telescope around a cycle
Existing machinery      power_bound_word, power_bound_word_strict,
                        power_bound_contracts, cycle_itinerary_formally_expanding,
                        cycleMin_finance, exponent-budget CLOSE
Maximum Phase-0 scope   monotone equivalence; expanding/contracting
                        witnesses; first-E event; L(T)<ρ L(n) iff the
                        mixed envelope. No Lean, no finance reopen, no N0
Promotion criterion     a Φ that decreases on every CycleMin-legal
                        block for a reason that is not T<n
Stop criterion          the candidates are monotone rewrites of
                        contraction, and the cycle Lyapunov is
                        impossible for n-only Φ
```

## Closed-bridge gates

Do not reopen the exponent budget, finance, Baker, or
compensated contraction as a global Lyapunov.

- **CLOSE** if \(\log\) and \(\log\log\) have the same descent
  sign as \(T<n\).
- **CLOSE** if CycleMin-legal first blocks never decrease \(L\).
- **CLOSE** if the expanding witness \(115\to 8165\) increases
  every increasing \(\Phi\).
- **CLOSE** if contracting blocks are `power_bound_contracts`.
- **CLOSE** if \(L(T)<\rho L(n)\) is `power_bound_word_strict`.
- **CLOSE** if the first \(E\) always decreases and does not
  forbid return.
- **CLOSE** if a state-only \(\Phi\) cannot telescope around a
  cycle.
- **PROMOTE** only if a \(\Phi\) decreases on every
  CycleMin-legal block for a reason that is not \(T<n\).

Do **not** raise \(N_0\). Do **not** open \(L=55293\). Do
**not** reintroduce finance. Do **not** edit Paper A. Do
**not** add Lean.

## Explicitly out of Phase-0

A \(K=11\) proof, defect amplification, Fourier / residues /
\(Q\)-sections, a branch-and-bound engine, ledger row, new Lean,
CLI, visualization, Paper A edit, an itinerary-dependent ranking
function, a finance floor raise.

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- \(\Phi=\log n\) and \(\Phi=\log\log n\) —
  **REPARAMETERIZATION** of \(T<n\)
- CycleMin-legal first-block decrease —
  **REFUTED**; valley \(\ge n\) by definition; witness \(115\)
- Contracting-block decrease —
  **KNOWN** (`power_bound_contracts`)
- Floor-strict \(L(T)<\rho L(n)\) —
  **REPARAMETERIZATION** of `power_bound_word_strict`
- First-\(E\) event —
  **KNOWN**; true and insufficient
- State-only cycle Lyapunov —
  **REFUTED** by telescoping
- Block-potential leftover-killer —
  **REFUTED** (`juggler_cycle_block_potential`)
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_block_potential`
- Dataset: `data/research/juggler/cycle_finance/block_potential/summary.json`
- Tests: `tests/research/juggler_sequence/test_cycle_block_potential.py`
- Window: witnesses \(25\) and \(115\); monotone check and first-\(E\)
  on OO-launches in \([13,2001)\). Fast suite only. No CLI.
  No new Lean. No \(N_0\) raise.

## Conjectures

`juggler_cycle_block_potential` — **REFUTED**.

## Counterexamples

- \(\log\) and \(\log\log\) decrease if and only if \(T<n\).
  Falsifier of a new logarithmic Lyapunov.
- \(115\xrightarrow{\mathtt{O}^5E^2}8165\). Falsifier of
  “every CycleMin-legal block decreases \(L\)”.
- \(25\xrightarrow{\mathtt{OOOEE}}15\). Falsifier of “floors
  obstruct contraction”: this is `power_bound_contracts`.
- \(T^{2^{a+r}}<n^{3^a}\) on those mixed blocks. Falsifier of
  a new floor-strict scale law.
- First \(E\) at the peak of \(115\) drops, and the block still
  ends at \(8165>115\). Falsifier of “one decreasing event per
  block forbids a cycle”.
- \(\Phi(n)=\Phi(n)\) on a closed orbit. Falsifier of a
  state-only cycle Lyapunov.

## Formalization

None added. Contraction is already `power_bound_contracts`.
The mixed scale is already `power_bound_word_strict`. Formal
expansion is already `cycle_itinerary_formally_expanding`. Paper A
is unchanged. Do not add `BlockPotential.lean`.

## Results

- **Monotone collapse** — **KNOWN** /
  **REPARAMETERIZATION** (`block_potential/summary.json`).
- **CycleMin first blocks** — **KNOWN**: \(L\) never drops.
- **Expanding witness** — **COMPUTATIONALLY VERIFIED** at
  \(115\).
- **Contracting witness** — **KNOWN** (`power_bound_contracts`).
- **First \(E\)** — **KNOWN**; insufficient.
- **No new cyclic obstruction.**

## Open questions

None from the block potential. Do not reopen the exponent
budget, finance, or compensated contraction as a global
Lyapunov. Do not start an itinerary-dependent ranking function from
this close.

## Decision

**CLOSE**. The natural block potential is \(\log n\). Because
it is monotone, a strict decrease is exactly \(T<n\).
CycleMin-legal first blocks are forbidden from dropping, and
the expanding witness \(115\to 8165\) raises every increasing
\(\Phi\). Contracting blocks already have
`power_bound_contracts`. The floor-strict form \(L(T)<\rho L(n)\)
is the mixed envelope and does not give \(L(T)<L(n)\) when
\(\rho>1\). A first-\(E\) decrease is true and does not kill
cycles. A function of \(n\) alone cannot strictly decrease
around a cycle; the formal product of the \(\rho_i\) is the
closed exponent budget, and the floors are finance. This is
Attack #1 as a Lyapunov slogan, not a new invariant. No
Paper A edit, no ledger row, no new Lean, no \(N_0\) raise,
no leftover-killer census.

Best next question: none from the strict block potential.

## Publication assessment

Status: `ARCHIVED`. Laboratory negative knowledge on a
Lyapunov rewrite of \(L\mapsto\rho L\); not a second
manuscript and not a Paper A edit.

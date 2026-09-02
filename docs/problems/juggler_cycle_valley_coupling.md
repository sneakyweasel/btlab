# Juggler cheap-valley return coupling

Status: **ARCHIVED**

Refinement of
[juggler_cycle_budget_opt.md](juggler_cycle_budget_opt.md),
not a new paper. After Section 5 named
\(\max\sum 1/(x_i\log x_i)\) over realizable geometry, this phase
asks whether a return-cost coupling forces
\(N_{\mathrm{cheap}}<o-e\) on a realized `CycleMin` strongly
enough to raise the period cutoff. Not a halt theorem, not a
leftover-itinerary census, and not a floor raise.

## Problem

Theorem 4.7 charges \(o-e\) copies of `OOE` at the cycle minimum
(one at \(n\), the rest at \(n+2\)). After one cheap `OOE` the
next valley is at envelope \(9/8\), not at \(n+2\). Does the
cost of returning to \(n\)-scale cut \(N_{\mathrm{cheap}}\)
below \(o-e\) with a certified finance bound?

## Exact statement

**No exact exponent reset (EXACT — HUMAN PROOF).**
A circuit of \(k\ge 1\) odds and \(\ell\ge 1\) evens from
height \(n^{9/8}\) lands at envelope
\(3^{k+2}/2^{k+\ell+3}\). This equals \(1\) if and only if
\(3^{k+2}=2^{k+\ell+3}\), which is impossible.

**Shortest envelope descent (EXACT — HUMAN PROOF).**
The least letter-cost legal descent from \(9/8\) is
\(O^5E^3\), landing at \(2187/2048\). Peak legality
\((9/8)(3/2)^5\ge 2^3\) is the same comparison
\(3^7\ge 2^{11}\). No legal circuit with fewer than eight
letters lands strictly below \(9/8\).

**`OOE` next valley is not \(n+2\) (EXACT — HUMAN PROOF /
COMPUTATIONALLY VERIFIED).**
If \(v\) is odd and \(T(v)\) is odd, the landing
\(F_2(v)=\bigl\lfloor\sqrt{T^2(v)}\bigr\rfloor\) is
\(\asymp v^{9/8}\). On the scanned `OOE` starts
\(\{37,365,1999\}\) and five starts near \(10^6+53\),
\(F_2(v)>v+2\). The \(n+2\) slot of Theorem 4.7 is not the
next valley of a realized `OOE`.

**Separated-count diagnostic (OBSERVATION).**
If every extra \(n\)-scale `OOE` had to pay a \((5,3)\)
return and restart at exponent \(1\), then
\[
N\le\min\bigl(\lfloor(o+5)/7\rfloor,\lfloor(e+3)/4\rfloor\bigr).
\]
At \(L=25781\) this is \(2324<6751=o-e\). The hypothesis is
false: a \((5,3)\) landing is \(n^{2187/2048}\), not \(n\),
and a first circuit \(O^{12}E^7\) or \(O^{53}E^{31}\) lands
closer to \(n\) than \(9/8\) without being an `OOE`.

**Lowest landing from exponent \(1\) (EXACT — HUMAN PROOF).**
Among circuits with \(k\le 53\) and \(\ell\le 32\), the
lowest legal landing from height \(n\) is \(O^{53}E^{31}\)
at \(3^{53}/2^{84}\). The \(k\le 12\) champion is
\(O^{12}E^7\) at \(3^{12}/2^{19}\). Both are near-convergents
of \(\log 2/\log 3\). Floors of size \(O(1/x)\) do not pull
those landings down to \(n+2\).

**Leftover-killer (REFUTED).**
A certified length-only upper bound that uses only this
coupling and excludes \(L=25781\) at floor \(10^6\) does not
exist. Envelope walks give *upper* bounds on later-valley
height, hence *lower* bounds on \(1/(x\log x)\). Treating
them as exclusions is invalid. The diagnostic
\(9/8\)-charge and the height-minimizing \(k\le 12\) walk
leave \(L=25781\) live
(\(\theta\approx 2.546\cdot 10^{-5}\) versus diagnostic RHS
\(1.07\cdot 10^{-4}\) and \(8.58\cdot 10^{-5}\)). The
\(k\le 53\) walk sits at \(2.59\cdot 10^{-5}\), still above
\(\theta\), and is a specific strategy, not an upper bound.
A later-valley lower bound that applies to *every* legal
first circuit is still \(\asymp n\).

No cycle of any length — not claimed.

## Current literature

- Run-type packing, \(N_{\mathrm{cheap}}=o-e\) —
  **EXACT — HUMAN PROOF**
  ([juggler_cycle_budget_opt.md](juggler_cycle_budget_opt.md));
  cyclic adjacency leftover-killer **REFUTED**
  (`juggler_cycle_run_extremum_leftover_killer`)
- Unique visit of \(n\), \(n+2\) as leftover-killer —
  **REFUTED**
  ([juggler_cycle_equal_valleys.md](juggler_cycle_equal_valleys.md))
- Second-valley \(\ge 281\) at leftover \(84\) —
  **REFUTED**
  ([juggler_cycle_second_valley.md](juggler_cycle_second_valley.md))
- `OOE` cell \(w^8\le v^9\); two-block \(243<256\) —
  **EXACT — HUMAN PROOF** /
  leftover-killer **REFUTED**
  ([juggler_cycle_ordered_excursion.md](juggler_cycle_ordered_excursion.md))
- Collatz-style financing —
  **known** (`simons-de-weger-2005-collatz-m-cycles`)
- Every start reaches 1 — not claimed

Project relationship: **refuted** as a leftover-killer; the
\((5,3)\) descent and the `OOE` next-valley comparison are
negative knowledge on the named Section 5 program.

## Branch budget

```text
Mathematical target     A coupling that forces N_cheap < o-e on a
                        realized CycleMin, with a certified finance
                        bound that moves the cutoff or shrinks
                        E_run(10^6)
Novelty hypothesis      After cheap OOE the orbit is at n^{9/8};
                        a CycleMin-legal return to n-scale has a
                        letter cost, so o-e independent n-valleys
                        are not realizable
Falsifier               The only later-valley lower bound that
                        applies to every legal first circuit is
                        still ~n (near-convergent landings); or
                        N_cheap < o-e is unique visit rewritten;
                        or the bound is word-conditional on OOE
Existing machinery      run-type packing; run_extremum Level C;
                        power_bound_word; ooe_cell; unique visit;
                        second-valley CLOSE; CycleMin even-ge-sq
Maximum Phase-0 scope   Exponent-walk legality; shortest descent
                        from 9/8; OOE landing versus n+2; N_sep
                        diagnostic; greedy walks at L=25781; scan
                        of the 99 as diagnostics only. No Lean,
                        no floor raise, no Paper A theorem
Promotion criterion     A reusable inequality N_cheap <= f(o,e) <
                        o-e that certifies a smaller leftover set
                        or a larger cutoff
Stop criterion          The count law is unique visit; n+2 after
                        OOE is the existing F_2 cell; long first
                        circuits land at n^{1+ε}; no certified
                        leftover dies
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Envelope landing \(3^{k+2}/2^{k+\ell+3}\) from \(9/8\) —
  **EXACT — HUMAN PROOF**
- Shortest descent \((5,3)\) to \(2187/2048\) —
  **EXACT — HUMAN PROOF**
- Exact reset to exponent \(1\) —
  **REFUTED**
- \(F_2(v)>v+2\) on realized `OOE` —
  **EXACT — HUMAN PROOF** / **COMPUTATIONALLY VERIFIED**
- \(N_{\mathrm{sep}}(5,3)=2324<6751\) at \(L=25781\) —
  **OBSERVATION**; not a restart-at-\(n\) theorem
- Lowest landing from \(1\) is a \(\log 2/\log 3\)
  near-convergent —
  **EXACT — HUMAN PROOF**
- Leftover-killer —
  **REFUTED** (`juggler_cycle_valley_coupling_leftover_killer`)
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_valley_coupling`
- Dataset: `data/research/juggler/cycle_finance/valley_coupling/summary.json`
- Tests: `tests/research/juggler_sequence/test_cycle_valley_coupling.py`
- Window: exponent search \(k\le 53\), \(\ell\le 32\); `OOE`
  landings on \(\{37,365,1999\}\) and five starts near
  \(10^6+53\); diagnostic scan of the \(99\) run-type
  leftovers. Fast suite does not rerun the \(99\)-walk.
  No CLI. No Lean.

## Conjectures

`juggler_cycle_valley_coupling_leftover_killer` — **REFUTED**.

## Counterexamples

- \(O^{53}E^{31}\) from exponent \(1\) lands at
  \(3^{53}/2^{84}\approx n^{1.002}\). Falsifier of a uniform
  later-valley lower bound that beats \(n+2\) enough to
  move the cutoff.
- \(O^{12}E^7\) lands at \(3^{12}/2^{19}\approx n^{1.014}\),
  below \(9/8\). Falsifier of “every subsequent valley is at
  least \(n^{9/8}\)”.
- Diagnostic \(9/8\)-charge and \(k\le 12\) greedy walks
  leave \(L=25781\) live. Falsifier of a cutoff raise.

## Formalization

None. No `CycleValleyCoupling.lean`. Paper A is unchanged.
Do not formalize the diagnostic walks.

## Results

- **\((5,3)\) descent** — **EXACT — HUMAN PROOF**.
- **No exact reset** — **EXACT — HUMAN PROOF**.
- **`OOE` landing \(>n+2\)** — **COMPUTATIONALLY VERIFIED**
  (`valley_coupling/summary.json`).
- **\(N_{\mathrm{sep}}<o-e\) on all \(99\)** —
  **OBSERVATION**, not a certified charge.
- **No certified leftover dies.** \(L=25781\) remains the
  first survivor. Diagnostic greedy \(k\le 12\) would drop
  \(86\) lengths if envelope heights could be used as an
  upper bound on the sum; they cannot.

## Open questions

None from this coupling. A later-valley *lower* bound that
beats \(n^{1+\varepsilon}\) for every legal first circuit is
the same near-convergent obstruction as the closed
second-valley branch.

## Decision

**CLOSE**. The coupling is real for a realized `OOE`: the
next valley is at \(n^{9/8}\), not at \(n+2\), and the
shortest envelope descent is \(O^5E^3\). That does not
certify \(N_{\mathrm{cheap}}<o-e\) as a length-only law.
Exact reset to exponent \(1\) is impossible, so
\(N_{\mathrm{at}\,n}=1\) is unique visit. Long first
circuits land at \(n^{1+\varepsilon}\) and restore the
Theorem 4.7 price up to a negligible factor. No Paper A
edit, no ledger row, no Lean.

Best next question: none from return-cost coupling.

## Publication assessment

Status: `ARCHIVED`. Laboratory negative knowledge on the
Section 5 program; not a second manuscript and not a
Paper A edit.

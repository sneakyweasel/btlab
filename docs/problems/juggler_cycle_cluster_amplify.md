# Juggler cheap-cluster Amplify versus surplus

Status: **ARCHIVED**

Refinement of
[juggler_amplify_surplus.md](juggler_amplify_surplus.md) and
[juggler_cycle_descent_next_run.md](juggler_cycle_descent_next_run.md),
not a new paper. After a cheap-band descent was shown to start
\(a=2\), this phase asks whether first-defect Amplify on
\(w_k=(\mathtt{OOE})^k\) beats the formal surplus
\(G=n^{3^{2k}}-n^{2^{3k}}\) for some \(k\le 25\). Not a halt
theorem, not a leftover-itinerary census, and not a floor raise.

## Problem

A single `OOE` has Amplify \(\sim n^{6}\rho\) against
\(G\sim n^{9}\). Does a cheap climb of \(k\le 25\) copies —
the length of one cluster before the landing leaves the
\(19n\) band — close that \(n^3\) gap?

## Exact statement

**Linear gap is \(3\) (EXACT — HUMAN PROOF).**
On \(w_k=(\mathtt{OOE})^k\) with the first remainder inserted
at letter \(0\), the tight-scale linear Amplify exponent is
\(9^k-3+\rho_{\mathrm{exp}}\). Surplus is \(n^{9^k}-n^{8^k}\),
so the leading gap is \(3-\rho_{\mathrm{exp}}\). For
\(\rho=1\) the gap is \(3\); for optimistic \(\rho\asymp n^{3/2}\)
it is \(3/2\).

**Inductive step (EXACT — HUMAN PROOF).**
After \(k\) blocks the state scale is \(x=9^k/8^k\) and the
letter count is \(3k\). The next two odds add \(2\cdot 9^k\)
and \(6\cdot 9^k\). Hence
\[
(9^k-3)+8\cdot 9^k=9^{k+1}-3.
\]
Appending `OOE` does not close the gap. The identity holds
for every \(0\le k<25\) as an exact dyadic check, and the
induction gives every \(k\ge 1\).

**Cubics stay behind (EXACT — HUMAN PROOF).**
At the last odd lift, the cubic-to-linear ratio has exponent
\(\rho_{\mathrm{exp}}-3\). The \(D^2,D^3\) terms are
\(n^{-3}\) relative to the linear term (\(\rho=1\)) and cannot
eat a surplus gap of \(n^{3}\) or \(n^{3/2}\).

**Realized \(k=1\) (COMPUTATIONALLY VERIFIED).**
The starts \(365\), \(1517\), and \(1000057\) follow `OOE`
and satisfy \(\operatorname{Amplify}<\Delta<G\). At
\(n=1000057\),
\(\operatorname{Amplify}\approx 1.31\cdot 10^{45}\) against
\(G\approx 1.00\cdot 10^{51}\). The start \(10^6+1\) does not
follow `OOE`. Realized follow depth of successive `OOE` is
\(4,3,2,0\) at those four seeds.

**Leftover-killer (REFUTED).**
\(\operatorname{Amplify}/G\sim n^{-3}\) (or \(n^{-3/2}\) at
max \(\rho\)) for every cheap-cluster length. The ratio tends
to \(0\). It never exceeds \(1\).

No cycle of any length — not claimed.

## Current literature

- First-defect Amplify versus \(G\) on the thirty length-11
  leftovers —
  **REFUTED**
  ([juggler_amplify_surplus.md](juggler_amplify_surplus.md));
  the linear term is \(n^{2184}\rho\) against \(n^{2187}\)
- `amplifyDefect` / odd cubic lift —
  **EXACT — LEAN VERIFIED**
- Cheap-band descent can start \(a=2\) —
  **REFUTED** as a leftover-killer
  ([juggler_cycle_descent_next_run.md](juggler_cycle_descent_next_run.md))
- \(1+q\) concatenation —
  **EXACT — LEAN VERIFIED**
  ([juggler_normalized_defect.md](juggler_normalized_defect.md))
- Uniform \(c/(\lambda-1)\) —
  **REFUTED**
  ([juggler_expansion_slack.md](juggler_expansion_slack.md))
- Every start reaches 1 — not claimed

Project relationship: **refuted**. The \(n^3\) gap of the
length-11 Amplify branch is the same invariant, now checked
on cheap `OOE` clusters.

## Branch budget

```text
Mathematical target     For w_k=(OOE)^k, k=1..25, does
                        Amplify/G stay away from 0 or exceed 1?
Novelty hypothesis      k cubic lifts close the n^3 gap
Falsifier               Amplify/G → 0 like a positive power of n
                        for every k before the cluster leaves
                        the cheap band, or Amplify>G is T<n
Existing machinery      amplifyDefect; linear exponent walk;
                        1+q concat; cheap band [n,19n]
Maximum Phase-0 scope   Exact dyadic exponents k=1..25; inductive
                        step; cubic-to-linear exponent; realized
                        k=1 at 365, 1517, 1000057. No Lean
Promotion criterion     Some k with Amplify>G, not rewritten as T<n
Stop criterion          The exponent gap stays a positive power
                        of n for every such k
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Linear Amplify exponent \(9^k-3\) —
  **EXACT — HUMAN PROOF**
- Inductive addend \(8\cdot 9^k\) —
  **EXACT — HUMAN PROOF**
- Optimistic gap \(3/2\) —
  **EXACT — HUMAN PROOF**
- Cubic / linear exponent \(\rho-3\) —
  **EXACT — HUMAN PROOF**
- Realized \(\operatorname{Amplify}<G\) on `OOE` —
  **COMPUTATIONALLY VERIFIED**
- Leftover-killer —
  **REFUTED** (`juggler_cycle_cluster_amplify`)
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_cluster_amplify`
- Dataset: `data/research/juggler/cycle_finance/cluster_amplify/summary.json`
- Tests: `tests/research/juggler_sequence/test_cycle_cluster_amplify.py`
- Window: exact exponents \(k\le 25\); realized `OOE` at
  \(365,1517,1000057\). Fast suite does not materialise
  \(n^{9^{25}}\). No CLI. No Lean.

## Conjectures

`juggler_cycle_cluster_amplify` — **REFUTED**.

## Counterexamples

- Gap \(3\) at every \(k\le 25\). Falsifier of “\(k\) lifts
  close the gap.”
- Gap \(3/2\) at max \(\rho\). Falsifier of optimistic
  closure.
- Cubics \(n^{-3}\) relative to the linear term.
- \(1000057\): Amplify \(<G\) by about \(10^{6}\).

## Formalization

None. No `CycleClusterAmplify.lean`. Paper A is unchanged.
Do not formalize the exponent walk. `amplifyDefect` already
exists.

## Results

- **Gap \(3\)** — **EXACT — HUMAN PROOF**, checked as dyadic
  integers through \(k=25\).
- **Cubics do not close it** — **EXACT — HUMAN PROOF**.
- **Realized \(k=1\) loses** — **COMPUTATIONALLY VERIFIED**.
- **No leftover dies.** Option B is closed on cheap `OOE`
  clusters. The factor-\(23\) finance gap is unchanged.

## Open questions

None from cheap-cluster Amplify. A relative tax on \(\Delta\)
that is not Amplify versus \(G\) would have to be a new
object. Do not open one from this census.

## Decision

**CLOSE**. Appending `OOE` adds \(8\cdot 9^k\) to the linear
Amplify exponent and \(9^{k+1}-9^k=8\cdot 9^k\) to the
surplus exponent. The \(n^3\) gap is invariant. Cubics stay
\(n^{3}\) behind the linear term. Realized `OOE` loses.
This is the length-11 Amplify obstruction on the cheap
cluster. No Paper A edit, no ledger row, no Lean.

Best next question: none from cheap-cluster Amplify. The
Section 5 program stays **PARK**. Option B is closed as a
finance input on this itinerary.

## Publication assessment

Status: `ARCHIVED`. Laboratory negative knowledge on
Option B; not a second manuscript and not a Paper A edit.

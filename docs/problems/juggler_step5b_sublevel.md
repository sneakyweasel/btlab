# Juggler Step 5b sublevel geometry

Status: **PROMOTE** (Phase-0 geometry table). Paper B stays
frozen at \(13/16\). No retag of `J-kernel-cancellation`.

Child of
[juggler_two_step_parity.md](juggler_two_step_parity.md).
Item 4 of the Paper B hypothesis census. Sibling of the
decoration-budget, sign-critical, kernel-\(P_0\), and
[Step 5b interpolant \(P_0\)](juggler_step5b_p0.md) gates.
Not a second \(P_0\) census, not a \(K_3\) attack, and
not a Paper B edit.

## Problem

The Phase-25 hole in Theorem 5.3 Step 5b was summing
inverse-power van der Corput terms once per short cell.
Lemma 3.9 repairs this by measuring the sublevel
\(\Omega_V=\{|f''|\le V\}\) once on a global three-term
model. Does that geometry actually stay \(O_E(1)\) and
inside the Vandermonde length bound, or does the interval
count still track the cell inventory?

## Exact statement

On the printed zero-offset triple
\(\Phi(\nu)=a\nu^{5/4}+b\nu^{11/8}+w\nu^{3/2}\) of
Paper B Theorem 5.3 Step 5b, at
\(P\in\{10^6,10^8,10^{10}\}\) and middle-band
\((u,u',w,k,h_1,h_2)\), are \(|\Omega_V|\) and its
interval count below the explicit Lemma 3.9 Vandermonde
bound, is the transition set \(T\) (the \(r\neq 2\)
pieces) \(O_E(1)\) rather than one piece per cell, and
does a per-cell \(V^{-1/2}\) sum overpay relative to the
global trivial bound?

## Current literature

- Paper B Lemma 3.9 / Theorem 5.3 Step 5b
  (`J-kernel-cancellation`) —
  **EXACT — HUMAN PROOF**. **reproduced** (geometry
  only, not the exponential-sum bound).
- Phase-26 repair: per-cell inverse-power summation was
  invalid on cells of length \(\asymp P^{1/2}/h\).
  **reproduced**.
- Step 5b interpolant \(P_0\)
  ([juggler_step5b_p0.md](juggler_step5b_p0.md)) —
  **reproduced** the constant \(c_7=1/288\) and the
  \(V\le c_7S/2\) threshold; this branch does not rerun
  that chain.
- Decoration-and-mode budget census —
  **independent** (item 1).
- Sign-critical domain scan — **independent** (item 2).
- Kernel \(P_0\) hypotheses — **independent** (item 3).
- Scale-invariant copy of Theorem R —
  **REFUTED**. Not re-tested.

## Branch budget

```text
Mathematical target     On the printed zero-offset triple, is
                        |Ω_V| and its interval count below the
                        Vandermonde bound, and is the transition
                        set T (r≠2 pieces) O_E(1) rather than
                        one piece per cell?
Novelty hypothesis      None as mathematics. A P-growing interval
                        count, or |Ω_V| above the explicit length
                        bound at large P, is a Phase-26-species
                        hole in the repaired Step 5b.
Falsifier               interval_count(Ω_V) or interval_count(T)
                        growing with P or with N; |Ω_V| larger
                        than C(PV/S + P(V/S)^{1/2}) at large P;
                        complement not single-signed; or the
                        repaired costs exceeding P^{89/96} while
                        the lemma is cited as saving them.
Existing machinery      Paper B Lemma 3.9 / Step 5b (Φ, S, V);
                        Lemma 3.8 two-term control; decoration
                        budget / kernel_p0 as sibling gates.
Maximum Phase-0 scope   One thin probe on the closed-form model
                        Φ'' and the printed interpolant Λ. Grid
                        plus root refinement. No n-walk of frozen
                        integers, no sums, no Paper B edit, no
                        Lean, no items 1–3, no α=33/32.
Promotion criterion     A named hole (bound or count fails at
                        large P), or a sharp explicit C(E), c_7
                        that the paper lacked.
Stop criterion          After the table. If the geometry matches
                        the lemma, CLOSE as OBSERVATION. Do not
                        open a visualizer or a finer P-grid.
```

## Balanced-ternary formulation

None required. The objects are real monomials on
\((P,2P]\).

## Why BT may be relevant

It is not required. The 2-adic / BT bridge stays closed.

## Candidate operations / invariants

- Explicit \(c_7=1/288\) of the Vandermonde matrix on
  \(\bigl(\tfrac54,\tfrac{11}{8},\tfrac32\bigr)\) —
  **COMPUTATIONALLY VERIFIED** (reproduced from the
  interpolant-\(P_0\) sibling)
- Sublevel \(\Omega_V\) length and interval count versus
  the proof's \(r=3,4\) length constants —
  **COMPUTATIONALLY VERIFIED**
- Transition set \(T\) interval count —
  **COMPUTATIONALLY VERIFIED**
- Per-cell inverse-power diagnostic versus the global
  trivial bound — **OBSERVATION**
- Kernel bound, Paper B text — untouched
  **EXACT — HUMAN PROOF**

## Experiments

Runner:
`python -m research.juggler_sequence.step5b_sublevel`.
Writes
`data/research/juggler/step5b_sublevel/summary.json`.
Tests:
`tests/research/juggler_sequence/test_step5b_sublevel.py`.

Float evaluation on a uniform grid of \(2\cdot 10^5\)
points plus bisection. No odd-\(n\) walk.

## Conjectures

None new. `J-kernel-cancellation` stays
**EXACT — HUMAN PROOF**.

## Counterexamples

None recorded. A \(P\)-growing interval count or a
large-\(P\) length overflow would be a hole; none
appeared in the Phase-0 table.

## Formalization

None added. Packaging a measure statement already proved
in prose is machinery gravity.

## Results

- **\(c_7=1/288\) (COMPUTATIONALLY VERIFIED; already
  named by the interpolant-\(P_0\) sibling).**
  Vandermonde matrix on
  \(\bigl(-\tfrac34,-\tfrac58,-\tfrac12\bigr)\),
  \(\lVert M^{-1}\rVert_\infty=288\). Positive octant
  gives \(1\). The printed “hence \(V\le c_7S/2\)”
  hides this constant.
- **Interval counts are \(O_E(1)\)
  (COMPUTATIONALLY VERIFIED).** At
  \(P\in\{10^6,10^8,10^{10}\}\) and the six middle-band
  families, \(\#\Omega_V\le 1\) and \(\#T\le 1\). Counts
  do not track the cell inventory
  \(N\le 3.5P^{13/24}\) (\(\#\Omega_V/N\sim 10^{-6}\)).

  **Corrected 2026-09-19: this read \(\#\Omega_V\le 3\),
  and the \(3\) was floating-point noise.** `_delta`
  computed its two derivatives as direct differences of
  \(1.5\)-powers of nearby large numbers, carrying
  \(3.4\times10^{-7}\) relative error at \(P=10^{10}\).
  That made \(\Lambda\) a staircase: inside a single
  \(200\,000\)-point grid cell the predicate
  \(\lvert\Lambda\rvert\le V\) flipped **1845 times**
  before the fix and **once** after, the step height
  falling from \(1.8\times10^{-4}V\) to
  \(4.2\times10^{-9}V\). Two rows at \(P=10^{10}\)
  reported \(3\) and \(2\) intervals where the truth is
  \(1\), and one of them recorded
  `count_ok = False` against `interval_cap = 2` -- a
  published cap violation that never happened. The
  bound \(\le 3\) stayed true, but it was presented as
  the measurement. Fixed in `ad94d39c`; the payload was
  regenerated and `verdict.max_omega_intervals` is now
  \(1\). The conclusion of this bullet is unchanged and
  slightly strengthened.
  The Phase-25 “one inverse-power term per cell” error
  is not hiding as one new interval per cell.
- **Cancellation fills the block (COMPUTATIONALLY
  VERIFIED).** On the zero-crossing families,
  \(|\Omega_V|=\Theta(P)\) at every census \(P\)
  (exactly \(P\) at \(10^6\) and \(10^8\); \(0.82P\) to
  \(P\) at \(10^{10}\)). Dyadic ratios
  \(n^{\alpha-\beta}\) move by only \(2^{1/8}\), so a
  three-term zero keeps \(|f''|\) below the printed \(V\)
  on almost the whole of \((P,2P]\). The trivial bound
  therefore costs \(P\), not the printed
  \(P^{89/96}\). This is the geometric meaning of the
  sibling’s \(V\le c_7S/2\) line (first \(P_0\)
  \(3.92\cdot 10^{24}\)), not a new threshold hunt.
- **Same-sign and wave-dominant edges have empty
  \(\Omega_V\).** Lemma 3.8-style two-term control
  without a zero is empty at the paper \(V\). Complement
  intervals are single-signed. \(|\Lambda-\Phi''|=o(V)\)
  on every sample (`resid_ok`).
- **Lemma length holds; printed assembly does not, at
  these \(P\).** Worst
  \(|\Omega_V|/(\text{proof }r=3,4\text{ bound})=0.019\).
  Repaired total on cancellation is \(\Theta(P)\),
  above \(P^{89/96}\). The old per-cell
  \(n_{\mathrm{meet}}V^{-1/2}\) is large because many
  cells meet one long interval, not because the
  interval count grew.
- No exponential sum. Paper B not edited.
  `J-kernel-cancellation` stays **EXACT — HUMAN PROOF**.

## Open questions

The independent human check of Paper B Section 5 remains.
Do not open a visualizer, a finer \(P\)-grid, or another
\(P_0\) census.

## Decision

**PROMOTE** the geometry table. Interval counts stay
\(O_E(1)\) and do not track \(N\), so the Phase-25
per-cell inverse-power error is not still hiding in
Lemma 3.9. On cancellation, \(\Omega_V\) is the dyadic
block at every laboratory \(P\) in the census: the
global trivial bound costs \(P\), which is the already
named \(V\le c_7S/2\) ineffectivity, not a new hole and
not a retag of the kernel. The geometry honesty
(\(\Omega_V\) of length \(\Theta(P)\) until the large
\(P_0\); \(c_7=1/288\)) is absorbed in the 2 September
2026 writeup. Claim set still \(13/16\). Do not
auto-continue.

Best next question: one independent human check of
Paper B Section 5, not another \(P_0\) census.

## Publication assessment

Status: `EXPLORATORY` (laboratory geometry gate). Not a
Paper B edit.

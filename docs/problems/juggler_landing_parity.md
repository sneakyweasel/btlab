# Juggler landing-parity and square-threshold dynamics

Status: **EXPLORATORY**

Standalone arithmetic layer on the rewritten Juggler formalization. It
is **not** a Research Engine control-layer experiment and not a claim
that every positive integer reaches 1.

## Problem

Does the position of \(F(x)\) inside its consecutive-square cell carry
a compact arithmetic state that decides whether a persistent residual
landing stays odd-to-odd, beyond residues, defect size, and the
already-known envelope?

## Exact statement

Write \(m=T(x)\) and \(F(x)=x\) or \(x^3\) according to the branch.
The landing cell is the existing inverse-floor interval

\[
T(x)=m\iff m^2\le F(x)<(m+1)^2.
\]

The landing gap is the local remainder \(\rho=F(x)-m^2\), already
known to satisfy \(0\le\rho<2m+1\). The normalized threshold
coordinate is

\[
\theta(x)=\frac{\rho(x)}{2T(x)+1}.
\]

Odd landing is membership of \(F(x)\) in a union of odd-\(m\) cells.
That equivalence is tautological in \(T(x)\). Persistence at an odd
\(y\) is exactly `landingParity y = 1`.

The research claim under test is stronger: \(\theta\) occupies a
proper subinterval on odd-to-odd or PE-continuation states, or a
coarse \(\theta\)-bin predicts the next landing better than a residue
class.

## Current literature

- Inverse-floor cells
  `floorPower_even_eq_iff_sq_interval` /
  `floorPower_odd_eq_iff_cube_interval` —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.Preimages`.
- Remainder window \(\rho<2T+1\) —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.Defect`.
- Residual-state finite quotients need the integer itself —
  **CLOSE** as `RESIDUAL_STATE_NEEDS_X`.
- Residue modulo \(8\) does not decide PE continuation —
  **REFUTED** in the two-block and expanding-grammar dossiers.
- Scale-induced \(\eta=\rho/T^2\to 0\) —
  **EXACT — LEAN VERIFIED**; this does not force \(\theta\to 0\).
- Expanding grammar is persistence —
  **CLOSE** as `EXPANDING_GRAMMAR_IS_PERSISTENCE`.

Project relationship: **extended**.

## Branch budget

```text
Mathematical target     Does θ=ρ/(2T+1), or the square-threshold
                        cell, constrain future landing parity in a
                        way residues and defect size do not?
Novelty hypothesis      Persistent odd-to-odd occupies a proper
                        threshold interval, or a cell coordinate
                        predicts the next landing
Falsifier               θ unrestricted on odd-odd; bins no better
                        than residues; cell iff is T itself
Existing machinery      inverse-floor iff, localDefect, PersistentOddResidual
Maximum Phase-0 scope   Name the cell/gap interface; cheap θ census
                        on odd starts and PE landings; no halt
Promotion criterion     Persistent ⇒ θ∈I for a proper I, or a
                        cell transition that residues miss
Stop criterion          Falsifier A–E; ResidualState replay; halt
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- `landingIndex` / `landingPreimage` / `landingPreimage_iff` —
  **REPARAMETERIZATION** of the inverse-floor one-step preimages
- `landingGap` / `landingGap_bound` / `normalizedLandingGap` —
  **REPARAMETERIZATION** of `localDefect` and \(\rho<2T+1\)
- `landingParity_odd_iff` / `landingParity_even_iff` —
  **EXACT — LEAN VERIFIED** (tautological in \(T\))
- `persistent_landing_constraint` —
  **EXACT — LEAN VERIFIED** (unpacks `PersistentOddResidual`)
- Persistent odd-to-odd forces \(\theta\in I\subsetneq[0,1]\) —
  **REFUTED**
- A \(\theta\)-bin predicts the next landing better than
  \(x\bmod 8\) —
  **REFUTED**
- \(\theta(T(x))\) is a function of \(\theta(x)\) and the branch —
  **REFUTED** on the scanned window
- Infinite PE orbit — not claimed

## Experiments

Cheap threshold census, not a new raw search.

- Odd starts \(n\le 2000\): odd-odd and odd-even \(\theta\) both
  occupy every tenth of \([0,1]\). Odd-odd range is
  \([0,0.997]\). Mean binary entropy of \(T(T(x))\bmod 2\) given a
  \(\theta\)-bin is \(\approx 0.99\), indistinguishable from
  \(x\bmod 8\). The \(\theta\to\theta\) transition on either branch
  fills essentially all bins.
- PE landings \(n\le 2000\): continuation and exit both occupy
  \(\theta\) from \(0\) to \(1\). Continuation is not a proper
  interval.
- The `OOE` chain at \(365\) uses \(\theta\approx 0.32, 0.82,
  0.07, 0.93, 0.46\). No common cell inequality persists.

Tests: `tests/research/juggler_sequence/test_landing_parity.py`.

## Conjectures

None opened in `conjectures/`.

## Counterexamples

- “Odd-to-odd forces \(\theta\) into a proper subinterval.” False:
  odd-odd \(\theta\) reaches \(0\) and \(0.997\) on \(n\le 2000\).
- “PE continuation occupies a restricted \(\theta\) interval.”
  False: continuation at PE landings spans \([0,0.995]\).
- “A \(\theta\)-bin decides the next landing parity.” False:
  every bin produces both parities, entropy \(\approx 1\).
- “Landing cells predict better than residues.” False: \(\theta\)-bin
  entropy matches \(x\bmod 8\).

## Formalization

`formal/Problems/Juggler/LandingParity.lean`, after
`ExpandingGrammar` and before `Cycles`. No `sorry`. No halt theorem.
No discretized threshold automaton.

## Results

- The cell language is the existing inverse-floor theorem.
- \(\theta\) is the position inside a cell already named by
  \(\rho<2T+1\). It stays order-\(1\) while \(\eta=\rho/T^2\)
  decays.
- Persistent odd-to-odd does not restrict \(\theta\).
- \(\theta\) does not predict the next landing and does not
  compose as a branch map.
- Exact landing information that decides \(T(x)\) odd is \(T(x)\)
  itself.

## Open questions

The leftover is still whether an odd-to-odd residual chain can
continue indefinitely. That is not a threshold-coordinate problem.
Sequential near-Mordell composition is not that arithmetic either;
see [juggler_sequential_mordell.md](juggler_sequential_mordell.md).
The 2-adic remainder law is \(y\bmod 8\); see
[juggler_landing_valuation.md](juggler_landing_valuation.md).
Do not reopen residues, slack, or expanding-word grammar.

## Decision

**CLOSE** the landing-threshold attack as
`LANDING_THETA_UNRESTRICTED`. The cell interface is a packaging of
lemmas already in `Cells` and `Defect`. The candidate state
\(\theta\) is unrestricted on odd-to-odd and PE-continuation
states, and it is no more predictive than a residue class. Landing
parity that is not \(T\) itself was not found. Do not claim
termination.

Best next question: is there any arithmetic, other than the integer
\(y\) itself, that decides whether a persistent residual landing
stays odd-to-odd?

## Publication assessment

Status: `EXPLORATORY`. A negative threshold-state result and a thin
cell interface, not a paper candidate and not a Juggler totality
result.

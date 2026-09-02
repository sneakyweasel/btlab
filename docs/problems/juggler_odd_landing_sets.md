# Juggler iterated odd-landing sets

Status: **EXPLORATORY**

Standalone arithmetic layer on the rewritten Juggler formalization. It
is **not** a Research Engine control-layer experiment and not a claim
that every positive integer reaches 1.

## Problem

Do the sets of integers whose next \(r\) Juggler landings all remain
odd develop a recursively exploitable cylinder, residue, or
square-gap structure as \(r\) grows?

## Exact statement

Write \(F(y)=T(y)\). The one-step odd-landing set is

\[
\mathcal P_0=\{y\text{ odd}:F(y)\text{ odd}\}.
\]

Iterate by

\[
\mathcal P_{r+1}=\{y\text{ odd}:F(y)\in\mathcal P_r\}.
\]

Equivalently, \(y\in\mathcal P_r\) if and only if \(F^j(y)\) is odd
for \(0\le j\le r+1\). The Phase-0 question is whether this recursion
is more than repeated evaluation of \(F\): a shrinking family of
intervals, a finite \(2\)-adic automaton, a constrained \(\theta\)
tree, or a new compatibility law among consecutive odd-odd
remainders.

Do not search first for a universal finite bound on odd-run length.
This says nothing about totality.

## Current literature

- Odd floor cells contain at most one integer —
  **EXACT — LEAN VERIFIED** as `odd_preimage_unique`.
- `landingParity_odd_iff` —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.LandingParity`.
- Residual-state finite quotients need the integer itself —
  **CLOSE** as `RESIDUAL_STATE_NEEDS_X`.
- Landing \(\theta\) unrestricted —
  **CLOSE** as `LANDING_THETA_UNRESTRICTED`.
- \(v_2(\rho)\) is \(y\bmod 8\) —
  **CLOSE** as `LANDING_VALUATION_IS_Y_MOD_8`.
- Predecessor cylinders do not constrain \(T(y)\) beyond \(y\) —
  **CLOSE** as `PREIMAGE_CYLINDER_IS_Y`.

Project relationship: **extended**.

## Branch budget

```text
Mathematical target     Do the sets P_r of iterated odd landings
                        have exploitable recursive structure as r
                        grows?
Novelty hypothesis      A cylinder/interval/finite-state recursion
                        P_{r+1}=Φ(P_r) that is not just T
Falsifier               Stay rate 1/2; singleton cells; no modular
                        or θ refinement
Existing machinery      landingParity_odd_iff, odd_preimage_unique,
                        odd-odd census
Maximum Phase-0 scope   Name P_r and the exact recursion; census
                        geometry/modulus/θ; unique-preimage lemma.
                        No halt, no density theorem
Promotion criterion     A nontrivial Φ, or a new chain constraint
                        on long odd runs
Stop criterion          Falsifiers A–E; evaluate-T rewrite
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- `oddLanding` / `oddLanding_iff` / `oddLanding_cell` —
  **REPARAMETERIZATION** of `landingParity`
- `oddRun` / `oddRun_recursive` —
  **EXACT — LEAN VERIFIED**, and a **REPARAMETERIZATION** of
  iterated `T`
- `oddLanding_preimage_unique` —
  **EXACT — LEAN VERIFIED**, wrapping `odd_preimage_unique`
- \(\mathcal P_r\) occupies shrinking arithmetic cylinders —
  **REFUTED**
- Iteration creates a finite \(2\)-adic automaton —
  **REFUTED** on the scanned window
- Long odd runs constrain successive \(\theta\) —
  **REFUTED** on the scanned window
- Finite odd-run bound — not claimed

## Experiments

Dedicated \(\mathcal P_r\) census, not another PE-start scan.

- Among odd \(n\le 8000\), \(|\mathcal P_r|\) tracks
  \(2^{-(r+1)}\) of the odds. The stay fraction
  \(|\mathcal P_{r+1}|/|\mathcal P_r|\) is \(0.49\)–\(0.53\) through
  \(r=7\). The same ratios hold at \(n\le 40000\).
- Interval geometry is isolated odds: \(\mathcal P_0\) is already
  half singletons; \(\mathcal P_4\) is \(130/134\) singletons. There
  is no stable positive-length cylinder.
- Every observed odd image has exactly one odd preimage in the
  window, matching `odd_preimage_unique`.
- All odd classes modulo \(8,16,32\) remain occupied through
  \(\mathcal P_4\). Every residue modulo \(64\) both stays and
  exits at each of the first four levels.
- \(\theta\) on \(\mathcal P_r\) and on the exit from
  \(\mathcal P_{r-1}\) both occupy \([0,1]\). Successive
  \(\theta\)-pairs on \(\mathcal P_3\) fill all four quadrants.

Tests: `tests/research/juggler_sequence/test_odd_landing_sets.py`.

## Conjectures

None opened in `conjectures/`.

## Counterexamples

- “\(\mathcal P_{r+1}\) occupies a proper subcylinder of
  \(\mathcal P_r\).” False: stay is one half, and \(\theta\) and
  every odd residue class survive.
- “Iteration is recognized modulo \(2^m\).” False: modulo \(64\),
  every odd class both continues and exits.
- “An odd landing \(m\) has a metric interval of odd preimages.”
  False: `odd_preimage_unique` and the census both give \(0\) or \(1\)
  preimage.
- “Successive square-gap coordinates on a long odd run are
  constrained.” False: \(\theta_i,\theta_{i+1}\) occupy all
  quadrants of \([0,1)^2\).

## Formalization

`formal/Problems/Juggler/OddLandingSets.lean`, after
`PreimageCylinders`. No `sorry`. No halt theorem. No density
theorem. No odd-run automaton.

## Results

- The exact recursion is \(y\in\mathcal P_{r+1}\) if and only if
  \(y\) is odd and \(T(y)\in\mathcal P_r\).
- The backward cylinder of an odd landing is empty or a singleton.
- Computationally, iterated membership behaves as independent
  parity samples. No interval, modular, or \(\theta\) refinement
  appears.

## Open questions

The leftover is still whether an odd-to-odd residual chain can
continue indefinitely. The set \(\mathcal P_r\) is the forward
orbit of \(T\) under an odd constraint, not a new arithmetic
state. Do not reopen residues, \(\theta\), valuation, or
predecessor cylinders.

## Decision

**CLOSE** the iterated-landing-set attack as
`ODD_LANDING_SETS_ARE_FORWARD_ORBITS`. The recursion is exact and
is repeated evaluation of \(T\). Odd cells are singletons, stay
is one half, and neither modulus nor \(\theta\) refines. Do not
claim a finite odd-run bound or termination.

Best next question: is there any arithmetic, other than the integer
\(y\) itself, that decides whether a persistent residual landing
stays odd-to-odd?

## Publication assessment

Status: `EXPLORATORY`. An exact recursion packaging and a negative
set-structure result, not a paper candidate and not a Juggler
totality result.

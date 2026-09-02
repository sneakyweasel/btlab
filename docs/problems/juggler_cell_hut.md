# Juggler cell-hut quotient

Status: **EXPLORATORY**

Standalone Phase-0 test of whether Juggler's wide-even / singleton-odd
predecessor cells define a natural local class whose forward transitions
are simpler than the exact integer map. It is **not** a Research Engine
control-layer experiment, not a Collatz hut, not an automaton, not a
scalar-invariant search, and not a claim that every positive integer
reaches 1.

Closed PE-factor, Word Atlas factor, realization-set geometry,
landing-image, residual-future quotient, arithmetic projections of
\(y\), summed-rho, finite-itinerary NC-boundary, first-return, adversarial
parity-path, information-complexity, ordinary backward predecessor
geometry, accelerated odd-to-odd, and 2-adic bridge branches are not
reopened. Word Atlas and landing-image are **PARK** in their dossiers
and remain fixtures-only.

## Problem

Does the intrinsic asymmetry of Juggler's predecessor cells define a
natural local equivalence class whose transition dynamics are simpler
than the exact integer dynamics?

## Exact statement

Write \(T\) for the unaccelerated floor-power map. For \(m\ge 1\),

\[
\operatorname{Pred}_E(m)=\{n\text{ even}:m^2\le n<(m+1)^2\},
\quad
\operatorname{Pred}_O(m)=\{n\text{ odd}:m^2\le n^3<(m+1)^2\},
\]

with \(\lvert\operatorname{Pred}_O(m)\rvert\le 1\). The raw hut
\(H(m)=(\operatorname{Pred}_E(m),\operatorname{Pred}_O(m))\) is the
exact local neighborhood. It determines \(m\) and is therefore **not**
the class. A compact signature \(\operatorname{hut\_signature}(m)\)
forgets identifying coordinates. Phase 0 asks whether

\[
\operatorname{sig}(x)=\operatorname{sig}(y)
\implies
\operatorname{sig}(T(x))\text{ and }\operatorname{sig}(T(y))
\text{ lie in one small structured family.}
\]

The Collatz predecessor \(n=(2^k m-1)/3\) is a different map and is
not used. This says nothing about totality. Hut descent is not a
termination theorem.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Inverse-floor cells `even_preimage_iff` / `odd_preimage_iff` /
  `odd_preimage_unique` — **EXACT — LEAN VERIFIED** in
  `Problems.Juggler.Preimages`.
- \(\lvert\operatorname{Pred}_E(m)\rvert=m\) or \(m+1\) — **KNOWN**
  from the cell; recorded in the closed backward-geometry census.
- Backward predecessor geometry —
  **CLOSE** as `BACKWARD_COMPLEX`. Repeated inversion is nested cells.
  Reused as the cell API only.
- Residual future-quotient / arithmetic projections of \(y\) —
  **CLOSE** as `FUTURE_QUOTIENT_REPACK`.
- 2-adic / BT bridge — **CLOSE** as `BRIDGE_COMPLEX`.
- PE-factor, realization geometry, landing-image, sum-rho, NC-boundary,
  first-return, adversarial paths, information-complexity, accelerated
  odd-to-odd — **CLOSE** or **PARK**. Fixtures only.

Project relationship: **extended**. The leftover after those decisions
is whether a *forward* quotient of *cell neighborhoods* simplifies
\(T\), rather than renaming it.

## Branch budget

```text
Mathematical target     Does a compact signature of Pred_E(m) / Pred_O(m)
                        send equivalent neighborhoods to a small family
                        of successor neighborhoods, or does it only rename J?
Novelty hypothesis      the wide-even / singleton-odd asymmetry is a
                        natural local class with a simpler transition algebra
Falsifier               every candidate signature is bijective with m,
                        has unbounded out-degree, or same-class states
                        have incompatible successor families
Existing machinery      even_preimage, odd_preimage_integers, pred_even / pred_odd,
                        floor_power, even_preimage_iff / odd_preimage_unique,
                        hard/PE fixtures; no hut module exists
Maximum Phase-0 scope   exact geometry + frozen signature ladder on
                        m<=4000; one-step H -> H(J); odd-spine;
                        even-fan on that window; selected extension
                        to 10^5; Border-Hut then valuation comparison;
                        no GPU; no full trajectory census; no Lean
                        unless a nontrivial rule appears
Promotion criterion     a proper quotient (many states per class) with
                        uniformly bounded / parameterized successor
                        families, not a table of renamed J-edges
Stop criterion          HUT_COMPLEX, or every survivor is a cell corollary,
                        a modulus, or a 2-adic reparameterization
```

## Balanced-ternary formulation

States are ordinary positive integers. Balanced-ternary metadata
(`lsd`, length-4 integer jet) are recorded as a diagnostic reference
on each hut geometry. A fixed suffix determining the hut would reopen
the rejected finite-information projection and is treated as a
falsifier, not a candidate invariant.

## Why BT may be relevant

The laboratory's canonical representation might describe cell
endpoints or the unique odd predecessor more simply than the integer
interval. That is a question, not a claim. \(D\) / \(I_a\) are
compared only if the data support a hut transformation.

## Candidate operations / invariants

- Raw \(H(m)=(\operatorname{Pred}_E,\operatorname{Pred}_O)\) as a class —
  **rejected a priori**; the even cell determines \(m\)
- \(\lvert E(m)\rvert\) or width \(2m+1\) as a class feature —
  **rejected a priori**; both recover \(m\)
- Frozen Cell-Hut signatures `v1_occupancy` … `v4_mod3` —
  **OBSERVATION** to be decided by out-degree and merge pairs
- Border-Hut neighbor-image type —
  **OBSERVATION**; secondary view
- Valuation border \(v_2(m-1),v_2(m+1)\) —
  comparison only; **REPARAMETERIZATION** unless new structure appears
- Odd-spine iteration —
  already the unique descending odd cell; a new law is required
- Even-fan class collapse —
  **OBSERVATION**; growth like \(\lvert E(m)\rvert\) is negative
- Well-founded hut rank —
  searched only after a structured transition rule

## Experiments

- Probe: `research.juggler_sequence.cell_hut`
- Records: [juggler_cell_hut.md](../research/juggler_cell_hut.md)
- Dataset: `data/research/juggler/cell_hut/`
- Tests: `tests/research/juggler_sequence/test_cell_hut.py`

No GPU. No CLI. No Streamlit. No Lean unless a one-line rule survives.

## Conjectures

None opened.

## Counterexamples

- Raw \(H(m)\) as a class: even-cell endpoints recover \(m\).
- Same class, different successor: \(2\) and \(4\) on `v1`–`v3` and
  `vC`; \(2\) and \(8\) on `v4_mod3`; \(4\) and \(10\) on Border-Hut.
  Versions were not retuned.
- Strict hut rank: every frozen version has a class self-loop
  (the fixed point \(1\), and other self-returns).
- Even-fan collapse: members of \(E(m)\) are even, so the fan only
  sees the even slice of a finite label set. For the valuation
  signature, neighbors of even \(n\) are odd, hence \(v_2=0\).
- Length-4 BT jet \((1,0,0,0)\) at \(1\) versus \(82\) splits
  `v3_oddpos`.
- Out-degree growth on \(m\le 10^5\): `v3` \(6\to 8\), Border-Hut
  \(6\to 7\), valuation \(15\to 28\).

## Formalization

None added. Existing `Preimages.lean` lemmas are reused. No `sorry`.

## Results

Phase 0 is recorded in
[juggler_cell_hut.md](../research/juggler_cell_hut.md).
Classification **HUT_COMPLEX**.

On \(1\le m\le 4000\), \(126\) odd cells are occupied. For every
\(m>1\) with an odd predecessor the order is \(o(m)<m<E(m)\). Every
frozen signature is a finite label set: occupancy, type, tertile,
mod \(3\), neighbor-image type, or a bounded \(v_2\) pair. Same-class
states take incompatible successors. Class graphs are dense or cyclic.
Even fans occupy only the even slice of those labels. Odd spines
stop at an empty odd cell or at the fixed point \(1\). Length-4 BT
jets all split, and \(D\) / \(I_a\) do not supply a hut calculus.
Selected extension to \(10^5\) grows several out-degrees. No
well-founded rank was invented.

## Open questions

None from this branch. Do not invent a second hut. Do not infer
totality from a class graph.

## Decision

**CLOSE**. The wide-even / singleton-odd asymmetry is real and already
certified, but it does not define a local quotient whose forward
transitions are simpler than \(T\). Finite signatures coarsen the
state without constraining the successor. Do not add arbitrary
features. Do not claim termination.

Best next question: none from this branch.

## Publication assessment

Status: `EXPLORATORY`. Not a paper candidate and not a Juggler
totality result.

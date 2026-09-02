# Juggler pointwise image-parity discrepancy

Status: **EXPLORATORY**

Standalone Archimedean counting layer on the exact Juggler floor-power
map. It is **not** a Research Engine control-layer experiment, not a
parity-frequency theorem, and not a claim that every positive integer
reaches 1.

## Problem

Does the one-step image-parity count

\[
O(N)=\#\{n\le N:J(n)\ \mathrm{odd}\}
\]

admit an explicit discrepancy bound \(|O(N)-N/2|\le E(N)\), and which
floor-cell family produces it?

## Exact statement

Write \(J(n)=\lfloor\sqrt n\rfloor\) for even \(n\) and
\(J(n)=\lfloor n^{3/2}\rfloor\) for odd \(n\). Split
\(D(N)=O(N)-N/2\) into even-start and odd-start pieces \(D_E\) and
\(D_O\). Phase 0 asks for an explicit majorant of \(D_E\) from the
square cells, and whether \(D_O\) — occupancy of odd-\(m\)
singletons of \(n^{3/2}\) — has an explicit \(o(N)\) envelope.
This is interval counting, not a residue-class statement, and it says
nothing about totality.

## Current literature

- `even_preimage_iff` / `odd_preimage_iff` / `odd_preimage_unique` —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.Preimages`.
- `landingParity = J(n)\bmod 2` —
  **EXACT — LEAN VERIFIED** and tautological in \(T\); landing-θ
  **CLOSE** as `LANDING_THETA_UNRESTRICTED`.
- `floorPower_odd_macro_direction` —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.Dynamics`.
- Same residue, both next parities —
  **EXACT — LEAN VERIFIED** in `PreimageCylinders`; 2-adic bridge
  **CLOSE** as `BRIDGE_COMPLEX`.
- Uniform one-step start-parity \(P(O)=1/2\) —
  **KNOWN** counting, recorded in the probabilistic census
  (`STATISTICAL_ONLY` / **PARK**). Orbit \(P(O)=1/2\) as a
  dynamical law is **REFUTED**. Large-deviation comparison **CLOSE**
  as `MODEL_ONLY`.
- Prasad–Prasad 2025 (`prasad-prasad-2025-juggler-like`) —
  literature context only; M0 assumes iid fair parity.
- OEIS A007320 (`oeis-A007320`) — step counts. **known**.

Project relationship: **independent** interval-counting question.
Totality remains unclaimed.

## Branch budget

```text
Mathematical target     Is there an explicit E(N) such that
                        |#{n≤N: J(n) odd} − N/2| ≤ E(N), and which
                        of the two floor-cell families produces it?
Novelty hypothesis      A deterministic Archimedean discrepancy law
                        for floor(n^{3/2}) on odd n, not a residue
                        class and not a statistical frequency.
Falsifier               Total discrepancy is only the even-cell
                        O(√N) rewrite; odd-start error is Ω(N^{1−ε})
                        or a linear bias; or the count is T itself.
Existing machinery      floor_power; even_preimage_iff / odd_preimage_iff /
                        odd_preimage_unique; landingParity = T mod 2
                        (tautological); 2-adic bridge CLOSE; θ-landing
                        CLOSE; probabilistic P(O) PARK/CLOSE.
Maximum Phase-0 scope   Exact even/odd split; human even-cell bound;
                        one-pass census N≤10^6 (spot 10^7); candidate
                        E_odd(N); no k-step iteration; no CLI; no Lean
                        unless an odd-start inequality is proved.
Promotion criterion     An explicit E_odd(N)=o(N) with a proof, or a
                        total E(N) that is not just even_preimage_iff.
Stop criterion          All KNOWN/REPARAMETERIZATION; machinery
                        gravity (plots, word iteration, Weyl engine);
                        halt claim; flipping parity_frequency_theorem
                        on a census.
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required. The 2-adic / BT bridge is closed.

## Candidate operations / invariants

- Start-parity count on \([1,N]\) —
  **KNOWN**
- `landingParity` as a predictive state —
  **REPARAMETERIZATION** of \(T\)
- Even-cell closed form for \(O_E(N)\) —
  **EXACT — HUMAN PROOF**
- \(|D_E(N)|\le\lfloor\sqrt N\rfloor+1\) —
  **EXACT — HUMAN PROOF**
- Odd-start \(N^{1/3}\) envelope —
  **OBSERVATION**
- Linear odd-start bias —
  **REFUTED** on the Phase-0 window
- Total discrepancy as a new \(n^{3/2}\) law —
  **REFUTED**; \(D_E\) dominates
- `parity_frequency_theorem` —
  not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.parity_discrepancy`
- Records: [juggler_parity_discrepancy.md](../research/juggler_parity_discrepancy.md),
  [juggler_parity_discrepancy.json](../research/juggler_parity_discrepancy.json)
- Dataset: `data/research/juggler/parity_discrepancy/`
- Tests: `tests/research/juggler_sequence/test_parity_discrepancy.py`

No GPU. No atlas recensus. No new Lean file. The Research Engine
control layer is not modified.

## Conjectures

None opened. A named \(N^{1/3}\) envelope is an observation, not a
conjecture file.

## Counterexamples

- “\(P(O)=1/2\) as a trajectory law”: already false on hard / record
  orbits; this branch does not revive it.
- “Total \(|O(N)-N/2|\) is a new cube-cell law”: false; \(D_E\)
  dominates (`max|D_E|=499.0` vs
  `max|D_O|=128.0` on `n<=1000000`).
- “Odd-start image parity has a linear bias”: false on the window;
  `|D_O(1000000)|=73.0`.
- “A residue class determines the second letter”: already false
  (`ooe_cylinder_both_next_parities`).

## Formalization

None added. Existing Cells / Dynamics / LandingParity /
PreimageCylinders lemmas stay as they are. No `sorry`.

## Results

Classification **IMAGE_PARITY_CENSUS**.

The even-cell discrepancy is an explicit O(sqrt(N)) identity. The odd-start n^{3/2} count has no linear bias and tracks a named N^{1/3} envelope (max|D_O|/N^{1/3} ≈ 1.06524464 on the window), but that envelope is only a census.

On `n<=1000000`: `O=499927`, `D=-73.0`,
`D_E=0.0`, `D_O=-73.0`,
`max|D|=613.0`, `max|D_E|=499.0`,
`max|D_O|=128.0`. Closed even-cell formula matches
the census: `True`. Even bound holds:
`True`. Odd-start spot `n<=10000000` has `max|D_O|=229.5` and `max|D_O|/N^{1/3}=1.06524464`.

## Open questions

Prove an explicit \(E_O(N)=o(N)\) for the odd-start \(n^{3/2}\)
count. Do not iterate counting estimates until that bound exists. Do
not reopen residues, θ, or the random-walk model.

## Decision

**PARK**. The even-cell discrepancy is an explicit O(sqrt(N)) identity. The odd-start n^{3/2} count has no linear bias and tracks a named N^{1/3} envelope (max|D_O|/N^{1/3} ≈ 1.06524464 on the window), but that envelope is only a census. Do not claim
termination. Do not flip `parity_frequency_theorem`.

Best next question: prove \(E_O(N)\ll N^{1/3}(\log N)^c\) (or
the named census class) by an Archimedean exponential-sum argument,
then ask whether that bound iterates.

## Publication assessment

Status: `EXPLORATORY`. An elementary even-cell counting identity plus
an odd-start discrepancy census, not a paper candidate and not a
Juggler totality result.

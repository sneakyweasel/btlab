# Juggler parity discrepancy transfer

Status: **EXPLORATORY**

Follow-up of the parked odd-image discrepancy theorem. It is **not**
a Research Engine experiment, not a frequency theorem, and not a
claim that every positive integer reaches 1.

## Problem

Can the exact expanding-branch parity discrepancy of an integer
interval be transferred through one Juggler image?

## Exact statement

For `I=[A,B] ∩ Z` write `D(I)=sum_{n odd in I} (-1)^{floor(n^{3/2})}`
and `Y=J_O(O(I))`. Phase 0 asks for an interval-uniform form of
`D(I)` and for a nontrivial bound on the same sign sum evaluated on
`Y` (or a simple deterministic weighting). Iterated transfer, a
Weyl engine, and totality are out of scope.

## Current literature

- Parent [juggler_odd_image_discrepancy.md](juggler_odd_image_discrepancy.md)
  **PARK** / `ODD_IMAGE_DISCREPANCY_GREEN`. `|S_O(N)| << N^{5/6}`.
- Image-parity census [juggler_parity_discrepancy.md](juggler_parity_discrepancy.md)
  **PARK**.
- `odd_preimage_unique` / `odd_preimage_iff` —
  **EXACT — LEAN VERIFIED**.
- 2-adic bridge, landing-θ, PE / residual / LD / local floor-boundary —
  **CLOSE**. Do not reopen.
- Prasad–Prasad 2025 (`prasad-prasad-2025-juggler-like`) —
  motivation only.

Project relationship: **extended** from the parked interval theorem.
Totality remains unclaimed.

## Branch budget

```text
Mathematical target     Can D([A,B]) be given a useful interval-uniform
                        form, and does the same image-parity sum
                        transfer to Y = J_O(O(I))?
Novelty hypothesis      A translation-uniform |I|^alpha bound, or a
                        one-step bound for D(Y) that is not prefix
                        differencing of S_O(N)
Falsifier               Monochromatic runs kill |I|-uniform laws;
                        Y is too fragmented for the interval theorem;
                        some J-generated sets concentrate; only
                        B^{5/6} differencing remains
Existing machinery      S_O, odd_image_sign, odd_preimage_unique,
                        |S_O(N)| << N^{5/6}, floor_power
Maximum Phase-0 scope   Exact CPU, N<=1e6, L<=1e5 records, gaps,
                        location grid, one-step Y, simple weights,
                        J^2 diagnostic only; no Weyl engine, no
                        CUDA, no Lean ANT, no iterated theorem
Promotion criterion     A proved |I|-uniform law, or a proved
                        one-step image-transfer inequality
Stop criterion          Only differencing; |I|-uniform false;
                        no useful transfer; weight fishing
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required. The 2-adic / BT bridge is closed.

## Candidate operations / invariants

- `D([A,B])=S_O(B)-S_O(A-1)` —
  **EXACT — HUMAN PROOF**
- `c_I(m) in {0,1}` —
  **EXACT — LEAN VERIFIED**
- `|D([A,B])| << B^{5/6}` —
  **EXACT — HUMAN PROOF**, not transfer
- `|D| <= C |I|^alpha` uniformly in `A` —
  **REFUTED**
- `D(Y)` transfer —
  **REFUTED** as a uniform law; census elsewhere
- `parity_frequency_theorem` —
  stays false
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.parity_discrepancy_transfer`
- Records: [juggler_parity_discrepancy_transfer.md](../research/juggler_parity_discrepancy_transfer.md),
  [juggler_parity_discrepancy_transfer.json](../research/juggler_parity_discrepancy_transfer.json)
- Dataset: `data/research/juggler/parity_transfer/`
- Tests: `tests/research/juggler_sequence/test_parity_discrepancy_transfer.py`

No GPU. No new Lean file.

## Conjectures

None opened.

## Counterexamples

- `|I|`-uniform sublinear bound: monochromatic run
  `[952525,952627]` of length
  `52`.
- “`Y` is an interval to which `N^{5/6}` applies.” Fragmented
  expanding images.
- Uniform unweighted transfer to every generated set: concentrated
  `Y` / `J^2` samples in the dataset.

## Formalization

None added. The cell uniqueness and odd-image monotonicity lemmas
already exist. Differencing is an elementary prefix identity and
is not a transfer theorem. Analytic number theory is not
Lean-packaged. No `sorry`.

## Results

Classification **TRANSFER_COMPLEX**.

D([A,B]) equals the prefix difference S_O(B)-S_O(A-1), so the classical |S_O(N)| << N^{5/6} bound yields only a location-dependent majorant << B^{5/6}. That is not a transfer theorem and is not |I|-uniform: a monochromatic run of length 52 on [952525,952627] has |D|=#odds. The expanding image Y=J_O(O(I)) is strictly increasing and highly fragmented, so the interval theorem does not apply to Y. Witness: Y of [1000,1099] has 25 odd points and |D(Y)|/#odd(Y)=0.36. 19 odd-images with at least 20 odd points concentrate at level 0.25; 12 diagnostic J^2 samples do as well. Interval cancellation does not survive Juggler-generated sets in a useful uniform form.

On `n<=1000000`: prefix `max|S_O|=256`,
max run `52`, concentrated generated sets
`19`.

## Open questions

None from this branch. A sparse-sequence discrepancy law for
`Y=J_O(O(I))` would be a different, Weyl-type project and is not
opened here.

## Decision

**CLOSE**. D([A,B]) equals the prefix difference S_O(B)-S_O(A-1), so the classical |S_O(N)| << N^{5/6} bound yields only a location-dependent majorant << B^{5/6}. That is not a transfer theorem and is not |I|-uniform: a monochromatic run of length 52 on [952525,952627] has |D|=#odds. The expanding image Y=J_O(O(I)) is strictly increasing and highly fragmented, so the interval theorem does not apply to Y. Witness: Y of [1000,1099] has 25 odd points and |D(Y)|/#odd(Y)=0.36. 19 odd-images with at least 20 odd points concentrate at level 0.25; 12 diagnostic J^2 samples do as well. Interval cancellation does not survive Juggler-generated sets in a useful uniform form. Do not claim
termination. Do not flip `parity_frequency_theorem`. Do not add
further weights.

Best next question: none from this branch.

## Publication assessment

Status: `EXPLORATORY`. A negative transfer test sitting on a
classical interval bound, not a paper candidate and not a Juggler
totality result.

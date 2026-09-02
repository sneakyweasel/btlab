# Juggler extremal control and realizability gap

Status: **EXPLORATORY**

Standalone deterministic-control layer on the exact Juggler
floor-power map. It is **not** a Research Engine control-layer
experiment, not a reopen of any closed symbolic-compression branch,
not a new statistical census, and not a claim that every positive
integer reaches 1.

## Problem

How close can an exact Juggler trajectory come to the most dangerous
ideal O/E control path allowed by the macroscopic growth laws
`δ(O)=log(3/2)`, `δ(E)=log(1/2)`?

## Exact statement

Write `S_j = o_j log 3 − j log 2`. Equivalently
`S_j ≥ 0 ⇔ 3^{o_j} ≥ 2^j` and `S_k < 0 ⇔ 3^o < 2^k`.
An ideal first-return control of length `k` satisfies
`S_j ≥ 0` for `j < k` and `S_k < 0`. Phase 0 asks:

1. which binary word maximises `H(w) = max_j S_j` under that
   constraint;
2. whether that optimiser coincides with the 2025 large-deviation
   ascent (`p^*=3/4`);
3. whether exact first-return trajectories of `J` realize that
   itinerary, and what the same-horizon peak gap is on `n ≤ 4000` and
   selected hard `n ≤ 10^5`.

A finite gap is not a bound on `τ_<`. This is not a termination
theorem.

## Current literature

- OEIS A007320 (`oeis-A007320`) — computational step counts.
  **known**. Totality is not claimed.
- Prasad–Prasad 2025 juggler-like random-walk preprint
  (`prasad-prasad-2025-juggler-like`) — literature context only.
  The reconstructed optimiser `p^*=3/4` is a **MODEL PREDICTION**,
  not a theorem on exact `J`.
- `power_bound_contracts`, `floorPower_odd_ge` —
  **EXACT — LEAN VERIFIED**. The landing corridor
  `2^{k-1} ≤ 3^o < 2^k` lives in the same exponent comparison
  and is **not** promoted as a new envelope lemma.
- Parked statistical phase — **STATISTICAL_ONLY**. Used here only
  as an extremal-target list. Not reopened as a fitting exercise.
- PE / residual-future / residual projections / summed-rho /
  realization-set / landing-image / finite-itinerary `N_w` / first-return
  structural laws / generic adversarial paths / information-complexity /
  backward cells / acceleration / floor-boundary / 2-adic bridge —
  **CLOSE**. Do not reopen.

Project relationship: **independent** control reading of exact `J`.
Totality remains unclaimed.

## Branch budget

```text
Mathematical target     How close can exact Juggler trajectories
                        come to the most dangerous ideal first-return
                        O/E control?
Novelty hypothesis      A deterministic realizability gap between
                        unconstrained bang-bang control and exact J
Falsifier               Juggler realizes the bang-bang word at every
                        tested admissible k, or the control problem
                        is only 3^o vs 2^k rewritten
Existing machinery      floor_power, _walk_returns, envelope
                        3^o vs 2^k, parked statistical hard list,
                        Word Atlas PE a_k table
Maximum Phase-0 scope   ideal k<=50 exact combinatorics; exact
                        comparison n<=4000; selected hard n<=1e5;
                        Atlas reused, no new census; no CUDA
Promotion criterion     A sorry-free realizability theorem or a
                        uniform all-horizon gap
Stop criterion          CONTROL_REPACKAGING / CONTROL_COMPLEX /
                        CONTROL_STATE_DEPENDENT / CONTROL_MODEL_MISMATCH;
                        closed-branch reopen; halt claim; new scalar
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required. The 2-adic / BT bridge is closed.

## Candidate operations / invariants

- All-O maximises raw endpoint growth —
  known; **not promoted**
- `S_k = o log 3 − k log 2` —
  known exponent surplus; **not promoted**
- Unique first-return optimiser `O^{o_k^*} E^{k-o_k^*}` with
  `2^{k-1} ≤ 3^o < 2^k` —
  **EXACT — HUMAN PROOF** (ideal control layer only)
- That optimiser equals the LD ascent `p^*=3/4` —
  **REFUTED**
- Exact `J` never realizes a bang-bang first-return word —
  **REFUTED** at `n=3` (`OOOEE`)
- Known hard records lie on the control boundary —
  **REFUTED**
- Floor error is the source of the long-record gap —
  **REFUTED** at bit length `≥ 64`
- Uniform realizability gap / `F(k)` lower bound —
  **not proved**
- `∑ ε_i` as a new invariant — not used
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.extremal_control`
- Records: [juggler_extremal_control.md](../research/juggler_extremal_control.md),
  [juggler_extremal_control.json](../research/juggler_extremal_control.json)
- Dataset: `data/research/juggler/extremal_control/`
- Tests: `tests/research/juggler_sequence/test_extremal_control.py`

No GPU. No new Lean file. No automaton. No new Atlas census.

## Conjectures

None opened. The candidate “every admissible bang-bang word is
realized by some `n`” is recorded on the research page and is
**not** entered in `conjectures/`.

## Counterexamples

- LD optimiser = control optimiser: `p^*=3/4` is not a first-return
  word; deterministic frequency tends to `log 2 / log 3`.
- No exact realizer of the frontier: `n=3` realizes `OOOEE`.
- Every length-`k` first-return is bang-bang: `n=9` is `OOEOE`.
- Hard records sit on the control boundary: `193`, `425`, `2183`,
  `3889` have Hamming distance `14`–`30` to same-horizon bang-bang.
- Floor arithmetic keeps those records off the frontier: large-bit
  `|ε|` is at float noise.

## Formalization

None added. The ideal corridor is integer and is a later Lean
target (`ideal_first_return_frontier`) only if a realizability
statement is promoted. Existing Envelope / Dynamics lemmas stay
as they are. No `sorry`.

## Results

Classification **CONTROL_FRONTIER_GREEN** as a computational
label: the ideal first-return frontier is characterised exactly,
and actual long first-return records sit a definite same-horizon
peak gap below it.

That is **not** `CONTROL_REALIZABILITY_GREEN` or
`CONTROL_GAP_GREEN`. Admissible `k ≤ 13` are realized as bang-bang
words in `n ≤ 4000`, and the `A`-peak gap there is floor error.
Admissible `k ∈ {15,16,18,20}` have no bang-bang realizer in the
window. No `F(k)` theorem. No CUDA Phase 2.

## Open questions

Whether every admissible bang-bang word is realized by some
positive integer, and whether the missing `k=15,16,18,20`
realizers in `n ≤ 4000` are a scale effect or a genuine
obstruction.

## Decision

**PARK**. The ideal control problem is solved: the unique
first-return peak maximiser is bang-bang and is not the
large-deviation ascent. Exact Juggler realizes that optimiser at
small admissible horizons and misses it at longer tested
horizons and on the known hard records. No uniform realizability
theorem and no all-horizon gap were obtained. Do not claim
termination. Do not launch Phase 2.

Best next question: is there an admissible `k` whose bang-bang
word `O^{o_k^*} E^{k-o_k^*}` has no positive-integer realizer?

## Publication assessment

Status: `EXPLORATORY`. An exact combinatorial control lemma plus
a finite-window realizability measurement, not a paper candidate
and not a Juggler totality result.

# Juggler survivor rounding-phase distribution

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a reopen of
excursion transfer, word density, prefix cylinders, episode
automata, cumulative floor loss, mixed-OE defect cuts, \(Z_5\),
length-11, or p-adic systems, not a new atlas language tag, not
Paper A, and not a claim that every positive integer reaches 1.

Those branches already closed words, envelopes, local defects as
identities, and episode transfer. This phase measures a different
object: whether long `AboveAnchor` survivors occupy a
scale-matched exceptional region of the exact square/cube
rounding interval.

## Problem

Are long-surviving Juggler trajectories distributed through the
square/cube rounding landscape like generic states of the same
scale, or do they increasingly require exceptional near-power
alignments or avoidances?

## Exact statement

For odd \(x\) write \(y=\lfloor x^{3/2}\rfloor\),
\(d_O=x^3-y^2\), \(u_O=d_O/(2y+1)\). For even \(x\) write
\(y=\lfloor\sqrt{x}\rfloor\), \(d_E=x-y^2\),
\(u_E=d_E/(2y+1)\). Both \(u\) lie in \([0,1)\).

Phase 0 streams these coordinates on `AboveAnchor` prefixes,
bins starts by survival depth \(S(n)\), and compares the
one-step and lag-1 histograms of long survivors to (i)
ordinary short survivors and (ii) scale-and-parity-matched
generic integers. Hold-out is by starting \(n\).

A histogram gap is not a theorem. Absence under a bound is
`NOT OBSERVED WITHIN SEARCH BOUND`. This is not a halt
theorem.

## Current literature

- \(0\le d<2y+1\) —
  **EXACT — LEAN VERIFIED** (`localDefectOdd_lt_succ`,
  `localDefectEven`)
- Normalized defect on a cube-band fills \([0,1)\) —
  **REFUTED** as a cut (`J-mixed-oe-defect-gap`)
- Cumulative floor-loss budget —
  **CLOSE** as `CUMULATIVE_FLOOR_LOSS_CLOSED`
- Sum-rho aggregation —
  **CLOSE** / **REFUTED**
- Excursion transfer —
  **CLOSE** as `EXCURSION_TRANSFER_CLOSED`
- Nested start-set occupancy —
  **CLOSE** as `ANCHOR_CYLINDER_CLOSED`
- Formal versus AAn itinerary gap —
  **CLOSE** as `FORMAL_REALIZED_GAP_CLOSED`
- Cube cell without a square cell — a **separate** leftover
- Every start reaches 1 — not claimed

Project relationship: **extended**. The designated
state-distribution diagnostic after those closes.

## Branch budget

```text
Mathematical target     Do long-AA states have a scale-matched
                        u_O / u_E / lag-1 law that differs
                        stably from generic integers, beyond
                        the known [0, 2y+1) window?
Novelty hypothesis      Long survival requires exceptional
                        near-power alignment or avoidance.
Falsifier               Hard and generic histograms agree
                        after scale+parity matching; lag-1
                        matches ordinary survivors; small-d
                        rates match; hold-out/scale kill any
                        apparent bias; already localDefect.
Existing machinery      floor_power; localDefectOdd/Even;
                        mixed_oe theta; HARD_LABS;
                        J-mixed-oe-defect-gap
Maximum Phase-0 scope   Stream u-histograms and lag-1; S(n)
                        bins vs scale-matched controls;
                        edge occupancy; small-d excess;
                        hold-out by n; lab traces. No Lean,
                        no FloorPhase, no p-value theorem.
Promotion criterion     Scale+hold-out stable concentration
                        or avoidance with an exact interval.
Stop criterion          Generic; window artefact; already
                        Lean defect; only record laboratories.
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- \(u_O,u_E\in[0,1)\) —
  **REPARAMETERIZATION** of `localDefect*`
- Long versus ordinary / generic histograms —
  **COMPUTATIONALLY VERIFIED** as a bounded observation:
  \(D\le 0.009\) after scale matching
- Lag-1 dependence unique to long survivors —
  **REFUTED** at the Phase-0 window (both indep-\(D=0.0002\))
- Small-\(d_O\) excess among hard states —
  **REFUTED** as a hard-state law (long rate below the
  generic control)
- Edge avoidance of \([0,\varepsilon)\cup(1-\varepsilon,1)\) —
  **REFUTED** (edge rates \(\approx 0.10=2\varepsilon\))
- Global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.survivor_phase`
- Records: [juggler_survivor_phase.md](../research/juggler_survivor_phase.md),
  [juggler_survivor_phase.json](../research/juggler_survivor_phase.json)
- Dataset: `data/research/juggler/survivor_phase/`
- Tests: `tests/research/juggler_sequence/test_survivor_phase.py`

Science window: odd \(n\le 2\cdot 10^7\) plus laboratories
\(37,69,89,365,501,1517,6187,329,33391\). Hold-out split
\(10^7\). Tests use \(n\le 400\). No CLI. No Lean.

## Conjectures

None opened.

## Counterexamples

- “Long survivors concentrate in a narrow \(u\)-interval.”
  False: long-vs-control CDF gap \(D_{\mathrm{odd}}=0.009\),
  long-vs-ordinary \(D_{\mathrm{odd}}=0.006\).
- “Long survivors avoid \(u\in[0,0.05)\cup[0.95,1)\).”
  False: edge rates \(0.101\) / \(0.102\) / \(0.102\) for
  long / ordinary / generic.
- “Long survival requires unusually small \(d_O\).”
  False: the long small-\(d\) rate \(1.5\cdot 10^{-4}\) is
  below the generic control \(1.1\cdot 10^{-3}\). Labs
  \(37\) and \(501\) do hit an odd square (\(d_O=0\)); that
  is the known `localDefectOdd_eq_zero_iff`, not a hard
  family.
- “Successive floor positions of long survivors are more
  dependent than ordinary survivors.” False: lag-1
  independence gap is \(0.0002\) for both.
- “The unit interval is unoccupied on long paths.” False:
  long odd histograms occupy the bins; \(1517\) and
  \(33391\) reach \(u>0.999\).

## Formalization

None added. Existing `localDefectOdd` / `localDefectEven`
already contain the identities. No `FloorPhase.lean`. No
`sorry`. Paper A is unchanged.

## Results

Classification **SURVIVOR_PHASE_CLOSED**. Outcome C.

Science window: odd \(n\le 2\cdot 10^7\) (\(9\,999\,999\)
starts), \(S\)-bins ordinary \(5\,000\,067\), mid
\(3\,516\,206\), long \(1\,341\,492\), hold-out split
\(10^7\) (`COMPUTATIONALLY VERIFIED` as a bounded
observation; a histogram is not a theorem):

- Long-vs-control CDF gaps \(D_{\mathrm{odd}}=0.009\),
  \(D_{\mathrm{even}}=0.006\). Long-vs-ordinary
  \(D_{\mathrm{odd}}=0.006\). Train-vs-hold long
  \(D=0.001\).
- Edge occupancy is the generic \(2\varepsilon=0.10\).
- Lag-1 independence gap is \(0.0002\) for both long and
  ordinary paths.
- The unit interval remains occupied. Named laboratories
  span nearly \([0,1)\).
- Histograms use only states with \(\log_{10}x\le 12\), so
  the comparison is scale-matched. Bit-cap aborts
  \(142\,234\). Horizon at the step cap: \(477\).

This is the generic-distribution falsifier. User Outcome C.
The coordinates \(u_O,u_E\) are already `localDefect*`.

## Open questions

None from rounding-phase occupancy at this window. Do not
add `FloorPhase.lean`. Do not treat a histogram as a
conjecture. The leftover residual is still the cube cell
without a square cell.

## Decision

**CLOSE**. Long `AboveAnchor` survivors occupy the
square/cube rounding interval like scale-matched generic
integers and like ordinary short survivors. There is no
hold-out-stable concentration, avoidance, or extra lag-1
law. The only exact statements are already
`localDefectOdd` / `localDefectEven`. A branch of that
kind is a close.

Best next question: none from rounding-phase occupancy.
The leftover hole is still a cube cell without a square
cell.

## Publication assessment

Status: `EXPLORATORY`. A bounded histogram census, not a paper
candidate and not a Juggler totality result.

# Juggler ResidualStep future-equivalence (`~_H`)

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1.

## Problem

After the residual-state sufficiency CLOSE, the next constraint vector
\(V(y)\) is a function of the current integer. Distinct landings can
still share \(V\) at one step and split later. Form the empirical
future-equivalence \(\sim_H\) of ResidualStep landings and measure
how the number of classes grows with \(H\).

## Exact statement

Keep the existing successor. Do not replace it with a state machine.

\[
\mathrm{ResidualStep}(x,y)
\iff
\exists\,a,b\ (b\ge 1\ \wedge\ x\ \text{follows}\ O^aE^b\ \wedge\ T_{O^aE^b}(x)=y).
\]

The dynamics are a deterministic labeled transition: from \(x\) there
is at most one excursion. So \(\sim_H\) is **trace equivalence**, not
balanced-ternary tree equivalence on all trit inputs.

Fix a finite landing set \(Y\) and an observation alphabet \(\Sigma\)
that does **not** contain the next integer. Write \(\mathrm{obs}(x)\)
for one `residual_excursion` from \(x\), or a terminal
\(\mathrm{HALT}\) / \(\mathrm{NO\_EVEN}\). Then

\[
x\sim_H x'
\iff
\mathrm{obs}^H(x)=\mathrm{obs}^H(x').
\]

\(Q_H=\lvert Y/\sim_H\rvert\). Iterate `residual_excursion`
intrinsically from each \(y\in Y\). Do not use the start-relative
stop \(y<n\) of `residual_chain`. Stop only at \(y\le 1\), no even
residual, or the horizon cap. Mark \(\mathrm{CAPPED}\) so a truncated
prefix is not treated as a completed future.

Three projections of the same traces:

- `block`: the ResidualStep witness \((a,b)\)
- `V`: the existing intrinsic constraint vector
- `class`: intrinsic `residual_class(x,y)`

This says nothing about totality. Do not add `ResidualState`. Do not
extend `ResidualStep`. Do not prove a halt theorem. Do not reopen the
word-language factor census or a PE automaton.

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**. Totality
  is not claimed.
- Residual-step certificate propagation —
  **EXACT — LEAN VERIFIED**.
- Residual-state sufficiency — **CLOSE** as `RESIDUAL_STATE_NEEDS_X`.
  Proposed coordinates do not predict the next constraint. That test
  was \(H=1\) only.
- Word-language prefix Myhill–Nerode — **CLOSE** as
  `JUGGLER_LANGUAGE_IS_KNOWN_GRAMMAR`. That object is PE-run *word*
  prefixes, not landing futures. Do not reopen it.
- BT finite-horizon \(\equiv_k\) / \(M_k\) — **EXACT** in
  `bt.calculus.myhill_nerode`. Cubic counting is **CLOSE**. This
  branch is not that measurement.

Project relationship: **extended**. The leftover after the
sufficiency CLOSE is the \(H\)-growth of landing trace classes.
Totality remains unclaimed.

## Branch budget

```text
Mathematical target     On the deterministic ResidualStep graph, how many
                        distinct H-step futures exist among visited
                        landings, and does |Y / ~_H| saturate below |Y|
                        or refine toward the integer itself?
Novelty hypothesis      A stable proper quotient of landings — not y,
                        not incoming history, not a PE-run word prefix —
                        is visible as saturation of |Q_H| with multi-y
                        fibers that survive the horizon cap.
Falsifier               Every H-class with |fiber|>1 splits before the
                        cap, or the only unsplit fibers are the same
                        complete observation word to HALT (the trace is
                        a certificate of y, not a new state).
Existing machinery      residual_excursion, residual_class, intrinsic_V,
                        residual_chain landings, HARD_PROBES, odd-odd
                        n≤80 window, lean ResidualStep unchanged
Maximum Phase-0 scope   One probe, two nested windows, H=0..8, three
                        observation alphabets from the same traces.
                        No Lean, no CLI, no GPU, no ResidualState.
Promotion criterion     |Q_H| plateaus for H≥H* < cap, plateau ≪ |Y|,
                        and some multi-y fiber shares a long future that
                        is not just “both reach 1 in ≤1 step”.
Stop criterion          ResidualState.lean; ResidualStep rewritten;
                        automaton / ResidualGraph / cycle engine; halt;
                        reopening word-language factor MN; object C.
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required. Finite-horizon \(\equiv_k\) is a different object
(tree equivalence of residual polynomials) and is not reused here.

## Candidate operations / invariants

- `ResidualStep` as the only successor —
  **EXACT — LEAN VERIFIED** (already present; not rewritten)
- \(\sim_0\) is a single class; \(\sim_{H+1}\) refines \(\sim_H\) —
  **COMPUTATIONALLY VERIFIED** on the Phase-0 windows
- \(H=1\) / `V` class count equals \(\lvert\{V(y):y\in Y\}\rvert\) —
  **COMPUTATIONALLY VERIFIED** (\(19\) on \(n\le 80\); \(38\) on
  \(n\le 200\))
- a stable proper quotient of landings, not \(y\) itself —
  **REFUTED** on both windows: leftover multi-\(y\) classes are
  identical complete block-words to HALT
- “same complete observation word to HALT is a new state” —
  **REPARAMETERIZATION**
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.residual_minimize`
- Records: [juggler_residual_minimize.md](../research/juggler_residual_minimize.md),
  [juggler_residual_minimize.json](../research/juggler_residual_minimize.json)
- Dataset: `data/research/juggler/residual_minimize/`
- Tests: `tests/research/juggler_sequence/test_residual_minimize.py`
- The Research Engine control layer is not modified.
- `ResidualStep` is not extended. No `ResidualState.lean`.

Windows: odd-odd residual landings from starts \(2\le n\le 80\) and
\(2\le n\le 200\). Horizon \(H=0..8\). First-even cap \(24\).
Hard traces: `HARD_PROBES = (9, 37, 49, 69, 77)`.

Do not test coordinate ablation, PE-run factors, or interval-width
tightening.

## Conjectures

None opened.

## Counterexamples

- “\(H=1\) merges survive as a proper quotient”: on \(n\le 80\),
  block \(Q_1=14\) with \(23\) pair refinements at the next step;
  \(V\) goes \(19\to 23\) by \(H=2\).
- “a live multi-\(y\) prefix survives the cap”: \(0\) capped traces
  on \(n\le 80\); the \(13\) capped traces on \(n\le 200\) are
  pairwise distinguished at \(H=8\).
- “\(7\) and \(11\) have different ResidualStep futures”: both emit
  \(O E^3\) and HALT.
- “\(25\) and \(59\) split before HALT”: both emit
  \(O^3E^2,\,OE,\,OE^3\) and HALT.
- “\(Q_H\) reaches \(\lvert Y\rvert\)”: block \(Q_H\) plateaus at
  \(23<30\) (\(n\le 80\)) and \(76<111\) (\(n\le 200\)).

## Formalization

None added. `ResidualStep` and `ResidualChain` already live in
`formal/Problems/Juggler/Residuals.lean`. No `ResidualState.lean`.
`GlobalDefect.lean` is not edited. No `sorry`. No ledger row.

## Results

Classification **RESIDUAL_MN_REPACK**.

On odd-odd residual landings from \(n\le 80\) there are \(18\)
starts, \(43\) landings, \(30\) distinct \(y\). Block \(Q_H\) is

\[
1,14,22,23,23,23,23,23,23
\]

and plateaus from \(H=3\). \(H=1\) / `V` has \(19\) classes, matching
\(\lvert\{V(y)\}\rvert\). No trace is capped. The six leftover
multi-\(y\) fibers are complete halt words:

| members | block word |
|---|---|
| \(25,59\) | \(O^3E^2,\,OE,\,OE^3\) |
| \(53,55\) | \(O^2E^2,\,O^2E,\,OE^3\) |
| \(33,35,73\) | \(O^2E^2,\,OE^3\) |
| \(15,31\) | \(OE,\,OE^3\) |
| \(7,11\) | \(OE^3\) |
| \(43,45\) | \(O^2E^4\) |

On \(n\le 200\) there are \(56\) starts, \(162\) landings,
\(111\) distinct \(y\). Block \(Q_H\) is

\[
1,26,64,74,75,76,76,76,76
\]

and plateaus from \(H=5\). Thirteen traces are capped; those live
prefixes are pairwise distinct. The plateau below \(\lvert Y\rvert\)
is again shared complete words to HALT.

Hard traces: \(9\to 11\to 1\), \(11\to 1\),
\(37\to 9317\to 2233\to 1\), \(49\to 79\to 5\to 1\),
\(69\to 117\to 3\to 1\),
\(77\to 1523\to 243\to 21\to 9\to 11\to 1\).

No `ResidualState.lean`. `ResidualStep` is unchanged.

## Open questions

Object C — a global \(\sum\rho\) bound in \((n,\text{word
statistics})\) — stays recorded, not opened. Do not reopen
word-language Myhill–Nerode automata.

## Decision

**CLOSE** the ResidualStep \(\sim_H\) census as `RESIDUAL_MN_REPACK`.
\(Q_H\) plateaus below \(\lvert Y\rvert\) only because some landings
share a complete observation word to HALT. That itinerary is a certificate
of those integers, not a new ResidualStep state. \(H=1\) merges
refine away or collapse to the same halt word. No live multi-\(y\)
prefix survives the cap. Do not add Lean. Do not claim a finite
ResidualStep automaton. Do not reopen word-language MN. Do not claim
termination.

Best next question: a global \(\sum\rho\) bound in
\((n,\text{word statistics})\) — object C — not another residual
relation.

## Publication assessment

Status: `EXPLORATORY`. A negative trace-class census, not a paper
candidate and not a Juggler totality result.

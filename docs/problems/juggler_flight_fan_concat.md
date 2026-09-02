# Juggler fan-block concatenability (local glue of shortest positive-θ blocks)

Status: **PARK** (no \(19\to 19\) glue on the existing windows; no
launch invariant; infinite fan-following remains a coherent
surviving failure mode, not a constructed orbit)

The flight program's descriptive arc is terminal. This branch asks
the one dynamical question that A–F still leave open: after a
realized record segment of shortest fan type \((p,o)=(19,12)\), can
the terminal state launch another \(R_\varepsilon\) fan block? Not a
halt theorem, not a divergence exclusion, not a CF fan census, not a
reopen of record composition, mechanical lift, expanding-residual
concatenation, hug-cylinder \(C_L\), or Paper A.

## Problem

An infinite fan-following ascent is not ruled out structurally.
Most of the necessary list is already on the ledger
(`J-flight-divergent-structure`, `J-flight-return-quantization`,
Lean hug domination). The missing pair is realizability plus
**dynamical concatenability**. Does the shortest positive-\(\theta\)
fan block glue to another fan block on the orbits the laboratory
already walks?

## Exact statement

Write \(R_{0.05}=\{p:\theta_p\le 0.05\}=\{19,38,84,\dots\}\) with
\(\theta_p=o_{\min}(p)\log_2 3-p\), so
\(\theta_{19}=12\log_2 3-19\approx 0.01955\). A *near-return* of
length \(p\in\{19,38\}\) is an AboveAnchor segment from an anchor
\(m\ge 400\) whose doubly-log jump satisfies \(\delta\le 0.05\)
(the return-quantization census). *Glue* \(19\to 19\) (resp.
\(19\to 38\)) means the 19-endpoint is a remaining-tail record and
the next AboveAnchor segment from that endpoint realizes a 19-
(resp. 38-) near-return. *Factorization* \(38=19\mid 19\) means a
mid-record at step 19 whose both halves are near-returns.

**Observation (COMPUTATIONALLY VERIFIED).** On \(n\le 2000\) there
are exactly the 44 length-19 and 7 length-38 near-returns of
`J-flight-return-quantization`. All have \((p,o)=(19,12)\) or
\((38,24)\). None is the hug word (window Hamming \(\ge 2\)).
Seventeen of the 44 length-19 endpoints are odd, so a hug-admissible
\(R_{0.05}\) word is formally launchable; all 44 endpoints are
remaining-tail records. None glue: \(19\to 19\), \(19\to 38\),
\(19\to R_{0.05}\), and \(38=19\mid 19\) are all zero. Twenty-seven
of the 44 have next-segment length 0; only one has next length
\(\ge 19\) (\(n=761\), 41 steps) and it still misses a second
near-return.

On the seven high-flyers: 8 length-19 and 6 length-38 near-returns,
again all quantized \((19,12)\) / \((38,24)\), none hug, none glue.
One long tail (\(n=1245741\), 118 steps after an odd 19-endpoint)
still misses a second \(R_{0.05}\) near-return.

No launch invariant is claimed. No infinite A–F sequence is
constructed. Exclusion of divergent flights is not claimed.

## Current literature

- Pointwise divergent structure and recurrent hug domination —
  **EXACT — HUMAN PROOF** (`J-flight-divergent-structure`).
- Record-jump quantization, shortest near-return 19, census
  \(\{19{:}44,\,38{:}7\}\) on \(n\le 2000\) — **EXACT — HUMAN
  PROOF** / **COMPUTATIONALLY VERIFIED**
  (`J-flight-return-quantization`).
- Hug word prefix-min and \(\theta_{19}>0\) — **EXACT — LEAN
  VERIFIED** (`aboveAnchor_prefix_odds_ge_hug`, `hugOdds_pow_lt`).
- Record-composition of \(\delta\)-totals — **CLOSE** /
  **REPARAMETERIZATION**
  ([juggler_flight_record_composition.md](juggler_flight_record_composition.md)).
  Not reopened: this branch is word/state glue, not lattice sums.
- Infinite PE concatenation — **CLOSE** as the CE leftover
  ([juggler_expanding_residual_concat.md](juggler_expanding_residual_concat.md)).
  Not reopened: an infinite A–F sequence *would* be a divergent
  flight; Phase-0 asked a local question that can fail independently.
- Exact hug(19) integer lifts — **CLOSE**
  ([juggler_cycle_mechanical_lift.md](juggler_cycle_mechanical_lift.md)),
  death at `empty_ooe`. Not reopened: realized 19-near-returns here
  are not hug words.
- Hug-prefix realization, formal-versus-realized, valley-composition
  exclusion, DK-as-kill, odd towers, hug-cylinder \(C_L\neq\emptyset\)
  (PARK), interval-ET depth 2 — not reopened.

Project relationship: **independent** as a local glue measurement
on already-walked orbits.

## Branch budget

```text
Mathematical target     After a realized record segment of shortest
                        fan type (p,o)=(19,12), can the terminal
                        state launch another R_ε fan block as a
                        subsequent record segment — or is there a
                        local launch obstruction?
Novelty hypothesis      Word/state glue at fan-block boundaries is
                        a different object from jump-lattice
                        composition (CLOSE) and from infinite PE
                        concatenation (CLOSE as CE leftover)
Falsifier               Glue is a restatement of empty_ooe /
                        SCALE_HUG / first-descent / MinimalNonTerm;
                        or the A–F list is only packaging
Existing machinery      J-flight-divergent-structure,
                        J-flight-return-quantization (44×19 and
                        7×38 near-returns on n≤2000), hug(19)
                        prefix-min walk, mechanical-lift follow
                        depths, seven high-flyers, two-sided
                        transport (Lean)
Maximum Phase-0 scope   Classify existing 19/38 witnesses and
                        high-flyer ascent prefixes; no new n-window,
                        no CF fan census, no Lean, no Paper A,
                        no flight-note rewrite, no CLI/viz
Promotion criterion     A launch invariant that is not an archived
                        cell / scale / envelope fact
Stop criterion          REPARAMETERIZATION of mechanical-lift,
                        expanding-residual-concat, or record
                        composition; or finite glue with no
                        structural law (PARK, do not auto-continue)
```

## Balanced-ternary formulation

None required. The blocks live on the exponent walk
\(\{o\log_2 3-p\}\) and the integer orbit.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- A–F necessary list for infinite fan-following — packaging of
  existing rows, not a new theorem: (1)–(4), (6)–(7), (D), (F) are
  `J-flight-divergent-structure` and `J-flight-return-quantization`;
  hug(19) already supplies a prefix-safe positive-\(\theta\) block;
  \((\theta_{19})^\infty\) already diverges, so \(\theta_i\sim 1/i\)
  is unnecessary. Only (A) and (E) were open.
- Local \(19\to 19\) / \(38=19\mid 19\) glue — **OBSERVATION**
  (absent on both windows).
- Formal odd-end launch — **OBSERVATION** (17/44 window, 7/8 flyer
  length-19s); not sufficient for realized glue.
- A launch invariant that is not `empty_ooe`, SCALE_HUG, or
  first-descent — not obtained.
- Infinite A–F sequence — not constructed; not claimed.

## Experiments

- Probe: `research.juggler_sequence.flight_fan_concat`
- Artifact:
  `data/research/juggler/flight_fan_concat/summary.json`
- Tests:
  `tests/research/juggler_sequence/test_flight_fan_concat.py`

Same anchors, dip test, and \(\delta\le 0.05\) cut as the
return-quantization census. No \(n_{\max}\) raise. No CF
enumeration.

## Conjectures

None opened. Absence of glue on terminating orbits is not a
conjecture that glue is impossible.

## Counterexamples

None to a claimed obstruction (none was claimed). The two long
post-19 tails that still miss a second near-return are witnesses
against “the next segment is always too short,” not
counterexamples to a theorem:

- \(n=761\), next-segment length 41;
- \(n=1245741\), next-segment length 118.

## Formalization

None new. The quantitative components used for definitions are
existing Lean (`aboveAnchor_prefix_odds_ge_hug`,
`follows_log_le_walkWeight`, `aboveAnchor_transport`). No `sorry`.
No Paper A edit.

## Results

Classification **FAN_CONCAT_NO_GLUE**.

- The existing 44+7 near-returns are quantized
  \((19,12)\)/\((38,24)\) and are not hug words.
- Formal launch (odd endpoint) occurs; realized glue does not,
  including two tails long enough to host another 19.
- The typical 19-near-return sits at the end of a dying
  AboveAnchor climb (27/44 next length 0). That is the shape of a
  terminating orbit, not a concatenable block.
- The 7 length-38 hits are single 38-windows, not \(19\mid 19\).
- No launch law, no infinite sequence, no ledger row.

## Open questions

- Does a long post-19 AboveAnchor tail have a walk-height reason
  to miss a second \(R_\varepsilon\) near-return, or is the
  \(1245741\) miss only a finite-orbit effect? Answered by
  [juggler_flight_post19_tail.md](juggler_flight_post19_tail.md)
  (PARK): long miss \(=\) overshoot, not descent; overshoot is
  not forced.
- Infinite dynamically concatenable positive fan blocks with
  divergent total \(\theta\) remain unconstructed and unobstructed.
  That is the surviving failure mode this branch named; it is not
  a demonstrated trajectory.

## Decision

**PARK.** Phase-0 answered the local question on the windows it
was allowed to walk: glue is absent, including after formally
launchable odd endpoints and after two long tails. That is not a
launch invariant (so not PROMOTE) and not an archived cell /
SCALE_HUG / CE leftover under a new name (so not CLOSE). Finite
data on terminating orbits cannot obstruct an infinite
fan-follower. Do not raise \(n_{\max}\), do not resume a CF census,
do not claim a divergent-flight mechanism. Best next question:
does a long post-19 tail miss the next \(R_\varepsilon\) time for
a walk-height reason, or only because these orbits later descend?

## Publication assessment

Status: `EXPLORATORY`. A glue census for the laboratory record.
Not a paper candidate. No Paper A/B edit. No flight-note rewrite.

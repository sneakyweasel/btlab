# Juggler twin-flight of nearby same-parity starts

Status: **ARCHIVED**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a reopen of
`high_merge` / minimal-anchor closure, not a leftover-itinerary census,
not a \(10^9\) stopping-time census, not Paper A, and not a claim
that every positive integer reaches 1. Coalescence is not evidence
of termination.

The current program has mostly followed one trajectory at a time.
This phase treated a same-parity pair \((n,n+2)\) as one object
and closed it.

## Problem

Do nearby same-parity starts merge, shadow, phase-shift, or isolate
under the floor-power map, especially around already-identified
hard trajectories?

## Exact statement

For odd \(n\) the first images have the same letter and satisfy
\[
\delta_1=\frac{|T(n+2)-T(n)|}{\max(T(n),T(n+2))}\approx\frac{3}{n}.
\]
First-step closeness is the setup, not a shadow.

Phase 0 walked named hard laboratories and a cheap generic control.
At synchronized time \(k\) it recorded \(d_k\) and \(\delta_k\), the
first synchronized merge time \(\tau_{\mathrm{merge}}\), the first
common state above \(2\) with phase shift \(r\), the high-water
ratio \(R_\pm(n)=H(n\pm 2)/H(n)\), and whether a merge occurs on
an even step. Classes are mutually exclusive:

- `exact_merge` — \(T^k(n)=T^k(n+2)\) at some \(k\ge 1\), state
  \(>2\);
- `shifted_flight` — a common state \(>2\) at unequal times, never
  synchronized;
- `long_shadow` — no common state \(>2\), \(\max\delta_k\le 0.05\)
  on a prefix of at least \(8\) steps;
- `separate` — \(\delta\) leaves \(0.05\) and no common state \(>2\).

Capped orbits are `capped_*`, not silent `separate`. The trivial
sink \(\{1,2\}\) is excluded from common-tail detection, so meeting
at \(1\) is not a merge. The known \(365/501\) share of \(763\) is
calibration of the detector, not a substitute for the \(\pm 2\)
question (`high_merge` is a different object: a smaller \(m\)
hitting a high state of \(n\)).

A bounded pair census is not a theorem. Absence under a cap is
`NOT OBSERVED WITHIN SEARCH BOUND`. This is not a halt theorem.

## Current literature

- Floor-power map — **KNOWN** (`oeis-A094683`,
  `pickover-1991-computers-imagination`).
- Stopping times to \(1\) — **KNOWN** (`oeis-A007320`); totality
  is not claimed.
- \(365/501\) merge at \(763\) / later \(12707\) —
  **COMPUTATIONALLY VERIFIED** (`J-minimal-anchor-leftover-spine`);
  non-adjacent hard-to-hard inheritance, not an \(n,n+2\) law.
- `high_merge` — **OBSERVATION** on leftover controls
  ([juggler_minimal_anchor_closure.md](juggler_minimal_anchor_closure.md));
  different object.
- Stopping-time memoization — implementation coalescence, not the
  pair object.
- Cell-hut merge pairs — quotient-graph phenomenon; **REFUTED** as
  a simplifying rule.
- Inverse cells — backward many-to-one, not forward pair
  shadowing.
- Neighboring-start forward census — not found in the local
  literature store.
- Every start reaches 1 — not claimed.

Project relationship: **independent**, then **refuted** as a
hard-family law.

## Branch budget

```text
Mathematical target     Do nearby same-parity starts merge, shadow,
                        phase-shift, or isolate — especially around
                        already-identified hard trajectories?
Novelty hypothesis      The even square-root cell is many-to-one, so
                        nearby odd starts may coalesce into common
                        tails or persistent shadows; a hard flight
                        may be a local family rather than a singleton.
Falsifier               Named hard windows decorrelate like the
                        generic (n, n+2) control, or records are
                        isolated with no shared states / no height
                        correlation.
Existing machinery      floor_power / itinerary; HARD_LABS;
                        high_merge (different object: smaller m
                        hitting n's high states); 365/501 already
                        share 763; stopping_times memoization
Maximum Phase-0 scope   HARD_LABS ±10 same-parity matrices;
                        named record extras; odd n≤2000 (n,n+2)
                        control; cross-lab tails among HARD_LABS.
                        No 10^9 census, no 10^5 expansion, no Lean,
                        no CLI, no Streamlit, no paper edit.
Promotion criterion     Hard windows show merge / shifted-flight /
                        persistent shadow at a rate clearly above
                        the control, with a reusable pair object.
Stop criterion          Generic decorrelation; generic coalescence
                        at the same rate as the control; isolation
                        of records with no new law; machinery
                        gravity; any halt reading of coalescence.
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Same-parity pair \((n,n+2)\) with synchronized \(\delta_k\) —
  **COMPUTATIONALLY VERIFIED** as a bounded observation;
  first-step \(\delta_1(37)=18/243\approx 0.074\) against \(3/37\)
- Hard-specific coalescence or persistent shadow —
  **REFUTED** (contact \(0.522\) vs control \(0.550\); zero
  long shadows)
- First-step closeness persists under the map —
  **REFUTED** (lab-neighbor \(\max\delta=1\))
- Named records sit in a local high-water basin —
  **REFUTED** (\(R_\pm\ll 1\); \(37\) isolated from both
  neighbors)
- \(365/501\) share \(763\) — **COMPUTATIONALLY VERIFIED**
  calibration of the common-tail detector; not an \(n,n+2\) law
- Coalescence implies termination — not claimed
- Global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.twin_flight`
- Records: [juggler_twin_flight.md](../research/juggler_twin_flight.md),
  [juggler_twin_flight.json](../research/juggler_twin_flight.json)
- Dataset: `data/research/juggler/twin_flight/`
- Tests: `tests/research/juggler_sequence/test_twin_flight.py`

Named laboratories \(37,69,89,365,501,1517,6187,329,33391\) with
same-parity window \(\pm 10\); record extras
\(193,425,557,761,1181,1721,1773,2183,3889\); control odd
\((n,n+2)\) for \(n\le 2000\); cross-lab tails among `HARD_LABS`.
Caps: \(400\) steps, \(4096\) bits. No CLI. No Lean.

## Conjectures

None opened.

## Counterexamples

- “Nearby same-parity starts around hard laboratories coalesce
  more than generic odd pairs.” False: hard-window adjacent
  contact \(0.522\) versus control \(0.550\) on \(n\le 2000\).
- “The first-step gap \(\delta_1\approx 3/n\) persists as a
  shadow.” False: every hard-lab \(\pm 2\) neighbor reaches
  \(\max\delta=1\); long-shadow count is \(0\) on both the
  laboratories and the control.
- “A record high-water mark is surrounded by similarly high
  neighbors.” False: \(R_\pm(37)\sim 10^{-10}\),
  \(R_\pm(33391)\sim 10^{-184}\), and \(37\) shares no state
  \(>2\) with \(35\) or \(39\).
- “Neighbor contact around a hard start is a shared high
  flight.” False: recorded commons are \(11,27,5,4,3\), not
  the high PE climb. The \(365/501\) share of \(763\) is the
  known non-adjacent inheritance.

## Formalization

None added. No `TwinFlight.lean`. No `sorry`. Paper A is
unchanged.

## Results

Classification **TWIN_FLIGHT_CLOSED**.

Hard-window adjacent pairs (\(90\)) versus control odd
\((n,n+2)\) for \(n\le 2000\) (\(999\) pairs),
**COMPUTATIONALLY VERIFIED** as a bounded observation:

- Contact (exact merge or shifted flight above \(2\)):
  \(0.522\) versus \(0.550\).
- Long shadows: \(0\) versus \(0\).
- Separate: \(0.456\) versus \(0.450\).
- Even-reset merges: \(24/90\) hard-window, \(306/999\)
  control — the even cell does collapse pairs, at the generic
  rate.
- First-step scale: \(\delta_1(37)=18/243\approx 0.074\)
  against \(3/37\approx 0.081\).
- Calibration: \(365\) and \(501\) share \(763\)
  (`shifted_flight`, \(r=8\)).
- Isolation: only \(37\) among `HARD_LABS` is height-isolated
  *and* state-disjoint from both odd neighbors. Other records
  have \(R_\pm\ll 1\) but later meet a neighbor at a small
  state (\(11\), \(27\), \(4\)).
- Cross-lab: \(16/36\) `HARD_LABS` pairs share a state \(>2\);
  all but \(365/501\) at \(763\) are small-basin joins.

The pair object exists. It is not special around hard
trajectories. Meeting at \(1\) was excluded; residual contact
is late joining of the small attractor basin, not a twin
flight of the excursion.

## Open questions

None from twin-flight at this window. Do not run the
hardest-\(10^5\) expansion. Do not add `TwinFlight.lean`.
Do not treat coalescence as termination.

## Decision

**CLOSE**. Hard-window adjacent pairs match the generic
\((n,n+2)\) control (contact \(0.522\) versus \(0.550\); zero
long shadows). First-step closeness amplifies immediately.
Named records are high-water isolated from \(\pm 2\); neighbor
“contact” is late joining at \(11,27,5,4,3\), not a shared
high flight. The local-family hypothesis is **REFUTED**. The
\(365/501\) share of \(763\) remains the known non-adjacent
inheritance. A branch of that kind is a close.

Best next question: none from twin-flight. The leftover hole
is still the live paper program, not a pair census.

## Publication assessment

Status: `ARCHIVED`. A bounded pair census that matched its
control, not a paper candidate and not a Juggler totality
result.

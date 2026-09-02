# Juggler residual-floor leftover census for length 84

Status: **ARCHIVED**

Laboratory companion to
[position-dependent finance](juggler_cycle_position_finance.md)
and [L=84 at \(m\ge 3\)](juggler_cycle_l84_m3.md).
It asks whether killing leftover \(L=84\) for all \(m\) at
residual floor \(1981\) (joint/height) or \(4756\) (global)
renames the laboratory leftover or jumps it to the next record
\(569\). It is not a Lean floor factory, not a Paper A edit, not
a walk-charge / blocker reopen, and not a halt theorem.

## Problem

Height finance already excludes length \(84\) at \(m\le 2\) at
floor \(261\). Joint/height kill every \(m\) at \(1981\); global
finance kills \(L=84\) at \(4756\). Both floors sit under the
certified descent floor \(162849448\). After those kills, is the
new named leftover an \(84\)-multiple (rename) or the record
\(569\) (jump)?

## Exact statement

Write \(\theta=1-2^L/3^{o_{\min}}\). Lean `cycleMin_finance` uses
constant \(1\). At a residual floor \(n_0\), a length survives
globally when \(n_0\ln n_0\le L/\theta\), and survives
joint/height when some circuit count \(m\le L-o\) has
\(\theta\le\mathrm{RHS}(n_0,m)\).

**Named leftover after a method.** The smallest \(L\) that
survives global finance at \(n_0\) and is not killed for every
\(m\) by that method.

Constant \(1\), \(L\le 600\):

- Floor \(1981\): global leftover \(84\); joint/height leftover
  \(168\) (\(o=106\), global floor \(4761\)).
- Floor \(4756\): global leftover \(168\); joint/height leftover
  \(569\).
- Family height/joint all-\(m\) floors: \(84\) at \(1981\),
  \(168\) and \(252\) at \(1983\), \(336\) at \(1985\),
  \(420\) at \(1987\), \(504\) at \(1989\), \(588\) at \(1991\),
  record \(569\) at \(19975\).

Killing \(L=84\) at the cheap all-\(m\) floor \(1981\) is a
leftover rename to \(168\). Not a halt theorem.

## Current literature

- Lean leftover is period \(84\) with \(m\ge 3\) or \(\ge 85\) —
  **EXACT — LEAN VERIFIED**
  (`cycle_itinerary_length_eighty_four_m_ge_three_or_ge_eighty_five`)
- Joint/height all-\(m\) for \(L=84\) at \(1981\), global at
  \(4756\) —
  **COMPUTATIONALLY VERIFIED** (`l84_floors.json`)
- “\(4756\) is the cheapest kill of \(L=84\)” —
  **REFUTED** (`juggler_cycle_finance_l84_floor_4756`)
- Cheap refinements of \(L=84\) at \(m\ge 3\) at floor \(261\) —
  **REFUTED** (`juggler_l84_m_ge_three_floor_261`)
- Descent floor \(162849448\) —
  **COMPUTATIONALLY VERIFIED**
  (`J-residual-floor-one-hundred-sixty-two-million`); covers
  both candidate floors
- Residual-floor factory to \(1981\) / \(4756\) — previously
  **PARK**; this census keeps that decision
- Every start reaches 1 — not claimed

Project relationship: **extended** census of an already parked
campaign. Collatz \(m\)-cycle height —
`simons-de-weger-2005-collatz-m-cycles` — is the known source
of the height law, not a new transfer.

## Branch budget

```text
Mathematical target     After killing L=84 for all m at floor 1981
                        (joint/height, const 1) or 4756 (global,
                        const 1), what is the new laboratory leftover?
Novelty hypothesis      Height-at-1981 also kills the 84-multiples
                        (168, 252, …), jumping the named leftover
                        to 569 rather than renaming 84 → 168
Falsifier               the named leftover is 168 (or another
                        84-multiple) with global floor still ~4756
Existing machinery      l84_exclusion_floors, finance_surviving_scan,
                        finance_rows, position_rhs / steiner_rhs,
                        verify_floor_certified (N162849448 already
                        covers both floors), atlas CUDA harvest,
                        cycle_floor_hard_seeds / gmpy2
Maximum Phase-0 scope   leftover census at 1981 and 4756; name the
                        leftover under global / joint / height;
                        companion certificates for new-odd orbit
                        cost; no Lean, no Paper A, no N0 raise
Promotion criterion     leftover jumps past the 84-family (e.g. to
                        569) at 1981 by height
Stop criterion          leftover rename, or machinery gravity
                        (new CUDA kernel, Lean factory, walk-charge)
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Height/joint all-\(m\) leftover at floor \(1981\) is \(569\) —
  **REFUTED** (named leftover is \(168\))
- Global leftover at floor \(4756\) is \(569\) —
  **REFUTED** (named leftover is \(168\); \(168\) needs \(4761\))
- Family kill floors for \(\{84,168,252,336,420,504,569,588\}\) —
  **COMPUTATIONALLY VERIFIED** (`leftover_at_floors.json`)
- Companion floors \(1981\) and \(4756\) reach 1 —
  **COMPUTATIONALLY VERIFIED** (implied by
  `J-residual-floor-one-hundred-sixty-two-million`; checksums
  `N1981`, `N4756`)
- Residual floor \(273\) / Lean factory to \(1981\) — **PARK**
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_l84_residual_floor`
- Tests: `tests/research/juggler_sequence/test_cycle_l84_residual_floor.py`
- Artifact: `data/research/juggler/cycle_position_finance/leftover_at_floors.json`
- Totality witness:
  `data/research/juggler/cycle_finance/floor_verify/N162849448/certificate.json`
- Laboratory checksums:
  `data/research/juggler/cycle_finance/floor_verify/N1981/`,
  `N4756/`
- CUDA first-descent companion:
  `data/research/juggler/cycle_l84_residual_floor/harvest_261_4756.tsv`
- No CLI. No new Lean. Paper A is unchanged. Walk-charge GPU
  was not called.

## Conjectures

None. Computational leftover names are not conjectures. The
already **REFUTED** slogan
`juggler_cycle_finance_l84_floor_4756` is not re-tested.

## Counterexamples

Height at \(n=1981\), constant \(1\), \(L=168\), \(o=106\),
\(\theta\approx 0.004168\): some \(m\) survives, so the named
leftover after killing \(84\) is \(168\). Height first kills
every \(m\) of \(168\) at \(1983\). Global finance first kills
\(168\) at \(4761\).

## Formalization

None added. `TerminationFloor257.lean` stays at residual floor
\(261\). `CycleHeightFinance.lean` is unchanged. Not added:
`reachesOne_of_lt_1981`, `CyclePositionFinance.lean`. No `sorry`.
Paper A is unchanged. Not a halt theorem.

## Results

Classification **L84_RESIDUAL_FLOOR_PARK**. The novelty
hypothesis is false at the cheap all-\(m\) floor.

- Height/joint at \(1981\) kill \(L=84\) and rename the leftover
  to \(168\), whose global floor \(4761\) is the same scale as
  \(84\)'s \(4756\).
- Global finance at \(4756\) also renames to \(168\) (\(168\)
  needs \(4761\)).
- Height/joint at \(4756\) would jump to \(569\), but that is
  the expensive campaign. The family table first reaches \(569\)
  by height at \(1991\) (after \(588\) dies). Those raises stay
  **PARK**.
- Companion checksums: \(N=1981\) walks \(990\) odds, peak
  \(900\) bits at seed \(193\); \(N=4756\) walks \(2377\) odds,
  peak \(19694\) bits at seed \(2183\). Both already implied by
  \(N_0=162849448\). \(1981<53^2=2809\), so `even_lt_sq` is
  unchanged.
- Atlas CUDA harvest on \([261,4756]\) is a first-descent
  companion (\(52\) overflows, \(72\) uncapped). Not a totality
  claim.

## Open questions

Stop. The laboratory leftover remains period \(84\) with
\(m\ge 3\), or \(\ge 85\). Do not raise the residual floor. A
height factory to \(1991\) would jump the leftover to \(569\)
and is not opened from this census.

## Decision

**PARK**. Killing \(L=84\) for all \(m\) at floor \(1981\) is a
leftover rename to \(168\), not a jump to \(569\). The
promotion criterion did not fire. This is not a reason to raise
the Lean residual floor. Not a halt theorem.

Best next question: the laboratory leftover remains \(84\) with
\(m\ge 3\), or \(\ge 85\), as recorded in
[juggler_cycle_finance_note.md](../theory/juggler_cycle_finance_note.md).

## Publication assessment

Status: `ARCHIVED`. Negative knowledge on a parked residual-floor
campaign. Not a paper candidate.

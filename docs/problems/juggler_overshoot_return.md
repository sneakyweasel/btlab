# Juggler later ReturnBelow after forced overshoot

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1. It is not a two-excursion retry,
not a Paper B engine, and not a \(K_3\) attack.

## Problem

After \(e\le 3\) the first even residual of a leftover start always
overshoots. Does the even-\(y\) class then admit a uniform later
word from \(y>n\) that lands below the original \(n\)?

## Exact statement

`Progress` already inducts: if every \(n>1\) has `FiniteProgress`,
every positive integer reaches 1. Automatic coverage is `E` and
`OE`. The leftover is odd-to-odd.

On `MinimalNonTerm n` or `CycleMin n w`, the first `O^a E` cannot
return to \(n\): that itinerary has even-count 1, now excluded by
`no_cycle_itinerary_even_count_le_three`. Therefore the first even
residual overshoots:

\[
(n+1)^2\le T^a(n)
\qquad\text{and}\qquad
n<T^{a+1}(n).
\]

Halt on that leftover is `ReturnBelow`: a later finite itinerary from
\(y=T^{a+1}(n)>n\) lands strictly below \(n\). A prefix to \(y\)
together with `ReturnBelow` is `FiniteProgress`.

The even-\(y\) class splits. For \(a\in\{2,3\}\) the itineraries `OOEE`
and `OOOEE` are already Paper B contractors
(\(3^a<2^{a+2}\)). For \(a\ge 4\), \(O^a\mathrm{EE}\) is formally
expanding and sits in the `OOOO*` tree. Phase 0 asks whether those
starts share one later contractor — a completed first excursion,
the next excursion from the landing, or one `ReturnBelow` suffix
after \(O^a\mathrm{EE}\) (or a one-parameter family in \(a\)).

Do not prove a universal return-below theorem. Do not prove
totality. Do not reopen \(K_3\).

## Current literature

- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**.
  Totality is not claimed.
- Finite-progress spine; leftover class odd-to-odd —
  **EXACT — LEAN VERIFIED**.
- First-even residual trichotomy —
  **EXACT — LEAN VERIFIED**.
- Two excursions do not always return below \(n\) (\(37\), \(77\),
  both odd \(y\)) — **REFUTED** as a general law.
- Even-count \(\le 3\) cycle itineraries —
  **EXACT — LEAN VERIFIED**.
- Paper B certified descent density \(13/16\); laboratory
  length-5 repair \(7/8\) (`J-five-step-descent-density`);
  densities \(57/64\) and \(29/32\) remain **CONJECTURE**;
  `OOOO*` and \(K_3\) — **PARK**.

Project relationship: **extended**. The return disjunct of the
first-even dichotomy is now excluded. The even-\(y\) halt fragment
is not a density engine.

## Branch budget

```text
Mathematical target     Does every first-E overshoot with even y
                        admit a uniform later word from y that
                        lands below the original n?
Novelty hypothesis      After e≤3 the first even always overshoots;
                        the even-y class then has one later
                        contractor, giving FiniteProgress on that class
Falsifier               a≥4 return words scatter, or only Paper B
                        engines, or an even-y stay like 37 / 77
Existing machinery      Progress spine; ReturnBelow; e≤3; Paper B;
                        K3 parked
Maximum Phase-0 scope   Lean overshoot corollary; even-y census,
                        novelty only at a≥4; no CLI, no K3, no
                        length-11, no new a≤3 engine
Promotion criterion     A named later comparison that is not a
                        Paper B engine and that yields ReturnBelow
Stop criterion          No uniform later word; REPARAMETERIZATION
                        of OOEE/OOOEE; machinery gravity; K3 reopen
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- first even residual overshoots on `MinimalNonTerm` /
  `CycleMin` —
  **EXACT — LEAN VERIFIED**
- \(a\in\{2,3\}\) even-\(y\) first excursion descends on
  \(n\le 10^4\) —
  **COMPUTATIONALLY VERIFIED** (Paper B replay)
- \(a\ge 4\) even-\(y\) first excursion is not uniform
  (\(147\) descend, \(170\) stay; \(N_0=9883\)) —
  **COMPUTATIONALLY VERIFIED**
- next excursion from those stays is not uniform —
  **COMPUTATIONALLY VERIFIED**
- \(96\) distinct `ReturnBelow` suffixes after \(O^a\mathrm{EE}\),
  lengths \(7..115\) —
  **COMPUTATIONALLY VERIFIED**
- a uniform later contractor for \(a\ge 4\) even \(y\) —
  **REFUTED** as a Phase-0 law on \(n\le 10^4\)
- global halt — not claimed
- every overshoot later returns — not claimed

## Experiments

- Probe: `research.juggler_sequence.overshoot_return`
- Records: [juggler_overshoot_return.md](../research/juggler_overshoot_return.md),
  [juggler_overshoot_return.json](../research/juggler_overshoot_return.json)
- Tests: `tests/research/juggler_sequence/test_overshoot_return.py`
- The Research Engine control layer is not modified.

## Conjectures

None opened.

## Counterexamples

None to the overshoot corollary. The stronger halt fragment that
fails:

- “every \(a\ge 4\) even-\(y\) overshoot shares one later
  contractor” — \(96\) suffixes, not a family in \(a\); second
  excursion fails from \(n=293\) onward in the window. Ordinary
  terminating orbits, not `MinimalNonTerm` witnesses.
- “first excursion \(O^a E^b\) is that contractor” — \(170\) stays
  above \(n\).
- “\(37\) and \(77\) are even-\(y\) stays” — both have odd \(y\).
  Counted only; not reopened.

## Formalization

`formal/Problems/Juggler/EvenCountThree.lean`. Added:

- `evenCount_oddEvenBlock` / `oddEvenBlock_length`
- `no_cycle_itinerary_oddEvenBlock_one`
- `minimal_first_even_overshoots`
- `cycleMin_oddEvenBlock_starts_two_odds` /
  `cycleMin_first_even_overshoots`

`FloorPower` and `Progress` are not rewritten. Not imported by
`Problems.JugglerPaper`. No `sorry`. No `juggler_reaches_one`.
No universal `overshoot_return_below`. No
`odd_odd_two_excursion_progress`. No cycle engine. No
`PowerHeight`.

## Results

Classification **EVEN_Y_RETURN_SUFFIX_SCATTER**.

The first even residual of a leftover start always overshoots.
That upgrades the odd-to-odd gap; it is not `FiniteProgress`.
On \(n\le 10^4\), the easy even-\(y\) starts \(a\in\{2,3\}\)
replay Paper B. The expanding class \(a\ge 4\) has \(317\)
overshoots, no missing return in the horizon, and no uniform
later word. A cycle of length \(\ge 11\) remains exactly one
`FiniteProgress` failure.

## Open questions

Stop. Do not open odd-\(y\) overshoot, \(K_3\), or another
`non-OOOO` engine contractor.

## Decision

**PARK**. The overshoot corollary is a real theorem and is
recorded. The Phase-0 halt question — a uniform later contractor
on first-E overshoot with even \(y\), novelty only at \(a\ge 4\) —
fails by suffix scatter. This is not a halt result and not a
longer cycle bound.

Best next question: stop.

## Publication assessment

Status: `EXPLORATORY`. A leftover-class sharpening plus a
negative halt fragment, not a paper candidate and not a Juggler
totality result.

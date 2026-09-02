# Juggler first-E transport of the two-even tail

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment and not a claim that
every positive integer reaches 1. It is not a length-8 or length-9
census, not a bunched-tail programme, and not induction on \(n\) or
on the period.

## Problem

Once both two-even leftover families are excluded, do three-even
leftovers with a long second gap die as `CycleMin` by transporting
that tail across the first even letter?

## Exact statement

On a `CycleMin` the even-terminating word is
\(O^{a_0}EO^{a_1}\cdots EO^{a_{e-1}}E\). Bootstrap already kills
\(a_{e-1}\ge 2\). A three-even leftover has \(a_0\ge 2\) and
\(a_2\in\{0,1\}\). It is **gapped** when the remainder after the
first \(E\) is a two-even leftover family:

- \(O^aEO^bEE\) with \(a\ge 2\), \(b\ge 4\) (remainder \(O^bEE\),
  length \(b+2\ge 6\));
- \(O^aEO^bEOE\) with \(a\ge 2\), \(b\ge 3\) (remainder \(O^bEOE\),
  length \(b+3\ge 6\)).

Write \(y=T_{O^aE}(n)\). `CycleMin` gives \(y\ge n\). The leftover
cell is measured against the cycle start \(n\), so

\[
y^{3^{\ell-2}}<2^{e_{\ell-2}}(n+1)^{2^\ell}
\le 2^{e_{\ell-2}}(y+1)^{2^\ell},
\]

where \(\ell\) is the remainder length. The shared two-even tail at
\(y\) is the opposite inequality. Phase 0 asks whether this
contradiction fires whenever \(y\ge 256\), whether \(2\le n<256\)
is empty on the finite window \(k=9,\ldots,16\), and whether
\(k\ge 17\) is sealed by seven consecutive odds.

This is not a `CycleItinerary` theorem on those itineraries (a non-minimum
start may have \(y<n\)). It is not a length-8 or length-9 census
and not a halt theorem. There is no
`no_cycle_itinerary_length_eight` and no `no_cycle_itinerary_length_nine`.

## Current literature

- Leftover length-six and length-seven orientations —
  **EXACT — LEAN VERIFIED**.
- Uniform two-even leftover families —
  **EXACT — LEAN VERIFIED** (`no_cycle_itinerary_two_even_ee`,
  `no_cycle_itinerary_two_even_eoe`, `shared_two_even_tail`).
- Internal-E bootstrap —
  **EXACT — LEAN VERIFIED**. Last gap \(a_{e-1}\ge 2\).
- `CycleMin` scale barrier —
  **EXACT — LEAN VERIFIED**. \(y\ge n\) after any prefix.
- Length-9 three-even leftovers —
  **COMPUTATIONALLY VERIFIED** as prefix-cell tails. The two
  \(a=2\) words are the \(k=9\) gapped cases; transport was
  recorded there as a `CycleMin` simplification, not a method.
- Prefix-OOO extra scale from \(n=3\) —
  **REFUTED**. That `CLOSE` is not reopened.

Project relationship: **extended**. This is step (ii) of the
even-count attack, after the uniform \(e=2\) families.

## Branch budget

```text
Mathematical target     Do gapped three-even CycleMins die by
                        first-E transport of the two-even tail?
Novelty hypothesis      y≥n tightens the leftover cell against
                        the shared tail at y; k≥17 small-n is
                        seven-odd on the prefix or the remainder
Falsifier               A CycleMin realization; y≥n failing to
                        close the tail; a k≥17 small-n leak
Existing machinery      uniform two-even Lean; CycleMin;
                        trailing-even / last-odd cells
Maximum Phase-0 scope   classify gapped vs bunched; verify the
                        chain; CycleItinerary tables for k=9..16
                        below 256; seven-odd split for k≥17.
                        No Lean, no length-8/9 census, no
                        bunched-tail attack, no halt
Promotion criterion     Chain valid, finite window empty, k≥17
                        sealed; bunched remainder named
Stop criterion          A realization; chain gap; a census;
                        bunched-tail machinery
```

Phase 1 (this branch): Lean-exclude both gapped `CycleMin`
families. No length-8/9 census, no bunched tails, no halt.

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- remainder after the first \(E\) of a leftover with \(c\in\{0,1\}\)
  is \(O^bEE\) or \(O^bEOE\) —
  **EXACT — HUMAN PROOF**
- gapped iff \(b\ge 4\) (EE) or \(b\ge 3\) (EOE) —
  **EXACT — HUMAN PROOF**
- `CycleMin` gives \(y\ge n\), which tightens the leftover cell
  and contradicts the shared tail at \(y\) once \(y\ge 256\) —
  **EXACT — LEAN VERIFIED** (`no_cycleMin_gapped_three_even_ee`,
  `no_cycleMin_gapped_three_even_eoe`)
- transport requires \(y\ge n\); it does not exclude a
  non-minimum `CycleItinerary` start —
  **EXACT — HUMAN PROOF**
- for \(k\ge 17\), a gapped leftover has \(a\ge 7\) or \(b\ge 7\),
  so \(n<256\) dies by seven odds —
  **EXACT — HUMAN PROOF**
- 72 gapped words at lengths \(9\le k\le 16\) have no `CycleItinerary`
  on \(2\le n<256\); the Lean tables cover the short-gap
  \(a,b\le 6\) window, and longer gaps are seven-odd —
  **EXACT — LEAN VERIFIED**
- bunched remainder is \(b\le 3\) (EE) or \(b\le 2\) (EOE),
  independent of \(k\) —
  **EXACT — HUMAN PROOF**
- every three-even cycle itinerary is impossible — not claimed
- no cycle of length eight or nine — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.first_e_transport`
- Records: [juggler_first_e_transport.md](../research/juggler_first_e_transport.md),
  [juggler_first_e_transport.json](../research/juggler_first_e_transport.json)
- Tests: `tests/research/juggler_sequence/test_first_e_transport.py`
- The Research Engine control layer is not modified.
- No cycle-state search. No length-8 or length-9 census.
- Gapped `CycleMin` Lean is in `FirstETransport.lean`. No
  bunched-tail Lean. Paper A records the transport as Theorem 3.13.

## Conjectures

None opened.

## Counterexamples

None to the transport chain or to the empty finite window. The
stronger claims that remain false or unproved:

- “first-E transport excludes the itinerary as `CycleItinerary` at a
  non-minimum start” — false as stated; \(y<n\) loosens the cell.
- “rotation of a gapped leftover is again gapped” — false.
  Length-9 leftovers with \(b\ge 2\) share a necklace with a
  bootstrap itinerary.
- “induction on the period reduces \(e=3\) to \(e=2\)” — still
  false. This is a `CycleMin` reduction on even-count, not on
  period.
- “every three-even leftover dies” — not claimed. Bunched
  \(a_1\)-short leftovers remain.
- “\(N_0\) tends to 2” — still **REFUTED** on the two-even tail.

## Formalization

`formal/Problems/Juggler/FirstETransport.lean` excludes the gapped
`CycleMin`s: `no_cycleMin_gapped_three_even_ee` and
`no_cycleMin_gapped_three_even_eoe`. Large \(y\) is the shared
two-even tail at the leftover start; \(n<256\) is seven-odd or
the short-gap `native_decide` tables in
`FirstETransportEval.lean`. This is not a `CycleItinerary` theorem at
a non-minimum start. `SmallCycleCensus.lean` still assembles only
through length seven. No `no_cycle_itinerary_length_eight`. No
`no_cycle_itinerary_length_nine`. No bunched-tail Lean. No `sorry`.
No halt theorem. Paper A records Theorem 3.13 as CycleMin-only.

## Results

Classification **FIRST_E_TRANSPORT_GREEN**.

Gapped three-even leftovers are one type: the remainder after the
first \(E\) is a uniform two-even leftover, and `CycleMin` puts
that remainder at \(y\ge n\). Lean now excludes both families as
`CycleMin` for every \(n\ge 2\). Large \(y\) is the shared
two-even tail; below \(256\), short gaps are tables and long
gaps are seven-odd.

The bunched remainder is independent of \(k\): EE leftovers with
\(b\le 3\) and EOE leftovers with \(b\le 2\). At length 9 those
are the seven leftovers that are not `OOEOOOOEE` / `OOEOOOEOE`.

This is a `CycleMin` reduction, not a length-9 census and not a
no-cycles theorem.

## Open questions

`CycleItinerary` exclusion of these gapped leftovers is now Paper A
Theorem 3.21 (`no_cycle_itinerary_gapped_three_even_ee`,
`no_cycle_itinerary_gapped_three_even_eoe`). Theorem 3.13 remains
CycleMin-only. First-E at \(e=4\) is `CLOSE` as a
reparameterization ([first-E at four evens](juggler_first_e_e4.md)).
The thirty-shape remainder is `PARK`
([four-even short-first-gap](juggler_four_even_short_gap.md)).
Rotation and internal-E next-square are `CLOSE`
([length-11 non-pullback](juggler_length11_nonpullback.md)).
Stop on the thirty length-11 leftovers as a leftover-path
target. Do not assemble `no_cycle_itinerary_length_eight` or
`no_cycle_itinerary_length_nine`. Do not claim halt.

## Decision

**PROMOTE**. First-E transport is now a Lean exclusion of every
gapped three-even `CycleMin`. It is not a period-by-period can.
The bunched \(a_1\)-short leftovers are a named remainder, not a
failure of the reduction.

Best next question: bunched-tail cells for the \(a_1\)-short
remainder (\(b\le 3\) EE, \(b\le 2\) EOE), or first-E transport
at \(e\ge 4\).

## Publication assessment

Status: `EXPLORATORY`.

A Lean `CycleMin` exclusion for gapped three-even leftovers,
recorded in Paper A as Theorem 3.13, not a length-9 census and
not a Juggler totality result.

# Juggler realization-set geometry

Status: **EXPLORATORY**

Standalone arithmetic layer on the parked word atlas. It is **not** a
Research Engine control-layer experiment, not a reopening of the
closed PE-factor, residual-future, or sum-rho branches, and not a
claim that every positive integer reaches 1.

## Problem

What arithmetic geometry of the realizing set \(R_w\) causes a
prefix in the Juggler \(O/E\) trie to become unary?

## Exact statement

For a finite itinerary \(w\) and a bound \(N\),

\[
R_w(N)=\{n\le N:\operatorname{follows}(n,w)\}.
\]

The child sets satisfy \(R_{wb}(N)\subseteq R_w(N)\). The observed
degree \(d(w)\) is the number of nonempty children among \(wO\) and
\(wE\). Keep the quantifiers existential. A missing child under a
scan bound is

\[
\texttt{NOT\_FOUND\_WITHIN\_BOUND},
\]

never a forbidden factor, unless a separate arithmetic certificate
exists. Empty children are classified as `SCALE_LIMITED`,
`CELL_EMPTY`, `SEARCH_UNOBSERVED`, or `CERTIFIED_EMPTY`. The three
first rooted holes are `SCALE_LIMITED`.

This says nothing about totality.

## Current literature

- `follows` / `image` / `floorPower` —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.Itinerary` and
  `Dynamics`.
- `even_tower_to_one` —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.Collapse`.
- Inverse-floor cells `even_preimage_iff` / `odd_preimage_iff` /
  `odd_preimage_unique` —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.Preimages`.
- Word atlas prefix trie —
  **PARK** as machinery; graph reading in
  [juggler_atlas_graph.md](../research/juggler_atlas_graph.md).
- Word-language / PE-factor arrangement —
  **CLOSE**. Do not reopen.
- Residual-future quotient —
  **CLOSE**. Do not reopen.
- Global sum-rho / word-statistics —
  **CLOSE**. Do not reopen.

Project relationship: **extended**.

## Branch budget

```text
Mathematical target     What geometry of R_w makes a prefix unary?
Novelty hypothesis      inverse-floor cells or scale of R_w force
                        d(w)=1 by an explicit arithmetic rule
Falsifier               unary without monochrome landings; a square
                        amplification law that survives mixed itineraries;
                        only tautological restatements of landing parity
Existing machinery      follows_itinerary, image_after, even_preimage,
                        odd_preimage_integers, parked atlas continuations
Maximum Phase-0 scope   exact R_w on n<=4000 then n<=1e5; selected
                        roots n<=1e7; child split; prepend cells;
                        interior-state certificates for first holes
Promotion criterion     an explicit A(w),B(w) or cell rule for d(w)=1
                        that is not landing-parity restated
Stop criterion          only scan-bound tautologies; PE-factor,
                        residual-quotient, or sum-rho reopen;
                        automaton; halt claim
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Nested realizing sets \(R_{wb}\subseteq R_w\) —
  **EXACT — HUMAN PROOF** from `follows`
- Append child split by parity of \(T_w(n)\) —
  **EXACT — HUMAN PROOF** (definitional)
- Prepend-\(E\) cell union
  \(R_{Ew}(N)=\bigcup_{q\in R_w(N)}(\mathrm{even\_cell}(q)\cap 2\mathbb{Z}\cap[1,N])\) —
  **EXACT — HUMAN PROOF**, Lean `even_preimage_iff`;
  **COMPUTATIONALLY VERIFIED** on \(n\le 4000\), \(k\le 12\)
- Prepend-\(O\) cell union closed on a finite window —
  **REFUTED**; odd landings escape \([1,N]\)
- \(m(E^r)=2^{2^{r-1}}\) —
  **EXACT — HUMAN PROOF**, Lean `even_tower_to_one`
- \(m(wE)\ge m(w)^2\) for mixed itineraries —
  **REFUTED** on `OOOE` / `OEEE`
- First rooted holes as forbidden factors —
  **REFUTED**; they are `SCALE_LIMITED` with interior witnesses
- Unary iff \(R_w\) is a single interval —
  **REFUTED**; 259 `UNARY_O` prefixes on \(n\le 4000\) are `FRAGMENTED`
- Unary iff landing parity of \(T_w(R_w)\) is monochrome —
  **EXACT — HUMAN PROOF** (definitional on the exact split)

## Experiments

- Probe: `research.juggler_sequence.realization_geometry`
- Diagnostic window: \(n\le 4000\), \(k\le 12\)
- Confirm window: \(n\le 10^5\), \(k\le 12\)
- Selected exact roots: \(n\le 10^7\) for the three first holes
  and their parents
- Atlas: `wa-20260827T200310Z-cuda-k20-n100000000`
- Records: [juggler_realization_geometry.md](../research/juggler_realization_geometry.md)
- Tests: `tests/research/juggler_sequence/test_realization_geometry.py`

No new census. No GPU. No new atlas SQLite tables. No automaton.

## Conjectures

None opened in `conjectures/`.

## Counterexamples

- “`m(wE)\ge m(w)^2` after an odd letter.” False: `OOOE` has
  \(m(\texttt{OOOE})=m(\texttt{OOOOE})=3\); `OEEE` has
  \(m=7\) and \(m(\texttt{OEEEE})=41<49\).
- “A length-6 even-ish word absent as a rooted prefix is forbidden.”
  False: `EEEEEE` occurs inside \(2906\) length-20 realized prefixes,
  at realizing states \(\ge 4294972782\).
- “Unary corridors never regain two children.” False: \(52\) returns
  in the confirm window, and \(5\) atlas `EE…` parents thaw.
- “Unary means \(R_w\) is an interval.” False: diagnostic unary
  nodes include \(259+148\) `FRAGMENTED` sets.
- “Prepend-\(O\) is a closed operator on \(R_w(N)\).” False: on
  \(N=4000\) the empty-word prediction keeps \(126\) odds and
  misses \(1874\).

## Formalization

None added. Certification uses `Collapse.lean` and `Preimages.lean`.
No `sorry`. No automaton.

## Results

Phase 0 is recorded in
[juggler_realization_geometry.md](../research/juggler_realization_geometry.md).
Classification **REALIZATION_GEOMETRY_COMPLEX**.

Appending a letter is the landing-parity filter of \(T_w(R_w)\).
Prepending \(E\) is the even-cell union already in `even_preimage_iff`,
and it is exact on every finite window. Prepending \(O\) leaks the
window. The first holes are `SCALE_LIMITED`, not `CELL_EMPTY`:

| word | certificate | bound |
|------|-------------|-------|
| `EEEEEE` | even tower | \(m=2^{32}>10^8\) |
| `EEEEOE` | interior state | \(10^8<m\le 39062504258660\) |
| `EEEOEO` | interior state | \(10^8<m\le 2608762880\) |

Selected exact roots at \(n\le 10^7\) find no member of any first
hole. `EEEE` looks `UNARY_O` at \(n\le 4000\) only because
\(m(\texttt{EEEEE})=65536\); the atlas class is `BINARY`.

## Open questions

None from this branch. The append rule is `follows`. The prepend-\(E\)
rule is `even_preimage_iff`. Do not reopen PE factors, residual quotients,
or sum-rho.

## Decision

**CLOSE**. Every exact statement is `follows`, `even_preimage_iff`, or
`even_tower_to_one`. The square law does not lift past odd letters.
Unary is not an interval predicate. The first holes are
`SCALE_LIMITED` root absences with interior witnesses, not empty
cells. Do not promote a restatement. Do not invent another scalar.
Do not pursue termination.

Best next question: none from this branch.

## Publication assessment

Status: `EXPLORATORY`. A realizing-set reading of the parked atlas,
not a paper candidate and not a Juggler totality result.

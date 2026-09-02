# Juggler odd-escape two-sided corridor

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a reopen of
the closed pivot-corridor branch, not a second `Scale` layer, not a
relational \(\Sigma\) automaton, not Paper A, and not a claim that
every positive integer reaches 1.

After scalar source descent, episode rank, \(Q\)-sections, and
prefix growth balance failed, the promoted spine left a two-sided
object \(n^L\le x<n^U\). This phase asks whether that object, built
only from proved event lowers and the inherited `EnvelopeState`
upper, constrains leftover odd escape beyond either side alone.

## Problem

Can an indefinitely surviving odd-escape trajectory maintain
compatible lower and upper power bounds forever, or do the two
envelopes necessarily collide after a sufficiently structured
transition?

## Exact statement

For a realized `AboveAnchor` state \(x=T^i(n)\) write
\(\operatorname{EnvelopeState}(n,x)\) as \(x^A\le n^B\) with
\(A=2^i\) and \(B=3^{\#O}\). The integer upper is the smallest
\(U\) with \(B<UA\), i.e. `envelope_lt_pow`. The integer lower
\(L\) is the strongest *proved* event bound that applies:

- even plus next image \(\ge n\) gives \(n^2\le x\)
  (`even_ge_sq_of_aboveAnchor`);
- an `AboveAnchor` even-run of length \(r\) gives \(n^{2^r}\le x\)
  (`aboveAnchor_even_run_ge_pow`);
- `CubeOddLanding` gives \(n^2\le x<n^3\);
- `cube_odd_lift` gives \(n^3\le T(x)<n^5\) (or the tighter
  envelope cell);
- `cube_lift_odd_ge_fourth` gives \(n^4\le T^2(x)\).

Do not manufacture \(L>1\) from \(x\ge n\). Phase 0 asks whether
the pair \((L,U)\) on the named residuals

\[
37,69,89,365,501,1517,6187
\]

and the interior chain

\[
3375\to 196069\to 86818724\to 9317
\]

is a new progress variable \(\Gamma=U-L\), or a reparameterization
of the named cube/even lemmas.

This is not a halt theorem.

## Current literature

- Pivot stay-above corridor
  \(x^{2^r}\le n^{3^o}\) and \(n^{2^s}\le x^{3^q}\) —
  **CLOSE** (`juggler_corridor.md`, `CORRIDOR_REPACKAGING`).
  A different object: the reverse word typically gives \(L<1\).
- `EnvelopeState` / `envelope_lt_pow` —
  **EXACT — LEAN VERIFIED** (`J-envelope-lt-pow`)
- `PowerCorridor` / `envelope_corridor_contradiction` —
  **EXACT — LEAN VERIFIED** (architecture packaging)
- `AboveAnchor` / `aboveAnchor_even_run_ge_pow` —
  **EXACT — LEAN VERIFIED** (`J-above-anchor`)
- Cube-not-square split and `CubeOddLanding.corridor` —
  **EXACT — LEAN VERIFIED** (`J-cube-not-square-split`)
- Cube-odd lift \([n^3,n^5)\) and even reset —
  **EXACT — LEAN VERIFIED** (`J-cube-odd-even-reset`)
- Source-relative odd reset —
  **REFUTED** (`J-source-relative-odd-reset`); the \(3375\)
  chain is reused here only as a corridor-language test
- Prefix growth/retention balance —
  **CLOSE** (`juggler_growth_balance.md`)
- OEIS A007320 (`oeis-A007320`): step counts to 1. **known**.
  Totality is not claimed

Project relationship: **extended**, then **reparameterized**. The
designated question after the envelope/corridor spine packaging.

## Branch budget

```text
Mathematical target     On a realized AboveAnchor residual, does a
                        proved event-triggered lower power L>1 plus
                        an EnvelopeState upper U give a corridor
                        n^L <= x < n^U whose gap constrains odd
                        escape beyond either side alone?
Novelty hypothesis      History/event lowers compose with the
                        inherited upper envelope to a transition
                        law on Gamma = U-L
Falsifier A             every generic odd lower collapses to x>=n
Falsifier B             Gamma oscillates with no structural
                        restriction
Falsifier C             every collision is already FiniteProgress
Falsifier D             (L,U,parity) repeats while x unbounded
Falsifier E             named residuals share no lower-envelope
                        relation
Existing machinery      EnvelopeState, PowerCorridor, AboveAnchor,
                        even_ge_sq_of_aboveAnchor,
                        aboveAnchor_even_run_ge_pow, CubeOddLanding,
                        cube_odd_lift, cube_lift_odd_ge_fourth
Maximum Phase-0 scope   audit table + named-start probe; no Lean;
                        no Scale; no Sigma automaton
Promotion criterion     a proved L>1 on an odd residual that is
                        not already cube_odd_lift / fourth, or a
                        one-way (L,U,parity) law that is not
                        FiniteProgress in disguise
Stop criterion          Falsifier A or C; machinery gravity;
                        halt claim; reopen of juggler_corridor.md
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- \(L=1\) from \(x\ge n\) — **REPARAMETERIZATION** of
  `AboveAnchor` (flagged `trivial_anchor`, not a theorem)
- even \(L=2\) — **EXACT — LEAN VERIFIED**
  (`even_ge_sq_of_aboveAnchor`)
- even-run \(L=2^r\) — **EXACT — LEAN VERIFIED**
  (`aboveAnchor_even_run_ge_pow`)
- `CubeOddLanding` \([2,3)\) — **EXACT — LEAN VERIFIED**
- `cube_odd_lift` \([3,5)\) — **EXACT — LEAN VERIFIED**;
  the itinerary envelope often tightens the integer upper to \(4\)
- `cube_lift_odd_ge_fourth` \(L=4\) — **EXACT — LEAN VERIFIED**
- \(\Gamma=U-L\) as an independent Lyapunov function —
  **REFUTED** on the named set (oscillates on \(37\); holds at
  width \(1\) on leftovers; corridor types recur with growing
  \(x\))
- even reset \(U<2L\Rightarrow T(x)<n^{U/2}\) —
  **REPARAMETERIZATION** of `even_below_anchor_pow`
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.odd_escape_corridor`
- Records: [juggler_odd_escape_corridor.md](../research/juggler_odd_escape_corridor.md),
  [juggler_odd_escape_corridor.json](../research/juggler_odd_escape_corridor.json)
- Tests: `tests/research/juggler_sequence/test_odd_escape_corridor.py`

No CLI. No Lean. No \(\Sigma\) automaton. No arbitrary power search.

## Conjectures

None opened.

## Counterexamples

“A generic odd residual has a proved lower \(L>1\)” is false.
On every named start the states at \(i=0,1\) are
`trivial_anchor`. The first \(L>1\) event is the \(i=2\) landing
after `OO`: cube-odd on \(37\), cube-even on
\(69,89,365,501,1517,6187\).

“\(\Gamma\) shrinks when \(x\) grows on \(3375\to 9317\)” is
false. Both endpoints are the same cell \([n^2,n^3)\) with
\(\Gamma=1\), while \(9317>3375\).

“A repeated corridor type is arithmetic recurrence” is false.
The cell \([2,3)\) odd recurs at \(3375,9317,2233\) on the
\(37\)-orbit with unbounded (relative to the cell) \(x\). That is
scale recurrence, not `CycleMin`.

## Formalization

None added. Existing `Envelope`, `Corridor`, and
`MinimumRelative` already contain the cells. No
`OddEscapeCorridor.lean`. No `CorridorGap.lean`. Do not add
`LowerPowerBound` (that name is a different coarse object in
`Preimages.lean`). Paper A is unchanged. No `sorry`.

## Results

Classification **ODD_ESCAPE_CORRIDOR_CLOSED**.

### Lower-envelope audit

| Statement | Needs | Bound vs \(x\ge n\) |
|-----------|--------|---------------------|
| `aboveAnchor_iterate_ge` | `AboveAnchor` | equal (\(L=1\)) |
| `even_run_exit_ge` | `MinimalNonTerm` | equal (\(L=1\)) |
| `even_run_pow_le` | `follows` | exponent on \(T^r(m)\), not \(n^L\le x\) |
| `even_ge_sq_of_aboveAnchor` | `AboveAnchor` + even | \(n^2\) |
| `aboveAnchor_even_run_ge_pow` | `AboveAnchor` + \(E^r\) | \(n^{2^r}\) |
| `minimal_nonterm_even_ge_sq` and wrappers | `MinimalNonTerm` | same via `aboveAnchor_of_minimalNonTerm` |
| `CubeOddLanding` | cube band + odd | \([n^2,n^3)\) |
| `cube_odd_lift` | `CubeOddLanding` | \([n^3,n^5)\) |
| `cube_lift_odd_ge_fourth` | cube-odd then odd | \(n^4\le T^2(x)\) |
| `even_cube_not_square` | cube band + even | reset into \([n,n^2)\) |
| `Cells.LowerPowerBound` | leftover cells | different object |

### Named-start census

Every start has first \(L>1\) at step \(i=2\). Leftovers land
even in the cube band. The \(37\) laboratory lands odd there.

On leftovers, every nontrivial cell has width \(\Gamma=1\):
\([2,3)\), or a lift tightened by the itinerary envelope to
\([3,4)\) or \([4,5)\). Even-reset \(U<2L\) fires exactly on
those named even cells and is `even_below_anchor_pow`. No
realized prefix has \(U\le L\).

The \(37\) chain in corridor language is

\[
[2,3)\xrightarrow{O}[3,4)\xrightarrow{O}[4,6)\xrightarrow{E}[2,3).
\]

The integer lift upper \(5\) is not sharp: `envelope_lt_pow`
already gives \(U=4\) at \(196069\). The even state
\(86818724\) has \(L=4\) from `cube_lift_odd_ge_fourth` and
\(U=6\) from the itinerary envelope; \(U<2L\) resets into the cube
band at \(9317\), which is larger than \(3375\). \(\Gamma\)
holds at \(1\) on that pair and later oscillates
(\(1,2,5,3,1\)). The type \([2,3)\) odd recurs with growing
\(x\).

This is Falsifier A on generic odd states, Falsifier C on
collisions, and Falsifier D on corridor recurrence. It is not a
new lower-envelope theorem.

## Open questions

None from two-sided corridor width. Do not build a relational
\(\Sigma\) automaton. Do not add `OddEscapeCorridor.lean`. Do
not reopen the pivot corridor, source-relative reset, or prefix
growth balance. The leftover hole is unchanged: a cube cell
without a square cell.

## Decision

**CLOSE**. Every nontrivial two-sided cell on the named residuals
is `CubeOddLanding`, `cube_odd_lift` (sometimes with a tighter
`envelope_lt_pow` upper), `cube_lift_odd_ge_fourth`,
`even_ge_sq_of_aboveAnchor`, or `aboveAnchor_even_run_ge_pow`.
Generic odd states stay `trivial_anchor` until one of those
events. \(\Gamma\) is not a Lyapunov function: leftovers sit at
width \(1\), the \(37\) laboratory oscillates, and corridor
types recur while \(x\) grows. A branch of that kind is a close.

Best next question: taken up and closed in
[juggler_above_anchor_first_fail.md](juggler_above_anchor_first_fail.md).
The residual hole is still a cube cell without a square cell.

## Publication assessment

Status: `EXPLORATORY`.

A negative two-sided-gap fragment. Not a paper candidate and not
a Juggler totality result.

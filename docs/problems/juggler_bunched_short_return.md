# Juggler exact short-cluster return sets

Status: **EXPLORATORY**

Standalone application phase on the Juggler floor-power map. It is
**not** a Research Engine control-layer experiment, not a leftover-suffix
path table, not a predecessor-cell interval census, not a \(Z_5\)
family, not a length-11 assembler, not a four-even leftover cell, and
not a claim that every positive integer reaches 1.

## Problem

After the predecessor-cell attack on bunched-short last clusters is
**PARK** — because the stronger statement \(S_{b,c}(y)\notin[n,y]\)
is false — does exact cycle closure

\[
T_{O^bEO^cE}(y)=n
\]

force an arithmetic condition incompatible with a `CycleMin` prefix
landing \(y=T_u(n)\)?

## Exact statement

Let
\[
S=\{(0,0),(1,0),(2,0),(3,0),(0,1),(1,1),(2,1)\}
\]
and
\[
R_{b,c}(n)=\{y\ge n:T_{O^bEO^cE}(y)=n\}.
\]
The Phase-0 questions are:

1. What is the exact even inverse of \(n\), and is it the singleton
   \(\{n^2\}\)?
2. What is the exact odd inverse of \(n^2\), and how many integers
   occupy
   \[
   n^{4/3}\le z<(n^2+1)^{2/3}?
   \]
3. For each \((b,c)\in S\), what is the exact backward equation for
   \(y\in R_{b,c}(n)\), organised by \(c=0\) versus \(c=1\)?
4. Is \(R_{b,c}(n)\) disjoint from the landings of admissible
   `CycleMin` prefixes?

This is not the parked interval statement \(S_{b,c}(y)\notin[n,y]\).
It is not a `CycleItinerary` theorem at a non-minimum start, not a
four-even cell, and not a halt theorem.

## Current literature

- Last-cluster split —
  **EXACT — HUMAN PROOF** (`J-cyclemin-last-cluster`).
- Last two-even leftover after an arbitrary prefix —
  **EXACT — LEAN VERIFIED**.
- Last three-even bunched leftover after an arbitrary prefix —
  **EXACT — LEAN VERIFIED**. Those theorems start at
  \(a\ge a_{\min}\).
- Leftover-suffix path table on \(a<a_{\min}\) —
  **REFUTED** (`J-cyclemin-bunched-short-path`).
- Predecessor cells / interval seal —
  **PARK** (`J-cyclemin-short-front-census`). Four leaks with
  \(S>n\).
- Front overshoot plus later `OO` —
  **PARK** (`J-cyclemin-front-oo-raise`).
- Even / odd one-step preimages —
  **EXACT — LEAN VERIFIED**
  (`floorPower_even_eq_iff_sq_interval`,
  `floorPower_odd_eq_iff_cube_interval`, `odd_preimage_unique`).
- Last even landing of a cycle is not an odd square —
  **EXACT — LEAN VERIFIED** (`cycle_last_even_ne_odd_sq`).

Project relationship: **extended**. The designated next question of
the parked predecessor-cell branch.

## Branch budget

```text
Mathematical target     Characterize R_{b,c}(n) exactly and test
                        R ∩ CycleMin prefix landings
Novelty hypothesis      the seven short tails have extremely
                        narrow exact preimage sets, incompatible
                        with the constraints already on y
Falsifier               an abundant exact-return family; a fat
                        odd cell of n^2; no rigidity beyond y≥n
Existing machinery      even/odd one-step preimages; odd_preimage_unique;
                        cycle_last_even_ne_odd_sq; CycleMin
Maximum Phase-0 scope   exact inverses; |R| census; CycleMin
                        exact hits; no Lean, no Z5, no interval
                        census
Promotion criterion     reusable exclusion of form A/B/C:
                        impossible arithmetic; CycleMin+return
                        ⊥; or tiny R plus a general CycleMin
                        argument
Stop criterion          another interval/cell census; only
                        S>n; seven unrelated word lemmas; a new
                        modulus; Z5 / length-11 / four-even
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- even inverse of \(n\) is the singleton \(\{n^2\}\) —
  **REFUTED**. \(T_E(z)=n\) iff \(z\) is even and
  \(n^2\le z<(n+1)^2\) (`floorPower_even_eq_iff_sq_interval`).
  Interval length \(2n+1\). On a `CycleMin`, \(n\) is odd, so
  \(n^2\) is odd and cannot be the last even landing
  (`cycle_last_even_ne_odd_sq`)
- odd inverse of \(n^2\) is a uniformly fat set —
  **REFUTED**. `odd_preimage_unique` gives at most one integer.
  Through \(n\le 500\) the odd cell of \(n^2\) is empty for 477
  values, even-blocked for 10, and odd for 12
  (`J-cyclemin-short-odd-square-preimage`)
- \(\lfloor z^{3/2}\rfloor=n^2\) is the CycleMin last-odd
  condition —
  **REFUTED** as a CycleMin equation. CycleMin \(n\) is odd, so
  \(n^2\notin[n^2,(n+1)^2)\cap 2\mathbb{Z}\). The last odd step
  of an `EOE` tail must hit some even in the last-even one-step preimage
- last-odd layer of the last-even one-step preimage is tiny —
  **COMPUTATIONALLY VERIFIED** through \(n\le 48\): empty for
  15 values, size at most 2
- all seven \(R_{b,c}(n)\) are extremely narrow —
  **REFUTED**. \(R_{0,0}(n)\) has order \(n^3\)
  (\(|R_{0,0}(12)|=2041\), \(|R_{0,0}(13)|=2379\)). The \(c=1\)
  families are thin; \(R_{2,1}\) is almost empty
- `CycleMin` \(n\) (\(u{+}{+}O^bEO^cE\)) for two-even
  isolated-odd fronts on \(12\le n<64\) —
  **COMPUTATIONALLY VERIFIED** empty of exact returns
  (one prefix landing, no short tail follows)
- bunched-short `CycleMin` is impossible — not claimed
- every cycle itinerary is impossible — not claimed
- global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.bunched_short_return`
- Records: [juggler_bunched_short_return.md](../research/juggler_bunched_short_return.md),
  [juggler_bunched_short_return.json](../research/juggler_bunched_short_return.json)
- Tests: `tests/research/juggler_sequence/test_bunched_short_return.py`
- No Lean. Not imported by `Problems.JugglerPaper`. No
  `sorry`. No halt theorem.

## Conjectures

None opened.

## Counterexamples

The Attack-1 singleton \(z=n^2\) is **REFUTED** by the even
floor cell. Witness: \(n=13\) has last-even one-step preimage
\([169,196)\) and even preimages \(\{170,172,\ldots,194\}\).

The hypothesis that every short family has a tiny exact
preimage set is **REFUTED** by the `EE` fibre:
\[
|R_{0,0}(n)|=\sum_{\substack{w\text{ even}\\n^2\le w<(n+1)^2}}
\#\{\,y\text{ even}:w^2\le y<(w+1)^2\,\},
\]
which is of order \(n^3\).

Exact odd return to the square edge is rare, not abundant.
The twelve odd hits through \(n\le 500\) are
\( (6,11),\ (15,37),\ (27,81),\ (79,339),\ (125,625),\ (150,797),\ (165,905),\ (168,927),\ (188,1077),\ (273,1771),\ (276,1797),\ (343,2401) \).
That list does **not** control CycleMin last-odd return.

Named exact returns that are not CycleMin fronts include
\(R_{1,1}(12)=\{91,93\}\) and \(R_{2,1}(6)=\{9\}\).

The stronger claims that remain false or unproved:

- “\(T_E(z)=n\) forces \(z=n^2\)” — false.
- “\(\lfloor z^{3/2}\rfloor=n^2\) is the CycleMin last-odd
  equation” — false for odd \(n\).
- “every \(R_{b,c}\) is a finite exceptional set” — false for
  \(c=0\).
- “\(S_{b,c}(y)\notin[n,y]\)” — already **REFUTED** on the
  parked front branch; not retested here.
- “every last-cluster class is now excluded” — false.
- “every cycle itinerary is impossible” — not claimed.

## Formalization

None. Existing `Preimages.lean` and `CycleCore.lean` lemmas are
cited, not rewritten. No `no_cycleMin_prefix_short`. No
`no_cycleMin_four_even`. No `no_cycle_itinerary_length_eleven`. No
`no_juggler_cycle`. Paper A is unchanged.

## Results

Classification **SHORT_RETURN_PARK**.

Exact backward equations, derived from `floorPower` rather
than from a singleton-square ansatz:

| \((b,c)\) | necessary condition for exact return |
|---|---|
| \((0,0)\) | \(y\) even in the `EE` fibre of \(n\) |
| \((1,0)\) | \(T_O(y)\) even in that `EE` fibre |
| \((2,0)\) | \(T_{OO}(y)\) even in that `EE` fibre |
| \((3,0)\) | \(T_{OOO}(y)\) even in that `EE` fibre |
| \((0,1)\) | \(T_E(y)\) odd in the last-odd layer of the last-even one-step preimage |
| \((1,1)\) | \(T_O(y)\) even and \(T_{OE}(y)\) in that last-odd layer |
| \((2,1)\) | \(T_{OO}(y)\) even and \(T_{OOE}(y)\) in that last-odd layer |

The `EE` fibre is abundant. The last-odd layer is thin (size
\(\le 2\) for \(n\le 48\)). Odd cells of \(n^2\) are almost
empty, but they are the wrong edge for CycleMin. One
two-even CycleMin-shaped landing occurs below 64
(\(37\xrightarrow{\mathtt{OOOOEOOOE}}4990602\)); no short tail
follows it, and there is no exact hit.

This is not \(Z_5\), not a length-11 census, not a four-even
assembler, and not a halt theorem.

## Open questions

The leftover-suffix, predecessor-cell, front-overshoot, and
defect-closure attacks remain parked
([juggler_bunched_short.md](juggler_bunched_short.md),
[juggler_bunched_short_front.md](juggler_bunched_short_front.md),
[juggler_front_overshoot.md](juggler_front_overshoot.md),
[juggler_bunched_short_defect.md](juggler_bunched_short_defect.md)).
The isolated-odd prefix attack is **CLOSE**
([juggler_isolated_odd_return.md](juggler_isolated_odd_return.md)).
Do not write \(Z_5\). Do not assemble
`no_cycle_itinerary_length_eleven`. Do not reopen four-even cells
or the interval seal \(S\notin[n,y]\).

## Decision

**PARK**. Exact return is rigid at the last odd step and fat
at `EE`. That is a genuine characterisation of \(R_{b,c}(n)\),
not an empty intersection \(R\cap P=\varnothing\) and not a
reusable A/B/C exclusion. Terminal arithmetic alone does not
control the seven-family class. Do not claim that every cycle
word is impossible.

Best next question: answered in
[juggler_isolated_odd_return.md](juggler_isolated_odd_return.md)
and [juggler_isolated_odd_fibre.md](juggler_isolated_odd_fibre.md).
Isolated-odd prefixes cannot land in \(R_{b,c}(n)\). The leftover
question is a `CycleMin` prefix with \(a_0\ge 2\).

## Publication assessment

Status: `EXPLORATORY`.

A named exact-return census plus a refuted singleton-square
ansatz. Not a paper candidate and not a Juggler totality
result.

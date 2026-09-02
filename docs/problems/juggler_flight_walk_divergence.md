# Juggler flight walk-divergence (Paper B × hug flights)

Status: **PROMOTE** (walk-divergence theorem recorded; the Paper B
route is answered negatively and stays closed)

The above-anchor branch's standing question: can the proved
depth-\(\le 4\) parity layer of Paper B kill extremal hug-hugging
descent-free flights the way the parity/walk finance killed short
cycle leftovers? Answer: Paper B cannot (its proved layer is
ambient-density and the ambient-to-orbit transfer is REFUTED,
`TRANSFER_COMPLEX`), but the extremal flights die anyway,
unconditionally, by pigeonhole plus the strict expansion of realized
period words. Not a halt theorem, not a divergent-orbit existence
claim, and not a Paper A or Paper B edit.

## Problem

A descent-free flight is an infinite orbit \(x_0=n\ge 2\),
\(x_{k+1}=T(x_k)\), with \(x_k\ge n\) for all \(k\). Its exponent
walk is \(u_k=a_k\log_2 3-k\) (\(a_k\) = odd letters among the first
\(k\)). The above-anchor layer proves the floor \(u_k\ge 0\) and hug
domination \(a_k\ge\mathrm{hugOdds}(k)\) (Lean). The extremal
adversary is the *hug-hugging* flight: one whose walk stays within a
bounded band above the hug walk (which itself sits in
\([0,\log_2 3)\), Lean `hugOdds_pow_ge` / `hugOdds_pow_lt`). Does any
proved layer kill it?

## Exact statement

**Theorem (flight walk-divergence; EXACT — HUMAN PROOF, components
Lean).** Every descent-free flight has unbounded exponent walk:
\(\sup_k u_k=\infty\). Consequently no descent-free flight stays
within bounded excess of the hug itinerary.

*Proof.* Suppose \(u_k\le B\) for all \(k\). The defect-free upper
envelope (Lean `power_bound_word` / `follows_log_le_walkWeight`)
gives \(x_k\le n^{2^{u_k}}\le n^{2^B}\), so the flight visits
finitely many states. Determinism supplies the uniqueness lemma
below: a first repetition closes a cycle, and until then every
state is a new integer in the finite window
\([n,n^{2^B}]\). Hence the flight is eventually periodic
(pigeonhole of a finite injective prefix). Its period word \(v\)
(length \(p\ge 1\), \(o\) odds) is a realized return
\(T^p(x_i)=x_i\) with \(x_i\ge 2\), hence strictly expanding:
\(2^p<3^o\) (Lean `cycle_strict_envelope`; \(3^o=2^p\) is
impossible by unique factorization and a contracting return
contradicts itself). So each traversal adds
\(\delta=\log_2(3^o/2^p)>0\) to the walk: \(u_{i+tp}=u_i+t\delta\to
\infty\), contradiction. Since the hug walk is bounded
(\(u^{\mathrm{hug}}_k<\log_2 3\)), the excess
\(a_k-\mathrm{hugOdds}(k)\ge(u_k-\log_2 3)/\log_2 3\) is unbounded.
\(\square\)

**Lemma (flight uniqueness; EXACT — HUMAN PROOF; KNOWN
determinism).** If \(x_i=x_j\) with \(i<j\), then
\(x_{i+t}=x_{j+t}\) for all \(t\ge 0\). Hence if \(r\) is the first
repeated index, \(x_0,\ldots,x_{r-1}\) are pairwise distinct and
\(x_r\) is the first return. This is a finite-flight combinatorial
constraint, independent of the envelope. The pigeonhole above is
exactly this lemma on a finite admissible window: a long
descent-free prefix without repetition cannot outrun
\(\#\{n,\ldots,n^{2^B}\}\).

**Corollary (flight dichotomy at the laboratory frontier).** A
descent-free flight necessarily starts at
\(n>162\,849\,448\) (the certified floor: every smaller start
reaches \(1\), `J-residual-floor-one-hundred-sixty-two-million` on
top of `J-residual-floor-twenty-six-million`). The distinction is
not really bounded versus unbounded states. It is

\[
\text{finite injective prefix + closure}
\quad\text{versus}\quad
\text{infinite injective trajectory,}
\]

and exactly one of:

1. **closure** — a first repetition occurs; the preperiod is
   pairwise distinct in \(\{n,n+1,\ldots\}\) and the flight enters
   a nontrivial cycle with minimum \(>162\,849\,448\) and period
   \(\ge 478\,245\)
   (`J-cycle-period-four-hundred-seventy-eight-thousand`); its walk
   diverges linearly at the cycle's expansion rate
   \(\delta/p\); or
2. **infinite injective trajectory** — no state ever repeats, so
   \(\limsup_k x_k=\infty\): a genuinely divergent orbit
   (`J-flight-divergent-structure` upgrades this to pointwise
   \(x_k\to\infty\) and linear peak growth).

In particular the "flat" hug-hugging flight — walk in a band, states
forever in \([n,n^3)\) (the hug band exponent is exactly
\(2^{1+\log_2(3/2)}=3\)) — does not exist below the cycle frontier:
any such object *is* a cycle and inherits every cycle obstruction.

**Scope guard.** The theorem constrains descent-free flights only.
An orbit realizing the hug itinerary while dipping below its anchor
(a defect descent — never observed, not disproved) is outside the
statement. The hug-cylinder question (finite hug prefixes realized
at every depth, \(C_L\neq\emptyset\)) is untouched: realizing every
finite prefix from different starts is compatible with the infinite
hug flight being impossible.

## Current literature

- Above-anchor walk floor \(u_k\ge 0\), hug domination — **EXACT —
  LEAN VERIFIED** (`aboveAnchor_prefix_pow_le` in `CycleCore.lean`,
  `aboveAnchor_odds_ge_hug` in `AboveAnchorWalk.lean`)
- Flight envelope (two-sided transport on above-anchor prefixes) —
  **EXACT — LEAN VERIFIED** (`J-flight-envelope-transport`,
  `WalkTransport.lean`)
- Hug band \(0\le u^{\mathrm{hug}}_k<\log_2 3\) — **EXACT — LEAN
  VERIFIED** (`hugOdds_pow_ge`, `hugOdds_pow_lt`)
- Strict expansion of realized returns — **EXACT — LEAN VERIFIED**
  (`cycle_strict_envelope`, `Envelope.lean`)
- Certified floor (reach-1 to \(26\,254\,995\), first passage to
  \(162\,849\,448\), hence reach-1 by descent induction) —
  **COMPUTATIONALLY VERIFIED**
- Period bound \(\ge 478\,245\) for all nontrivial cycles —
  **COMPUTATIONALLY VERIFIED**
  (`J-cycle-period-four-hundred-seventy-eight-thousand`)
- Paper B depth-\(\le 4\) parity equidistribution (ambient, power
  savings; certified \(\le 4\)-step descent density \(13/16\)) —
  **EXACT — HUMAN PROOF**; laboratory length-5 repair lifts the
  certified class to \(7/8\) (`J-five-step-descent-density`) —
  **EXACT — HUMAN PROOF**, not imported into Paper B
- Ambient-to-orbit parity transfer — **CLOSE**, `TRANSFER_COMPLEX`
  (`juggler_parity_discrepancy_transfer`): no \(|I|\)-uniform bound,
  monochromatic run counterexample, generated images fragmented
- Paper A × Paper B merge — **CLOSE** (`juggler_cycle_paper_merge`)

Project relationship: **extended** (answers the above-anchor
branch's best next question; first flight-level consequence of the
cycle period bound).

## Branch budget

```text
Mathematical target    can the proved Paper B depth-≤4 layer kill
                       extremal hug-hugging descent-free flights?
Novelty hypothesis     the hug-domination floor is new since Paper B;
                       its proved layer might constrain open flights
                       pointwise
Falsifier              every route reduces to the REFUTED ambient→
                       orbit transfer or the parked K3/JJ wall
Existing machinery     power_bound_word, cycle_strict_envelope,
                       hugOdds_pow_ge/lt, certified floor 162849448,
                       period bound 478245, transfer refutation
Maximum Phase-0 scope  analysis + one light exact probe (hug band,
                       survivor drift table, escape times); dossier,
                       ledger row, journal; no Paper A/B edits, no
                       new Lean (components cited)
Promotion criterion    a theorem killing the bounded-excess flight
                       class, or a pointwise Paper B consequence
Stop criterion         everything reduces to transfer/K3 → CLOSE
```

## Balanced-ternary formulation

None required. The walk lives on the exponent lattice; the map is on
ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Exponent walk \(u_k=a_k\log_2 3-k\); upper envelope
  \(x_k\le n^{2^{u_k}}\) — **EXACT — LEAN VERIFIED**
- Strict expansion of realized period words \(2^p<3^o\) — **EXACT —
  LEAN VERIFIED** (`cycle_strict_envelope`)
- Per-period walk drift \(\delta=\log_2(3^o/2^p)>0\) — exact integer
  verdicts in the probe for all hug pairs at the leftover /
  survivor-lattice lengths
- Pigeonhole eventual periodicity of bounded flights — **EXACT —
  HUMAN PROOF** (infinite-object glue; the lab's Lean idiom is
  finite itineraries, packaging not attempted). The uniqueness lemma
  (pairwise-distinct preperiod until first return) is the
  combinatorial content of that pigeonhole.
- No divergent orbit exists / all flights killed — not claimed

## Experiments

- Probe: `research.juggler_sequence.flight_walk_divergence`
- Artifact: `data/research/juggler/flight_walk_divergence/summary.json`
- Tests: `tests/research/juggler_sequence/test_flight_walk_divergence.py`

Probe contents (exact integer verdicts, float logs diagnostic):
hug band \(2^k\le 3^{a_k}<3\cdot 2^k\) exact over \(2\cdot 10^5\)
letters (max \(u=1.58495721<\log_2 3=1.58496250\)); drift table at
\(L\in\{84,1054,25781,50508,176251,301994,478245\}\) — all strictly
expanding; escape times to walk excess \(10\) range from
\(2.8\cdot 10^5\) steps (\(L=84\), \(\delta=3.0\cdot 10^{-3}\)) to
\(9.4\cdot 10^{11}\) steps (\(L=478245\),
\(\delta=5.1\cdot 10^{-6}\)). The \(L=301994\) hug pair overshoots
by almost \(\log_2 3\) (\(2^L\) sits just above \(3^{190537}\)): a
near-convergent from the other side, drift \(1.5850\).

## Conjectures

None active. The branch question is resolved by theorem; no record
in `conjectures/` is needed (the refuted transfer record
`juggler_parity_discrepancy_transfer` already covers the Paper B
side).

## Counterexamples

None against the theorem. Negative knowledge honored: the Paper B
route was not re-tested — the transfer refutation
(`TRANSFER_COMPLEX`) and the merge CLOSE were taken as final; the
theorem replaces, not reopens, that mechanism.

## Formalization

All quantitative components are already Lean
(`power_bound_word`, `follows_log_le_walkWeight`,
`cycle_strict_envelope`, `hugOdds_pow_ge`, `hugOdds_pow_lt`,
`aboveAnchor_prefix_pow_le`). The only human glue is the
infinite-flight framing (pigeonhole on a finite state set plus the
period-word extraction), which lies outside the laboratory's
finite-itinerary Lean idiom; no new Lean file was added and none is
needed for the claim tag.

**Walk-height law (added at the September 2026 consolidation,
EXACT — LEAN VERIFIED, `J-flight-height-law`):** the finite-prefix
rate side of the theorem is now Lean end to end
(`aboveAnchor_height_of_walk` with weight form
`two_pow_le_walkWeight`, `WalkTransport.lean`): on `AboveAnchor n w`
with \(n\ge 400\), a walk height of \(B\) doublings at step \(k\)
(\(2^{k+B}\le 3^{a_k}\)) forces
\(2^B(\log n-D)\le\log x_k\), i.e.
\(x_k\ge(ne^{-D})^{2^B}\) — heights along a descent-free prefix are
doubly exponential in the walk height. Composing with the (human)
walk-divergence theorem: every descent-free flight realizes this
rate along an unbounded walk, so divergent orbits diverge doubly
exponentially in their walk height. Only the infinite pigeonhole
glue remains human.

## Results

Classification **FLIGHT_WALK_DIVERGENCE_CONFIRMED**.

- **Theorem:** every descent-free flight has unbounded exponent
  walk; no flight stays within bounded excess of the hug itinerary. The
  extremal hug-hugging adversary of the above-anchor branch is a
  phantom: below the cycle frontier it is a cycle.
- **Dichotomy:** descent-free flights start above \(162\,849\,448\)
  and are either a finite injective prefix plus closure (eventual
  cycles, period \(\ge 478\,245\), min above the floor — the cycle
  program's jurisdiction) or an infinite injective trajectory
  (\(\limsup x_k=\infty\) — beyond every finite-depth parity layer;
  pointwise structure in `J-flight-divergent-structure`). The
  pigeonhole is uniqueness on a finite admissible window, not an
  extra dynamical ingredient.
- **Paper B answer:** negative as mechanism. Its proved layer is
  ambient-density; the transfer refutation stands; nothing pointwise
  survives at depth \(\le 4\) (every odd-rooted window class has
  positive ambient density, so no finite window is forbidden). The
  kill that works uses pigeonhole + strict expansion instead.
- Probe: hug band exact on \(2\cdot 10^5\) letters, zero violations;
  all seven hug pairs strictly expanding with positive drift; Lean
  components wired.
- **Walk-height law (EXACT — LEAN VERIFIED,
  `J-flight-height-law`):** \(2^{k+B}\le 3^{a_k}\) on a descent-free
  prefix with anchor \(n\ge 400\) forces
  \(\log x_k\ge 2^B(\log n-D)\)
  (`aboveAnchor_height_of_walk`, `WalkTransport.lean`): the
  quantitative rate side of the divergence theorem, finite-itinerary and
  fully formal.

## Open questions

- Case 2 (divergent orbits) is untouched and is exactly the
  all-depth equidistribution frontier (the Juggler Terras program,
  `J-equidistribution-implies-density-one`); no finite-depth layer
  reaches it. Do not reopen from here.
- Whether the dichotomy plus the walk-charge fan structure yields a
  flight-side consequence at the blocker \(L=478\,245\) (the
  eventual cycle of a bounded flight must sit in the surviving fan)
  — deferred; the next useful floor is \(3.48\cdot 10^8\) and
  further campaigns are PARK.

## Decision

**PROMOTE.** The branch question is answered by an exact theorem
that retires the extremal hug-flight adversary unconditionally and
routes the remaining flight frontier into the two named programs
(cycles; all-depth equidistribution). Ledger row
`J-flight-walk-divergence`. The Paper B mechanism is answered
negatively without re-testing the refuted transfer. Branch ends
here; neither the cycle program nor the equidistribution program is
auto-opened.

## Publication assessment

Candidate remark for Paper A (a one-paragraph corollary next to the
§5 hug adversary: "the hug adversary is cycle-exclusive — open
flights cannot realize it"), deferred to the next consolidation
pass; no Paper A edit from this branch.

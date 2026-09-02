# Juggler flight DK pricing (Ostrowski blocks on recurrent hug tails)

Status: **CLOSE** (the named question is answered: DK prices open
hug prefixes without a Juggler return, and the walk-charge *kill*
still needs the cyclic close; no flight exclusion)

The odd-tower CLOSE's standing question: does recurrent hug
domination of divergent flights admit pricing by the certified
Ostrowski/DK blocks — a flight-side analogue of the walk-charge
envelope — or does DK pricing intrinsically require the closure
identity that only cycles provide? Answer: pricing does not need
closure; the kill does. Not a halt theorem, not a divergent-orbit
exclusion, not a Paper A edit. The occupancy reading of the
re-anchored envelope is CLOSE
([juggler_flight_valley_composition.md](juggler_flight_valley_composition.md)).

## Problem

Paper A Theorem 5.9 kills cycle lengths by comparing a left-hand
side \(\theta=1-2^L/3^o\) to a hug-charge right-hand side priced
census-free by Denjoy–Koksma over Ostrowski blocks. Recurrent hug
domination (`J-flight-divergent-structure`, point 5) restarts the
hug odd-count floor from infinitely many tail-minimum records of a
divergent flight. Does that translation-recurrent constraint feed
the same envelope and produce a flight-side kill?

## Exact statement

**Theorem (flight DK split; EXACT — HUMAN PROOF, components
Lean).** Recurrent hug domination does not yield a walk-charge
kill of divergent flights. The envelope splits as follows.

**(Pricing — no Juggler closure.)** The certified Ostrowski/DK
blocks price the hug-prefix charge of every length \(L\):
\(\lvert C_L-C_*(n')\rvert\le 2\,s(L)/L\) (Paper A Theorems 5.7–5.8).
That is a statement about the IET rotation of
\(\theta=\log(3/2)/\log 3\), not about a return \(T^L(x)=x\). Hug
charge maximality (`hug_charge_maximal`) holds for every
admissible odd-count profile \(a\) (every prefix \(2^k\le 3^{a_k}\))
and every length \(L\), with no cycle hypothesis. Every
`AboveAnchor` prefix is admissible
(`aboveAnchor_prefix_pow_le`, `aboveAnchor_prefix_odds_ge_hug`),
and every tail from a recurrent record is itself `AboveAnchor`.
Transport already bounds prefix defects by walk weights on open
prefixes (`aboveAnchor_transport`). Hence the *right-hand side* of
the walk-charge envelope — prefix charge \(\le\) hug charge
\(\le\) DK envelope — is available on every recurrent tail.

**(Kill — closure required.)** The contradiction step is
\(\theta\le\tfrac65\cdot\mathrm{charge}\) together with
charge \(\le\) hug bound (`cycleMin_hug_kill_criterion`). The
left-hand side \(\theta=1-2^L/3^o\) is produced by closing the
charged prefix invariant `cycleMin_charge_prefix` at \(x_L=n\)
(`cycle_iterate_period`) and reindexing
\(\sum_i f(x_{i+1})=\sum_k f(x_k)\) (`cycleMin_defect_finance`).
An open prefix has no such \(\theta\): the same unroll is the
transport identity \(w_k(\log n-C_k)\le\log x_k\), already the
flight envelope, which is compatible with descent-freeness.
Recurrent restarts supply a fresh RHS from each record and still
no \(\theta\).

**(What already kills infinite hugging.)** A flight whose hug
excess stays bounded is an eventual cycle, by walk-divergence
(pigeonhole plus Lean `cycle_strict_envelope`), not by DK. DK
would only help if a finite-\(L\) deficit analogous to \(\theta\)
existed. It does not.

So DK does not intrinsically require closure *to price*; it
intrinsically requires closure *to kill*. The flight-side analogue
of the walk-charge envelope exists as a bound and does not
constrain divergent flights beyond theorems already recorded.

No cycle of any length, and no exclusion of divergent flights, is
claimed.

## Current literature

- DK/Ostrowski envelope and itinerary identity — **EXACT — HUMAN
  PROOF** (`J-cyclemin-walk-ostrowski-arithmetic`,
  `juggler_walk_dk_envelope`, `juggler_walk_window_envelope`);
  Denjoy–Koksma per convergent block is **KNOWN**
- Hug charge maximality — **EXACT — LEAN VERIFIED**
  (`hug_charge_maximal`; no cycle hypothesis)
- Defect-sum finance and the kill criterion — **EXACT — LEAN
  VERIFIED** (`cycleMin_defect_finance`,
  `cycleMin_hug_kill_criterion`); the cyclic close is the last
  step of the finance proof
- Above-anchor hug domination and transport — **EXACT — LEAN
  VERIFIED** (`aboveAnchor_prefix_odds_ge_hug`,
  `aboveAnchor_transport`)
- Flight walk-divergence — **EXACT — HUMAN PROOF**
  (`J-flight-walk-divergence`); already recorded that cycle kills
  were powered by the closure identity and that the flight analogue
  is the pigeonhole reduction. This branch names the remaining
  split: pricing versus kill
- Recurrent hug domination — **EXACT — HUMAN PROOF**
  (`J-flight-divergent-structure`, point 5)
- Re-anchored excursion envelope — exclusion reading **CLOSE**
  (`juggler_flight_valley_composition`); height-law PARK stays
  with the flight-envelope branch
- Koksma \(+1/L\) — **REFUTED** (`juggler_walk_koksma_one_over_L`);
  not re-tested
- Every start reaches 1 — not claimed

Project relationship: **extended** (answers the odd-tower CLOSE's
named next question; packages existing Lean/human theorems, no new
mechanism).

## Branch budget

```text
Mathematical target     does recurrent hug domination of divergent
                        flights admit a DK/Ostrowski kill, or does
                        that kill need the cyclic close x_L = n?
Novelty hypothesis      translation-recurrent hug tails feed the
                        certified Ostrowski blocks and produce a
                        flight-side analogue of Theorem 5.9
Falsifier               DK applies to IET prefixes with no Juggler
                        return, while θ comes only from x_L = n
                        (pricing/kill split → CLOSE); or Ostrowski
                        blocks fail off-cycle (then the slogan
                        "DK needs closure" is literally true)
Existing machinery      hug_charge_maximal, cycleMin_defect_finance,
                        cycleMin_hug_kill_criterion,
                        aboveAnchor_transport,
                        aboveAnchor_prefix_odds_ge_hug,
                        J-flight-walk-divergence,
                        juggler_walk_dk_envelope
Maximum Phase-0 scope   distill only: read the Lean close step and
                        the DK hypotheses; dossier and journal;
                        no probe, no Lean, no ledger row, no
                        Paper A, no envelope composition
Promotion criterion     a flight-side θ-analogue, or a DK bound
                        that contradicts an open prefix
Stop criterion          the RHS is already available off-cycle and
                        the LHS is the cyclic close; or the claim
                        is a reparameterization of walk-divergence
```

## Balanced-ternary formulation

None required. The objects are the exponent walk, the IET
rotation, and the integer orbit.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Hug-prefix DK bound on every \(L\) — **EXACT — HUMAN PROOF**
  (existing; no cycle)
- `hug_charge_maximal` on admissible open prefixes — **EXACT —
  LEAN VERIFIED** (existing)
- Charged prefix invariant `cycleMin_charge_prefix` /
  `aboveAnchor_transport` — **EXACT — LEAN VERIFIED** (the open
  form of the finance unroll)
- Cyclic close \(x_L=n\) producing \(\theta\) —
  **EXACT — LEAN VERIFIED** (`cycleMin_defect_finance`)
- Flight-side \(\theta\)-analogue — none; not claimed
- DK kill of a divergent flight — not claimed; the target of this
  branch, answered negatively

## Experiments

None. The Lean close step (`cycle_iterate_period` inside
`cycleMin_defect_finance`) and the cycle-free statement of
`hug_charge_maximal` decide the question; a census would not.

## Conjectures

None new. The cycle DK envelope remains
`juggler_walk_dk_envelope` (proved). No flight-kill conjecture is
recorded, because the mechanism is identified as missing rather
than empirically false.

## Counterexamples

None. Negative knowledge honored: the REFUTED Koksma \(+1/L\)
slogan was not re-tested; the PARKed excursion-envelope
composition was not reopened; the walk-divergence slogan that
“open flights have no closure identity” is here made precise, not
re-proved.

## Formalization

None new. Consumed Lean:

- `hug_charge_maximal` (`WalkChargeMax.lean`) — pricing, no cycle
- `aboveAnchor_prefix_odds_ge_hug`, `aboveAnchor_prefix_pow_le`
  (`AboveAnchorWalk.lean` / `CycleCore.lean`)
- `aboveAnchor_transport` (`WalkTransport.lean`) — open unroll
- `cycleMin_charge_prefix`, `cycleMin_defect_finance`,
  `cycleMin_hug_kill_criterion` (`DefectFinance.lean`) — the close
  step is `cycle_iterate_period` plus charge reindexing

Denjoy–Koksma itself stays analytic prose, as in Paper A.

## Results

Classification **FLIGHT_DK_NEEDS_CLOSURE_TO_KILL**.

- **Pricing works off-cycle.** Ostrowski/DK and hug maximality
  apply to every `AboveAnchor` prefix and every recurrent tail.
- **The kill does not.** \(\theta\) is the cyclic close of the
  charged prefix invariant; without \(x_L=n\) the unroll is
  transport, already recorded as the flight envelope.
- **Infinite hugging is already dead** by walk-divergence, which
  does not use DK.
- No new period bound, no divergent-orbit exclusion, no ledger
  row: the components are existing theorems.

## Open questions

- A prefix identity other than \(x_L=n\) that would produce a
  \(\theta\)-analogue on `AboveAnchor` is not visible from the
  proved layers; searching for one is a reopen of transport.
  Not opened.
- Quantitative composition of envelopes across recurrent valleys
  has two readings. The exclusion/occupancy reading is **CLOSE**
  ([juggler_flight_valley_composition.md](juggler_flight_valley_composition.md)).
  The terminating-side height-law PARK stays with the
  flight-envelope branch and is not an exclusion question.

## Decision

**CLOSE.** The standing question is answered by a split, not by a
new mechanism: DK prices recurrent hug tails, and the walk-charge
kill still needs the closure identity that only cycles provide.
The statements are existing Lean and human theorems; the flight
program's last named laboratory attack is therefore not a theorem
and not a PARK. Best next question: none in the flight program;
the two named frontiers (the cycle Diophantine blocker
\(L=478245\); pointwise emptiness of infinite odd towers) are not
opened from here.

## Publication assessment

Status: `EXPLORATORY`. A one-paragraph clarification for any
future flight-program write-up (“DK prices open hug prefixes; the
kill is the cyclic close”). Not a paper candidate. No Paper A/B
edit.

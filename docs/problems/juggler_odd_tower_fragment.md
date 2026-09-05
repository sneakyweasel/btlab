# Juggler odd-tower fragment (placement)

Status: **CLOSE** (the fragment is a standalone pointwise digit
problem, incomparable to the equidistribution program; every lab
route into it is already recorded negative knowledge; two placement
corollaries recorded)

The divergent-structure branch's standing question: can the
eventually-all-odd subcase (infinite odd towers) be attacked as a
standalone fragment of the all-depth frontier, or does it already
embed the full equidistribution difficulty? Answer: neither. It is
*incomparable* to equidistribution (pointwise versus density), and
every arithmetic route the laboratory owns is already closed. Not a
halt theorem, not an exclusion claim, not a reopen of the
odd-landing-set CLOSE or the transfer refutation.

## Problem

Does some odd \(x\) have every iterate of \(F(x)=\lfloor
x^{3/2}\rfloor\) odd (an infinite odd tower), and where does that
question sit relative to the laboratory's proved layers and named
programs?

## Exact statement

Let \(F(x)=\lfloor x^{3/2}\rfloor\) and
\(\mathcal T_\infty=\{x\text{ odd}:F^j(x)\text{ odd for all }j\ge
0\}\). An infinite odd tower is an element of \(\mathcal T_\infty\);
its Juggler orbit takes only odd steps and is strictly increasing.
Questions: (a) is \(\mathcal T_\infty=\emptyset\) attackable with
lab machinery; (b) is its exclusion implied by, or does it imply,
all-depth parity equidistribution?

## Current literature

- Iterated odd-landing sets \(\mathcal P_r\) (exactly the depth-\(r\)
  tower sets) — **CLOSE**, `ODD_LANDING_SETS_ARE_FORWARD_ORBITS`
  (`juggler_odd_landing_sets`): stay fraction \(0.49\)–\(0.53\)
  through \(r=7\), singleton cells, every residue class modulo
  \(64\) both stays and exits, \(\theta\) unrestricted; cylinder /
  \(2\)-adic-automaton / \(\theta\)-chain structure **REFUTED**
  (`J-odd-landing-set-structure`). Explicit instruction not to
  reopen residues, \(\theta\), valuation, or predecessor cylinders —
  honored here.
- Paper B depth-\(\le 4\) parity equidistribution (ambient, power
  savings) — **EXACT — HUMAN PROOF**; the proved density control of
  tower starts stalls at depth \(4\).
- Ambient-to-orbit transfer — **CLOSE**, `TRANSFER_COMPLEX`
  (`juggler_parity_discrepancy_transfer`): counting deep tower
  tails by applying Paper B along the sparse image sets
  \(F^d(\mathcal P_d)\) is exactly this refuted transfer; not
  re-tested.
- Certified floor \(162\,849\,448\)
  (`J-residual-floor-one-hundred-sixty-two-million`) —
  **COMPUTATIONALLY VERIFIED**.
- Divergent flight structure (`J-flight-divergent-structure`) and
  walk-height law (`J-flight-height-law`, Lean) — towers are the
  extreme all-odd instance.
- External: the Juggler literature (Pickover; Guy-adjacent surveys;
  OEIS A007320 and neighbors) records only the termination
  conjecture and step censuses; no source in `literature/` or found
  in a fresh search poses the odd-tower fragment separately. The
  problem type — parity of an iterated floor-power orbit at all
  depths — is the same pointwise digit-extraction flavor as
  Mahler's \(Z\)-number problem for \((3/2)^n\) (open since 1968);
  no transfer in either direction is claimed, only the flavor.
  The geometric sibling \(\{(3/2)^n\}\) itself is placed and
  **CLOSE** in
  [juggler_three_halves_mod_one](juggler_three_halves_mod_one.md).

Project relationship: **extended** (placement of a named fragment;
no new mathematics beyond two corollaries).

## Branch budget

- **Target:** is the odd-tower fragment attackable standalone, and
  where does it sit relative to all-depth equidistribution?
- **Novelty hypothesis:** the fragment is incomparable to
  equidistribution; the depth bootstrap reduces to the refuted
  transfer; the flight program adds floor and pinning corollaries.
- **Falsifier:** a lab layer gives a pointwise tower bound (then
  the fragment is attackable and the branch grows).
- **Existing machinery:** \(\mathcal P_r\) CLOSE, Paper B, transfer
  refutation, certified floor, flight program.
- **Maximum Phase-0 scope:** literature check + placement analysis;
  dossier and journal only. The originally scoped tower census was
  dropped on discovery that it duplicates the closed
  \(\mathcal P_r\) census (stop criterion, machinery gravity).
- **Promotion criterion:** any pointwise tower statement from
  proved layers, or a genuinely new counting bound.
- **Stop criterion:** the fragment reduces to classical-open digit
  problems and all lab routes are recorded kills → CLOSE.

## Balanced-ternary formulation

None required. The question is the parity of iterated
\(\mathrm{isqrt}(x^3)\) on ordinary integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Floor corollary (below) — **EXACT — HUMAN PROOF** (one line on
  top of the certified floor)
- Doubly-exponential pinning (below) — **EXACT — HUMAN PROOF**
  (instance of Lean `aboveAnchor_flight_envelope` /
  `aboveAnchor_height_of_walk` at the all-odd itinerary)
- Incomparability placement (below) — **EXACT — HUMAN PROOF**
  (two trivial remarks, recorded to prevent re-attack)
- Any residue / cylinder / \(\theta\) recognition — **REFUTED**
  (prior branch; not re-tested)
- Tower exclusion, or a finite odd-run bound — not claimed

## Experiments

None new. The relevant census exists and is closed: the
\(\mathcal P_r\) census of `juggler_odd_landing_sets` (odd
\(n\le 40000\), depths through \(7\), stay fraction \(\approx 1/2\),
no arithmetic refinement). Re-running it larger would add no
mathematical consequence.

## Conjectures

None opened. \(\mathcal T_\infty=\emptyset\) is not conjectured in
`conjectures/` (it is a subclaim of termination, which the
laboratory does not claim).

## Counterexamples

None. Negative knowledge honored: neither the odd-landing CLOSE nor
the transfer refutation was re-tested.

## Formalization

None new. The two corollaries are one-line consequences of existing
Lean components (`aboveAnchor_flight_envelope`,
`aboveAnchor_height_of_walk`, `two_pow_le_walkWeight`) plus the
computational floor; packaging them would add no content.

## Results

**Corollary 1 (floor for towers; EXACT — HUMAN PROOF over the
computational floor).** Every state of a hypothetical infinite odd
tower exceeds \(162\,849\,448\). *Proof.* A tail of a tower is a
tower, so every state starts an infinite tower; a tower is strictly
increasing (odd steps only), hence a descent-free flight that never
reaches \(1\); every start \(\le 162\,849\,448\) reaches \(1\)
(certified floor). \(\square\)

**Corollary 2 (doubly-exponential pinning; EXACT — HUMAN PROOF,
components Lean).** An infinite odd tower from \(n\ge 400\) has
walk weight exactly \(w_k=(3/2)^k\) (all-odd itinerary), so by the flight
envelope \((3/2)^k(\log n-\Delta)\le\log x_k\le(3/2)^k\log n\) with
\(\Delta=0.7\,k/(n\sqrt n)\): tower states are pinned to
\(n^{(3/2)^k}\) up to a factor \(e^{-\Delta(3/2)^k}\), nonvacuous
while \(k\ll n^{3/2}\log n\). Its exponent walk is exactly
\(u_k=k(\log_2 3-1)\) — the fastest walk any itinerary admits. \(\square\)

**Placement (answers the standing question; EXACT — HUMAN
PROOF).** (i) All-depth parity equidistribution is a density
statement; its conclusion (density-one termination) is silent on
any single orbit, and a density-zero set can be nonempty — so even
the full equidistribution program would *not* exclude odd towers.
(ii) Tower exclusion is a single-cylinder pointwise statement and
implies no equidistribution. Hence the fragment neither embeds nor
is settled by the all-depth frontier: it is incomparable. (iii) The
only counting route past depth \(4\) — Paper B applied along the
sparse tower-tail images — is the refuted ambient-to-orbit
transfer. (iv) The only pointwise routes the laboratory owns —
residues, cylinders, \(\theta\), valuation, predecessor structure —
are the refuted candidates of the odd-landing branch. The fragment
is a self-contained pointwise digit problem (parity of iterated
\(\mathrm{isqrt}(x^3)\)) of Mahler flavor, and the laboratory has no
machinery for it.

## Open questions

- \(\mathcal T_\infty=\emptyset\) itself — open, now placed:
  pointwise, incomparable to equidistribution, beyond current lab
  machinery. Any future attack needs a genuinely new pointwise
  handle on the parity of \(\mathrm{isqrt}\) along orbits, not a
  density estimate. Do not reopen as a wrap of
  \(\{(3/2)^n\}\)
  ([juggler_three_halves_mod_one](juggler_three_halves_mod_one.md)).
- The named next question (DK/Ostrowski pricing of recurrent hug
  tails) is answered by
  [juggler_flight_dk_pricing.md](juggler_flight_dk_pricing.md):
  **CLOSE**. Pricing does not need closure; the kill does.

## Decision

**CLOSE.** The standing question is answered: the odd-tower
fragment is a standalone pointwise problem that neither embeds nor
is reachable from the equidistribution frontier, and every lab
route into it is recorded negative knowledge; the two corollaries
are instances of existing theorems, and the originally scoped
census would duplicate a closed branch. Nothing here justifies
machinery. Best next question: does the recurrent hug domination of
divergent flights (`J-flight-divergent-structure`, point 5) admit
pricing by the cycle program's certified Ostrowski/DK blocks — a
flight-side analogue of the walk-charge envelope on
translation-recurrent words — or does DK pricing intrinsically
require the closure identity that only cycles provide?

## Publication assessment

Status: `EXPLORATORY`. A placement record with two corollary
instances; not a paper candidate.

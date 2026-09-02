# Juggler flight envelope (fly exponent versus peak walk weight)

Status: **STRUCTURAL**

Standalone application phase on the Juggler floor-power map. It is
**not** Paper A, not a floor (\(N_0\)) campaign, not a finance reopen,
and not a reopen of the parked asymptotic-descent envelope program
(`juggler_above_anchor_walk`): no descent mechanism is claimed. It
packages the transport theorem on open descent-free prefixes and
audits the resulting two-sided fly-height envelope on realized
flights.

## Problem

Does the peak walk weight \(W=\max_k 3^{a_k}/2^k\) of the parity itinerary
predict the realized trajectory peak \(H(n)\), and how much of the
floor-suppression budget permitted by transport is actually consumed?

## Exact statement

For a start \(n\) write \(D(n)\) for the first-descent time, \(P(n)\)
for the peak time, \(H(n)=\max_k J^k(n)\), \(w_k=3^{a_k}/2^k\) for the
walk weight of the length-\(k\) prefix, and
\(\Phi(n)=\log H(n)/\log n\) for the fly exponent. The **flight
envelope** is: for every `AboveAnchor` prefix with anchor
\(n\ge 400\) and every \(k\le|w|\),

\[
w_k\,(\log n-\Delta)\ \le\ \log x_k\ \le\ w_k\log n,
\qquad
\Delta=\frac{1.05\,e}{n}+\frac{0.7\,o}{n\sqrt n}.
\]

The upper side needs no anchor (floors only lose) and holds on the
whole realized itinerary. At the prefix peak this sandwiches the fly
exponent: \(w_P(1-\Delta/\log n)\le\Phi\le w_P\). The audit question
with quantifiers: over \(n\le 2\cdot10^4\) and the high-flyer corpus,
is the realized fly excess \(E_H=\log_2 H-w_P\log_2 n\le 0\) within
the transport budget \(-w_P\Delta/\ln 2\), and how close to \(0\)?

## Current literature

- Transport on minimum-based cycles (Paper A Theorem 5.3) —
  **EXACT — LEAN VERIFIED** (`cycleMin_transport`,
  `WalkTransport.lean`). Never previously stated off-cycle.
- Above-anchor walk layer: `aboveAnchor_prefix_pow_le`,
  `aboveAnchor_prefix_odds_ge_hug` — **EXACT — LEAN VERIFIED**
  (`J-above-anchor-hug-domination`); the even-injection cell
  `even_ge_sq_of_aboveAnchor` was already anchor-form.
- Defect-free upper envelope `power_bound_word` —
  **EXACT — LEAN VERIFIED**.
- Defects idle at near-minimum visits (\(\rho\le 3\cdot10^{-3}\)),
  every observed first descent a gap descent — **OBSERVATION**
  (`juggler_above_anchor_walk`, PARKed envelope program).
- First-return excursion bookkeeping — **CLOSE, REPARAMETERIZATION**
  (`juggler_first_return_excursions`); cumulative floor loss —
  **CLOSE**.

Project relationship: **extended** (the transport induction ports
verbatim to `AboveAnchor`; the fly-exponent packaging and the peak
census are new bookkeeping on existing machinery).

## Branch budget

- **Target:** does \(\Phi(n)\) match the peak walk weight within the
  transport error on the high-flyer corpus, and does the
  CycleMin→AboveAnchor transport port close in Lean?
- **Novelty hypothesis:** the two-sided flight envelope as a packaged
  theorem on open descent-free prefixes; peak time \(P(n)\) and fly
  excess \(E_H\) as new coordinates.
- **Falsifier:** \(E_H\) large on some flight (floors bite at the
  peak), or the port stalls on an injection lemma off-cycle.
- **Existing machinery:** `WalkTransport.lean`,
  `aboveAnchor_prefix_pow_le`, `even_ge_sq_of_aboveAnchor`,
  `power_bound_word`, the above-anchor census, the excursions corpus.
- **Maximum Phase-0 scope:** one Lean port plus one atlas join
  \((n,D,P,F_1,H,W,\Phi,E_H)\) on \([3,2\cdot10^4]\) and the
  high-flyer list; no new CLI, no Paper A edit, no \(N_0\) change.
- **Promotion criterion:** the Lean envelope closes and covers the
  English statement, or a nontrivial \(E_H\) family appears.
- **Stop criterion:** \(\Phi\approx W\) confirmed with idle defects —
  record the sharpness audit and stop; do not enter the descent
  program.

## Balanced-ternary formulation

Not BT-specific: the envelope lives in the multiplicative exponents
\(3^{a}/2^{k}\), the same \(2\)–\(3\) data as the cycle finance and
walk layers. No balanced-ternary representation is claimed to bear on
the fly exponent.

## Why BT may be relevant

Only through the shared \(2\)–\(3\) multiplicative structure of the
laboratory; no direct representation claim.

## Candidate operations / invariants

- Fly exponent \(\Phi(n)=\log_2 H(n)/\log_2 n\) and walk height
  \(u_k=a_k\log_2 3-k\) (\(w_k=2^{u_k}\)) — the flight coordinate
  pair (**OBSERVATION**: \(\Phi\) is doubly exponential in the walk
  height \(u\)).
- Fly excess \(E_H=\log_2 H-w_P\log_2 n\in[-w_P\Delta/\ln 2,\,0]\)
  (**EXACT — LEAN VERIFIED** bounds, `aboveAnchor_flight_envelope`).
- Peak time \(P(n)\) versus first-descent time \(D(n)\): the global
  peak sits on the ascent prefix iff \(P<D\) (**OBSERVATION**: fails
  for \(19.6\%\) of odd starts through \(2\cdot10^4\); those peaks
  are priced only by the anchor-free upper side).

## Experiments

Runner: `python -m research.juggler_sequence.flight_envelope`
(probe `src/research/juggler_sequence/flight_envelope.py`).
Artifact: `data/research/juggler/flight_envelope/summary.json`.
Fast suite: `tests/research/juggler_sequence/test_flight_envelope.py`.

- Fly atlas on odd \(n\in[3,2\cdot10^4]\) (exact integer
  trajectories, float logs diagnostic only): \(D\), \(P\), \(F_1\),
  peak bits, \(u_{\max}\), \(u_P\), \(\Phi\), \(E_H\), both envelope
  residuals, peak-in-prefix flag.
- High-flyer pass (gmpy2) on
  \(48443,275485,412027,463157,1122603,1245741,1267909\)
  (peaks to \(6.49\cdot10^6\) bits).

## Conjectures

None new. The envelope is a theorem; the sharpness numbers are
observations. `juggler_asymptotic_descent` and
`juggler_descent_time_log` stay untouched in `conjectures/active/`.

## Counterexamples

None. The predicted falsifier (large \(E_H\)) did not appear: the
worst transport-applicable relative fly excess through
\(2\cdot10^4\) is \(1.61\cdot10^{-4}\) (at \(n=431\)) against a
permitted budget of order \(\Delta/\ln n\).

## Formalization

`formal/Problems/Juggler/WalkTransport.lean` (the former
`FlightEnvelope.lean` was merged into it during the September 2026
hygiene pass; the transport induction now runs once, on
`AboveAnchor`, and the `CycleMin` statements are corollaries via
`aboveAnchor_of_cycleMin`):

- `follows_log_le_walkWeight` — anchor-free upper envelope
  \(\log x_k\le w_k\log n\) (log form of `power_bound_word`).
- `one_le_walkWeight_aboveAnchor` — `aboveAnchor_prefix_pow_le`
  (`CycleCore.lean`) in weight form (\(w_k\ge 1\)).
- `aboveAnchor_transport_prefix`, `aboveAnchor_transport` — the
  Theorem 5.3 transport induction with the cycle hypothesis replaced
  by the anchor hypothesis: odd injections priced at
  `aboveAnchor_iterate_ge`, even injections at
  `even_ge_sq_of_aboveAnchor`.
- `aboveAnchor_flight_envelope` — the packaged two-sided sandwich.
- `two_pow_le_walkWeight`, `aboveAnchor_height_of_walk` — the
  walk-height law (`J-flight-height-law`): \(B\) doublings of walk
  height at step \(k\) (\(2^{k+B}\le 3^{a_k}\)) force
  \(\log x_k\ge 2^B(\log n-D)\); heights along a descent-free
  prefix are doubly exponential in the walk height.

No `sorry`; full `lake build` clean. Ledger row
`J-flight-envelope-transport` (**EXACT — LEAN VERIFIED**).

## Results

- **Flight envelope (EXACT — LEAN VERIFIED):** on open descent-free
  prefixes with anchor \(n\ge 400\),
  \(w_k(\log n-\Delta)\le\log x_k\le w_k\log n\); the upper side
  holds anchor-free on every realized prefix. The fly exponent of an
  ascent prefix equals its peak walk weight up to
  \(O(w_P\Delta/\log n)\).
- **The envelope is razor sharp (COMPUTATIONALLY VERIFIED, float
  diagnostics):** through \(2\cdot10^4\), zero violations of either
  side; worst transport-applicable relative fly excess
  \(1.61\cdot10^{-4}\); classification
  `FLIGHT_ENVELOPE_SHARP`. On the seven high-flyers the floors shave
  at most \(0.014\) **bits** off multi-million-bit ideal peaks
  (\(48443\): \(3230450\) bits, \(E_H=-0.0028\) bits,
  \(\Phi=207559.1\); \(275485\): \(6342922\) bits,
  \(E_H=-3\cdot10^{-6}\) bits, \(\Phi=350988.1\); \(1267909\):
  \(6485496\) bits, \(E_H=-7.8\cdot10^{-5}\) bits). \(\Phi=w_P\) to
  relative error \(10^{-9}\)–\(10^{-11}\) at height: the parity itinerary
  alone determines the peak to sub-bit precision.
- **Peak placement (OBSERVATION):** all seven high-flyers peak on the
  ascent prefix (\(P<D\)), but \(1964\) of \(9999\) odd starts
  through \(2\cdot10^4\) (\(19.6\%\)) peak *after* the first descent
  (smallest: \(n=19\), \(D=2\), \(P=4\)); those peaks satisfy the
  anchor-free upper side but are not priced from below without
  re-anchoring at the valley.
- **Atlas records (OBSERVATION):** max fly exponent through
  \(2\cdot10^4\) is \(\Phi=5687.9\) at \(n=15845\)
  (\(D=132\), \(P=43\), \(F_1=139\), peak \(79357\) bits,
  \(u_{\max}=12.47\)); the high-flyer record is
  \(\Phi=350988.1\) at \(275485\) (\(u=18.42\)).

## Open questions

- Can the lower side be extended past the first descent by
  re-anchoring at each valley (an excursion-decomposed envelope), and
  does the composed statement say anything the per-excursion one does
  not? This is a *height-law* question on orbits that leave
  `AboveAnchor`. The *exclusion* reading (comparable-scale occupancy
  as a kill of divergent flights) is **CLOSE**:
  [juggler_flight_valley_composition.md](juggler_flight_valley_composition.md).
- Is there any start class with \(E_H\) bounded away from \(0\) — a
  floor-suppressed flight family? (Empirics through \(2\cdot10^4\)
  say no; this is the same defect-lower-bound wall that parks the
  descent program.)

## Decision

**PROMOTE** the flight envelope into the platform
(`J-flight-envelope-transport`, Lean-verified: the Theorem 5.3
transport now prices open descent-free flight, and the fly exponent
of an ascent prefix is its peak walk weight up to an explicit
error). **PARK** any further fly-atlas expansion: the audit answered
the target — \(\Phi=W\) to sub-bit precision, the fly excess is
idle exactly like the walk defects, and converting the envelope into
descent or divergence statements reduces to the same per-visit
defect lower bounds (deterministic equidistribution) that park the
asymptotic-descent program. Not a halt theorem, not a divergence
theorem, not a cycle obstruction.

Best next question: does the excursion-decomposed (re-anchored)
envelope compose across valleys into a whole-trajectory height law,
or does composition lose exactly the information the single-anchor
form already loses at the \(19.6\%\) of starts that peak after first
descent? That question is not an exclusion mechanism
([juggler_flight_valley_composition.md](juggler_flight_valley_composition.md)
CLOSE) and is not opened from the occupancy distill.

## Publication assessment

Status: **STRUCTURAL**. The port is a clean one-paragraph theorem
beside `J-above-anchor-hug-domination` in any future termination
note; the sharpness audit is a strong sanity check on the Theorem
5.3 constants (the \(1.05\)/\(0.7\) prices are generous by orders of
magnitude on realized flights). Not a paper candidate on its own.

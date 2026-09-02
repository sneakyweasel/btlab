# Juggler Koksma \(+1/L\) envelope

Status: **ARCHIVED**

Refinement of
([juggler_cycle_walk_exchange.md](juggler_cycle_walk_exchange.md)).
Not a halt theorem, not a floor raise, not a uniform \(B/\theta\)
claim, and not a reopen of the REFUTED Christoffel slogans.

## Problem

Exchange identified leftover charge-per-letter with the Laplace
integral \(C_*(n)\) and recorded a \(O(1/L)\) excess. Does
Denjoy–Koksma with \(\mathrm{Var}(f)<1\) give
\(C_L\le C_*(n')+1/L\) on leftover hug itineraries, making the 18
walk-charge kills DP-free?

## Exact statement

**The \(+1/L\) slogan is false (REFUTED).** On the committed
19-row survey, \(C_{\mathrm{hug}}\le C_*+1/L\) fails at the six
offsets \(L=103124,128905,154686,178359,179413,180467\). The
worst constant is \((C_{\mathrm{hug}}-C_*)L=1.868\) at
\(L=180467\). Seeds stay at \(0.333\), the Euler–Maclaurin size.

**The failure is the rotation itself, not a budget dump
(COMPUTATIONALLY VERIFIED).** Leftover hug \(C\) equals the
IET-prefix average of length \(L\) to relative \(10^{-12}\). The
same six lengths fail \(C_{\mathrm{IET}}\le C_*+1/L\).
Denjoy–Koksma at constant \(1\) does not apply to these
denominators.

**Trial salvages fail (COMPUTATIONALLY VERIFIED).**
\(C_*+1/(2L)\) and \(C_*+1/(2L)+u_L/L\) each cover only \(7/19\)
rows. No closed two-term envelope appeared.

**The crude bound remains a 19-row observation.** Every leftover
\(C\) is still below \(1/(\ln 3\,\ln n')\). That fact was already
recorded by walk-exchange and is not a new theorem. Under that
envelope the same 18 lengths would die and \(L=176251\) would
still survive. Uniform \(B/\theta<1\) at this floor stays false.

No cycle of any length — not claimed.

## Current literature

- Hug exchange and \(C_*\) —
  **EXACT — HUMAN PROOF**
  ([juggler_cycle_walk_exchange.md](juggler_cycle_walk_exchange.md))
- Greedy hug-itinerary maximizer —
  **COMPUTATIONALLY VERIFIED**
  ([juggler_cycle_walk_greedy.md](juggler_cycle_walk_greedy.md))
- Denjoy–Koksma / Koksma for BV functions —
  **KNOWN**
- Christoffel leftover-cell reduction —
  **REFUTED** (`juggler_christoffel_one_parameter`)
- Baker/Rhin transfer —
  **REFUTED** (`juggler_baker_kills_near_convergents`)
- Every start reaches 1 — not claimed

Project relationship: **extended** (tests the finite-\(L\)
envelope named by walk-exchange; does not reopen leftover-cell
rigidity).

## Branch budget

```text
Mathematical target     Does leftover hug C_L satisfy
                        C_L ≤ C_*(n') + 1/L, or the cruder
                        C_L ≤ 1/(ln 3 ln n'), with a human
                        argument (Koksma / variation / surplus)?
Novelty hypothesis      Denjoy–Koksma + Var(f)<1 gives the +1/L
                        envelope and makes the 18 kills DP-free
Falsifier               A leftover with C_L > C_* + 1/L;
                        or the crude bound fails on a leftover;
                        or Koksma does not apply to the finite
                        hug and no replacement inequality is
                        visible
Existing machinery      c_star_integral, hug C, IET rotation
                        average, committed 19-row survey
Maximum Phase-0 scope   Check +1/L on hug and IET for all 19
                        leftovers; trial Euler-Maclaurin +
                        surplus; no Lean, no Paper A, no N0,
                        no new DP, no certified new kills
Promotion criterion     A correct human envelope that covers
                        the 19 leftovers and would recover the
                        18 kills
Stop criterion          +1/L fails and the Koksma transfer has
                        a hole with no salvage stronger than
                        the already-known crude bound
```

## Balanced-ternary formulation

None required. The walk lives on the exponent lattice
\(\mu a-b\).

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- \(C_L\le C_*+1/L\) on leftover hug itineraries —
  **REFUTED** (`juggler_walk_koksma_one_over_L`); six offsets
- Leftover hug equals IET prefix —
  **COMPUTATIONALLY VERIFIED** (difference \(10^{-12}\))
- \(C_*+1/(2L)+u_L/L\) —
  **REFUTED** as a 19-row envelope (\(7/19\))
- \(C_L<1/(\ln 3\,\ln n')\) on the 19 leftovers —
  **COMPUTATIONALLY VERIFIED** (already; walk-exchange)
- Uniform \(B/\theta<1\) at fixed \(N_0\) —
  **REFUTED** (already)
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_walk_koksma`
- Artifacts: `data/research/juggler/cycle_walk_koksma/summary.json`
- Tests: `tests/research/juggler_sequence/test_cycle_walk_koksma.py`

No CLI. No new Lean. Paper A is unchanged. The certified
walk-charge DP is not edited.

## Conjectures

`juggler_walk_koksma_one_over_L` — **REFUTED**. Leftover hug
(and the IET prefix of the same length) need not satisfy
\(C_L\le C_*(n)+1/L\).

## Counterexamples

- \(L=180467\): \((C_{\mathrm{hug}}-C_*)L=1.868>1\). Same for
  the IET prefix.
- Five further offsets: \(103124,128905,154686,178359,179413\).

## Formalization

None. No `WalkKoksma.lean`, no `sorry`. Paper A is unchanged.
Not a halt theorem.

## Results

Classification **WALK_KOKSMA_CLOSED**.

- \(+1/L\) holds on \(13/19\) leftovers, including every seed
  (seed constant \(0.333\))
- Fails on six offsets; worst constant \(1.868\) at \(L=180467\)
- Hug \(=\) IET to \(10^{-12}\); the same six lengths fail for
  the rotation
- Euler–Maclaurin \(+\) surplus covers \(7/19\)
- Crude bound still holds on \(19/19\)

## Open questions

A proof of \(C_L<1/(\ln 3\,\ln n')\) for leftover hug / IET
prefixes, by a method that is not Denjoy–Koksma at constant
\(1\). That would make the 18 kills DP-free. Do not raise
\(N_0\) and do not claim a uniform \(B/\theta\) gap.

## Decision

**CLOSE.** The Phase-0 falsifier fired: leftover offsets
violate \(C_L\le C_*+1/L\), and the IET prefix violates it in
lockstep, so the hole is not a letter-budget dump. Seeds sit at
the Euler–Maclaurin size \(\approx 1/3\), which is why the
slogan looked plausible. No two-term salvage covers the table.
The crude bound that would still kill 18 lengths is the
19-row observation already recorded by walk-exchange; repeating
it is a reparameterization, not a promotion.

Best next question: can one prove
\(C_L<1/(\ln 3\,\ln n')\) for leftover hug itineraries without
using Denjoy–Koksma at constant \(1\)?

## Publication assessment

Status: `ARCHIVED`.

A finite, exact obstruction to the Koksma \(+1/L\) slogan for
the walk-charge density. Not a paper candidate and not a halt
theorem.

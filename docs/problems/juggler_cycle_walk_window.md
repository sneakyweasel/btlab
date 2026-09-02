# Juggler uniform window envelope

Status: **ACTIVE** (Phase 0 decided)

Successor of
([juggler_cycle_walk_ostrowski.md](juggler_cycle_walk_ostrowski.md)),
answering its open question on the current window. Envelope only:
**no new kills are claimed**, the per-length finance comparison
still decides, and near-convergents such as \(L=176251\) still
survive. Not a halt theorem, not a floor raise, not a uniform
\(B/\theta\) claim.

## Problem

The DK/Ostrowski envelope priced the 19 leftovers census-free.
Is \(s(L)\) uniformly bounded on the window, so the envelope
prices **every** length — every future leftover — with no census
at all?

## Exact statement

**Itinerary identity (EXACT — HUMAN PROOF).** For every \(L\), the
budgeted hug itinerary at \((L,o_{\min})\) equals the exact IET
\(L\)-prefix. Proof: the exact rule (E iff \(u\ge 1\)) keeps
\(u\in[0,1+\alpha)\), so the prefix uses exactly
\(a_L=\lceil L/(1+\alpha)\rceil=\lceil Lx\rceil=o_{\min}\) odds;
if the budgeted word first diverged where a budget ran dry, the
exact prefix would use strictly more of that letter than its own
total — a contradiction. So budgets never bind and the itineraries are
identical. (Spot-checked with integer-exact letters at
\(60000,123456,250000,301993\) beyond the 19 leftovers.)

**Uniform digit bound (KNOWN + certified).** Greedy Ostrowski
digits satisfy \(b_j\le a_{j+1}\); with the certified partial
quotients of \(\theta=[0;2,1,2,2,3,1,5,2,23,2,2,1,\dots]\) the
cap sum on \([50508,301994)\) is \(47\). The exact scan maximum
is \(s(L)\le 37\) (attained at \(L=275632\)); every level stays
within its cap, level \(1054\) reaching \(23\) exactly.

**Uniform envelope (EXACT — HUMAN PROOF).** For every
\(L\in[50508,301994)\): the deficit obeys \(D\le 4.6\cdot10^{-3}\),
so \(\ln n'\ge 17.07\) and the \(J\)-gap is \(\ge 0.00514\);
hence
\[
\frac{2s(L)}{L}\le\frac{94}{50508}=1.87\cdot10^{-3}
<0.00514\le\frac1{\ln 3\,\ln n'}-C_*(n'),
\]
and by the DK/Ostrowski theorem
\(C_L\le C_*+2s(L)/L<1/(\ln 3\,\ln n')\) for the hug itinerary of
every window length, census-free. Scan sharpening: the worst
ratio of \(2s/L\) to the \(J\)-gap over the \(251486\) window
lengths is \(0.1823\) (at \(L=74654\), \(s=35\)) — envelope
margin at least \(5.48\) everywhere.

This discharges the crude-envelope caveat "not a theorem for
every \(L\ge 50508\)" on the window \([50508,301994)\). It does
**not** kill new lengths: kills still need
\(\theta(L)>(6/5)\,B\cdot\text{guard}\), and the Diophantine
survivors remain.

No cycle of any length — not claimed.

## Current literature

- DK/Ostrowski envelope — **EXACT — HUMAN PROOF**
  ([juggler_cycle_walk_ostrowski.md](juggler_cycle_walk_ostrowski.md))
- Ostrowski digit bound \(b_j\le a_{j+1}\) — **KNOWN**
- Crude envelope (occupancy census) — **PROMOTE**, now superseded
  on the window
  ([juggler_cycle_walk_envelope.md](juggler_cycle_walk_envelope.md))
- Hug exchange and \(C_*\) — **EXACT — HUMAN PROOF**
  ([juggler_cycle_walk_exchange.md](juggler_cycle_walk_exchange.md))
- Uniform \(B/\theta<1\) at a fixed floor — **REFUTED** (already)
- Every start reaches 1 — not claimed

Project relationship: **extended** (the 19-row word-identity
verification becomes a theorem for all \(L\); the envelope
becomes uniform on the window).

## Branch budget

```text
Mathematical target     Prove that for every L in [50508, 301994) at the
                        certified floor, the budgeted hug itinerary equals the
                        exact IET prefix and C_L <= C_* + 2 s(L)/L <
                        1/(ln 3 ln n') — the crude-envelope caveat "not a
                        theorem for every L" discharged on the whole window
Novelty hypothesis      (i) hug = exact IET prefix is a THEOREM for all L
                        (u stays in [0,1+alpha); a counting argument kills
                        budget divergence), upgrading the 19-row check;
                        (ii) greedy Ostrowski digits obey b_j <= a_{j+1},
                        so s(L) <= 47 on the window and 2s/L <= 1.9e-3
                        << J-gap 0.0051 — census-free for every length
Falsifier               a window length with s(L) > 47 or 2s/L >= J-gap;
                        a budget divergence between hug and the exact
                        prefix; or the claim is judged a REPARAMETERIZATION
                        of J-cyclemin-walk-dk-envelope
Existing machinery      certified q_j / a_j and exact_hug_word
                        (cycle_walk_ostrowski), deficit_D, gap_lower,
                        o_min = ceil(L x) decided by the x-sandwich
Maximum Phase-0 scope   one window-scan probe + dossier + conjecture +
                        ledger row + tests; no Lean, no Paper A, no N0,
                        no new DP, no new kill claims, no period change
Promotion criterion     human proofs of itinerary identity and digit bound;
                        exact window max of s; envelope margin > 1 on
                        every L in the window
Stop criterion          a falsifier fires, or the content reduces to the
                        already-recorded DK row
```

## Balanced-ternary formulation

None required. The walk lives on the exponent lattice
\(\mu a-b\).

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Budgeted hug \(=\) exact IET prefix for every \(L\) —
  **EXACT — HUMAN PROOF** (counting argument)
- \(o_{\min}=\lceil Lx\rceil\), decided by the certified sandwich
  — **EXACT — HUMAN PROOF**
- \(b_j\le a_{j+1}\), cap sum \(47\) on the window — **KNOWN** +
  certified quotients
- \(C_L<1/(\ln 3\,\ln n')\) for every window length —
  **EXACT — HUMAN PROOF** (given the DK row)
- Exact window maxima (\(s\le 37\), margin \(\ge 5.48\)) —
  **COMPUTATIONALLY VERIFIED**
- New kills from the uniform envelope — not claimed
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_walk_window`
- Artifacts: `data/research/juggler/cycle_walk_window/summary.json`
- Tests: `tests/research/juggler_sequence/test_cycle_walk_window.py`

No CLI. No new Lean. Paper A is unchanged. The certified
walk-charge DP is not edited.

## Conjectures

`juggler_walk_window_envelope` — **EXACT — HUMAN PROOF**.
Itinerary identity for all \(L\) plus the uniform census-free envelope
\(C_L<1/(\ln 3\,\ln n')\) on \([50508,301994)\).

## Counterexamples

None. Every window length passes with margin \(\ge 5.48\); every
greedy digit stays within its cap.

## Formalization

Since the 1 September 2026 consolidation the discrete side of the
itinerary identity is Lean: `WalkChargeItineraries.lean`
(`budgetedWord_eq_hugWord`, `hugOdds_pow_ge`, `hugOdds_pow_lt`,
`hugOdds_least`, `hugOdds_le_of_admissible`; ledger row
`J-cyclemin-walk-word-identity`, **EXACT — LEAN VERIFIED**). The
digit-cap argument and the scan stay human + certified
computation. Paper A Section 5 now prints the window theorem
(Theorem 5.8). No `sorry`. Not a halt theorem.

## Results

Classification **WALK_WINDOW_GREEN**.

- Itinerary identity proved for all \(L\); integer-exact spot checks
  at \(60000,123456,250000,301993\) pass
- Digit caps hold on all \(251486\) window lengths; exact max
  \(s=37\) at \(L=275632\) (cap sum \(47\)); level \(1054\)
  reaches its cap \(23\)
- Worst \(2s/L\) over \(J\)-gap \(=0.1823\) at \(L=74654\);
  uniform envelope margin \(\ge 5.48\)
- Digit-sum histogram: mode at \(s=12\), support \([1,37]\)
- No new kills; period bound unchanged: \(176251\)

## Open questions

Is the DK constant sharp here — is there a window length whose
hug excess approaches \(2s(L)/L\), or does the excess stay
\(O(1)/L\) uniformly (measured excesses on the leftovers were
\(\le 1.87/L\) even when \(2s=12\))? Do not raise \(N_0\) and do
not claim a uniform \(B/\theta\) gap.

## Decision

**PROMOTE.** Both open ends of the DK branch close on the
window: the itinerary identity is now a theorem for every \(L\)
(retiring the per-row verification), and the digit-cap chain
\(b_j\le a_{j+1}\), cap sum \(47\), \(94/50508<\) \(J\)-gap makes
the envelope uniform and census-free for every length in
\([50508,301994)\). This is not a reparameterization of the DK
row: that row priced 19 specific leftovers; this one prices all
\(251486\) lengths with a new human word-identity lemma. The
finance side is untouched — no new kills, survivors unchanged.

Best next question: is the DK constant \(2s(L)\) sharp here, or
does the hug excess stay \(O(1)/L\) uniformly on the window?

## Publication assessment

Status: `THEOREM`.

With the DK row this completes a self-contained census-free
envelope section: every length in the window has
\(C_L<1/(\ln 3\,\ln n')\) by a human chain whose only
computational input is exact integer arithmetic. Not a halt
theorem.

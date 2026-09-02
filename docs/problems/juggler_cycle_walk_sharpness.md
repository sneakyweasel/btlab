# Juggler DK sharpness and the excess arches

Status: **ACTIVE** (Phase 0 decided)

Successor of
([juggler_cycle_walk_window.md](juggler_cycle_walk_window.md)),
answering its open question empirically. Measurement only: the
envelope currency stays \(2s(L)\), no new kills, no envelope
edit. Not a halt theorem, not a floor raise, not a uniform
\(B/\theta\) claim.

## Problem

Is the DK constant \(2s(L)\) sharp — is there a window length
whose hug excess approaches \(2s(L)/L\) — or does the excess
\(e(L)=\sum_{k<L}F(\{k\alpha\})-LC_*\) stay \(O(1)\) uniformly?

## Exact statement

**Window facts (OBSERVATION, float census).** At the fixed
representative reduced base of the 50508 leftover
(\(\ln n'=17.0826\)), for every \(1\le L<301994\):
\(e(L)\in(-0.28,\,4.97]\) — one-sided and window-bounded. DK is
never tight: \(|e|/2s\le 0.476\) overall and \(\le 0.355\) on
\([50508,301994)\) (attained at \(L=125743\)). The running
maximum saturates: \(1.87\) by \(L=1054\), \(4.72\) by
\(L=24727\), only \(4.97\) by \(L=301993\). The fixed-base
excesses match the per-row DK-branch excesses to \(6\cdot10^{-4}\)
(base drift is second order).

**Arch mechanism (OBSERVATION).** Along the level-9 tower
\(L=m\cdot 1054\), the excess follows a quadratic arch:
\(0.48, 0.92, \dots\) peaking at \(2.99\) at \(m=12\) and
returning to \(-0.04\) at \(m=24\approx q_{10}/q_9\), then
repeating. The 50508-tower is flat (\(\le 0.33\)). This is the
classical sawtooth picture — per-block excess affine in the
linearly drifting phase — and it explains the saturation: only
the partial-quotient-23 tower can accumulate, and its arch closes.

**Three structural laws fail.** (i) alternating digit sum
\(e\approx\kappa\sum_j(-1)^jb_j\): Pearson \(r=0.21\);
(ii) additive digit law \(e\approx\sum_jb_jc_j\): least squares
\(r^2=-0.39\); (iii) endpoint coboundary \(e(L)=g(u_L)\): the
max bin range \(4.63\) is comparable to the global range
\(5.25\). The excess is a phase-history functional, not a
single-parameter one.

**What is *not* claimed.** No bound beyond the window, no human
proof of the arch height, no change to the certified envelope,
no new kills. The human currency stays \(2s(L)\).

No cycle of any length — not claimed.

## Current literature

- DK/Ostrowski envelope and uniform window envelope —
  **EXACT — HUMAN PROOF**
  ([juggler_cycle_walk_ostrowski.md](juggler_cycle_walk_ostrowski.md),
  [juggler_cycle_walk_window.md](juggler_cycle_walk_window.md))
- Sawtooth / Birkhoff sums with a jump over rotations
  (Hecke, Ostrowski, Schoissengeier) — **KNOWN** (quadratic
  arches per quotient tower)
- Koksma constant \(1\) — stays **REFUTED**
- Every start reaches 1 — not claimed

Project relationship: **extended** (quantifies the slack in the
laboratory's own DK envelope).

## Branch budget

```text
Mathematical target     Is the Birkhoff excess e(L) = Σ_{k<L} F({kθ}) − L·C_*
                        (orbit started at the wrap jump u_0 = 0) uniformly
                        bounded on [1, 301994), or does it genuinely grow
                        like the DK price 2 s(L)?
Novelty hypothesis      leftover excesses (≤ 1.87) sit far under 2s, but
                        leftovers are digit-sparse; the Ostrowski sawtooth
                        formula predicts e ≈ κ · Σ_j (−1)^j b_j, which would
                        make DK order-sharp at digit-rich lengths and refute
                        any bounded-remainder rescue
Falsifier               for boundedness: an L with large |e|; for sharpness:
                        e staying O(1) across digit-rich lengths
Existing machinery      exact hug-itinerary generator and certified CF/digits
                        (cycle_walk_ostrowski), c_star_integral, window scan
Maximum Phase-0 scope   one single-pass probe at a fixed representative
                        base + stats + structure tests; no Lean, no Paper A,
                        no new kills, no envelope edit, no N0
Promotion criterion     a verified structural law for e(L) (alternating
                        digit sum or coboundary collapse) worth a recorded
                        conjecture, or a human constant improvement
Stop criterion          e tracks 2s with no exploitable structure (DK is
                        the right currency — record and CLOSE), or the
                        data is structureless (PARK)
```

## Balanced-ternary formulation

None required. The walk lives on the exponent lattice
\(\mu a-b\).

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- \(e(L)\) window-bounded, one-sided, DK never tight —
  **OBSERVATION** (float census)
- Quadratic arch along the 1054-tower, closing at
  \(m\approx 24\) — **OBSERVATION**
- \(e\approx\kappa\sum(-1)^jb_j\) — failed (\(r=0.21\))
- \(e\approx\sum b_jc_j\) — failed (\(r^2=-0.39\))
- \(e(L)=g(u_L)\) coboundary — failed (no collapse)
- Improvement of the certified envelope constant — not claimed
- No cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.cycle_walk_sharpness`
- Artifacts: `data/research/juggler/cycle_walk_sharpness/summary.json`
- Tests: `tests/research/juggler_sequence/test_cycle_walk_sharpness.py`

No CLI. No new Lean. Paper A is unchanged. The certified
envelope and kill table are not edited.

## Conjectures

`juggler_walk_excess_arch` — **COMPUTATIONALLY_SUPPORTED**.
Per-tower quadratic arches bound the excess: on the window,
\(e(L)\in(-0.28, 4.97]\) with the accumulation confined to the
partial-quotient-23 tower whose arch closes at a full quotient
cycle.

## Counterexamples

The three failed laws above (fit diagnostics recorded in the
artifact). None against the DK envelope itself.

## Formalization

None. No Lean, no `sorry`. Paper A is unchanged. Not a halt
theorem.

## Results

Classification **WALK_SHARPNESS_BOUNDED**.

- \(e(L)\in(-0.28, 4.97]\) on all \(301993\) lengths; max at
  \(L=238541\) (\(s=17\))
- DK never tight: ratio \(\le 0.476\) overall, \(\le 0.355\) on
  the window — the envelope has \(\ge 2\times\) slack everywhere
- Running max saturates after the 1054-tower; the arch peaks at
  \(2.99\) (\(m=12\)) and closes at \(m=24\)
- Alternating-sum, additive-digit, and coboundary laws all fail
- Leftover cross-check: fixed-base vs per-row excesses agree to
  \(6\cdot10^{-4}\)
- Envelope, kill table, period bound unchanged

## Open questions

The quadratic-arch height \(e=O(\max_ja_{j+1})\) remains an
open human-proof question with no cycle consequence. Its
period-bound reading — pulling \(n^*(478245)\) below the
certified floor — is **REFUTED** by the child
([juggler_cycle_walk_arch.md](juggler_cycle_walk_arch.md)).
Do not raise \(N_0\) and do not claim a uniform \(B/\theta\)
gap.

## Decision

**PARK.** The sharpness question is answered on the window: DK
is never tight (factor \(\ge 2.8\) of slack in the envelope
regime) and the excess is one-sided and window-bounded by \(5\),
with the accumulation confined to the single large-quotient
tower whose arch closes. But no single-parameter law survived
testing, the arch bound has no human proof within Phase-0 scope,
and there is no consequence at the current floor — the uniform
envelope margin is already \(5.48\) via \(2s\). The recorded
reopening point (a human arch bound as a free period-bound
move) is now the child CLOSE
([juggler_cycle_walk_arch.md](juggler_cycle_walk_arch.md)).

Best next question: none as a cycle attack; the \(O(\max_j
a_{j+1})\) height stays PARKED with no period-bound payoff.

## Publication assessment

Status: `NOTE`.

A quantitative sharpness study of the laboratory's own envelope:
useful context for the DK section (the constant is generous by
\(\ge 2.8\times\) in the operating regime), not a standalone
result. Not a halt theorem.

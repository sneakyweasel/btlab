# Juggler walk coboundary (Lyapunov phase correction)

Status: **CLOSE** (no bounded-complexity phase correction gives
uniformly nonnegative one-step or block-step drift; the even-square
tower kills every bounded \(\psi\), and the fan defeats the rest)

Termination-side Phase 0. Not a halt theorem, not a DK tightening,
not a reopen of the closed state-only \(\log/\log\log\) Lyapunov
([juggler_cycle_block_potential.md](juggler_cycle_block_potential.md)),
and not a Paper A edit.

## Problem

The leading walk cocycle is
\[
\Delta u=\log_2(\ln J(x)/\ln x)
\to
\begin{cases}
+\log_2(3/2),&x\text{ odd},\\
-1,&x\text{ even},
\end{cases}
\]
plus floor defects. The fan survives because
\(o\log_2 3-L\approx 0\). Does a phase correction
\(\Phi(x)=\log_2\ln x+\psi(\xi(x))\) produce
\(\Phi(J(x))-\Phi(x)\ge c(x)\) with \(c\ge 0\) (and \(c>0\)
infinitely often) outside a finite set, or the same at block scale
on AboveAnchor transitions?

## Exact statement

**One-step bounded \(\psi\) is impossible
(EXACT — HUMAN PROOF).**
On every even perfect square \(x=k^2\ge 16\),
\(J(x)=k\) and \(\Delta u=-1\) exactly. Along the tower
\(k^{2^N}\to k^{2^{N-1}}\to\cdots\to k\), a one-step inequality
\(\Delta\Phi\ge 0\) would force \(\psi(k)-\psi(k^{2^N})\ge N\).
A bounded \(\psi\) cannot do this. A finite exceptional set cannot
absorb the infinite tower. Witness \(k=4\):
\(2^{32}\to 2^{16}\to 2^8\to 2^4\to 2^2\), leading sum \(-4\).

**Rational floor-error phases vanish on high even powers
(EXACT — HUMAN PROOF).**
\(\{\sqrt{x}\}\) and \(\{x^{3/2}\}\) have increment \(0\) on even
fourth powers (witness \(16\to 4\)). Any finite combination of
\(\{x^{2^{-m}}\}\) vanishes on even \(2^{m+1}\)-th powers.

**No bounded-complexity \(\psi\) rescues the sampled families
(COMPUTATIONALLY VERIFIED).**
On \(n\in[16,4000]\) plus the seven high-flyers, a grid of
sawteeth \(a\{\alpha x^\beta\}\), the three-phase floor-error
basis, and a \(2\)-mode Fourier basis was maximised for the
minimum drift. Best minima stay negative on universe one-step
(\(-1.20\)), AboveAnchor prefix one-step, sliding length-\(19\)
blocks (\(-3.76\) baseline, still \(<0\) after the search), and
first \(O^a E^r\) blocks (\(-2.7\)). Even-step
\(\Delta\{\xi\}\) has both wings for
\(\{\sqrt{x}\}\), \(\{x^{3/2}\}\), \(\{x^{1/4}\}\), and
\(\{\pi\log_2 x\}\).

**The fan defeats the correction (OBSERVATION).**
Near-neutral length-\(19\) windows have leading
\(\approx\theta_{19}\approx 0.0196>0\); zero correction is
optimal there (\(221\) windows, min \(0.0099\)). The same
prefixes carry post-peak \(19\)-blocks with leading \(\le -1\)
(adversary \(n=1999\): fan \(0.0195\), collapse \(-1.565\);
\(n=761\): \(11+11\) windows, fan \(0.0125\), collapse
\(-3.58\)). A \(\psi\) large enough to lift the
collapse exceeds the fan margin unless \(\Delta\psi\) is
magically aligned. No tested \(\psi\) is.

No cycle of any length, and no exclusion of divergent flights, is
claimed.

## Current literature

- State-only \(\log/\log\log\) Lyapunov —
  **REFUTED** / **REPARAMETERIZATION** of \(T<n\)
  ([juggler_cycle_block_potential.md](juggler_cycle_block_potential.md)).
  This branch is the coboundary, not that slogan.
- Flight envelope on `AboveAnchor` —
  **EXACT — LEAN VERIFIED**
  (`aboveAnchor_flight_envelope`).
- Return quantization / fan scale \(\theta_{19}\approx 0.01955\) —
  **EXACT — HUMAN PROOF**
  ([juggler_flight_return_quantization.md](juggler_flight_return_quantization.md)).
- DK as a kill —
  **CLOSE** on flights
  ([juggler_flight_dk_pricing.md](juggler_flight_dk_pricing.md));
  this branch does not tighten DK.
- Endpoint coboundary \(e(L)=g(u_L)\) —
  failed on the walk-excess census
  ([juggler_cycle_walk_sharpness.md](juggler_cycle_walk_sharpness.md)).
  Different object (word-excess, not a state phase).

Project relationship: **refuted** as a uniformly positive
cocycle correction of bounded complexity.

## Branch budget

```text
Mathematical target     Does any bounded-complexity phase
                        correction Φ = log₂ln x + ψ(ξ(x))
                        produce uniformly nonnegative one-step
                        or block-step drift on all sufficiently
                        large AboveAnchor transitions?
Novelty hypothesis      the fan is invisible to log log but not
                        to a fractional phase; floor errors may
                        cobound
Falsifier               every tested (a,α,β) and small Fourier
                        basis has a large-x transition with
                        ΔΦ < 0; or any bounded ψ fails on the
                        even-square tower
Existing machinery      flight envelope, AboveAnchor prefixes,
                        floor_power, closed state-only Lyapunov
Maximum Phase-0 scope   grid + small Fourier fit on exact
                        transitions in n ≤ 4000 and the named
                        adversaries; one-step and length-19 /
                        first-OE blocks. No Lean, no Paper A,
                        no N0
Promotion criterion     a non-zero ψ with min drift ≥ 0 on a
                        negative family of useful size
Stop criterion          one-step killed by bounded ψ; no
                        block-step rescue; the fan margin is
                        smaller than the collapse need
```

## Closed-bridge gates

- **CLOSE** if the even-square tower forces \(\sum\Delta u=-N\)
  against a bounded coboundary.
- **CLOSE** if every tested family keeps a negative min drift.
- **CLOSE** if near-neutral fan windows are already optimal at
  \(\psi=0\) and collapse windows need \(|\Delta\psi|\ge 1\).
- **PROMOTE** only if a non-zero \(\psi\) lifts a negative
  family of size \(\ge 32\).
- Do **not** raise \(N_0\). Do **not** tighten DK. Do **not**
  reopen the block potential. Do **not** edit Paper A. Do
  **not** add Lean.

## Explicitly out of Phase-0

An unbounded \(\psi\), a word-dependent ranking function, a new
DK envelope, a floor raise, CLI, visualization, Paper A/B edit.

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- \(\Phi=\log_2\ln x\) —
  **KNOWN**; even-square increment exactly \(-1\)
- Bounded coboundary one-step —
  **REFUTED** (tower telescoping)
- \(a\{\alpha x^\beta\}\) and the floor-error Fourier basis —
  **REFUTED** as a uniform correction on the sampled families
- Fan-window rescue by a phase —
  **false**; \(\psi=0\) is optimal on those windows
- Halt / no cycle of any length — not claimed

## Experiments

- Probe: `research.juggler_sequence.walk_coboundary`
- Artifact:
  `data/research/juggler/walk_coboundary/summary.json`
- Tests:
  `tests/research/juggler_sequence/test_walk_coboundary.py`
- Window: one-steps and first OE-blocks on \([16,4000]\);
  AboveAnchor prefixes to \(256\) bits; adversary prefixes
  \(761,1089,1999\) to \(900\) bits; seven high-flyer starts.
  Fast suite only. No CLI. No new Lean. No \(N_0\) raise.

## Conjectures

`juggler_walk_phase_correction` — **REFUTED**.

## Counterexamples

- Even squares \(x=k^2\to k\): leading \(-1\). Tower
  \(2^{32}\to\cdots\to 4\): any bounded \(\psi\) fails.
- \(16\to 4\): \(\{\sqrt{x}\}\) and \(\{x^{3/2}\}\) increments
  vanish, so those phases cannot move the \(-1\).
- \(24\to 4\): worst universe one-step, min \(\approx-1.20\).
- \(n=1999\): same prefix has fan leading \(0.0195\) and
  collapse \(-1.565\).
- \(n=761\): \(43\) length-\(19\) windows, \(11\) fan and
  \(11\) collapse, leading \(0.0125\) versus \(-3.58\).

## Formalization

None added. The even-square identity is elementary. No `sorry`.
No Paper A edit. Do not add `WalkCoboundary.lean`.

## Results

Classification **WALK_COBOUNDARY_DEFEATED**.

- One-step is a theorem against every bounded \(\psi\), not a
  grid accident.
- The computational search does not produce a block-step
  candidate either: sliding \(19\)-blocks and first OE-blocks
  stay negative, and the fan-scale windows are already
  nonnegative at \(\psi=0\).
- This is not a DK improvement and not a leftover-killer.

## Open questions

None from a bounded state-phase coboundary. An unbounded
correction, or a word-dependent ranking, would be a different
object; not opened. The fan-minimum CF reduction stays the
cycle frontier.

## Decision

**CLOSE.** The discovery criterion is answered in the negative.
Every bounded \(\psi\) fails one-step on the even-square tower,
and the fan’s \(0.02\)-margin is smaller than the collapse those
same prefixes actually take. The most natural cocycle corrections
are defeated. Best next question: none from this door; do not
start an unbounded-\(\psi\) rescue.

## Publication assessment

Status: `EXPLORATORY`. Laboratory negative knowledge on a
Lyapunov rewrite of the walk. Not a paper candidate and not a
Paper A/B or flight-note edit.

# Juggler `winkler_phase_collapse`

Winkler's normalised first-passage count, measured at every order rather than on the
record orders his theorem covers. Probe:
[winkler_phase_collapse.py](../../src/research/juggler_sequence/winkler_phase_collapse.py).
Test: [test_winkler_phase_collapse.py](../../tests/research/juggler_sequence/test_winkler_phase_collapse.py).
Ledger: `J-winkler-ratio-collapses-onto-the-phase`.

## Problem

Is Winkler's normalised count `R+_r = r c_r / C_r` of A100982 a function of the phase
`delta_r = {r log2 3}` alone?

## Exact statement

With `alpha = log2 3`, `m_r = floor(r alpha)`, `c_r = A100982(r) = M_(m_r + 1)` and
`C_r = binom(m_r - 1, r - 1)`: does there exist a function `F` on the circle with
`R+_r = F(delta_r) + o(1)` as `r` tends to infinity, and where is `F` discontinuous?

## Current literature

- `winkler-2026-admissible-qx1-sequences`, Corollary 12: `liminf R+_r = 1` and
  `limsup R+_r = alpha/(alpha - 1)`, attained exactly on the lower and upper record
  orders of `{r alpha}`. An envelope on two sparse sets of orders, with nothing said
  about a general `r`. The whole profile was first measured here; the qualitative specialization is now Lean-checked (Section 13 of the comparison note).
- `winkler-2026-marked-rotations`, Proposition 34: the asymptotic scale
  `C_r = kappa rho_alpha^(delta_r) B^r r^(-1/2) (1 + O(1/r))`, so the explicit part of
  the phase dependence sits in `C_r`, and `R+_r` carries the rest, bounded but unknown.
- Paper B, Section 6, and `J-paper-b-meander-prefactor-is-almost-periodic`: the survivor
  prefactor `psi({d beta})` with jumps on the orbit `{n beta}`, conjectural. Since
  `c_r = M_(m_r+1)` and `M_d = 2 N_(d-1) - N_d`, a limit for `psi` predicts one for
  `R+_r`. This branch measures the prediction on the other side.

## Branch budget

- **Target:** decide numerically whether `R+_r` depends on `r` only through `delta_r`.
- **Novelty hypothesis:** no public source describes `R+_r` away from the record orders.
- **Falsifier:** within-bin spread comparable to the across-bin range, or a shape that
  drifts between windows of `r`, or a shuffled-phase control that collapses as well.
- **Already killed by?:** none. Not a cycle, termination or floor claim, so none of the
  Diophantine walls or local-attack clusters in
  [negative_knowledge.md](../negative_knowledge.md) applies; it is a measurement on
  counts the laboratory already owns.
- **Existing machinery:** `jump_spectrum.survivor_counts`, the identity
  `c_r = M_(m_r+1)` of `J-winkler-sandwich-holds-on-the-laboratory-counts`.
- **Maximum Phase-0 scope:** one depth, 5000, three windows, one control.
- **Promotion criterion:** a stable collapse with a failing control.
- **Stop criterion:** any falsifier above.

## Balanced-ternary formulation

None. The object is the binary Beatty staircase of `log2 3`; balanced ternary plays no
role.

## Why BT may be relevant

It is not. The branch lives in the Collatz-side counting that Paper B shares with the
Juggler map.

## Candidate operations / invariants

The phase `delta_r`; the one-sided means of `R+` across an orbit point `{n alpha}`.

## Experiments

Depth 5000 gives the orders `r = 1..3154`. `c_r` reproduces A100982. Binned by
`delta_r` into 20 bins:

| window of r | across-bin range | within-bin spread | signal |
|---|---|---|---|
| 395 to 788 | 1.6852 | 0.0334 | x50.5 |
| 789 to 1577 | 1.6860 | 0.0324 | x52.0 |
| 1578 to 3154 | 1.6869 | 0.0326 | x51.7 |
| shuffled phases, 1578 to 3154 | | | x0.39 |

The per-bin shape drifts by 0.0069 and then 0.0011 between successive windows. Jumps
across the orbit points, one-sided windows of width 0.006, orders `r >= 1052`:

| n | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|---|---|
| jump | +0.633 | +0.148 | +0.188 | +0.066 | +0.098 | +0.039 | +0.023 | +0.042 |

Six control points, at the midpoints of the widest gaps between the first 40 orbit
points, show +0.0017 to +0.0045. The first hand-picked controls were not controls: two
of four sat on orbit points 8 and 11, which is why the controls are now chosen by rule
and checked by a test.

## Conjectures

`R+_r = F(delta_r) + o(1)` with `F` rising from 1 at `delta = 0+` to `alpha/(alpha - 1)`
at `delta = 1-`, and upward jumps exactly on the orbit `{n alpha}`.

## Counterexamples

None found.

## Formalization

The original numerical investigation supplied no formalization. The 23 September
extension [BeattyPhaseTransfer.lean](../../formal/Problems/Juggler/BeattyPhaseTransfer.lean)
checks the two phase coordinates, exact normalized count identity, cancellation of
survivor jumps into certificate counts, and monotonicity, one-sided limits and jump
sizes of a summable positive series. Its moving-kernel convergence theorem assumes
uniform domination, fixed-index approximation and a vanishing far remainder.
The continuation in
[BeattyRenewalLimit.lean](../../formal/Problems/Juggler/BeattyRenewalLimit.lean)
and [BeattyRenewalSeries.lean](../../formal/Problems/Juggler/BeattyRenewalSeries.lean)
now proves the analytic inputs for coefficients of the formal exponential:
recurrence, summability, three-halves decay, the near/far split and moving limit.
[BeattySurvivorProfile.lean](../../formal/Problems/Juggler/BeattySurvivorProfile.lean)
reaches the existing `MeanderShape` for an explicit positive profile using the
actual survivor counts, conditional on the exact counting exponential identity
and the terminal binomial asymptotic. The new
[BeattyCounting.lean](../../formal/Problems/Juggler/BeattyCounting.lean)
discharges the actual counting input, and
[BeattyBinomialBounds.lean](../../formal/Problems/Juggler/BeattyBinomialBounds.lean)
proves coarse terminal bounds and unconditional sharp three-halves order.
The subsequent endpoint and certificate modules discharge the fine terminal
input and identify the complete jump series. The formal limit is `o(1)`;
the quantitative error remains written mathematics.

Extracted corollaries: the actual exponential identity is equivalent to the
purely integer recurrence `n N_n = sum_{j<n} T_(n-j) N_j`; coarse two-sided
square-root terminal bounds already imply sharp three-halves coefficient
order without a phase limit; and summability yields a uniform finite-profile
error bound at every phase, including jumps. These compile in the same
modules. Section 12 discharges the counting, coarse-bound and summability
premises at the logarithmic slope. See the
[comparison note](../theory/juggler_beatty_phase_transfer_note.md).

## Results

`J-winkler-ratio-collapses-onto-the-phase`, computationally verified: the collapse, its
convergence, the failing control, and the jumps on the orbit, as tabulated above.

**23 September: explicit profile and written convergence argument.** With
`beta = 1/alpha`, `q = 1-beta`, `B = alpha^alpha/(alpha-1)^(alpha-1)` and
`w_r = c_r/(B^r q^delta_r) = c_r beta^r q^(m_r-r)`, the new
[comparison note](../theory/juggler_beatty_phase_transfer_note.md) derives

    F(delta) = 1 + sum_{delta_r < delta} w_r,
    sum_r w_r = 1/(alpha-1),
    R+_r = F(delta_r) + O(r^(-1/2)).

The first jump is exactly `beta = 0.630929753571457...`. The written proof constructs
the survivor profile from the binomial-tail Spitzer series; it obtains the necessary
coefficient bound before passing to a limit, and handles the moving discontinuities
without continuity assumptions. The qualitative logarithmic-slope specialization is now an end-to-end Lean
theorem. The general irrational-slope statement and the quantitative rate
remain written mathematics; no manuscript revision is made.

New probe: [beatty_phase_transfer.py](../../src/research/juggler_sequence/beatty_phase_transfer.py).
Test: [test_beatty_phase_transfer.py](../../tests/research/juggler_sequence/test_beatty_phase_transfer.py).
Exact counts through depth 8000 give orders 1–5047; an independent binomial-coefficient
recurrence is checked through depth 256. The first eight predicted jumps agree with
the earlier window estimates at their resolution. Floating-point profile diagnostics
are not interval certificates.

**23 September: unconditional sharp order in Lean.** The exact integer
recurrence now holds for every degree, not merely through the finite check.
The first-term comparison `binom(n,k) <= T_n <= (5/2) binom(n,k)`, with
`k=floor(n*beta)+1`, and coarse global Stirling estimates imply square-root
terminal bounds. The compiled conclusion is `N_n=Theta(v^n/(n sqrt(n)))`,
with positive constants uniform at every positive depth. The existing
`survivorDensity =Theta[atTop] model` is therefore unconditional.
Summability of `N_n/v^n` is unconditional too; it makes the existing profile
bounds and uniform finite approximation applicable. The next continuation, recorded below, completes the fine phase limit
and the full certificate profile. No priority or
integer-trajectory termination claim is attached to this formalization.

Continuation triage: target the exact normalization and full jump formula; possible
novelty is the positive cumulative series, not the classical counting identity.
Falsifiers are a normalization mismatch, wrong jump signs or a nonvanishing
uncontrolled remainder. Already killed by? Neither the closed recurrence-only route
nor residue-class fitting applies: this uses the full generating-function identity.
Existing machinery is the exact DP, certificate recurrence and ladder profile.
Maximum scope: this comparison note, one bounded probe and one Lean transfer module.
Promote a checked formula with an explicit proof boundary; park the limit if its
tail interchange is unjustified. No next branch is opened.

**23 September: completed qualitative phase theorem.** The new endpoint module
proves the exact fractional-part Stirling correction and geometric-tail limit.
The critical mass module uses finite first moments and survivor decay to prove
first-passage mass one. The certificate series module proves positive weights,
total jump mass `1/(alpha-1)`, first jump `beta`, phase injectivity and exact
one-sided traces. The identification module proves equality of the full
transferred profile with `1+sum_{delta_r<delta}w_r` on `(0,1)`, including at
atoms. Finally `certificate_phase_asymptotic` proves the original
`r c_r/binom(m_r-1,r-1)-F(delta_r) -> 0` without unproved inputs. See Section 13
of the [comparison note](../theory/juggler_beatty_phase_transfer_note.md).

**23 September: complete accumulation set.** The new
[certificate cluster module](../../formal/Problems/Juggler/BeattyCertificateCluster.lean)
proves that all subsequential limits of `R+_r` form exactly the envelope
`[1,alpha/(alpha-1)]` with the open intervals
`(F(delta_j),F(delta_j)+w_j)` removed. This is a nonempty compact perfect set
of Lebesgue measure zero. Both endpoints of every gap are subsequential
limits; every closed interval strictly inside a gap is eventually avoided.
The generic geometry and recurrent-sampling argument are in
[BeattyProfileGeometry.lean](../../formal/Problems/Juggler/BeattyProfileGeometry.lean).
Section 14 of the comparison note records the proof and scope.

Continuation triage:

```text
Mathematical target     Identify all certificate accumulation values and exact gaps.
Novelty hypothesis      The specialization refines the known extremal envelopes;
                        the generic pure-jump geometry is not claimed new.
Falsifier               A missing continuous component or overlapping gaps.
Already killed by?      No matching obstruction; the proved exact series identity
                        removes the missing-component issue. No recurrence-only
                        shortcut or unproved frequency assumption is used.
Existing machinery      Positive weights, total mass, one-sided traces, phase limit.
Maximum Phase-0 scope   Generic range geometry and logarithmic-slope specialization.
Promotion criterion     Kernel-checked exact cluster set and null perfect geometry.
Stop criterion          A new unproved analytic premise is needed.
PROMOTE
```

## Open questions

The qualitative logarithmic-slope phase theorem and normalization are complete
in Lean, as is the complete accumulation set. An empirical limiting distribution
is not yet formalized. Other remaining mathematical extensions are a quantitative remainder,
effective numerical truncation bounds, and generalization from the concrete
logarithmic slope to arbitrary irrational `1<alpha<2`. Literature comparison
is separate from proof checking; existing paper claims and releases retain
their earlier evidence labels.

## Decision

`PROMOTE` -- the actual normalized certificate counts have the explicit positive
jump-series asymptotic, with its full normalization and strict atom convention
proved. The continuation also identifies the full null perfect accumulation set
and its exact gaps. No new branch, publication, priority claim or
trajectory-termination claim is opened.

## Publication assessment

Status: `PAPER_CANDIDATE`, as a remark in Paper B, Section 6, not as a paper of its own:
a nontrivial computation with a clear distinction from Corollary 12, the envelope.

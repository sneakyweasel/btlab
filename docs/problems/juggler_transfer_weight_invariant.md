# Juggler transfer-weight invariants for the four-step moment

Status: **CLOSE** (listed candidates saturate, are support-local, or
are the already-named \(L^2\) / good-base objects; no new sufficient
inequality)

Not a third formulation of the frontier, not a pressure census, not a
halt theorem, and not a Paper C rewrite. The object is the existing
hypothesis `J-tao-pressure-form`. Here \(W_t\) is the tilted live
pushforward on current states \(m=J^t(n)\), not the BT tail-reverse
operator.

## Problem

The death-adjusted four-step product of
[TiltedShare.lean](../../formal/Problems/Juggler/TiltedShare.lean)
contracts when \(Z_{t+4}/Z_t\le a_\theta^4\). Deaths vanish on the
high odd-heavy states that produce pressure. Do the actual reachable
weights \(W_t\) carry a map-specific invariant — ancestral capacity,
landing multiplicity, or collision concentration — that forces the
\(W_t\)-mass of \(\mathtt{EOOO},\mathtt{OEOO},\mathtt{OOEO},\mathtt{OOOE},\mathtt{OOOO}\)
below that threshold without \(L^2\), cylinder estimates, or PS
inversion?

## Exact statement

Let \(x=e^\theta\), \(a_\theta=\tfrac12(1+x)\), and \(\theta=\theta_{19}\).
Write \(S\) for the five positive four-letter cells and \(\mu=W_t/\|W_t\|_1\).
The exact four-step number is the word expansion of \(W_t\) (deaths
contribute 0), equal to the TiltedShare product
\(\prod_{j=0}^{3}(1+(x-1)r_{t+j})\). Need \(Z_{t+4}/Z_t\le a_\theta^4\).

A one-sided bound on \(\mu(S)\) forces that inequality only if the
remaining live mass sits on two-odd words (factor \(x^2<a_\theta^4\)).
At \(\theta_{19}\) the cut is
\[
1.117\,\mu_{\mathtt{OOOO}}+0.449\,\mu_{3\text{-odd}}<0.0749.
\]
Fair-coin already puts unweighted mass \(1/16+4/16\) on those cells and
misses the cut, yet its exact moment is \(a_\theta^4\) because the
eleven complementary words pay the deficit. So a one-sided five-word
bound strong enough to force contraction is stricter than fair-coin
unless the rest is also controlled.

Location-free inequalities supplied by the listed candidates:

- total mass: \(\mu(S)\le 1\)
- max atom: \(\mu(S)\le n_S\cdot\max W/\|W\|_1\le 1\)
- collision energy \(E=\sum\mu(m)^2\): \(\mu(S)\le\sqrt{n_S E}\); large
  \(E\) makes this worse
- ancestry multiplicity: the same bound on the counting measure

None meets the cut without a bound on \(n_S=\#(\mathrm{supp}\cap S)\),
which is location.

**\(OOOO\) injectivity (EXACT geometry; COMPUTATIONALLY VERIFIED).**
Four odd steps are unique
(`odd_preimage_unique` in
[Preimages.lean](../../formal/Problems/Juggler/Preimages.lean)).
On the five live starts \(265,271,289,293,309\) the normalized atom
profile, energy \(1/5\), and ancestry \((1,1,1,1,1)\) are relabelled;
tilted mass grows by \(x^4\approx 2.04\,a_\theta^4\). Every
concentration statistic saturates on the most expanding cell.

**Unbounded \(OE\) landing (EXACT geometry; COMPUTATIONALLY VERIFIED).**
All evens in \([M^2,(M+1)^2)\) map to \(M\)
(`even_preimage_iff`). Odd starts with
\(M^4\le n^3<(M+1)^4\) and even image collide at \(M\) after
\(\mathtt{OE}\). The integer span of that \(n\)-interval is
\(3,6,14,29,62\) at \(M=10,10^2,10^3,10^4,10^5\). On the separated
favorable targets \(2001\) (\(\mathtt{OOOO}\)), \(20001\)
(\(\mathtt{OOOE}\)), \(200001\) (\(\mathtt{OOEO}\)) the genuine odd
ancestor counts are \(3,9,21\). Relative mass of one target is small,
so this does not refute an aggregate four-step theorem. It kills every
bounded-multiplicity or support-local capacity.

**Bounded pushforward (OBSERVATION).** Odd starts in \((2001,3999]\)
at \(N_0=260\), depths \(0..8\): \(\mathrm{ratio}_4\le 0.904<1\), and
the one-sided cut never holds. Deaths at this floor pay the deficit.
This is not an invariant and does not promote.

## Current literature

- Tao note §10 / Paper C §9, `J-tao-pressure-form` — `known`.
- [juggler_pressure_direct.md](juggler_pressure_direct.md) /
  `J-pressure-direct-routes` — `known`: last-even reset, \(S\)-sampling,
  Walsh product. Not reopened.
- [juggler_pressure_external_average.md](juggler_pressure_external_average.md)
  / `J-pressure-external-average` — `known`.
- [juggler_effective_tower_height.md](juggler_effective_tower_height.md)
  / `J-tower-absorption` — `known`: good-base reset. Not reopened as a
  location invariant.
- `J-tao-cylinder-forms-reparameterization` — `known`: collision energy
  of \(W_t\) is the \(L^2\) form.
- `odd_preimage_unique`, `even_preimage_iff` — `known`.
- First-collision / seam ancestry — `known`; those are word meetings,
  not this object. Not reopened.

## Branch budget

```text
Mathematical target     Find a transfer-preserved I(W_t) that forces
                        the W_t-mass of EOOO,OEOO,OOEO,OOOE,OOOO
                        below the exact four-step contraction threshold.
Novelty hypothesis      Even fibers are intervals, odd fibers are unique,
                        and atoms record ancestry. A capacity or collision
                        invariant might survive maximal spatial variation.
Falsifier               Reachable weights concentrate on the five cells
                        while satisfying every candidate, or controlling
                        the candidate is live pressure / pair correlation.
Existing machinery      WeightSplit / TiltedShare product; Walsh identity
                        (Tao §10.4(c)); even_preimage_iff,
                        odd_preimage_unique; first-collision factorization
                        (cycle/word meetings, not this object);
                        pressure censuses.
Maximum Phase-0 scope   Write the sharp inequalities; lock the two geometric
                        kills on tiny exact witnesses; one small bounded
                        pushforward. No framework unless a candidate crosses.
Promotion criterion     One map-specific I is propagated and gives a strict
                        one-sided five-word bound without L^2, cylinders,
                        or PS inversion.
Stop criterion          Every listed candidate saturates on reachable
                        weights, needs forbidden correlation, or gives
                        only a constant loss.
```

## Balanced-ternary formulation

None. The objects are tilted pushforwards of ordinary positive integers.

## Why BT may be relevant

Not relevant here; recorded for the template.

## Candidate operations / invariants

- Mass / max-atom / collision energy / ancestry multiplicity —
  **REFUTED** as one-sided contraction invariants: location-free
  bounds are \(1\), and on \(\mathtt{OOOO}\) the profile is only
  relabelled.
- Ancestral capacity / landing multiplicity — **REFUTED** as
  support-local invariants: the \(\mathtt{OE}\) span is unbounded.
- Collision energy of \(W_t\) as a global \(I\) —
  **REPARAMETERIZATION** of
  `J-tao-cylinder-forms-reparameterization`.
- Location of atoms after a high-walk \(E\) —
  **REPARAMETERIZATION** of the good-base / sparse-image split
  (`J-pressure-direct-routes`, tower-height CLOSE).
- Bounded pushforward \(\mathrm{ratio}_4<1\) — **OBSERVATION** only.

## Experiments

- Probe: `research.juggler_sequence.transfer_weight_invariant`
  (`python -m research.juggler_sequence.transfer_weight_invariant`).
- Artifact: `data/research/juggler/transfer_weight_invariant/summary.json`.
- Tests: `tests/research/juggler_sequence/test_transfer_weight_invariant.py`.
- Fast suite locks the inequalities, the \(\mathtt{OOOO}\) relabel, and
  the \(\mathtt{OE}\) span. The 1000-start pushforward is in the
  artifact only.

## Conjectures

None new. `juggler_loglog_depth_cylinder_bound` stays **ACTIVE**;
\(\mathrm P_\theta\) / \(\mathrm M_{\theta,q}\) remain its weakest
form.

## Counterexamples

Not a counterexample to \(\mathrm P_\theta\) or \(\mathrm M_{\theta,q}\).
The \(\mathtt{OOOO}\) five-start cohort is a counterexample to
"concentration statistics control the five-word mass": \(\mu(S)=1\)
while energy and max-atom stay \(1/5\). The \(\mathtt{OE}\) targets
are a counterexample to any bounded landing multiplicity.

## Formalization

None new. The two geometric kills are
`odd_preimage_unique` and `even_preimage_iff`. Lean-ifying the
inequalities ahead of an estimate would be machinery gravity.

## Results

Classification **TRANSFER_WEIGHT_INVARIANTS_SATURATE_OR_REPARAM**
(`J-transfer-weight-invariant`).

- The one-sided five-word cut at \(\theta_{19}\) is
  \(1.117\,\mu_4+0.449\,\mu_3<0.0749\). Fair-coin misses it; the
  exact moment identity does not.
- Location-free mass / max-atom / energy / ancestry bounds are \(1\)
  and do not meet the cut.
- \(\mathtt{OOOO}\) injectivity relabels every concentration
  statistic and grows mass by \(e^{4\theta}\approx 2.04\,a_\theta^4\).
- \(\mathtt{OE}\) preimage spans and favorable-target ancestor
  counts are unbounded. Support-local capacity dies.
- Controlling where the atoms sit is the good-base reset or the
  pair-correlation form, both already named.
- A small exact pushforward has \(\mathrm{ratio}_4<1\). OBSERVATION
  only.
- Not claimed: \(\mathrm M_{\theta,q}\), \(\mathrm P_\theta\),
  termination, any new cylinder bound.

## Open questions

None in this laboratory. The statement to export remains
\(\mathrm M_{\theta,q}(C)\) with the depth budget \(2^{-d/C}\), as the
Tao dossier already recorded.

## Decision

**CLOSE.** The stop criterion fired: mass, max-atom, collision
energy, and ancestry saturate on the injective \(\mathtt{OOOO}\)
cell or give only the constant loss \(1\); landing multiplicity is
unbounded on genuine \(\mathtt{OE}\) collisions; any leftover
location invariant is the good-base / \(\mathrm H_q\) split or the
\(L^2\) pair-correlation form. The small pushforward contraction is
an observation, not an invariant. Do not reopen as a
concentration statistic, a bounded-multiplicity capacity, a
location/gap/even-fiber framework, a Walsh expansion, or another
pressure census. Best next question: none on this line; the
no-momentum form stays the export.

## Publication assessment

Status: `ARCHIVED`. A classification of three candidate invariants
on the existing pressure object. Not a paper claim; no Paper A or
Paper C edit.

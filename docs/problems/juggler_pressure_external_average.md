# Juggler pressure: external averaging of \(M_{\theta,q}\) / \(P_\theta\)

Status: **CLOSE** (both ANT readings of “external averaging” are
reparameterizations or recorded kills; no new sufficient inequality)

Not a third formulation of the frontier, not a proof of
\(\mathrm M_{\theta,q}\) or \(\mathrm P_\theta\), not a halt theorem,
and not a Paper C rewrite. The objects stay `J-tao-pressure-form`.

## Problem

Tao note §10.5 / Paper C §9.4 recorded the pressure / no-momentum
hypotheses as a mean-over-cylinders question for analytic number theory
and did not pursue an approach. The notes’ own phrase “mean over
characters, not a supremum” is already the pair-correlation form of
\(\mathrm H(C,A)\) (`J-tao-cylinder-forms-reparameterization`); do not
re-derive it. After the laboratory routes were classified
([juggler_pressure_direct](juggler_pressure_direct.md)), two other
natural readings remain: complete the single live-tilted odd sum
without a Walsh expansion of the tilt, and take a harmonic / dyadic
average of \(\mathrm P_\theta\). Is either a new sufficient inequality?

## Exact statement

Let \(\tau(n)\) be the entrance time into \([1,N_0]\), \(o_t(n)\) the
odd count of the first \(t\) letters, \(N=y/2\),
\(d=\lceil C L(y)\rceil\), \(a_\theta=\tfrac12(1+e^\theta)\), and
\[
Z_t(y)=\sum_{\substack{n\text{ odd}\in(y,2y]\\ \tau(n)>t}}e^{\theta o_t(n)}.
\]
Write \(s_\theta(t)=Z_t^{\mathrm{odd}}(y)/Z_t(y)\) with
\(Z_t^{\mathrm{odd}}\) as in Identity A. Live restriction and tilt
are as in `J-tao-pressure-form`.

**Parseval / large sieve (already classified; not re-derived).** The
notes’ “mean over characters” is the \(L^2\) mean of the Walsh sums
\(W_T=\sum_n\prod_{s\in T}(-1)^{J^s(n)}\). Parseval converts that mean
into the collision count \(\mathcal C_t\), and Walsh inversion converts
any two-sided bound back into \(\mathrm H(C,A)\) with another \(A\).
That is `J-tao-cylinder-forms-reparameterization`.

**Identity A (completed single sum).**
\[
Z_t^{\mathrm{odd}}(y)=\sum_{\substack{n\text{ odd}\in(y,2y]\\ \tau(n)>t}}e^{\theta o_t(n)}\,1_{\mathrm{odd}}(J^t(n)).
\]
The averaging reading: estimate this as one arithmetic sum by
completing \(1_{\mathrm{odd}}(m)=(1-(-1)^m)/2\) and smoothing
\((y,2y]\), without expanding \(e^{\theta o_t}\) in Walsh characters.

The identity \(1_{\mathrm{odd}}(m)=(1-(-1)^m)/2\) is elementary, so
\[
Z_t^{\mathrm{odd}}=\tfrac12 Z_t-\tfrac12\sum_{\tau(n)>t}e^{\theta o_t(n)}\,(-1)^{J^t(n)}.
\]
Vaaler replaces \((-1)^{J^t(n)}=e(J^t(n)/2)\) by a short Fourier
polynomial in the nested floor \(J^t(n)\). The amplitude
\(e^{\theta o_t(n)}1_{\{\tau>t\}}\) is constant on every depth-\(t\)
cylinder. The completed sum is therefore a cylinder-weighted nested
phase
\[
\sum_w e^{\theta o(w)}\,1_{\mathrm{live}(w)}\sum_{n\in[w]\cap(y,2y]}e\bigl(h\,J^t(n)/2\bigr).
\]
Three laboratory inputs, all recorded:

- Expand the amplitude in Walsh characters: pressure-direct route B2.
  Fixed order is \(e^{o(d)}\); the tail is \(e^{\Theta(d)}\); two-sided
  tail control is `J-tao-cylinder-forms-reparameterization`.
- Apply van der Corput / Weyl differencing to the nested phase
  \(e(h J^t(n)/2)\) without expanding the amplitude: the two-monomial
  leftover, or the depth-uniformity budget \(cC<1\) (Paper C
  Proposition 10.3). Differencing has \(c\ge 1\).
- Drop the amplitude, or truncate it to the first \(k=o(d)\) letters:
  Paper B at depth \(t\to\infty\), killed by Tao note §10.4(e).

Completing \(1_{\mathrm{odd}}\) without a Walsh expansion of the tilt
does not evade the cylinder partition: the tilt *is* that partition.
Identity A is not a new sufficient inequality.

**Identity B (harmonic / dyadic average).**
\[
\Pi(Y)=\frac1{\log Y}\sum_{2^k\le Y}\frac{Z_{d(2^k)}(2^k)}{N_k\,a_\theta^{d(2^k)}}.
\]

*Sufficiency of \(\Pi\) as written.* Let
\(\rho_k=Z_{d(2^k)}(2^k)/(N_k a_\theta^{d_k})\). A bound
\(\Pi(Y)\le e^{o(d(Y))}\) is a Cesàro mean of the *normalized tilted
moments*. Markov converting a moment into a live count is per-scale:
\(\#\{\tau>d\}_k\le e^{-\theta p_C d_k}Z_{d_k}\). The Cesàro mean
allows a spike \(\rho_{\max}\lesssim(\log Y)^{1+o(1)}\), and that one
block contributes \((\log Y)^{1-e(C)+o(1)}\) to the harmonic live
sum. For \(e(C)\approx 0.55<1\) the contribution grows and does not
beat contagion. \(\Pi\) as written does not suffice.

*Sufficiency of the harmonic average of live counts.* The sum
\(\sum_{n\le x}1_{\{\tau(n)>d(n)\}}/n\), restricted to a window
\((\sqrt x,x]\), is the log-measure
\(\mathbb P^{\log}_x(\tau>d)\). Proposition 11.1 of the Tao note
identifies the \(OO\)-restriction of the \(d\to\infty\) limit with
the free term \(\psi_F\). The finite-depth all-odds form differs by a
bounded factor (Paper B, depth two, on the first two letters). That
object is `J-tao-free-term-is-live-mass`. It is not named as a new
hypothesis.

*Estimate by even-block / \(OE\)-fiber productions.* A recursion for
the tilted harmonic live mass has an easy even step (backward
intervals) and an odd step that is unique-odd-preimage sampling of
the live tilted weight: tilted \(S\)-fairness of the live set,
pressure-direct route B1 / `J-tao-free-term-is-live-mass`. Even-block
and \(OE\)-fiber geometry is backward and does not intervalize a
forward cylinder \(J^t((y,2y])\); contagion productions are not the
law of \(J^t(n)\). The exact map (6.1) cannot replace contagion
(Corollary 11.2). Do not run a production estimate.

No fate is excluded. No halt theorem.

## Current literature

- Tao note §10–11 / Paper C §§9–10, §12 — `known`: the estimate those
  notes recorded as a question; the “mean over characters” sentence
  is already `J-tao-cylinder-forms-reparameterization`.
- [juggler_pressure_direct](juggler_pressure_direct.md) /
  `J-pressure-direct-routes` — `known`: last-even reset, \(S\)-sampling,
  Walsh product. Not reopened.
- `J-tao-pressure-form`, `J-tao-free-term-is-live-mass` — `known`.
- Exponent-pair two-monomial leftover — `known`; not reopened.
- Paper C Proposition 10.3 (depth-uniformity budget) — `known`.

## Branch budget

```text
Mathematical target     Is either natural ANT reading of “external
                        averaging” a sufficient inequality for
                        M_{θ,q} or P_θ that is not H, H_q,
                        S-fairness, pair-correlation, Weyl, or
                        §10.4(e)?
Novelty hypothesis      Completion of the single live-tilted odd
                        sum, or a harmonic/dyadic average of P_θ,
                        might be strictly weaker than H and not
                        already named.
Falsifier               Each identity’s error is a recorded kill
                        or a third formulation of the frontier.
Existing machinery      Tao note §10–11; Paper C §9–10, §12;
                        pressure_direct CLOSE;
                        J-tao-cylinder-forms-reparameterization;
                        J-tao-free-term-is-live-mass;
                        J-pressure-direct-routes.
Maximum Phase-0 scope   Write two identities; classify; decide.
                        No Lean, no Paper C/Tao rewrite, no
                        census, no Walsh expansion, no reset,
                        no S-sampling campaign, no N_0 raise.
Promotion criterion     A new sufficient inequality that is not H.
Stop criterion          Both identities reparameterize, hit a
                        recorded kill, or open a third
                        formulation.
```

## Balanced-ternary formulation

None. The objects are the exponent walk and nested-floor parities on
ordinary positive integers.

## Why BT may be relevant

Not relevant here; recorded for the template.

## Candidate operations / invariants

- Parseval / large sieve of Walsh characters — already
  **REPARAMETERIZATION** (`J-tao-cylinder-forms-reparameterization`).
  Pointed at, not re-derived.
- Identity A, completed single sum — **REPARAMETERIZATION** of
  pressure-direct B2 / nested-phase Weyl / §10.4(e). Completing
  \(1_{\mathrm{odd}}\) leaves a cylinder-constant amplitude.
- Identity B, \(\Pi\) as written — does not suffice (Markov does not
  pass through Cesàro). Not a sufficient inequality.
- Identity B, harmonic average of live counts — **REPARAMETERIZATION**
  of `J-tao-free-term-is-live-mass` (finite-depth log-measure live
  mass). Not named as a third formulation.
- Identity B, production estimate — **REPARAMETERIZATION** of tilted
  \(S\)-fairness / pressure-direct B1.

## Experiments

None. Classification by identities. No probe, no census, no new CLI.

## Conjectures

None new. `juggler_loglog_depth_cylinder_bound` stays **ACTIVE**;
\(\mathrm P_\theta\) / \(\mathrm M_{\theta,q}\) remain its weakest
form.

## Counterexamples

None. The identities died by reparameterization, by the recorded
Weyl / §10.4(e) kills, and by a sufficiency failure of the Cesàro
moment average, not by a counterexample to \(\mathrm M_{\theta,q}\).

## Formalization

None. The completion identity for \(1_{\mathrm{odd}}\) and the
comparison of the harmonic live sum with Proposition 11.1 are
elementary. Lean-ifying them ahead of an estimate would be machinery
gravity.

## Results

Classification **PRESSURE_EXTERNAL_AVERAGE_IS_REPARAM**
(`J-pressure-external-average`).

- The notes’ “mean over characters” is the pair-correlation form of
  \(\mathrm H(C,A)\). Not re-derived.
- Identity A: Vaaler of \(1_{\mathrm{odd}}(J^t(n))\) produces a
  cylinder-weighted nested phase. Every input is Walsh-tail
  pair-correlation, the two-monomial / Weyl budget, or §10.4(e).
- Identity B: \(\Pi\) as a Cesàro mean of tilted moments does not
  suffice. The harmonic average of live counts is the finite-depth
  log-measure live mass of Proposition 11.1. A production recursion
  has odd step equal to tilted \(S\)-fairness.
- Not claimed: \(\mathrm M_{\theta,q}\), \(\mathrm P_\theta\),
  termination, any new cylinder bound, any new frontier statement.

## Open questions

None in this laboratory. The statement to export remains
\(\mathrm M_{\theta,q}(C)\) with the depth budget \(2^{-d/C}\), as the
Tao dossier already recorded.

## Decision

**CLOSE.** The stop criterion fired: both natural ANT readings of
“external averaging” are the pair-correlation reparameterization of
\(\mathrm H(C,A)\), a cylinder-weighted nested phase already killed
as Walsh / Weyl / §10.4(e), a Cesàro moment average that does not
suffice, or the free-term live-mass reparameterization (including
tilted \(S\)-fairness on the odd step). No third formulation was
opened. Do not reopen as a signed Walsh tail, a short-interval Paper B
on the completed sum, a Tauberian upgrade of \(\Pi\), or another
pressure census. Best next question: none on this line; the
no-momentum form stays the export.

## Publication assessment

Status: `ARCHIVED`. A classification of two readings of a sentence
the paper deferred. Not a paper claim; no Paper A or Paper C edit.

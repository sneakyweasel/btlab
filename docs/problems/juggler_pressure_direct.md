# Juggler pressure: a direct attack on \(M_{\theta,q}\) / \(P_\theta\)

Status: **CLOSE** (both laboratory routes are reparameterizations or
§10.4(e) kills; no new sufficient inequality)

Not a third formulation of the frontier, not a new orbit census, not a
halt theorem, and not a Paper C rewrite. The objects are the existing
hypotheses `J-tao-pressure-form`.

## Problem

Paper C Theorem 4(c) / Tao note §10 isolated the live pressure
\(\mathrm P_\theta(C)\) and the no-momentum form \(\mathrm M_{\theta,q}(C)\)
as the weakest sufficient conditions on the concentration route, and
explicitly left open an *estimate* of those objects (a method that
addresses the pressure statement directly is not covered by the Weyl
budget). Do either of the two remaining laboratory estimates bound
them without becoming \(\mathrm H(C,A)\), a killed Paper B sum, or a
bounded-depth statement?

## Exact statement

Let \(\tau(n)\) be the entrance time into \([1,N_0]\), \(o_t(n)\) the
odd count of the first \(t\) letters, \(N=y/2\),
\(d=\lceil C L(y)\rceil\), \(a_\theta=\tfrac12(1+e^\theta)\), and
\(\mu_{\theta,t}\) the measure on live starts with density
\(\propto e^{\theta o_t}\). Write \(s_\theta(t)=\mu_{\theta,t}(J^t(n)\ \mathrm{odd})\)
and \(\mu_k=\mu_{\theta,t}(\mathrm{suffix}\ O^{\ge k})\).

**Reset split (EXACT — HUMAN PROOF, elementary).** If complementary
cylinders (an even letter among the last \(k\) steps) have odd-share
at most \(\tfrac12+\varepsilon\) and the suffix-\(O^{\ge k}\) mass is
allowed to split at 1, then
\(s_\theta(t)\le\tfrac12+\tfrac12\mu_k+\varepsilon\). Usable for
\(\mathrm M_{\theta,q}\) only if \(q_\star=\tfrac12+\tfrac12\mu_k<p_C\).

**Fair-coin suffix masses (COMPUTATIONALLY VERIFIED).** On the
odd-start fair-coin walk-live measure at the Tao depths, with the
Theorem B‴ tilt \(\theta_C=\log(p_C/(1-p_C))\):

- \(k=3\): \(\mu_3\in[0.22,0.25]\), so \(q_\star\in[0.611,0.625]\),
  above \(p_{19}=0.598\) and at \(C=41\) still above \(p_{41}=0.616\).
  No room.
- \(k=4\): \(\mu_4\in[0.13,0.17]\), so \(q_\star\in[0.567,0.584]\),
  below \(p_{19}\) at every scale \(y=10^{12},10^{50},10^{100}\).
  Numerical room exists.

**High-walk reset images are sparse (COMPUTATIONALLY VERIFIED;
geometry EXACT).** After a letter \(E\), \(J^t([w]\cap(y,2y])\) is the
forward image of a start-cylinder, not a dyadic block of odd starts.
At \(y=10^5\):

- contracted \(\mathtt{OEE}\) (\(u<0\)): 12455 members fill a span of
  24, density 1;
- high-walk \(\mathtt{OOOE}\) (\(u=0.755\)): 6342 members in a span
  \(6.08\cdot 10^8\), density \(1.04\cdot 10^{-5}\);
- high-walk \(\mathtt{OOOOE}\) (\(u=1.34\)): density \(1.45\cdot 10^{-10}\).

Paper B Theorems 4.1 / 4.4 / 4.7 apply to dyadic odd *starts*, not to
those images. The complementary term of the reset split is therefore
\(\mathrm H_q\) at unbounded depth, and dies by Tao note §10.4(e).
Even-block / OE-fiber geometry is backward and does not intervalize a
forward cylinder. Contagion productions are not the law of \(J^t(n)\).

**Forward \(S\)-sampling (REPARAMETERIZATION).** For odd starts,
odd preimages are unique, so
\(Z_d(y)=e^\theta\sum_{m\in S\cap I(y),\ \tau(m)>d-1}e^{\theta o_{d-1}(m)}\)
with \(I(y)=(y^{3/2},(2y)^{3/2}]\) and
\(S=\{\lfloor n^{3/2}\rfloor:n\ \mathrm{odd}\}\). Bounding this
sample is \(S\)-fairness of the live set: already odd generation
(Paper C Theorem 2) and `J-tao-free-term-is-live-mass`. Not a new wall.

**Walk-live Walsh product (REPARAMETERIZATION / §10.4(e)).**
\(\{\tau>d\}\subseteq\{\mathrm{walk\ live}\}\). The unstopped expansion
is Tao note §10.4(c), weight \(\rho=\tanh(\theta/2)\approx 0.196\) at
\(\theta_{19}\). Crude \(|W_T|\le N\) on \(|T|\le k_0\) fixed costs
\(e^{O(\log d)}=e^{o(d)}\). The tail is
\((1+\rho)^d=e^{\Theta(d)}\) (\(\log(1+\rho)\approx 0.179\); at
\(d=49\), \(\log\mathrm{full}=8.75\) versus \(\log\mathrm{partial}_{k_0=4}=6.22\)).
Two-sided control of the tail is
`J-tao-cylinder-forms-reparameterization`. Vaaler plus van der Corput
on \(e(\tfrac12\sum_{s\in T}J^s(n))\) is a nested-floor phase: the
two-monomial leftover or the Weyl budget \(cC<1\) (Paper C Prop. 10.3).
Paper B on \(\max T\le 4\) is §10.4(e).

No fate is excluded. No halt theorem.

## Current literature

- Tao note §10–11 / Paper C §§9–10 — `extended`: the estimate those
  notes recorded as a question, not an approach.
- Paper B Theorems 4.1, 4.4, 4.7 — `known`: dyadic odd starts, depth
  \(\le 4\); not forward images of deep cylinders.
- `J-tao-pressure-form`, `J-tao-cylinder-forms-reparameterization`,
  `J-tao-free-term-is-live-mass` — `known`.
- Exponent-pair two-monomial leftover — `known`; not reopened.

## Branch budget

```text
Mathematical target     Is there an upper bound on Z_d or on
                        Σ_t (s_θ(t)-q)^+ that uses the Juggler step
                        and is not a reparameterization of H(C,A)?
Novelty hypothesis      Either a last-even reset splits s_θ into a
                        Paper-B-controlled piece plus a suffix whose
                        worst-case mass still leaves q < p_C, or the
                        live generating function organises errors as
                        one object rather than 2^d cylinder counts.
Falsifier               The identity's error is H(C,A); the needed sum
                        is a killed Paper B / two-monomial object;
                        the argument only sees o(log log y) depths;
                        Weyl loss per depth is ≥ 2^{1/C}; after an
                        even letter the image of a deep cylinder is
                        still sparse; fair-coin μ_k already exceeds
                        2q-1 for every q < p_C.
Existing machinery      Tao note §10–11; Paper B Thms 4.1 / 4.4 / 4.7;
                        FateContagion productions; fair_tilted_live
                        in tao_reduction.py.
Maximum Phase-0 scope   Write the two identities; one fair-coin suffix
                        DP; classify; decide. No Lean, no Paper C
                        rewrite, no new CLI, no orbit census.
Promotion criterion     A new sufficient inequality that is not H(C,A).
Stop criterion          Every route is REPARAMETERIZATION, a killed
                        exponential sum, or insufficient by §10.4(e).
```

## Balanced-ternary formulation

None. The objects are the exponent walk and cylinder images on ordinary
positive integers.

## Why BT may be relevant

Not relevant here; recorded for the template.

## Candidate operations / invariants

- Reset split of \(s_\theta\) — **EXACT — HUMAN PROOF** (elementary);
  fair-coin \(\mu_k\) — **COMPUTATIONALLY VERIFIED**; complementary
  geometry — **COMPUTATIONALLY VERIFIED** sparse, hence
  **REPARAMETERIZATION** of \(\mathrm H_q\) / §10.4(e).
- Forward \(S\)-sampling of \(Z_d\) — **REPARAMETERIZATION** of
  \(S\)-fairness / `J-tao-free-term-is-live-mass`.
- Walk-live Walsh product — **REPARAMETERIZATION** of
  `J-tao-cylinder-forms-reparameterization` (two-sided tail) or
  §10.4(e) (fixed-depth characters) or the recorded Weyl / two-monomial
  kills (unexpanded phase).

## Experiments

- Probe: `research.juggler_sequence.pressure_direct`
  (`python -m research.juggler_sequence.pressure_direct`).
- Artifact: `data/research/juggler/pressure_direct/summary.json`.
- Tests: `tests/research/juggler_sequence/test_pressure_direct.py`.
- No orbit sample. The suffix DP reuses the exponent-walk state of
  `fair_tilted_live`; the geometry check is exhaustive on
  \((10^5,2\cdot 10^5]\).

## Conjectures

None new. `juggler_loglog_depth_cylinder_bound` stays **ACTIVE**;
\(\mathrm P_\theta\) / \(\mathrm M_{\theta,q}\) remain its weakest
form.

## Counterexamples

None. The routes died by reparameterization and by the recorded
bounded-depth barrier, not by a counterexample to \(\mathrm M_{\theta,q}\).
The fair-coin \(\mu_4\) is compatible with no-momentum; it does not
prove it.

## Formalization

None. The reset split and the \(S\)-sampling identity are elementary
consequences of unique odd preimages and of the definition of
\(\mu_{\theta,t}\). Lean-ifying them ahead of an estimate would be
machinery gravity.

## Results

Classification **PRESSURE_DIRECT_ROUTES_ARE_H_OR_REPARAM**
(`J-pressure-direct-routes`).

- Route A has numerical room at \(k=4\) and none at \(k=3\). The
  complementary term is not Paper B: high-walk E-ending images are
  sparse. The split is \(\mathrm H_q\) at unbounded depth.
- Route B1 is \(S\)-fairness of the live set.
- Route B2: fixed-order Walsh is \(e^{o(d)}\); the tail is
  \(e^{\Theta(d)}\); every laboratory input for the tail is already
  recorded as a reparameterization or a kill.
- Not claimed: \(\mathrm M_{\theta,q}\), \(\mathrm P_\theta\),
  termination, any new cylinder bound.

## Open questions

None in this laboratory. The statement to export remains
\(\mathrm M_{\theta,q}(C)\) with the depth budget \(2^{-d/C}\), as the
Tao dossier already recorded.

## Decision

**CLOSE.** The stop criterion fired: every direct estimate available
to the laboratory is \(\mathrm H_q\) at unbounded depth, a
reparameterization of \(S\)-fairness or of the Walsh pair-correlation
form, a killed nested-floor exponential sum, or a bounded-depth
statement excluded by Tao note §10.4(e). Numerical room for the
\(k=4\) reset is real and recorded; it does not promote the route,
because the complementary cylinders are not dyadic intervals.
Do not reopen as a short-interval Paper B, a \(K_3\) rescue of
\(k=5\), a third formulation, or another pressure census. Best next
question: none on this line; the no-momentum form stays the export.

## Publication assessment

Status: `ARCHIVED`. A classification of two estimates the paper
deferred. Not a paper claim; no Paper A or Paper C edit.

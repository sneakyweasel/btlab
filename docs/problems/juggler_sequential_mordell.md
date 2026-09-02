# Juggler sequential near-Mordell steps

Status: **EXPLORATORY**

Standalone arithmetic layer on the rewritten Juggler formalization. It
is **not** a Research Engine control-layer experiment and not a claim
that every positive integer reaches 1.

## Problem

Do two consecutive odd Juggler steps \(x\to y\to z\) carry Diophantine
information that neither one-step floor identity
\(x^3=y^2+\rho\) nor \(y^3=z^2+\sigma\) carries alone? In particular,
is the pair \((\rho,\sigma)\) coupled, and does the earlier peak
Diophantine machinery apply to a persistent odd-odd landing?

## Exact statement

An odd Mordell step is the existing local identity

\[
x^3=y^2+\rho,\qquad 0\le\rho<2y+1,\qquad y=T(x),\quad x\text{ odd}.
\]

Two consecutive odd steps give a second copy of the same identity at
\(y\). The two-step polynomial is exact substitution:

\[
(x^3-\rho)^3=(z^2+\sigma)^2
\]

is \(y^6=y^6\). The sequential defect is the existing OO envelope

\[
\Gamma=x^9-z^4=\texttt{globalDefect}(x,[\mathrm{odd},\mathrm{odd}]).
\]

On an odd-to-odd step both \(x\) and \(y\) are odd, so \(\rho\) is
even. The peak law `peakOddDefect_odd` needs an even maximum \(M\),
so \(\delta\) is odd. Persistent odd-odd supplies \(y\) odd, the
opposite parity hypothesis.

This says nothing about totality. Do not introduce a Mordell solver
or a three-step hierarchy.

## Current literature

- Local remainder window \(\rho<2T+1\) —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.Defect`.
- OO slack \(x^9=z^4+\Delta_{\mathrm{OO}}\) —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.GlobalDefect`
  (`global_defect_identity`, `slack_identity`).
- Peak pair \((\delta,\varepsilon)\) with even maximum then even run —
  **CLOSE** as `DIOPHANTINE_REPACKAGING` in
  [juggler_cycle_diophantine.md](juggler_cycle_diophantine.md).
- One-step near-equality rigidity —
  **REFUTED** (`J-approx-equality-rigidity`).
- Scale-induced \(\eta=\rho/T^2\to 0\) —
  **EXACT — LEAN VERIFIED**; small \(\rho/y^2\) is not a finding here.
- Landing \(\theta\) unrestricted —
  **CLOSE** as `LANDING_THETA_UNRESTRICTED`.

Project relationship: **extended**.

## Branch budget

```text
Mathematical target     Do two consecutive odd steps x→y→z carry
                        Diophantine information that neither
                        x³=y²+ρ nor y³=z²+σ carries alone?
Novelty hypothesis      The pair (ρ,σ) is coupled: a new
                        divisibility/valuation, or a sequential
                        defect Γ=x⁹-z⁴ that is not globalDefect(OO)
Falsifier               (x³-ρ)³=(z²+σ)² is y⁶=y⁶; Γ is the OO
                        slack identity; peak needs an even M
Existing machinery      localDefectOdd, peakOddDefect,
                        peak_diophantine_slack, global_defect_identity,
                        slack_identity for word OO (x⁹=z⁴+Δ)
Maximum Phase-0 scope   Name OddMordellStep; identify Γ with Δ_OO;
                        cheap (ρ,σ,Γ) census; peak-hypothesis check
Promotion criterion     A coupling that is not substitution and
                        not Δ_OO, or a clean proof that peak
                        hypotheses are absent on persistent OO
Stop criterion          Falsifiers A–E; Baker/Thue/Mordell solver;
                        three-step Lean; halt
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- `oddMordellStep` / `twoOddMordellSteps` —
  **REPARAMETERIZATION** of `localDefectOdd`
- \(\rho\) even on an odd-to-odd step —
  **EXACT — LEAN VERIFIED**
- \((x^3-\rho)^3=(z^2+\sigma)^2\) —
  **EXACT — LEAN VERIFIED**, and a **REPARAMETERIZATION**
  (both sides are \(y^6\))
- \(\Gamma=x^9-z^4\) —
  **REPARAMETERIZATION** of `globalDefect` of the itinerary `OO`
- Peak slack transports to persistent OO —
  **REFUTED** (needs even \(M\); the landing \(y\) is odd)
- A \(\rho\)–\(\sigma\) coupling beyond independent floor windows —
  **REFUTED** on the scanned window
- Infinite odd-odd orbit — not claimed

## Experiments

Cheap integer census, not a new raw search.

- Odd-odd starts \(n\le 400\): 96 pairs. Identity failures 0;
  \(\Gamma\neq\Delta_{\mathrm{OO}}\) failures 0; odd \(\rho\) 0;
  even-\(y\) peak shape 0. \(\gcd(\rho,\sigma)=1\) is the mode
  (39 pairs). Every residue of \(\rho\bmod 8\) realises more than
  one \(\sigma\bmod 8\). The pairs \((v_2(\rho),v_2(\sigma))\) are
  not locked.
- Probe \(n\le 2000\): 505 pairs, the same four failure counts
  remain 0, and every \(\rho\bmod 8\) class still splits
  \(\sigma\bmod 8\).
- Persistent residual starts \(365\), \(763\), \(1749\): each has
  odd \(y\), even \(\rho\), and \(\Gamma=\Delta_{\mathrm{OO}}\).
  The iterate \(365\to 6973\to 582276\) has \(\rho=4396\),
  \(\sigma=949141\), \(\gcd=1\).
- Small \(\rho/y^2\) is the already-known scale window, not a
  sequential coupling.

Tests: `tests/research/juggler_sequence/test_sequential_mordell.py`.

## Conjectures

None opened in `conjectures/`.

## Counterexamples

- “\(\Gamma=x^9-z^4\) is a new sequential defect.” False: it is
  `globalDefect` of `OO`.
- “The two-step polynomial is not substitution.” False: both
  sides equal \(y^6\).
- “\((\rho,\sigma)\) is coupled beyond floor windows.” False on
  \(n\le 2000\): \(\gcd=1\) is typical, and \(\rho\bmod 8\) does
  not lock \(\sigma\bmod 8\).
- “Peak Diophantine slack applies to persistent OO.” False: the
  second state \(y\) is odd, so the even-\(M\) hypothesis of
  `peakOddDefect_odd` is absent.

## Formalization

`formal/Problems/Juggler/SequentialMordell.lean`, after
`CycleDiophantine`. No `sorry`. No halt theorem. No Mordell
solver. No three-step hierarchy.

## Results

- Two consecutive odd steps are two copies of the local floor
  identity. The composed polynomial is \(y^6=y^6\).
- \(\Gamma=\Delta_{\mathrm{OO}}\) exactly.
- On odd-odd, \(\rho\) is even. That is the opposite parity of
  the peak law, which needs even \(M\).
- The census finds no transported divisor or valuation that is
  not a rewrite of `powGap` / `globalDefect`.

## Open questions

The leftover is still whether an odd-to-odd residual chain can
continue indefinitely. Sequential near-Mordell composition is not
that arithmetic. The even remainder lifts to \(\rho\equiv y-1
\pmod 8\), which is not history-sensitive; see
[juggler_landing_valuation.md](juggler_landing_valuation.md).
Do not open a three-step attack, a Mordell solver, or a halt claim.

## Decision

**CLOSE** the sequential near-Mordell attack as
`SEQUENTIAL_MORDELL_IS_OO_DEFECT`. The two-step polynomial is
substitution, \(\Gamma\) is the OO global defect, \((\rho,\sigma)\)
show no coupling beyond independent floor windows, and peak slack
needs an even maximum that persistent odd-odd does not supply.
Do not claim termination.

Best next question: is there any arithmetic, other than the integer
\(y\) itself, that decides whether a persistent residual landing
stays odd-to-odd?

## Publication assessment

Status: `EXPLORATORY`. A negative sequential-identity result and a
one-line odd-odd remainder-parity lemma, not a paper candidate and
not a Juggler totality result.

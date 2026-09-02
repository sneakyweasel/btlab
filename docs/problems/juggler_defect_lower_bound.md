# Juggler first-defect amplification

Status: **STRUCTURAL**

Standalone arithmetic layer on the rewritten Juggler formalization. It
is **not** a Research Engine control-layer experiment and not a claim
that every positive integer reaches 1.

## Problem

Given the first unavoidable local remainder of a realized Juggler
itinerary, what is the smallest global defect the remaining word can
produce?

## Exact statement

For a realized itinerary \(w\), let \(j=\operatorname{firstDefect}(n,w)\) be
the first index with \(\rho_j>0\), or \(|w|\) if every remainder
vanishes. The prefix before \(j\) is tight, hence an even or odd
power-of-two tower. After inserting that remainder, later remainders
may be dropped. The resulting suffix operator \(\operatorname{Amplify}\)
satisfies

\[
\Delta_w(n)
\ge
\operatorname{Amplify}_{w[j+1:]}\!\left(T^{j+1}(n),\,\rho_j^{2^j}\right).
\]

An odd letter lifts an already-inserted defect by the exact cubic

\[
(x^a+D)^3-x^{3a}
=
3x^{2a}D+3x^a D^2+D^3
\ge
3x^{2a}D.
\]

The factor \(3\) is sharp as \(D/x^a\to 0\).

This does **not** claim

\[
\Delta_w(n)
>
n^{3^o}-n^{2^k}
\]

on expanding mixed itineraries. That inequality is \(T_w(n)<n\).

## Current literature

- Global accumulated defect and composition —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.GlobalDefect`.
- Equality rigidity / monochrome towers —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.Equality`.
- Local remainder window \(0\le\rho<2T+1\) —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.Defect`.
- Naive “\(\Delta\) beats surplus on expanding `OOE`” —
  **REFUTED** already as the endpoint rewrite \(T_w(n)<n\).

Project relationship: **extended**.

## Branch budget

```text
Mathematical target     Given the first unavoidable local defect, what
                        is the smallest Δ the remaining itinerary can
                        produce?
Novelty hypothesis      Odd-step cubic lift + tight-prefix rigidity
                        give a scale-sensitive F that is not a rewrite
                        of T<n
Falsifier               Every candidate F is the endpoint inequality,
                        or Amplify fails to lower-bound Δ
Existing machinery      globalDefect, powGap, localsTight,
                        power_bound_eq_iff_extremal, ResidualStep
Maximum Phase-0 scope   firstDefect + Amplify + odd lift + one residue
                        remainder bound + one mixed-class bound +
                        residual wrapper + targeted census
Promotion criterion     A new exact amplification mechanism that is
                        not T<n in disguise
Stop criterion          All bounds tautological; halt claim
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- `firstDefect` / tight-prefix tower —
  **EXACT — LEAN VERIFIED**
- `odd_defect_lift` and the factor-\(3\) lower bound —
  **EXACT — LEAN VERIFIED**
- `amplifyDefect` (later remainders dropped) —
  **EXACT — LEAN VERIFIED**
- `normalizedDefect` as the pair \((D,\,x^{2^k})\) —
  **EXACT — LEAN VERIFIED**
- Residue remainders: \(x\equiv 2\pmod{4}\) and \(T\) even \(\Rightarrow\rho_E\ge 2\);
  \(x\equiv 3\pmod{8}\Rightarrow\rho_O\ge 2\);
  \(x\equiv 7\pmod{8}\Rightarrow\rho_O\ge 3\) —
  **EXACT — LEAN VERIFIED**
- `OOE` bound: first defect before the even letter, and
  \(\Delta\ge 3T(n)^4\rho_0\) or \(\Delta\ge\rho_1^2\) —
  **EXACT — LEAN VERIFIED**
- Those `OOE` bounds exceed the formal surplus on expanding starts —
  **REFUTED** (census, and equivalent to \(T_w(n)<n\))

## Experiments

Targeted scan, not a new prefix hunt.

- Remainder residues on \(1\le n\le 4000\): even \(x\equiv 2\pmod{4}\)
  has \(\rho\ge 1\), and \(\rho\ge 2\) when \(T(x)\) is even; odd
  \(x\equiv 3\pmod{8}\) has \(\rho\ge 2\); odd \(x\equiv 7\pmod{8}\)
  has \(\rho\ge 3\).
- Amplification census \(n\le 60\), length \(\le 5\): Amplify never
  exceeds \(\Delta\); the crude \(\rho_j^{2^j}\) is recovered when the
  suffix does not lift.
- Frontier words `OOE`, `OOEO`, `OOOE` on odd \(n\le 180\): first
  defect is always before the first even letter; no expanding start
  has \(F>n^{3^o}-n^{2^k}\). Expanding defect/surplus ratios sit in
  \((0,1]\), down to about \(3\cdot 10^{-3}\) on the scanned window.

Tests: `tests/research/juggler_sequence/test_defect_lower_bound.py`.

## Conjectures

None opened in `conjectures/`.

## Counterexamples

`F_w(n)>n^{3^o}-n^{2^k}` for realized expanding `OOE` / `OOEO` /
`OOOE`. None exist on the scanned window, and the inequality is
\(T_w(n)<n\).

## Formalization

`formal/Problems/Juggler/DefectLowerBound.lean`. Residual wrappers
`residualStep_firstDefect` and `residualStep_amplify` in
`Residuals.lean`. No `sorry`. No halt theorem.

## Results

- Canonical first defect; the prefix is a rigid equality tower.
- A later even letter cannot follow a completely tight odd run, so
  `OOE` / `OOEO` have \(j\le 1\) and `OOOE` has \(j\le 2\).
- Exact cubic lift and the sharp universal factor \(3\).
- Suffix Amplify is the minimum forced contribution of an
  already-inserted defect.
- Residue-sensitive local remainders strictly stronger than
  \(\rho\ge 1\).
- Conditional `OOE` bounds. They do not beat the formal surplus.

## Open questions

Taken up by `docs/problems/juggler_normalized_defect.md`. The
preferred object is the relative slack \(1+q\), not \(R\).

## Decision

**PROMOTE** the first-defect amplification layer. The mechanism is a
new exact object. It does not prove termination, and it does not
forbid expanding `OOE`.

Best next question: taken up by `docs/problems/juggler_normalized_defect.md`.

## Publication assessment

Status: `STRUCTURAL`. Quantitative lower bound and suffix operator.
Not a Juggler totality result.

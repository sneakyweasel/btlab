# Juggler normalized defect dynamics

Status: **STRUCTURAL**

Standalone arithmetic layer on the rewritten Juggler formalization. It
is **not** a Research Engine control-layer experiment and not a claim
that every positive integer reaches 1.

## Problem

After the exact global defect identity, does a dimensionless slack
have an exact residual transition law, and does the surplus ratio
\(R=\Delta/S\) drift upward on persistent odd-to-odd residual chains?

## Exact statement

Write

\[
1+q_w(n)
=
\frac{n^{3^{\#O(w)}}}{T_w(n)^{2^{|w|}}},
\qquad
\eta(x)=\frac{\rho(x)}{T(x)^2}.
\]

For a realized concatenation \(w=uv\),

\[
1+q_{uv}(n)
=
\bigl(1+q_u(n)\bigr)^{3^{\#O(v)}}
\bigl(1+q_v(T_u(n))\bigr)^{2^{|u|}}.
\]

One even letter multiplies by \((1+\eta)^{2^k}\). One odd letter
multiplies by \((1+q)^3(1+\eta)^{2^k}\). Running \(1+q\) does not
decrease under a realized extension.

The surplus ratio

\[
R_w(n)=\frac{\Delta_w(n)}{n^{3^{\#O(w)}}-n^{2^{|w|}}}
\]

is defined only when the denominator is positive. Then
\(R_w(n)\le 1\) if and only if \(T_w(n)\ge n\). A realized return
\(T_w(n)=n\) uses the whole formal surplus.

## Current literature

- Global accumulated defect and composition —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.GlobalDefect`.
- First-defect Amplify and the pair \((D,x^{2^k})\) —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.DefectLowerBound`.
- ResidualStep / PersistentOddResidual —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.Residuals`.
- Forced positive drift of \(R\) on persistent residual chains —
  **REFUTED** as an independent attack: \(R\le 1\) is the endpoint
  comparison whenever \(S>0\); running \(R\) can fall; the next
  residual after a persistent expanding step left the \(S>0\) domain
  on the scanned window.

Project relationship: **extended**.

## Branch budget

```text
Mathematical target     Does a dimensionless slack have an exact
                        residual transition law, and does R drift
                        up on persistent odd-to-odd chains?
Novelty hypothesis      1+q multiplies under concatenation and is
                        not the endpoint rewrite T≥n
Falsifier               the q-law is only a rewrite of the identity;
                        or R→0 on admissible persistent chains;
                        or every drift is T<n
Existing machinery      globalDefect, powGap, amplifyDefect,
                        ResidualStep, PersistentOddResidual
Maximum Phase-0 scope   derive q vs R vs Q; exact step/concat;
                        residual census; Lean identities; no halt
Promotion criterion     exact normalized dynamics that is not T≥n,
                        or a clean refutation of forced R-drift
Stop criterion          Falsifier A–E; machinery gravity; halt claim
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- Relative slack \(1+q=n^{3^o}/T^{2^k}\) and the Nat pair
  `(slackNum, slackDen)` — **EXACT — LEAN VERIFIED**
- Local \(\eta=\rho/T^2\) as `(normalizedLocalDefect)` —
  **EXACT — LEAN VERIFIED**
- Concatenation product and even/odd one-step laws —
  **EXACT — LEAN VERIFIED**
- Running \(1+q\) nondecreasing under a realized extension —
  **EXACT — LEAN VERIFIED**
- \(R\le 1\) iff \(T_w(n)\ge n\) when \(S>0\) —
  **EXACT — LEAN VERIFIED** (reparameterization of the endpoint)
- Return \(T_w(n)=n\) uses the whole formal surplus —
  **EXACT — LEAN VERIFIED**
- Scale \(Q=\Delta/T^{3^o}\) — genuinely different; no simple
  product law. Not used.
- Forced one-step or block increase of per-block \(R\) on
  persistent residual chains — **REFUTED** as an independent
  mechanism (see Experiments)

## Experiments

Small exact census, not a new raw search.

- Short realized itineraries \(n\le 40\), length \(\le 4\): the \(1+q\)
  identity, concatenation product, even/odd one-step law, and
  running-\(1+q\) monotonicity match exactly.
- Whenever \(S>0\), \(R\le 1\) iff \(T\ge n\) on \(n\le 60\),
  length \(\le 4\).
- Persistent residual window: odd-odd starts \(n\le 80\) plus
  hard probes \((9,37,49,69,77)\), chain cap \(8\). Two persistent
  expanding steps: \(37\xrightarrow{\mathrm{OOOOE}}9317\) with
  \(R\approx 1.7\cdot 10^{-2}\) and \(69\xrightarrow{\mathrm{OOE}}117\)
  with \(R\approx 9.7\cdot 10^{-3}\). Both sequels are
  exponent-contracting, so the next \(R\) is undefined.
- Per-block \(q\) can reset downward at the next start
  (\(37\) then \(9317\); \(77\) then \(1523\)).
- Running \(R\) along one itinerary can fall when a later odd
  letter creates more formal surplus than defect (`EOO` to `EOOO`
  on \(n=12,14\)).
- Odd-odd \(\eta\) reaches \(0\) (tight odd letters). There is no
  positive lower envelope for the normalized local remainder.

Tests: `tests/research/juggler_sequence/test_normalized_defect.py`.

## Conjectures

None opened in `conjectures/`.

## Counterexamples

- \(R_{i+1}\ge R_i\) along a realized itinerary. False: `EOO` to
  `EOOO` on \(n=12\) drops from \(R>1\) to \(R<1\).
- Per-block \(q\) is monotone along a residual chain. False:
  \(37\xrightarrow{\mathrm{OOOOE}}9317\xrightarrow{\mathrm{OOOEE}}2233\)
  drops \(q\).
- \(\eta\ge\varepsilon>0\) on persistent odd-to-odd states. False:
  tight odds give \(\eta=0\).

No family of admissible persistent transitions with \(R\to 0\) was
produced. Falsifier B is not claimed.

## Formalization

`formal/Problems/Juggler/NormalizedDefect.lean`, after `Residuals`
and before `Cycles`. Residual wrappers live in the same file. No
`sorry`. No halt theorem.

## Results

- Preferred normalization is \(1+q\), not \(R\) and not \(Q\).
- Exact concatenation and one-step laws, including the new local
  remainder \(\eta\).
- Running \(1+q\) is nondecreasing. This is not \(T_w(n)\ge n\).
- \(R\) silently encodes the endpoint comparison whenever \(S>0\).
- Persistent expanding residual steps are rare on the window, and
  their immediate sequel left the surplus-positive domain.
- The attack “persistent chain implies \(R\) drifts past \(1\),
  hence \(T<n\)” is not a new obstruction.

## Open questions

Taken up by `docs/problems/juggler_two_block_residual.md`. Two
consecutive expanding persistent blocks exist
(\(365\xrightarrow{\mathrm{OOE}}763\xrightarrow{\mathrm{OOE}}1749\)).

## Decision

**PROMOTE** the exact \(1+q\) calculus. It is a new multiplicative
form of the global defect, not a rewrite of \(T_w(n)\ge n\). Do not
promote a drift-to-\(R>1\) attack. Do not claim termination.

Best next question: taken up by `docs/problems/juggler_two_block_residual.md`.

## Publication assessment

Status: `STRUCTURAL`. Exact multiplicative slack law. Not a Juggler
totality result.

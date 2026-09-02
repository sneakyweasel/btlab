# Juggler scale-induced near-tightness

Status: **STRUCTURAL**

Standalone arithmetic layer on the rewritten Juggler formalization. It
is **not** a Research Engine control-layer experiment and not a claim
that every positive integer reaches 1.

## Problem

Are the tiny relative slacks seen after large expanding persistent
blocks exceptional arithmetic rigidity, or the automatic consequence
of applying floors at large scale?

## Exact statement

The local remainder window is

\[
0\le\rho<2T(x)+1,
\]

hence

\[
0\le\eta(x)=\frac{\rho}{T(x)^2}<\frac{2}{T(x)}+\frac{1}{T(x)^2}.
\]

In particular \(\eta_E=O(T^{-1})=O(x^{-1/2})\) and
\(\eta_O=O(T^{-1})=O(x^{-3/2})\). For the mixed itinerary `OOE`,

\[
1+q_{\mathrm{OOE}}
=
(1+\eta_0)^3(1+\eta_1)^2(1+\eta_2)^4
<
\Bigl(1+\frac1{T_0}\Bigr)^6
\Bigl(1+\frac1{T_1}\Bigr)^4
\Bigl(1+\frac1{T_2}\Bigr)^8.
\]

The last even remainder dominates: \(q_{\mathrm{OOE}}(n)\) has order
\(n^{-9/8}\). A large-\(\lambda\) predecessor \(x\xrightarrow{u}y\)
enters only by making \(y\) large. Then

\[
q_v(y)\le F_v(y),\qquad F_v(y)\to 0\ (y\to\infty),
\]

so formally

\[
q_v(y)\le C_v\,x^{-\alpha_v\lambda_u}(1+q_u)^{\beta}.
\]

This is not an obstruction and not a halt theorem.

## Current literature

- Remainder window \(\rho<2T+1\) —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.Defect`.
- Relative slack \(1+q\) and concatenation —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.NormalizedDefect`.
- Weighted slack budget as an independent obstruction —
  **REFUTED** in `docs/problems/juggler_expansion_slack.md`.
- Exact equality rigidity (\(q=0\) implies a monochrome tower) —
  **EXACT — LEAN VERIFIED**. Approximate stability of that rigidity
  is **REFUTED** below.

Project relationship: **extended**.

## Branch budget

```text
Mathematical target     Is tiny q automatic floor-scale decay,
                        predicted by predecessor λ only through y?
Novelty hypothesis      η=O(1/T); fixed-itinerary q→0; OOE is dominated
                        by the last even remainder ~ n^{-9/8}
Falsifier               q does not decay; successor q ignores y;
                        large-y blocks keep η bounded away from 0
Existing machinery      ρ<2T+1, 1+q concat, expansion_slack near-tight pair
Maximum Phase-0 scope   Nat η bounds; OOE product/succ-ratio; q-vs-scale
                        census; 329 prediction check
Promotion criterion     Exact scale-decay/feedback inequality, or a
                        clean proof that tiny q is generic scale
Stop criterion          Falsifier A–E; rigidity hunt; halt claim
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- `even_remainder_bound` / `odd_remainder_bound` /
  `normalized_remainder_upper` / `one_plus_eta_lt_succ_sq` /
  `even_eta_le_two_over_T` —
  **EXACT — LEAN VERIFIED**
- `ooe_eta_product` and `ooe_one_plus_slack_lt_succ_ratio` —
  **EXACT — LEAN VERIFIED**
- `large_lambda_successor_q_bound` is the same `OOE` bound at the
  successor start —
  **EXACT — LEAN VERIFIED**
- `q_{\mathrm{OOE}}(n)\sim n^{-9/8}` on realized odd-odd starts,
  last even remainder dominant —
  **COMPUTATIONALLY VERIFIED**
- The \(329\xrightarrow{\mathrm{OOOOOOOOE}}y\) successor has
  \(q_{\mathrm{OOE}}(y)/y^{-9/8}\approx 2.64\) —
  **COMPUTATIONALLY VERIFIED**
- Mixed-word \(q\to 0\) implies a rigid monochrome tower —
  **REFUTED**
- Scale-induced near-tightness forbids a long PE chain —
  not claimed

## Experiments

- Remainder window: on \(1\le n\le 400\), every \(\eta\) is strictly
  below \(2/T+1/T^2\). Tight odds occur.
- Realized `OOE` on odd-odd \(n\le 2000\): last-even weighted
  remainder dominates in \(96\%\) of cases. Median
  \(q/n^{-9/8}\approx 4.25\) for \(n\ge 200\).
- After \(329\xrightarrow{\mathrm{OOOOOOOOE}}y\) with
  \(y\approx 1.80\cdot 10^{32}\) and \(\lambda_u\approx 12.81\), the
  next `OOE` has \(0<q<10^{-30}\) and
  \(q/y^{-9/8}\approx 2.64\). The three weighted local terms are
  \(10^{-48}\), \(10^{-73}\), and \(10^{-36}\).
- Persistent expanding pairs \(n\le 2000\): every `OOE` sequel
  satisfies \(0.39\le q_2/y^{-9/8}\le 7.72\). Larger \(\lambda_u\)
  gives smaller \(q_2\) exactly because \(y\) is larger. On
  \(y>10^6\), every sequel \(q_2\) is below \(10^{-8}\).

Tests: `tests/research/juggler_sequence/test_near_tight_scale.py`.

## Conjectures

None opened in `conjectures/`.

## Counterexamples

- Fixed-word near-tightness does not improve with scale. False:
  realized `OOE` tracks \(n^{-9/8}\).
- Successor \(q\) is not controlled by successor scale. False: the
  \(329\) successor and the PE-pair window both match \(y^{-9/8}\).
- Mixed realized `OOE` cannot have \(q\to 0\). False: the block at
  \(y=180370579261640036336071806107777\) is mixed and has
  \(0<q<10^{-30}\). Exact equality rigidity has no naive quantitative
  stability theorem.

## Formalization

`formal/Problems/Juggler/NearTightScale.lean`, after `ExpansionSlack`
and before `Cycles`. No `sorry`. No halt theorem. No real-analysis
limit layer.

## Results

- Local \(\eta\) decays as \(O(1/T)\). This is the floor window, not
  a new remainder law.
- For `OOE`, the exact product and the successor-ratio upper bound
  are Lean-certified.
- The observed \(q<10^{-30}\) is generic scale behavior. Large
  \(\lambda\) acts only by inflating \(y\).
- Approximate equality rigidity is false.
- This is not an obstruction to persistent expansion. It explains
  why long expanding chains can stay near the envelope.

## Open questions

Answered in [juggler_expanding_grammar.md](juggler_expanding_grammar.md):
the expanding-word grammar is persistence, not an independent
obstruction. Tiny \(q\) still does not punish expansion. The leftover
is the odd-to-odd landing, not another slack rewrite.

Cycle leftover convergents are not a NearTightScale job
([juggler_cycle_near_tight.md](juggler_cycle_near_tight.md),
**CLOSE**).

## Decision

**PROMOTE** the scale-decay / large-\(\lambda\) feedback description.
Tiny \(q\) is the unavoidable asymptotic of floors at large scale.
Do not claim that the feedback loop is an obstruction. Do not claim
termination.

Best next question: answered in
[juggler_expanding_grammar.md](juggler_expanding_grammar.md).

## Publication assessment

Status: `STRUCTURAL`. Exact remainder-to-slack scale bounds and a
quantitative explanation of near-tightness. Not a Juggler totality
result.

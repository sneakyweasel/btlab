# Juggler weighted slack budget and expansion density

Status: **EXPLORATORY**

Standalone arithmetic layer on the rewritten Juggler formalization. It
is **not** a Research Engine control-layer experiment and not a claim
that every positive integer reaches 1.

## Problem

After the exact `1+q` calculus, does the logarithmic affine law

\[
y_{i+1}=\lambda_i y_i-c_i,\qquad
y_i=\log x_i,\quad
\lambda_i=\frac{3^{o_i}}{2^{k_i}},\quad
c_i=\frac{\log(1+q_i)}{2^{k_i}}
\]

and its weighted cocycle put a nontrivial upper bound on the density
or run length of expanding persistent residual blocks?

## Exact statement

Every residual block satisfies the log-free identities

\[
n^{A}=T^{B}+\Delta,
\qquad
A=3^{\#O(w)},\quad B=2^{|w|},
\]

and

\[
1+q_{uv}
=
(1+q_u)^{A_v}(1+q_v)^{B_u}.
\]

In logs this is the affine recurrence and the cocycle

\[
y_m=\Lambda_m y_0-C_m,
\qquad
\Lambda_m=\prod_i\lambda_i,
\qquad
C_m=\sum_i c_i\prod_{j>i}\lambda_j,
\qquad
B_m=\frac{C_m}{\Lambda_m}.
\]

The local compatibility

\[
x_{i+1}>x_i\iff c_i<(\lambda_i-1)y_i
\]

is exactly \(T_w(n)>n\). The research claim under test is stronger:
positive local slack, after the exact expansion weights, constrains
the *sequence* of expanding persistent blocks independently of the
concatenated endpoint inequality.

## Current literature

- Global accumulated defect —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.GlobalDefect`.
- Relative slack \(1+q\) and concatenation —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.NormalizedDefect`.
- Two consecutive `PersistentExpandingResidual` blocks —
  **REFUTED** in `Problems.Juggler.Residuals` (`two_block_ooe_365`).
- Forced \(R\)-drift on persistent chains —
  **REFUTED** in the normalized-defect dossier.
- Uniform positive lower envelope for \(c/(\lambda-1)\) on expanding
  persistent blocks — **REFUTED** below.

Project relationship: **extended**.

## Branch budget

```text
Mathematical target     After the exact affine law y_{i+1}=λ_i y_i-c_i,
                        does the weighted slack budget constrain PE
                        run length or density independently of T≥n?
Novelty hypothesis      Expansion and slack are one budget: a
                        structural tax on expanding persistent blocks,
                        after the exact weights, forbids arbitrarily
                        long PE runs or density 1, and that constraint
                        is not y_m≥y_0
Falsifier               Long PE runs exist with B_m as small as the
                        endpoint tautology allows, or c_i/(λ_i-1) can
                        be made arbitrarily small (prompt A–E)
Existing machinery      1+q concat, globalDefect,
                        PersistentExpandingResidual, two_block_ooe_365,
                        firstDefect/Amplify, residual chains
Maximum Phase-0 scope   Log-free Lean packaging of λ and the Nat
                        cocycle; a cheap PE-chain census of λ, c, B_m,
                        run length, and c/(λ-1); decide from that
                        evidence
Promotion criterion     A sequence-level expansion/slack inequality,
                        or a clean refutation that the budget is only
                        T≥n
Stop criterion          Falsifier A–E; machinery gravity; halt claim
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- `blockMultiplier` / `expansionMargin` / `blockLogSlack` /
  `blockSlackTax` / `weightedSlack` / `normalizedSlackBudget` —
  **REPARAMETERIZATION** of `1+q` and `exponentExpanding`
- `block_power_identity` / `block_log_growth` /
  `weighted_slack_concat` / `weighted_slack_cocycle` /
  `normalized_budget_identity` —
  **REPARAMETERIZATION** of `slack_identity` and
  `onePlusSlack_concat`
- `block_growth_compat` —
  **REPARAMETERIZATION** of \(T_w(n)>n\) on an expanding itinerary
- Four consecutive `PersistentExpandingResidual` blocks —
  **EXACT — LEAN VERIFIED** (`four_block_pe_1999`)
- Five consecutive expanding persistent blocks starting at \(2183\) —
  **COMPUTATIONALLY VERIFIED** on the residual walker
- Uniform \(c/(\lambda-1)\ge\varepsilon>0\) on expanding persistent
  blocks — **REFUTED**
- \(B_m\) bounded below independently of the endpoint tautology
  \(B_m\le y_0(1-1/\Lambda_m)\) — **REFUTED** on the scanned window
- A finite run bound produced by the weighted budget —
  **REFUTED** as a mechanism; a raw finite \(M\) is not proved

## Experiments

Cheap structural census, not a new raw search.

- Identity `log y = λ log x - c` holds to float error
  \(<10^{-14}\) on the scanned PE blocks.
- Odd-odd starts \(n\le 4000\) plus extra landings: longest
  consecutive PE run has length \(5\), starting at \(2183\). A
  Lean-certified length-\(4\) run is
  \(1999\xrightarrow{\mathrm{OOE}}5169\xrightarrow{\mathrm{OOOOEE}}50093\xrightarrow{\mathrm{OOE}}193753\xrightarrow{\mathrm{OOE}}887471\).
- On \(n\le 10000\) the maximum run is still \(5\) (four such starts).
- Normalized budget: \(B_m\) stays orders of magnitude below the
  endpoint tautology. Typical \(B_m/B_{\mathrm{taut}}\) is
  \(10^{-5}\) to \(10^{-9}\).
- Slack tax versus margin: \(c/(\lambda-1)\) decays with scale
  (median about \(4\cdot 10^{-4}\) for \(x<10^3\),
  \(2\cdot 10^{-5}\) for \(10^3\le x<10^4\), and \(4\cdot 10^{-9}\)
  for \(x\ge 10^4\)).
- After \(329\xrightarrow{\mathrm{OOOOOOOOE}}180370579261640036336071806107777\),
  the next `OOE` is expanding and persistent with exact
  \(0<q<10^{-30}\). The compressed tax \(c/(\lambda-1)\) is
  numerically \(0\).

Tests: `tests/research/juggler_sequence/test_expansion_slack.py`.

## Conjectures

None opened in `conjectures/`.

## Counterexamples

- Uniform positive lower envelope \(c/(\lambda-1)\ge\varepsilon>0\)
  on expanding persistent blocks. False: the `OOE` block at
  \(180370579261640036336071806107777\) has \(0<q<10^{-30}\).
- \(B_m\) is bounded below independently of \(y_m\ge y_0\). False on
  the window: \(B_m/B_{\mathrm{taut}}\) reaches \(10^{-9}\).
- No four consecutive `PersistentExpandingResidual` blocks.
  Witness: `four_block_pe_1999`.
- No five consecutive expanding persistent blocks. Witness:
  \(2183\) with words `OOE`, `OOOOE`, `OOOOOOOOE`, `OOOE`,
  `OOOOOOOE`.
- The weighted cocycle forbids expansion density \(1\) on a finite
  persistent prefix. False: the length-\(5\) run at \(2183\) is all
  expanding.

## Formalization

`formal/Problems/Juggler/ExpansionSlack.lean`, after `NormalizedDefect`
and before `Cycles`. No `sorry`. No halt theorem. No real-analysis
layer. The affine/cocycle statements are the existing `ℕ` slack
identities under new names.

## Results

- The logarithmic affine law and the weighted cocycle are exact
  rewrites of `1+q`.
- `block_growth_compat` is \(T>n\) on an expanding itinerary.
- Four consecutive PE blocks are Lean-certified; five occur on the
  walker.
- There is no uniform positive tax \(c/(\lambda-1)\).
- The normalized budget \(B_m\) stays far below the endpoint
  tautology, so it does not constrain the internal sequence.
- The merged expansion/slack attack does not produce a finite-run
  or density theorem that is not \(T_w(n)\ge n\).

## Open questions

Answered in [juggler_near_tight_scale.md](juggler_near_tight_scale.md):
tiny \(q\) is automatic floor-scale decay, not a weighted-budget
obstruction. Large \(\lambda\) acts only by inflating the next start.

## Decision

**CLOSE** the weighted-slack-budget branch as
`WEIGHTED_SLACK_ENDPOINT`. The exact cocycle is a
reparameterization of `1+q`. The hoped-for sequence constraint
fails: local taxes can be arbitrarily small relative to the formal
margin, and the accumulated \(B_m\) stays negligible compared with
the endpoint budget. Four and five consecutive expanding persistent
blocks occur. Do not claim termination. Do not open a larger run
census.

Best next question: answered in
[juggler_near_tight_scale.md](juggler_near_tight_scale.md).

## Publication assessment

Status: `EXPLORATORY`. A negative budget result and a four-block
existence theorem, not a paper candidate and not a Juggler totality
result.

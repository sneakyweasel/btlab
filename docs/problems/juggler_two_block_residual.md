# Juggler two-step persistent residual compatibility

Status: **STRUCTURAL**

Standalone arithmetic layer on the rewritten Juggler formalization. It
is **not** a Research Engine control-layer experiment and not a claim
that every positive integer reaches 1.

## Problem

Does an expanding persistent residual block leave arithmetic at its
endpoint that forbids a second expanding persistent block?

## Exact statement

Write `PersistentExpandingResidual x y` for a `PersistentOddResidual`
whose realizing block `O^a E^b` is formally expanding:
\(2^{a+b}<3^a\).

The strongest two-block claim

\[
\text{PersistentExpandingResidual}(x,y)
\land
\text{PersistentExpandingResidual}(y,z)
\Longrightarrow
\bot
\]

is **false**. A Lean-certified witness is

\[
365\xrightarrow{\mathrm{OOE}}763\xrightarrow{\mathrm{OOE}}1749.
\]

The smallest odd-odd start of any two-block pair on the scanned
window is \(173\xrightarrow{\mathrm{OOE}}329\xrightarrow{\mathrm{OOOOOOOOE}}\cdots\).
Three consecutive expanding persistent blocks also occur
(\(365\xrightarrow{\mathrm{OOE}}763\xrightarrow{\mathrm{OOE}}1749\xrightarrow{\mathrm{OOE}}4447\)).

What the first block does leave at \(y\):

- \(y\) is odd-to-odd, so the next residual has at least two odd
  letters;
- an expanding residual block itself has at least two odd letters;
- that is exactly the grammar of another expanding block (`OOE` is
  the minimal one);
- \(y\) occupies all odd classes modulo \(8\).

This is not the concatenated endpoint inequality \(T_{uv}(x)<x\).

## Current literature

- ResidualStep / PersistentOddResidual —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.Residuals`.
- Formal exponent gap / drift —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.ItineraryStats`.
- Normalized slack \(1+q\) —
  **EXACT — LEAN VERIFIED** in `Problems.Juggler.NormalizedDefect`.
- “An expanding persistent residual block forces a contracting
  sequel” — **REFUTED** by the pairs above. The \(n\le 80\)
  contracting sequels at \(37\) and \(69\) were a small-window
  artifact.

Project relationship: **extended**.

## Branch budget

```text
Mathematical target     What arithmetic does an expanding persistent
                        residual block leave at y, and can a second
                        expanding persistent block start there?
Novelty hypothesis      the endpoint y is a constrained residual
                        state, not a fresh odd-odd start
Falsifier               an admissible pair with both blocks
                        persistent and expanding, or every
                        obstruction is z<y
Existing machinery      ResidualStep, PersistentOddResidual, 1+q,
                        firstDefect, residue ρ bounds
Maximum Phase-0 scope   cheap two-block census; characterize y;
                        one exact lemma or a recorded
                        counterexample; no halt
Promotion criterion     endpoint constraint that restricts the next
                        block, or a rigorous two-block
                        counterexample
Stop criterion          Falsifier A–E; machinery gravity; endpoint
                        rewrite only
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required.

## Candidate operations / invariants

- `exponentExpanding` and expanding residual \(\Rightarrow a\ge 2\) —
  **EXACT — LEAN VERIFIED**
- Persistent endpoint \(\Rightarrow\) next odd run \(a\ge 2\) —
  **EXACT — LEAN VERIFIED**
- `PersistentExpandingResidual` —
  **EXACT — LEAN VERIFIED**
- Two consecutive expanding persistent blocks impossible —
  **REFUTED** (`two_block_ooe_365`)
- Endpoint residue class \(\mathcal R_{\mathrm{persist}}\) narrower
  than odd-odd — **REFUTED** (all of \(1,3,5,7\pmod 8\) occur)
- Next local \(\rho\) forced large by the first block —
  **REFUTED** on the scanned window

## Experiments

Cheap structural census, not a defect hunt.

- Odd-odd starts \(n\le 4000\), following extra landings: \(316\)
  expanding persistent blocks, \(76\) of them have an expanding
  persistent sequel. Sequel words include `OOE` (\(63\)), `OOOE`,
  `OOOOE`, `OOOOEE`.
- Ordinary odd-odd PE rate \(\approx 28.5\%\). PE endpoints have a
  PE sequel about \(24\%\) of the time. The endpoint is not a
  qualitatively rarer class than a fresh odd-odd start.
- Smallest pair: \(173\to 329\). Smallest `OOE`/`OOE` pair:
  \(365\to 763\to 1749\). A triple starts at \(365\).
- The previous \(n\le 80\) window had only \(37\) and \(69\), both
  with contracting sequels. That does not survive a larger window.

Tests: `tests/research/juggler_sequence/test_two_block_residual.py`.

## Conjectures

None opened in `conjectures/`.

## Counterexamples

- No two consecutive `PersistentExpandingResidual` blocks.
  Witness: \(365\xrightarrow{\mathrm{OOE}}763\xrightarrow{\mathrm{OOE}}1749\),
  **EXACT — LEAN VERIFIED**.
- An expanding persistent block forces the sequel to be
  exponent-contracting. False: \(76\) expanding sequels on
  \(n\le 4000\).
- The intermediate \(y\) lies in a proper residue subclass of
  odd-odd. False: all odd classes modulo \(8\).

## Formalization

`exponentExpanding` in `ItineraryStats.lean`. Expanding residual
\(a\ge 2\) in `Scale.lean`. `PersistentExpandingResidual`, the
next-run bound, and `two_block_ooe_365` in `Residuals.lean`. No
new layer. No `sorry`. No halt theorem.

## Results

- Two-block impossibility is false, including \(m=2\) and \(m=3\).
- The transported state at \(y\) is odd-to-odd, hence next
  \(a\ge 2\). That is compatible with another expansion.
- \(R\)-drift and two-block contraction are both the wrong attack.
- The \(n\le 80\) contracting sequels are not a law.

## Open questions

Taken up independently on two machines. Density and run length:
`docs/problems/juggler_expansion_density.md` certifies a length-3 PE
chain and finds length 7 computationally; density among persistent
steps is 1 on the scanned windows. Slack:
[juggler_expansion_slack.md](juggler_expansion_slack.md) shows the
weighted slack cocycle is a reparameterization of \(1+q\) and does
not bound consecutive expanding persistent blocks; four and five
consecutive PE blocks occur. No finite \(M\) is proved.

## Decision

**PROMOTE** the refutation and the endpoint characterization. The
first block does change the admissible state at \(y\) (odd-odd,
next \(a\ge 2\)), but that state is compatible with another
expanding persistent block. Do not claim termination.

Best next question: taken up by
`docs/problems/juggler_expansion_density.md` and answered in
[juggler_expansion_slack.md](juggler_expansion_slack.md).

## Publication assessment

Status: `STRUCTURAL`. Certified counterexample and two exact
grammar lemmas. Not a Juggler totality result.

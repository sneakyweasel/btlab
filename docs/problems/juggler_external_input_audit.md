# Juggler: are the imported classical results the strongest available?

Status: **PROMOTE** (one chain assembled, one candidate found and left
unverified, one direction closed with numbers).

Not a halt theorem, not new mathematics, not a Juggler construction, not
a floor raise, and not a reopen of any Diophantine-wall member. An audit
of the programme's external inputs.

## Problem

On 14 September 2026 two defects of the same kind surfaced within hours.
[cycle_wuwang_reduction](juggler_cycle_wuwang_reduction.md) found Paper A
Corollary 4.11 running on Rhin while Wu-Wang sat in the repository cited
only as a fan-width cap — worth a factor \(2.795\) in the exponent of a
published corollary. A peer session found twelve theorem-ledger rows
sharing one defect, visible only because the gate stops at the first
failure. Neither needed new mathematics.

So: for every external result the programme leans on, is the cited
version the sharpest, and does anything imported for purpose X also apply
to a purpose Y still running on something weaker?

## Exact statement

**The transcendence chain collapses to one number (EXACT — HUMAN
PROOF).** Everything the cycle side takes from transcendence enters
through a lower bound on \(\Lambda=o\log3-L\log2\), and
`cycleMin_length_of_gap_power` turns a budget \(CL^{-p}\) into
\(n\log n\le(2/C)L^{p+1}\). Writing \(\alpha=\log2/\log3\) and \(\mu\)
for a proved irrationality measure of \(\alpha\),
\[
\lvert\Lambda\rvert=L\log3\,\lvert\alpha-o/L\rvert\ \ge\ cL^{1-\mu},
\qquad\text{so}\qquad n\log n\le\frac2cL^{\mu}.
\]
Hence \(p+1=\mu\) exactly:

> the closure-threshold exponent **is** the irrationality measure of
> \(\log2/\log3\) that you can prove.

That identity makes the audit mechanical and explains the Dirichlet floor
recorded in [cycle_wuwang_reduction](juggler_cycle_wuwang_reduction.md):
\(\mu\ge2\) for every irrational, so no Diophantine input takes the
target below \(L^2\).

**The chain, assembled (COMPUTATIONALLY VERIFIED as arithmetic).**

| \(\mu\) | route | effective | in use |
|---|---|---|---|
| \(2\) | Dirichlet | yes | the hard floor |
| \(5.116201\) | BLS 2018 | no | recorded, knowingly unimported |
| \(5.1163051\) | Wu-Wang 2014, linear form at \(a=0\), \(H=L\) | no (\(C_\varepsilon\)) | `J-cyclemin-gap-power-transfer` |
| \(8.616\) | Rhin p.160 eq. (8), the ratio measure | yes | **nothing** |
| \(14.3\) | Rhin p.160 eq. (7) via Simons-de Weger Lemma 12 | yes (constant \(915\)) | Paper A Corollary 4.11, deposited |

**The finding (OBSERVATION; UNVERIFIED against the primary source).**
Paper A cites Rhin's Proposition on p. 160 and takes equation (7). The
literature reports equation (8) of that same Proposition as
\(\mu(\log3/\log2)\le 8.616\)
([Spiegelhofer–Wallner, *Collisions of digit sums in bases 2 and 3*,
arXiv:2105.11173](https://arxiv.org/abs/2105.11173), introduction:
Rhin [48, Equation (8)]). Converting, that is \(n\log n\ll L^{8.616}\)
against the printed \(L^{14.3}\) — a sharper statement one equation
further down the same page of the same citation. **This is a third-party
report. Nobody in the laboratory has read Rhin equation (8), and whether
its constant is explicit is not established.** It must not be used until
someone does; the probe and its test enforce that an unverified row is
never the one in use.

It changes no current result: Wu-Wang's \(5.1163051\) is sharper than
\(8.616\) and is what the laboratory uses. Its interest is that Paper A's
own citation was not read to the end, and that the effective companion —
the row you quote when you need an explicit constant, since Wu-Wang's is
implied — is \(8.616\) and not \(14.3\).

**Paper C concentration: two closed directions (COMPUTATIONALLY
VERIFIED).** Both were the audit's primary target and both came up empty.

1. `tao_reduction.azuma_exponent` uses Azuma-Hoeffding on increments of
   range \(\log_2 3\). The increments are two-valued, so the sharp bound
   is Chernoff-KL — which the unbiased path in the same module already
   uses via `kl_bernoulli`. Azuma is genuinely lossy (at \(C=19\),
   \(q=1/2\): \(0.523541\) against KL's \(0.526927\)), and the integers
   do not move: least \(C=19\) at \(q=0.5\) and \(41\) at \(q=0.55\)
   under both. Only \(q=0.6\) moves, \(223\to214\), and nothing consumes
   it. A real defect with no downstream consequence.
2. The endpoint Chernoff bound versus the exact first-passage
   probability, which the module already computes by DP. The excess is
   positive at every finite depth and shrinks — \(0.2205\), \(0.1231\),
   \(0.0673\) at \(L=20,40,80\) for \(C=18\) — while
   \(\text{excess}\times L\) *grows* (\(4.41,4.92,5.38\)), the signature
   of an \(O(\log L/L)\) correction rather than \(O(1/L)\). A
   negative-drift walk conditioned to stay above a level pays the same
   exponential cost as one merely ending above it, so Chernoff already
   carries the true rate. No first-passage refinement lowers
   \(\text{least } C=19\).

## Current literature

- Wu-Wang linear independence measure — **KNOWN**
  (`wu-wang-2014-irrationality-measure-log3`); relationship **extended**
  by [cycle_wuwang_reduction](juggler_cycle_wuwang_reduction.md).
- Rhin 1987 — **KNOWN** (`rhin-1987-pade-irrationality`). Equation (7)
  is what the laboratory records; equation (8) is the gap this branch
  names and does not close.
- Spiegelhofer–Wallner, *Collisions of digit sums in bases 2 and 3* —
  **KNOWN**, `independent`; used here only as a secondary report of
  Rhin equation (8), not as mathematics. Not yet a `literature/` id.
- BLS 2018 — **KNOWN**
  (`bondareva-luchin-salikhov-2018-log3-irrationality`); sharper than
  Wu-Wang by \(1.04\cdot10^{-4}\), deliberately unimported per
  [juggler_cycle_walk_fan_growth](juggler_cycle_walk_fan_growth.md).
- Chernoff–Hoeffding / Azuma-Hoeffding — **KNOWN**, textbook. The KL
  form is the sharp exponential rate for a Bernoulli tail; Azuma is a
  range-only bound and is strictly weaker for two-valued increments.
- Exponent pairs (Bourgain 2017, Trudgian–Yang 2023, Tao–Trudgian–Yang
  2025, Cushing 2025) — **KNOWN**, audited 7 September 2026 in
  [exponent_pair_two_monomial](../theory/exponent_pair_two_monomial.md);
  the hull minimum \(95/112\) is certified and none of the 2023–2025
  pairs moves it. Re-audited here only for currency; no action.

## Branch budget

```text
Target                  For every external result the programme leans on, is
                        the cited version the sharpest available, and does
                        anything imported for purpose X also apply to a
                        purpose Y still running on something weaker?
Novelty hypothesis      The Rhin/Wu-Wang miss was not a one-off. The same
                        failure mode -- a stronger statement sitting in the
                        repository or in the cited paper, unapplied -- should
                        have other instances, and they are cheap to find.
Falsifier               Every import is already the sharpest, and every
                        candidate improvement is either in the noise or has
                        no consumer. (Partially fired: see Decision.)
Already killed by?      No. This is not a Diophantine-wall member: it opens
                        no kill, proposes no new estimate, and its criterion
                        is bibliographic rather than a function of the
                        surplus, so the standing prohibition in
                        juggler_cycle_method_ceilings does not apply. The
                        exponent-pair leftover was audited on 7 September
                        2026 and is re-checked, not reopened.
Existing machinery      literature/ (161 entries), tao_reduction, paper_a_audit,
                        cycle_wuwang_reduction, the exponent-pair note.
Maximum Phase-0 scope   One probe, one test, one dossier. No Lean, no new
                        estimate, no manuscript edit, no literature/ entry
                        for an unverified report.
Promotion criterion     At least one chain assembled into a statement the
                        laboratory did not have, or at least one direction
                        closed with numbers.
Stop criterion          Findings that are all in the noise, or that require
                        primary sources nobody can check.
```

## Balanced-ternary formulation

None. The objects are classical measures and inequalities.

## Why BT may be relevant

It is not.

## Candidate operations / invariants

- Closure exponent equals the provable irrationality measure of
  \(\log2/\log3\) — **EXACT — HUMAN PROOF**
- Chain assembled, Dirichlet-floored at \(\mu=2\) —
  **COMPUTATIONALLY VERIFIED** as arithmetic
- Rhin eq. (8) gives \(\mu\le8.616\) — **OBSERVATION**, third-party
  report, **UNVERIFIED** against the primary source
- Azuma is strictly weaker than Chernoff-KL for two-valued increments —
  **EXACT — HUMAN PROOF** (textbook), instance
  **COMPUTATIONALLY VERIFIED**
- The lossiness moves no consumed constant —
  **COMPUTATIONALLY VERIFIED**
- Chernoff carries the true first-passage rate —
  **COMPUTATIONALLY VERIFIED** (surplus shrinks, \(\text{excess}\times L\)
  grows)
- A sharper concentration inequality improves Paper C — **REFUTED**
- No cycle of any length — not claimed

## Experiments

`python -m research.juggler_sequence.external_input_audit`, writing
`data/research/juggler/cycle_finance/external_input_audit.json`. Schema:
`transcendence_chain`, `transcendence_checks`, `concentration`,
`first_passage`. `log2_bad` replaces
`tao_reduction.bad_word_probability`, which divides by `2.0**d` and
overflows past \(d=1023\); the logarithmic form is what lets the
asymptotics be read at all.

## Conjectures

None opened.

## Counterexamples

None. The audit's own falsifier partially fired: the concentration half
found nothing that moves a consumed constant, which is recorded as a
CLOSE rather than dressed up.

## Formalization

None, and none needed: the content is bibliographic plus arithmetic on
audited constants. `GapTransferWW.lean` already carries the theorem the
chain feeds, parametrically in \(p\), so a sharper \(\mu\) needs no new
Lean — only a new instantiation numeral.

## Results

Classification **EXTERNAL_INPUT_AUDIT_MIXED**.

- The transcendence chain reduces to one identity: closure exponent
  \(=\mu(\log2/\log3)\). The laboratory did not have this statement; it
  makes every future Diophantine import a one-line comparison.
- Rhin equation (8) is a candidate \(\mu\le8.616\), sharper than the
  printed \(14.3\) and weaker than the Wu-Wang \(5.1163051\) now in use.
  Left UNVERIFIED and load-bearing on nothing.
- Paper C's concentration constants are not improvable by a sharper
  inequality: Azuma's lossiness moves no consumed integer, and Chernoff
  already carries the true first-passage rate. **The direction this
  branch was opened to test is closed.**
- The exponent-pair leftover is current as of the 7 September 2026 audit;
  no action.

## Open questions

Read Rhin, *Approximants de Padé et mesures effectives d'irrationalité*,
Séminaire de Théorie des Nombres Paris 1985–86, p. 160, equation (8).
Confirm the \(8.616\) ratio measure and whether its constant is explicit.
That is a library errand, not a research branch, and it changes no
current result either way.

## Decision

**PROMOTE.** The promotion criterion is met twice: a chain assembled into
an identity the laboratory did not have, and a direction closed with
numbers rather than intuition. The concentration half is the honest
outcome — I opened this branch on the hypothesis that a sharper
large-deviation bound would move Paper C's constants, and it does not.
Best next question: none here. The unverified Rhin row is a library
errand, recorded above.

## Publication assessment

Status: `MEASUREMENT`. The identity belongs as a remark beside Paper A
Section 6.2 and the closure threshold; the concentration findings belong
in negative knowledge. Not a theorem of its own and not a halt theorem.

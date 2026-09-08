# Juggler \(V_k\) ladder ceiling: what the remaining rungs are worth

Status: **CLOSE** (downstream-inert past \(V_5\); \(V_6\) already bought nothing)

Theory: [juggler_oeoee_production.md](../theory/juggler_oeoee_production.md)
Theorem 5 and the family table.
Probe: `research.juggler_sequence.vk_ladder_ceiling`.
Parent chain: [juggler_v6_production.md](juggler_v6_production.md).
Not a new production, not \(V_7\) constants, not rest-average, not a Paper B
localization, not the \(OOEEE\) route, and it does not touch \(\psi_F\).

## Problem

Each rung of the elementary family costs a full dossier and audit, and
every one of them ends by naming the next rung as the best next question:
\(V_5\) names \(V_6\), \(V_6\) names \(V_7\). Theorem 5 already gives the
limit of the whole family in closed form, so the residual is known without
computing any rung. What was never asked is what that residual *buys*.

Ask it in the units that decide. The exponent \(\lambda^{**}\) reaches the
Tao reduction through one number, the required rate \(1-\lambda^{**}\), and
that feeds discrete constants: the least Chernoff depth \(C\) and the least
Azuma depth \(C(q)\) in the biased-split form. A discrete constant moves
only when the rate crosses a threshold.

## Exact statement

**The generic rung.** \(V_k\) contributes coefficient \(3^{-(k+1)}\) at
scale \(\tfrac12(3/4)^k\). Verified against the hand-audited coefficients
of \(V_3,V_4,V_5,V_6\) in `RECURSIONS`, term by term.

**The limit.** The tail
\(\sum_{k\ge2}3^{-(k+1)}xy^k=\tfrac{x}{3}\tfrac{(y/3)^2}{1-y/3}\) sums
exactly; the recursion collapses to \(x+y/3=1\), root
\(\lambda_\infty=0.4926580\). Computed two independent ways -- the
collapsed equation and the summed series -- agreeing to \(10^{-12}\).

**The residual.** \(\lambda_\infty-\lambda_6=8.64\cdot10^{-5}\). Gaps to
the limit shrink by \(y/3=0.2892855\) per rung; the measured ratio at
\(k=18\) is \(0.2892854\), a relative error of \(3\cdot10^{-7}\).

**The verdict.** Every discrete constant reaches its terminal value at
\(V_5\) and never moves again:

| rung | \(\lambda\) | rate | \(C\) | \(C(0.5)\) | \(C(0.55)\) |
|---|---|---|---|---|---|
| \(V_2\) | \(0.480115\) | \(0.519885\) | 19 | 19 | 42 |
| \(V_3\) | \(0.489068\) | \(0.510932\) | 19 | 19 | 42 |
| \(V_4\) | \(0.491623\) | \(0.508377\) | 19 | 19 | 42 |
| \(V_5\) | \(0.492359\) | \(0.507641\) | 19 | 19 | **41** |
| \(V_6\) | \(0.492572\) | \(0.507428\) | 19 | 19 | 41 |
| whole family | \(0.492658\) | \(0.507342\) | 19 | 19 | 41 |

## Current literature

- Theorem 5 of the production note: the family telescopes to
  \(x+y/3=1\), root \(0.4927\). The ceiling was known; its price was not.
- The \(V_5\) dossier records "Azuma \(C(0.55)\) drops from 42 to 41", the
  \(V_6\) dossier records "stays 41". The laboratory had already observed
  rung by rung that \(V_6\) changed nothing, and drew no conclusion.
- Fate note section 7: the depth-two ceiling without extra productions is
  \(0.4927\); \(OOEEE\) reaches \(0.5392\) because it is a third-letter
  production and needs Paper B.

## Branch budget

Phase 0 only: one probe, one test module, no new estimates and no \(V_7\)
constants. Reuses `lambda_root`, `chernoff_exponent`, `least_C`,
`azuma_exponent`, `least_C_biased`, `failure_margin`.

## Balanced-ternary formulation

None. The recursion is over dyadic and \(3/4\)-power scales; balanced
ternary plays no role in the exponent calculus.

## Why BT may be relevant

It is not. Recorded so the next reader does not look for a BT reading of
the ladder.

## Candidate operations / invariants

The invariant is the collapsed recursion \(x+y/3=1\): the family sum is
exactly what is needed to turn the three-term head into it. The per-rung
gap ratio \(y/3\) is the derived one.

## Experiments

`ladder_report` prices every truncation against the thresholds it would
have to cross; `geometric_ratio` confirms the gap law; `continuous_consumer`
prices the one non-discrete consumer.

## Conjectures

None opened. The statement is a computation on a closed form, not a
conjecture.

## Counterexamples

None. The falsifier was checked and did not fire: a continuous consumer of
the rate exists, `failure_margin`, so the residual does move something. It
moves it by at most \(7.5\cdot10^{-6}\), which is \(1.3\cdot10^{-4}\) of the
\(0.06\) census resolution the margin is read against.

## Formalization

None. No Lean module; the content is arithmetic on audited constants.

## Results

The nearest discrete threshold is Azuma at \(q=0.55\) dropping \(41\to40\),
which needs \(\lambda>0.510018\). The family limit is \(0.492658\), short by
\(0.017360\) -- **201 times the entire remaining infinite ladder**. The
Chernoff threshold needs \(\lambda>0.519593\) and Azuma at \(q=0.5\) needs
\(\lambda>0.522563\); both are further still.

So the last rung that paid for itself was \(V_5\). The \(V_6\) audit moved
\(\lambda^{**}\) by \(2.1\cdot10^{-4}\) and changed no constant, and no
finite or infinite collection of later rungs can change one.

## Open questions

None in this branch. The live question the ladder was standing in for is
unchanged and lies elsewhere: the \(r\ge2\) rungs, which need genuinely
nested floors and therefore Paper B, and which are exported.

## Decision

**CLOSE.** The elementary \(V_k\) ladder is downstream-inert past \(V_5\).
Recorded in [negative_knowledge.md](../negative_knowledge.md): do not open
\(V_7\) or any later truncation, and do not reopen this as a sharper tail,
a faster-converging reindexing, or a combined \(V_k\) estimate. Anything
that moves a constant has to move \(\lambda\) by at least \(0.0174\), which
is two hundred times more than the family has left, so it must come from
outside the family.

\(\lambda^{**}=0.4926\) stands as the official unconditional exponent; this
branch changes no published constant.

## Publication assessment

Status: `MEASUREMENT`. Belongs as a remark in the production note beside
Theorem 5, not as a theorem of its own. Not a halt theorem.

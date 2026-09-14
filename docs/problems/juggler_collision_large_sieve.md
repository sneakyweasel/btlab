# Juggler: does a restricted collision count buy the Tao-type bound?

Status: **PROMOTE**, conditional. One exact implication, one proved
separation, one refuted route to the hypothesis, and a Phase-0 census that
declines to falsify it.

Not a halt theorem, not a termination theorem, not a cycle obstruction, not a
floor raise, and not a Paper C edit. The implication below is conditional on a
hypothesis nobody has proved, and it is weaker in the exponent than the bound
Paper C already states.

## Problem

Paper C Theorem 8.3 bounds the count of odd \(n\in(y,2y]\) with entrance time
\(\tau(n)>d\) using \(\mathrm H(C,A)\). Is there a second route to a bound of
that shape through a *collision count* --- a second moment
\(\sum_w \#[w]^2\) over the depth-\(d(y)\) words --- and if so, what does it
cost, and is it the same hypothesis wearing different clothes?

## Exact statement

**The implication (EXACT --- HUMAN PROOF, `J-collision-bound-half-exponent`).**
If the depth-\(d(y)\) collision count restricted to \(L\)-bad words satisfies
\[
\sum_{w\ L\text{-bad}} \#[w]^2 \ \le\ K\,N^2\,2^{-(d-1)},\qquad K=O(1),
\]
then
\(\#\{n \text{ odd}\in(y,2y]: \tau(n)>d\}\le \sqrt{K}\,N\,2^{-e(C)L/2}\):
Theorem 8.3 at **half the exponent**. The proof is Cauchy--Schwarz against the
bad-word count of Lemma 8.2, and the halving is exactly that Cauchy--Schwarz.

**The separation (EXACT --- HUMAN PROOF,
`J-collision-bound-does-not-invert`).** The one-sided constant-factor
hypothesis above is not a restatement of \(\mathrm H(C,A)\). Paper C
Section 9.3(d) makes the pair-correlation *asymptotic* equivalent to
\(\mathrm H(C,A)\) by Parseval and Walsh inversion; the constant-factor
one-sided form does not invert, and the separation is proved rather than
assumed.

**The price.** Half the exponent costs depth. Against the live
`REQUIRED_RATE`, the least depth constant moves from \(20\) to \(30\); the
graded family at accuracy \(\gamma\in\{0,\tfrac14,\tfrac12,\tfrac34,1\}\)
reads \([30,25,23,21,19]\), so \(\gamma=1\) recovers \(19\) and costs nothing,
and \(\gamma=0\) is the crude form. These numbers moved with the laboratory's
\(\lambda^{**}\): they were \([32,27,24,22,20]\) when the work was written
against \(\lambda^{**}=0.4480\), and the module reproduces those exactly when
called with the old rate.

## Current literature

- Cauchy--Schwarz, Parseval, Walsh expansion --- **KNOWN**, textbook.
- Large sieve --- **KNOWN**; negative knowledge already records
  "Parseval / large sieve is the pair-correlation form already named above."
  See *Already killed by?* below.
- Paper C Theorem 8.3, Lemmas 8.1--8.2, Section 9.3(d) --- internal.

## Branch budget

```text
Target                  Is there a collision-count route to a Tao-shaped bound,
                        what exponent does it give, and is it H(C,A) again?
Novelty hypothesis      A one-sided constant-factor second moment over bad words
                        is strictly weaker than the pair-correlation asymptotic,
                        and still buys a bound --- at half the exponent.
Falsifier               The restricted second moment is false on data, or the
                        route inverts to H(C,A) and is therefore not new.
Already killed by?      No, and this was checked rather than asserted. Negative
                        knowledge fences "Parseval / large sieve" as the
                        pair-correlation form of H(C,A) and forbids reopening it
                        as a signed Walsh tail or a third formulation. That fence
                        binds the asymptotic; J-collision-bound-does-not-invert
                        proves the one-sided constant-factor form separates from
                        it. The branch does not reopen the fenced object.
Existing machinery      tao_reduction, Paper C Sections 8-9, the walk DP.
Maximum Phase-0 scope   One module, one census, ledger rows. No Lean, no
                        manuscript edit, no floor raise.
Promotion criterion     An implication stated exactly, with its price, plus a
                        census that either falsifies the hypothesis or does not.
Stop criterion          The hypothesis is refuted, or shown equivalent to H(C,A).
```

## Balanced-ternary formulation

None. The objects are words, cylinder counts and a tilted walk.

## Why BT may be relevant

It is not.

## Candidate operations / invariants

- Restricted second moment over \(L\)-bad words --- the hypothesis.
- Walsh spectrum of the bad-set indicator --- **REFUTED** as a route to it.
- Ladder / renewal factorisation of the live set at the walk minimum.
- The tilted live moment \(R_d\) against its fair value.

## Experiments

`python -m research.juggler_sequence.collision_large_sieve`, writing
`data/research/juggler/collision_large_sieve/summary.json`. Schema: `price`,
`graded_family`, `verdict`, `H_quantifier_defect`. The Phase-0 census runs on
exact odd orbits, not on a model.

## Conjectures

`J-walsh-restricted-product-shape` --- **CONJECTURE**. A product-shape bound
\(|W_T^{\mathrm{bad}}|\le KMb^{|T|}\) with \(b=\tanh(\theta_C/2)\), consistent
with every floor proved, and by itself insufficient to reach
\(\mathrm P_\theta\).

## Counterexamples

None found. The Phase-0 falsifier does not fire: the worst ratio to the
finite-sample null is \(1.0087\), and the hypothesis survives the census. That
is a failure to refute, not evidence for.

## Formalization

None, and none attempted. The implication is Cauchy--Schwarz over a counting
lemma; the hypothesis it is conditional on is the open object.

## Results

Seventeen ledger rows: eight **EXACT --- HUMAN PROOF**, six **OBSERVATION**,
one **REFUTED**, one **CONJECTURE**, one **REPARAMETERIZATION**.

- **The implication and its separation** hold exactly, at half the exponent.
- **The spectral route to the hypothesis is closed**
  (`J-bad-set-spectrum-cannot-win`, **REFUTED**): the bad-set factor of
  Cauchy--Schwarz is \(\sqrt{p_{\mathrm{bad}}}\) exactly, by Parseval for a
  0/1 indicator, so no sharper knowledge of the spectrum can help; the loss
  sits on the unrestricted Walsh energy, and
  \(K_{\mathrm{all}}\ge1>p_{\mathrm{bad}}\) always (measured \(8.81\),
  \(133.33\), \(532.30\) at \(d=12,16,18\)).
- **The live set is tilted-fair to a few tenths of a percent**, measured on
  400000 exact odd orbits, and the tilted mass sits on the hard class.
- **The renewal chain conserves depth** --- **REPARAMETERIZATION**, not a new
  wall: summed over \(n\), the coarse/fine split is exactly Paper B's parity
  balance with no twist.

## Open questions

Prove or refute the restricted second moment with \(K=O(1)\). The spectral
route to it is refuted; what remains is unattempted. Whether the graded family
at \(\gamma>0\) is reachable more cheaply than \(\gamma=0\) is also open.

## Decision

**PROMOTE, conditionally.** The promotion is of an implication, not of a
bound: `J-collision-bound-half-exponent` is exact and its hypothesis is
unproved, so nothing here improves any stated Juggler result today. What earns
the promotion is that the implication is stated with its exponent and its
price, that the separation from \(\mathrm H(C,A)\) is proved rather than hoped,
and that the most obvious route to the hypothesis is closed with numbers
instead of left open as a maybe.

Three things this does **not** license. It is not a second proof of Theorem
8.3 --- it is weaker in the exponent and conditional on more. It does not
reopen the fenced Parseval / large-sieve object. And its seventeen rows carry
their own tags, and they were extracted from an unmerged branch on 14 September
2026 on the strength of compiling, linting and passing their tests, which is a
statement about the code and not about the proofs. **Audited 14 September 2026.**
No claim was wrong and no tag fraudulent; fourteen rows needed no change. Three
carried a `REQUIRED_RATE` that had since moved, the Phase-0 census was marking
its operative depth at the retired constant (without changing the verdict), two
test assertions could not fail, and `J-tau-le-sigma` drew "at most 4%" from two
single-seed draws that a third seed exceeds. All five are fixed; see the research
journal. What is still not audited is nothing in the bookkeeping --- it is that
the eight EXACT --- HUMAN PROOF rows have been read for internal consistency and
backing, not independently re-derived.

## Publication assessment

Status: `MEASUREMENT`. A conditional implication and a closed route belong in
the laboratory record and in negative knowledge; neither is a theorem of its
own, and neither is a halt theorem.

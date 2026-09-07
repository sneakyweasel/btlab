# Juggler depth-one main term: the rational cubic dual and its cancellation on odd starts

Status: **CLOSE** (an exact statement about the first letter; nothing
reaches the frontier)

Not a Paper B estimate, not a census, not a reopening of the tower
question. The object is one exponential sum,
\(\sum_{M\le X}e(\tfrac12M^{3/2})\), and its restriction to odd \(M\).

## Problem

Does the depth-one parity sum of the Juggler odd branch have a genuine
main term, and does it survive the restriction to odd starts?

## Exact statement

**Proposition (EXACT — HUMAN PROOF sketch; COMPUTATIONALLY VERIFIED to
four digits).** Let \(F(M)=\alpha M^{3/2}\) with \(\alpha\in\mathbb Q\).
The van der Corput B-process dualises \(\sum_{M\le X}e(F(M))\) to the
frequency \(\nu=F'(M)\): with \(M_\nu=(2\nu/3\alpha)^2\),
\(F(M_\nu)-\nu M_\nu=-4\nu^3/(27\alpha^2)\), so
\[
\sum_{M\le X}e(\alpha M^{3/2})
=e(\tfrac18)\sum_{\nu\le\frac{3\alpha}2\sqrt X}\frac{\sqrt{8\nu}}{3\alpha}\,
e\!\Bigl(-\frac{4\nu^3}{27\alpha^2}\Bigr)+O(X^{1/4+\varepsilon}).
\]
The dual phase is a cubic with rational coefficient, so the dual sum is a
complete cubic Gauss sum on every period and does not cancel. At
\(\alpha=\tfrac12\): \(\sum_{r\bmod 27}e(-16r^3/27)=9\), and
\[
\Bigl|\sum_{M\le X}e(\tfrac12M^{3/2})\Bigr|
=\frac{4\sqrt8}{27}\Bigl(\frac34\Bigr)^{3/2}X^{3/4}(1+o(1))
=0.27217\,X^{3/4}(1+o(1)).
\]
Consequently \(\#\{M\le X:\lfloor M^{3/2}\rfloor\text{ even}\}
-\#\{\text{odd}\}=\kappa X^{3/4}(1+o(1))\) with \(\kappa=0.425\pm0.001\).

**Cancellation on odd \(M\), every harmonic (EXACT — HUMAN PROOF).**
For odd \(k\) the untwisted dual sum of \(\sum_Me(\tfrac k2M^{3/2})\) has
complete sum \(C_k=\sum_{r\bmod 27k^2}e(-16r^3/27k^2)\), and the
parity-twisted one \(C_k'=\sum_{\nu\bmod 27k^2}e(-2(2\nu-1)^3/27k^2)\).
Since \(2\) is invertible mod \(27k^2\), both \(r\mapsto 2r\) and
\(\nu\mapsto 2\nu-1\) permute the residues, so
\(C_k=C_k'=\sum_we(-2w^3/27k^2)\) exactly, for every odd \(k\)
(checked to \(10^{-6}\) for \(k\le11\); \(C_k=9k\) for \(3\nmid k\),
\(C_9=0\)). Hence every odd harmonic of the parity indicator loses its
\(X^{3/4}\) term on odd \(M\), and with the B-process error terms
(\(O(\lambda_2^{-1/2}+\log)=O(X^{1/4}k^{-1/2}+\log kX)\)) plus the
incomplete-period remainders of the dual sums (Weil-type,
\(O(q^{1/2+\varepsilon}\sqrt V)\)) and Erdős–Turán at \(H=X^{1/2}\):

**Theorem (depth-one super-fairness; EXACT — HUMAN PROOF sketch).**
\[
\#\{n\le X\ \text{odd}:\ \lfloor n^{3/2}\rfloor\ \text{odd}\}
=\tfrac X4+O(X^{1/2+\varepsilon}),
\]
against the \(O(X^{3/4})\) that the second-derivative test gives and
that is attained over even \(n\). Measured, the odd-restricted
harmonic sums are all \(\le 3.4X^{1/4}\) at \(X\le10^7\) and the parity
imbalance over odd \(n\) is \(30,146,210,16\) at
\(10^5,10^6,10^7,5\cdot10^7\), so the truth is nearer \(X^{1/4}\); the
\(X^{1/2+\varepsilon}\) is what the harmonic sum of the remainders
proves.

**Cancellation on odd \(M\), the first harmonic (EXACT — HUMAN PROOF sketch).**
\(\sum_{M\text{ odd}}=\tfrac12\bigl(S-S'\bigr)\) with
\(S'=\sum_Me(\tfrac12M^{3/2}+\tfrac12M)\). The twist shifts the dual
frequency by \(\tfrac12\): the stationary points of \(S'\) sit at
\(\nu-\tfrac12\), and with \(\mu=\nu-\tfrac12\) the dual phase is again
\(-16\mu^3/27\). As \(\nu\) runs mod \(27\), \(2\mu=2\nu-1\) runs over
a complete residue system mod \(27\), so the complete cubic sum is the
same \(9\) and the two \(X^{3/4}\) terms are equal. Hence
\(\sum_{M\le X,\ M\text{ odd}}e(\tfrac12M^{3/2})=o(X^{3/4})\);
measured, it grows like \(X^{0.31}\), below the random-walk order
\(X^{1/2}\).

## Current literature

- van der Corput B-process / Poisson summation — `known`; the
  observation that \(c=3/2\) has the integer dual exponent
  \(c/(c-1)=3\), making the dual a rational cubic, is classical in
  spirit (Piatetski-Shapiro sequences with \(c=3/2\)).
- Paper B Theorem 4.1 / Lemma 3.5 (Vaaler) and the second-derivative
  test (T3) of the OEOEE note §11 — `known`: they bound this sum by
  \(O(X^{3/4})\); this branch records that the bound is attained over
  all \(M\), with an explicit constant, and beaten on odd \(M\).
- No literature name audited for the odd-restricted cancellation.

## Branch budget

```text
Mathematical target     Is the X^{3/4} bound for Σ e(M^{3/2}/2) sharp,
                        and does the main term survive on odd M?
Novelty hypothesis      The rational cubic dual gives an explicit main
                        term; parity restriction might remove it.
Falsifier               The measured constant disagrees with the
                        stationary-phase prediction; or the odd sum is
                        of order X^{3/4}.
Existing machinery      numpy; the B-process by hand.
Maximum Phase-0 scope   The constant, the two complete cubic sums, the
                        sums at 1e5-5e7 split by parity, the tower
                        levels to 4 at 1e6-1e7. No Lean, no note edit.
Promotion criterion     A consequence at depth ≥ 5 or a sharpened
                        production saving.
Stop criterion          The statement is depth-one only.
```

## Balanced-ternary formulation

None.

## Why BT may be relevant

Not relevant here; recorded for the template.

## Candidate operations / invariants

- B-process dualisation of \(\alpha M^{3/2}\) to \(-4\nu^3/(27\alpha^2)\)
  — **EXACT — HUMAN PROOF**.
- Complete cubic sums mod \(27\): \(\sum e(-16r^3/27)=\sum e(-2r^3/27)=9\)
  — **EXACT** (computed; \(r=3s+t\) reduces both to \(3\cdot3\)).
- The constant \(0.27217\) and the even-\(M\) bias \(0.425X^{3/4}\) —
  **COMPUTATIONALLY VERIFIED** at \(10^5,10^6,10^7,5\cdot10^7\)
  (\(0.2701,0.2707,0.2721,0.2719\); \(0.425\) at every scale).
- Tower levels \(2\)–\(4\) over odd starts: imbalance of order
  \(\sqrt{\text{cylinder}}\) — **OBSERVATION** (\(10^5\)–\(10^7\)).

## Experiments

- Probe: `research.juggler_sequence.depth_one_main_term`.
- Artifact: `data/research/juggler/depth_one_main_term/summary.json`.
- Tests: `tests/research/juggler_sequence/test_depth_one_main_term.py`.

## Conjectures

None new.

## Counterexamples

None.

## Formalization

None. The complete cubic sums are finite and could be `decide`d; the
B-process is analysis. Not opened.

## Results

Classification **DEPTH_ONE_MAIN_TERM_CANCELS_ON_ODD_STARTS**.

```text
  X        |S_all|/X^(3/4)   |S_odd|    |S_odd|/X^(1/2)   even-M bias/X^(3/4)   odd-M imbalance
  1e5      0.2701            22.6       0.071             0.425                  30
  1e6      0.2707            51.4       0.051             0.425                 146
  1e7      0.2721            95.4       0.030             0.425                 210
  5e7      0.2719           156.1       0.022             0.425                  16
  predicted 0.27217
```

- The vdC/(T3) order \(X^{3/4}\) is attained over all \(M\), with the
  predicted constant; the whole bias sits on even \(M\), which the
  Juggler map sends to \(\lfloor\sqrt M\rfloor\), not to
  \(\lfloor M^{3/2}\rfloor\).
- Over the Juggler-relevant odd \(M\) the main term cancels and the sum
  is far below \(\sqrt X\): the odd branch's first letter is super-fair.
- The identity \(C_k=C_k'\) holds for every odd \(k\): the parity
  indicator's whole Fourier series loses its \(X^{3/4}\) terms on odd
  \(M\), and the odd-restricted harmonic sums are \(1.3\)–\(3.4\) times
  \(X^{1/4}\) for \(k=1,3,5,7\) at \(10^5\)–\(10^7\).
- Tower levels \(2\)–\(4\) (cylinders \(O^k\), odd starts to \(10^7\))
  have imbalances \(\approx(1.0,\,1.2,\,-1.1)\sqrt{\text{cylinder}}\):
  the rational-cubic structure is special to the exponent \(3/2\);
  \((3/2)^k\) for \(k\ge2\) has a non-integer dual and the levels look
  like a fair coin at the \(\sqrt N\) scale.

Not claimed: anything at depth \(\ge5\); any change to a production
saving (the OEOEE note's exponents do not depend on the savings).

## Open questions

- Whether the productions' binding sums (Half A/B of the OEOEE note
  §11, bounded by (T3) at order \(m'^{-4/9}\)) carry this main term
  over all \(w\), in which case the bound is attained and only an
  explicit secondary main term — not a better estimate — could move
  the saving. Not opened: the productions belong to the host session
  and their \(\lambda\) does not depend on the saving.

## Decision

**CLOSE.** The stop criterion fired: the statement is exact and
depth-one only. It sharpens the picture of the first letter — the
\(X^{3/4}\) bound is the truth over all \(M\) and is beaten by parity
restriction — and says nothing at unbounded depth. Best next question:
none on this line.

## Publication assessment

Status: `STRUCTURAL`. Two exact statements with checked constants: the
attained \(X^{3/4}\) over all \(n\) and the \(O(X^{1/2+\varepsilon})\)
super-fairness over odd \(n\); a remark for Paper B's Theorem 4.1.

# The nested parity discrepancy lemma (two-step parity)

> **Phase-26 withdrawals (29 August 2026, referee response).** A
> referee-style review of Paper B found real holes in the deeper
> harvest, and the corresponding ledger rows are retagged
> `CONJECTURE`: **Theorem T** (length-5 splits; the OOOE\* passenger
> modes of size \(\asymp lP^{3/16}\) exceed the kernel decoration
> budget as stated and the dominances were never rerun), **Theorem X**
> (length-7 splits; the rearrangement's Taylor remainder
> \(\tfrac{45}{32}v^{1/8}\asymp n^{9/32}\) *grows* and was discarded
> in decaying-remainder style — discarding costs \(kP^{1+9/32}\)),
> **Theorem AA** (length-8 quartet; \(|E|<1\) without control of
> \(E'\)), **Corollary R'** (proof-by-monotonicity, never rerun at
> any specific \(\alpha\)), and **Corollaries U/Y/AB** (densities
> \(7/8\), \(57/64\), \(29/32\), which inherit the holes). The
> certified density of Paper B was \(13/16\) until the
> 2 September 2026 import of the repaired Theorem T /
> Corollary U as Theorem 6.3 / Corollary 6.4 (density
> \(7/8\)). Length 7/8 remain withdrawn. Also repaired in
> Paper B: Step 5b of Theorem R (the per-cell summation of
> inverse-power van der Corput terms was invalid; replaced by global
> sublevel splitting with a trivial transition bound), the
> parity-reindexing Jacobian (new Lemma 3.10), and the old
> Theorem 7.4's false "in particular" (now Proposition 7.4 with the
> \(\sqrt{\log L}\) factor). Parts VII, X, and XI below are kept as
> **routes**, not proofs. Phase 28 reruns Theorem R at the single
> exponent \(\alpha=33/32\) (Part XIII); the Corollary R′ *family*
> stays withdrawn. Phase 29 classifies the length-7 remainder as
> an engine (Part XIV); Theorem X stays a route. Phase 34
> refutes the Theorem-T passenger slogan (Part XIX). Phase 35
> closes the isolated chirps \(e(un^{27/16})\) and
> \(e(Cn^{3/2})\) (Part XX, Lemma X5); the
> \(w^{3/2}\to n^{27/16}\) reduction is not a decoration,
> so Theorem X stays a route. Phase 37 refutes the
> X3-run plus Q/R3-carry slogan for \(e(uw^{3/2})\)
> (Part XXI). Phase 38 refutes the integer-\(w\)
> engine-line slogan (Part XXII).

> **Phase-25 correction (29 August 2026).** The Part-VI mixed-piece
> bound recorded below (frozen-coefficient model \(e(sX)\),
> \(s\asymp rP^{3/4}\), saving \(P^{1/8}/r^{1/6}\)) is **wrong**: the
> mixed pieces are exact level-2 waves \(e(qY)\), and the frozen model
> discards the sawtooth \(-\tfrac32 qX^{1/2}\theta\) of amplitude
> \(\asymp qP^{3/4}\) inside \(qY=q(X-\theta)^{3/2}\). The corrected
> bound is \(q^{-1/6}P^{23/24+\varepsilon}\) (depth-2 strength), and
> Theorem R's saving is \(\delta=1/96\) uniformly for
> \(k\le P^{1/24}\), not \(1/64\)/\(1/72\); downstream exponents
> \(1-1/72\) in Theorems S/T/X/AA become \(1-1/96\); **no density
> changes**. The authoritative full-length record is Paper B,
> Section 5
> ([juggler_parity_discrepancy_note.md](../theory/juggler_parity_discrepancy_note.md));
> this document's Part VI is kept as history and negative knowledge.

Analytic document for the promoted two-step parity branch, revised by
the Phase-2 review pass (see the review record after Theorem C) and
extended by the Phase-3 depth-4 part (Lemma D, Theorem E,
Corollary F) and the Phase-4 beyond-depth-4 part (Lemma G,
Propositions H/I/J, Conjecture K). Claim labels are per statement.
Ledger rows: `J-nested-parity-discrepancy`,
`J-fourth-letter-linearization`, `J-triple-parity-discrepancy`,
`J-four-step-descent-density`, `J-second-order-linearization`,
`J-equidistribution-implies-density-one`,
`J-even-branch-third-letter`, `J-tier2-gap-and-shifted-forms`,
`J-depth4-slow-branch`, `J-kernel-cancellation`,
`J-depth4-complete`, `J-depth5-contracting`,
`J-five-step-descent-density`,
`J-level3-inner-linearization`,
`J-scale-invariant-R-extension`,
`J-w-family-below-nine-eighths`,
`J-length7-remainder-engine`,
`J-length7-passenger-theorem-t`,
`J-length7-vdc3-chirps`,
`J-length7-x3-qr3-carry`,
`J-length7-integer-w-block`,
`J-depth7-engine-contracting`,
`J-seven-step-descent-density`,
`J-increment-linearization`,
`J-increment-first-K3`,
`J-x1-landing-criterion`,
`J-x1-absorption-K3`,
`J-nested-floor-without-W-family`,
`J-k3-toolkit-obstruction`.
Imported into the finite-dynamics note (consolidation phase, August
2026): Lemmas A/B as Lemma 5.3, Theorem C as Theorem 5.4,
Proposition L as Proposition 5.5, Lemma D as Lemma 5.6, Theorem E as
Theorem 5.7, Lemma A\u2032 and Theorem Q as Theorem 5.8, Corollary F
and Proposition I as Corollary 5.9, Proposition J as Proposition 6.1,
and Conjecture O as Conjecture 6.2. The floor reductions (Lemmas B/N
pattern, the parity bridge, and the Part-VI double-gap identity) are
Lean-verified in `formal/Problems/Juggler/GapCells.lean`. Part VI
(Phases 8–9) holds the double-differencing proof of Conjecture O
(Theorem R) and the depth-4 completion (Theorem S), both re-derived
by the Phase-9 adversarial review (record in Part VI); ledger rows
`J-kernel-cancellation` (retagged) and `J-depth4-complete`. The
note's Conjecture 6.2 paragraph is superseded and awaits editorial
consolidation. Part VII (Phase 10) closes the two length-5
contracting splits OOOEE and OOEOE (Theorem T, Corollary U), lifting
the certified-descent density to \(7/8\). Part VIII (Phase 11)
isolates the OOOO\* fifth letter as the level-3 floor-defect
kernel \(K_3\) (Lemma V1, Conjecture V); the bound is not claimed.
Part IX (Phase 12) refutes the scale-invariant copy of Theorem R
(Lemma V2, Proposition W). Part X (Phase 13) closes the two
length-7 engine contractors OOEOOEE and OOOEOEE (Theorem X,
Corollary Y), lifting certified descent to \(57/64\).
Part XI (Phase 14) refutes the increment-first attack on
\(K_3\) (Lemma Z1, Proposition Z).
Part XII (Phase 15) refutes X1-absorption of the \(K_3\)
leftover into a freezing integer (Lemma Z3, Proposition AA).
Part XIII (Phase 16) unifies the obstruction and parks the
toolkit (Proposition BB).
Not a termination claim; the remaining depth-\(\ge5\) expanders
(OOOO\*, OOEOO, OOOEO) and the density-one statement remain open.

Throughout, \(n\) is odd, \(X = n^{3/2}\), \(m = m(n) = \lfloor
n^{3/2}\rfloor = \operatorname{isqrt}(n^3)\), \(\theta = \theta_n =
\{n^{3/2}\} = X - m\), and \(\psi(x) = (-1)^{\lfloor x\rfloor}\). The
first two image parities of an odd start are \((-1)^m = \psi(n^{3/2})\)
and \((-1)^{\lfloor m^{3/2}\rfloor} = \psi(m^{3/2})\).

## Context

Theorem 5.1 of the finite-dynamics note bounds the depth-1 sum
\(\sum_{n \le N \text{ odd}} \psi(n^{3/2}) \ll N^{5/6}\). The Phase-0
census (see `juggler_two_step_parity.md`) shows the depth-2/3/4 joint
classes equidistribute empirically with envelope exponents
\(0.28\)–\(0.66\). A literature check (August 2026) found no
equidistribution result for nested floor powers
\(\lfloor\lfloor n^c\rfloor^d\rfloor\): the Piatetski-Shapiro corpus
covers single floors, intersections, and pseudo-polynomials only.
Novelty annotation: independent.

The naive Taylor expansion
\(m^{3/2} = n^{9/4} - \tfrac32\theta n^{3/4} + O(n^{-3/4})\) leaves a
fractional part with growing amplitude \(n^{3/4}\), which defeats the
van der Corput method directly (localizing \(\theta\) in short blocks
gives intervals of length \(\asymp \lambda_3^{-1/3}\), exactly the
threshold where the third-derivative test saves nothing). The route
below removes the fractional part exactly before any analysis.

## Lemma A (exact linearization) — EXACT — HUMAN PROOF

For every odd \(n \ge 3\),

\[
m^{3/2} \;=\; \tfrac32\, m\, n^{3/4} \;-\; \tfrac12\, n^{9/4}
\;+\; E(n),
\qquad
0 \;\le\; E(n) \;\le\; \tfrac38\,(n^{3/2}-1)^{-1/2}
\;\le\; \tfrac12\, n^{-3/4}.
\]

*Proof.* Let \(f(t) = (X - t)^{3/2}\) on \([0, \theta]\), so
\(f(\theta) = m^{3/2}\). Taylor with Lagrange remainder at \(0\):
\(f(\theta) = X^{3/2} - \tfrac32 X^{1/2}\theta + \tfrac38 (X -
\xi)^{-1/2}\theta^2\) for some \(\xi \in (0, \theta)\). Substitute
\(\theta = X - m\) in the linear term:
\(X^{3/2} - \tfrac32 X^{1/2}(X - m) = -\tfrac12 X^{3/2} + \tfrac32 m
X^{1/2} = -\tfrac12 n^{9/4} + \tfrac32 m n^{3/4}\). The remainder is
\(E(n) = \tfrac38 (X-\xi)^{-1/2}\theta^2 \in [0, \tfrac38(X -
1)^{-1/2}]\), and \((X-1)^{-1/2} \le \tfrac43 X^{-1/2} =
\tfrac43 n^{-3/4}\) already for \(n \ge 3\). \(\square\)

The point: the non-smooth integer \(m\) enters the phase *linearly*,
multiplied by the smooth function \(\tfrac32 n^{3/4}\); no fractional
part survives. Exact validation (`identity_scan`, scaled-integer
arithmetic at \(10^{30}\) precision): the bound holds on all odd
\(n \le 4001\) and at \(n = 10^6{+}1, 10^7{+}3, 10^9{+}1, 10^{12}{+}1\),
with worst observed ratio \(E(n) / (\tfrac12 n^{-3/4}) = 0.7494\),
matching the theoretical supremum \(3/4\) attained as
\(\theta \to 1^-\).

## Lemma B (gap cell structure) — EXACT — HUMAN PROOF

For \(h \ge 1\) and odd \(n\), let \(g(n) = m(n+2h) - m(n)\) and
\(\delta(n) = (n+2h)^{3/2} - n^{3/2}\). Then

\[
g(n) = \lfloor\delta(n)\rfloor + \kappa(n),
\qquad
\kappa(n) = \bigl[\{n^{3/2}\} \ge 1 - \{\delta(n)\}\bigr] \in \{0,1\}.
\]

*Proof.* \(g = \lfloor X + \delta \rfloor - \lfloor X \rfloor =
\lfloor \delta \rfloor + \lfloor \{X\} + \{\delta\} \rfloor\), and the
last floor is \(1\) precisely when \(\{X\} + \{\delta\} \ge 1\).
\(\square\)

Since \(\delta\) is smooth and increasing with \(\delta'(n) =
\tfrac32[(n+2h)^{1/2} - n^{1/2}] \asymp h n^{-1/2}\), the level sets of
\(G(n) = \lfloor\delta(n)\rfloor\) partition a dyadic block \(n \in
(P, 2P]\) into \(O(hP^{1/2})\) cells of length \(\asymp P^{1/2}/h\),
on which \(G\) is constant and \(G \asymp hP^{1/2}\). Exact validation
(`gap_decomposition_check`): thousands of consecutive odd \(n\) at
\(10^6\) and \(10^9\), \(h \in \{1,2,3,7\}\), all matches, only
exact-boundary samples skipped.

## Theorem C (nested parity discrepancy) — EXACT — HUMAN PROOF

For every \(\varepsilon > 0\) and every choice of signs
\((a, b) \in \{0,1\}^2\), \((a,b) \ne (0,0)\),

\[
\Bigl|\sum_{n \le N,\ n \text{ odd}}
\psi(n^{3/2})^{a}\,\psi(m(n)^{3/2})^{b}\Bigr|
\;\ll_\varepsilon\; N^{23/24 + \varepsilon}.
\]

Consequently each of the four joint parity classes of
\((m, \lfloor m^{3/2}\rfloor)\) on odd \(n \le N\) has cardinality
\(\tfrac{N}{8} + O(N^{23/24+\varepsilon})\); in particular the
odd-to-odd cylinder refines to
\(\#\{n \le N \text{ odd}: J(n) \text{ odd},\ J^2(n) \text{ even}\}
= \tfrac N8 + O(N^{23/24+\varepsilon})\),
one letter deeper than Theorem 5.1.

### Proof outline with exponent bookkeeping

Work on dyadic blocks \(n \in (P, 2P]\), odd. Fix truncations
\(J_1 = J_2 = P^{1/24}\) (wave modes), \(H = P^{1/12}\) (differencing),
\(R = P^{1/4}\) (cell modes).

**Step 1 (wave expansion).** By Vaaler's theorem applied to the
period-2 square wave, \(\psi(x) = V_J(x/2) + O(\Delta_J(x/2))\) where
\(V_J(t) = \sum_{0 < |q| \le J} a_q e(qt)\) with \(|a_q| \le
\min(1, 2/|q|)\), and \(\Delta_J \ge 0\) is a trigonometric polynomial
of degree \(J\) with constant term \(O(1/J)\) and coefficients
\(O(1/J)\). For the product, \(|\psi_1\psi_2 - V_1 V_2| \le \Delta_1 +
\Delta_2 + \Delta_1\Delta_2\), and \(\Delta^2\) is again a nonnegative
trigonometric polynomial (degree \(2J\), constant term \(O(1/J)\)),
so every error term is a majorant sum of the same shape. Expanding
both factors reduces the theorem to bounds, uniform in the mode
coefficients \(\mu, \nu \in \tfrac12\mathbb Z\) with \(|\mu| \le J_1\),
\(\tfrac12 \le |\nu| \le J_2\) (majorant modes contribute integer
\(\mu, \nu\); wave modes contribute odd-over-two values), for

\[
S_{\mu,\nu}(P) = \sum_{n \in (P,2P],\ n \text{ odd}}
e\bigl(\mu\, n^{3/2} + \nu\, m^{3/2}\bigr),
\]

plus pure first-factor majorant sums: \(\sum_n \Delta_{J_1}(n^{3/2}/2)
\ll P/J_1 + P^{5/6+\varepsilon} \ll P^{23/24+\varepsilon}\) by the
depth-1 machinery, while \(\sum_n \Delta_{J_2}(m^{3/2}/2)\) reduces to
the \(\mu = 0\) case of \(S_{\mu,\nu}\) itself. The analysis below
only uses \(|\nu| \ge \tfrac12\) and the truncation sizes; mode
weights sum to \(O(\log^2 P)\).

Below, write \(i = 2\mu\) and \(j = 2\nu\), so \(|i| \le 2J_1\),
\(1 \le |j| \le 2J_2\); every bound depends only on \(|i|, |j|\) and
absolute constants.

**Step 2 (linearization).** By Lemma A, replacing \(\tfrac j2 m^{3/2}\)
by \(\tfrac{3j}4 m n^{3/4} - \tfrac j4 n^{9/4}\) changes \(S_{\mu,\nu}\)
by at most \(2\pi \tfrac j4 \sum_{n \sim P} n^{-3/4} \ll j P^{1/4}
\le P^{7/24}\).

**Step 3 (van der Corput A-process).** With \(H = P^{1/12}\),
\(|S_{\mu,\nu}|^2 \le \tfrac{2P}H \sum_{0 \le h < H} |T_h|\), where
\(T_h\) sums \(e(\Phi(n+2h) - \Phi(n))\) over the overlap,
\(\Phi\) is the Step-2 linearized phase, and \(T_0 \le P\). The exact
rewrite \(m(n{+}2h)(n{+}2h)^{3/4} - m(n) n^{3/4} = g(n)(n{+}2h)^{3/4}
+ m(n)\,[(n{+}2h)^{3/4} - n^{3/4}]\) with \(m(n) = n^{3/2} - \theta_n\)
gives

\[
\Phi(n{+}2h) - \Phi(n) = A_h(n) +
\tfrac{3j}4\, g(n)\,(n{+}2h)^{3/4} + O(jhP^{-1/4}),
\]

where \(A_h\) is smooth (it collects the \(i\)-difference, the
\(-\tfrac j4\Delta(n^{9/4})\) term, and \(\tfrac{3j}4 n^{3/2}
\Delta(n^{3/4})\)), and the error is exactly the
\(-\tfrac{3j}4\theta_n[(n{+}2h)^{3/4} - n^{3/4}]\) term, of amplitude
\(\le \tfrac{9jh}8 P^{-1/4}\). Cumulative error cost
\(\ll jhP^{3/4} \le P^{7/8}\), and \(\tfrac PH\sum_h jhP^{3/4} \ll
jHP^{7/4} \le P^{15/8+1/24} \ll P^{23/12}\).

A cancellation makes the smooth part harmless: the two
\(n^{5/4}\)-scale contributions of \(A_h\) cancel at leading order.
In integral form \(A_h^{(5/4)} = \tfrac{9j}{16}\int_0^{2h}
(n+t)^{-1/4}[n^{3/2} - (n+t)^{3/2}]\,dt\), and the second
\(n\)-derivative of the integrand vanishes identically at \(t = 0\),
leaving \(A_h'' = \tfrac{81}{256}\,j h^2 n^{-7/4}(1 + o(1))\) plus the
\(i\)-part \(O(ihP^{-3/2})\), both \(o(jhP^{-3/4})\) in our ranges.
(The constant \(81/256 = 0.31640625\) is confirmed by the exact
scaled second-difference validator `smooth_cancellation_check`, which
returns \(0.3164\) across \(n = 10^4\) to \(10^8\) and
\(h \in \{1, 3, 10\}\).)

**Step 4 (cells).** Split \(T_h\) over the \(O(hP^{1/2})\) cells of
Lemma B. On a cell, \(g = G + \kappa\) with \(G\) constant,
\(G \asymp hP^{1/2}\), and \(\kappa(n) = [\{n^{3/2}\} \ge \rho(n)]\)
with \(\rho = 1 - \{\delta(n)\}\) smooth and monotone on the cell.
Vaaler-expand \(\kappa\) with modes \(e(r n^{3/2})\), \(0 < |r| \le
R\). The moving endpoint costs nothing: the coefficient
\(c_r(\rho(n))\) is a linear combination of \(1\) and \(e(-r\rho(n))\)
with weights \(O(1/|r|)\), and since \(\rho(n) = 1 + G - \delta(n)\),
the second piece contributes the *exact* smooth phase
\(r\delta(n)\); combined with the mode, \(e(rn^{3/2} + r\delta(n)) =
e(r(n{+}2h)^{3/2})\) up to a unimodular constant. So every
\(r\)-term falls into one of two smooth phase families,
\(e(rn^{3/2})\) or \(e(r(n{+}2h)^{3/2})\), and no partial summation
over coefficient variation is needed. The main term \(1 - \rho(n) = \delta(n) - G\) has total
variation exactly \(1\) per cell and is absorbed by one Abel
summation. The Vaaler majorant error has total mass \(O(\ell/R)\) per
cell plus mode sums of the same two families with weights
\(O(1/R)\).

**Step 5 (second-derivative test per cell).** The remaining phases are
smooth. For the \(r = 0\) parts, \(f'' = -\tfrac{9j(G+c)}{64}
(n{+}2h)^{-5/4}(1 + o(1))\), single sign, \(|f''| \asymp \lambda_0 =
jhP^{-3/4}\), and the ratio of \(f''\) across a cell is bounded (cell
length \(\ll P^{1/2} \ll P\)). Van der Corput II on a cell of length
\(\ell \asymp P^{1/2}/h\) gives \(\ll \ell\lambda_0^{1/2} +
\lambda_0^{-1/2}\); over all cells:

\[
\ll (jh)^{1/2} P^{5/8} + j^{-1/2} h^{1/2} P^{7/8}.
\]

For \(r \ne 0\), \(f''\) is dominated by the \(r\)-term
\(\asymp |r| P^{-1/2}\) of fixed sign (since \(jh \le P^{1/8} \ll
P^{1/4}\)); the same test and the \(1/|r|\) weights give
\(\ll R^{1/2}P^{3/4} + hP^{3/4}\log P \ll P^{7/8} + hP^{3/4}\log P\).
Majorant errors contribute \(O(P/R) = O(P^{3/4})\).

Total: \(|T_h| \ll P^{7/8}(1 + h^{1/2})\) uniformly in
\(|i| \le 2J_1\), \(1 \le |j| \le 2J_2\).

**Step 6 (assembly).** \(|S_{\mu,\nu}|^2 \ll P^2/H + P^{15/8} H^{1/2}
\ll P^{23/12}\) at \(H = P^{1/12}\), so \(|S_{\mu,\nu}| \ll
P^{23/24}\). Summing wave modes (\(\log^2\)), majorants, and dyadic
blocks (\(\log\)) gives the theorem with \(N^{23/24}\log^3 N\).
\(\square\)

### Review record (Phase 2)

Adversarial re-derivation of every step, at the rigor level applied to
Theorem 5.1. Checks performed and their outcomes:

- **Lemma A remainder**: re-derived with Lagrange form; the validator's
  worst ratio \(0.7494\) matches the theoretical supremum \(3/4\).
- **Smooth cancellation**: the second \(n\)-derivative of the
  \(A_h\)-integrand vanishes identically at \(t = 0\) (symbolic
  check), giving \(A_h'' = \tfrac{81}{256} jh^2 n^{-7/4}(1+o(1))\);
  the exact scaled validator returns \(0.3164 = 81/256\) across four
  decades of \(n\), confirming both the exponent and the constant.
- **Second-derivative dominance**: \(r\)-modes dominate the cell
  phases at scale \(|r|P^{-1/2}\) versus \(jhP^{-3/4}\) since
  \(jh \le P^{1/8} \ll P^{1/4}\); the \(i\)-part is smaller by
  \(P^{-3/4}\); \(f''\) ratio per cell is bounded, so the van der
  Corput II constant is absolute (Graham–Kolesnik Thm 2.2).
- **Moving Vaaler endpoint**: repaired — the coefficient
  \(n\)-dependence splits exactly into the two smooth families
  \(e(rn^{3/2})\), \(e(r(n{+}2h)^{3/2})\); no smooth-weight partial
  summation remains except one Abel summation on \(\delta - G\)
  (variation exactly 1).
- **Majorant products**: \(\Delta_1\Delta_2\)-terms are degree-\(2J\)
  nonnegative trigonometric polynomials with the same treatment;
  statement generalized to mode coefficients in \(\tfrac12\mathbb Z\).
- **Aggregation**: \(P^2/H + PH^{1/2}P^{7/8}\) balances at
  \(H = P^{1/12}\) to \(P^{23/12}\); all error channels
  (\(jP^{5/4}\), \(jHP^{7/4} \le P^{15/8+1/24}\), majorant
  \(P^{23/24}\)-terms) stay below budget.

No step failed. Exponent \(23/24\) deliberately unoptimized (slack at
every stage). Ledger row `J-nested-parity-discrepancy`; the module
flag `depth2_analytic_lemma_proved` is `True` as of this review.

Float sanity (not a verdict): \(|S_{0,1}(P)|/\#\{n\} =
0.0216,\ 0.0027,\ 0.0018\) at \(P = 10^4, 10^5, 10^6\) — cancellation
far stronger than \(P^{-1/24}\), consistent with the census envelope
exponent \(0.28\).

## Part II: the depth-4 extension

Throughout Part II, additionally \(v = v(n) = \lfloor m^{3/2}\rfloor
= \operatorname{isqrt}(m^3)\), \(Y = m^{3/2}\), \(\theta_2 = \{m^{3/2}\}
= Y - v\). For an odd start with \(m\) odd, \(J^2(n) = v\); if
moreover \(v\) is even, \(J^3(n) = \lfloor v^{1/2}\rfloor\). The three
sign functions are \(\psi_1 = \psi(n^{3/2}) = (-1)^m\),
\(\psi_2 = \psi(m^{3/2}) = (-1)^v\), and \(\psi_3 = \psi(v^{1/2}) =
(-1)^{\lfloor\sqrt v\rfloor}\), each evaluated unconditionally (no
branch condition).

**Branch consistency.** The OOEE class is exactly \(\{n \text{ odd}:
\psi_1 = -1,\ \psi_2 = +1,\ \psi_3 = +1\}\): the factor
\((1+\psi_2)/2\) in the indicator algebra vanishes precisely when
\(v\) is odd, i.e. exactly where \(J^3\) would take the odd branch, so
the unconditional \(\psi_3\) is only ever weighted on the even branch,
where it computes the true fourth letter. Exact check
(`ooee_indicator_identity_check`): `itinerary_word(n,4) == "OOEE"` iff
\((\psi_1,\psi_2,\psi_3) = (-1,+1,+1)\) for all odd \(n \le 20001\).

### Lemma D (fourth-letter linearization) — EXACT — HUMAN PROOF

For every odd \(n \ge 3\),

\[
v^{1/2} \;=\; n^{9/8} \;+\; D(n),
\qquad
-\tfrac34\, n^{-3/8} - n^{-9/8} \;\le\; D(n) \;\le\; 0 .
\]

More precisely \(D(n) = -\tfrac34\theta\, n^{-3/8}
- \tfrac12\theta_2\, m^{-3/4} - E_3(n) - E_2(n)\) with
\(0 \le E_3 \le \tfrac3{32}(X-1)^{-5/4}\) and
\(0 \le E_2 \le \tfrac18 (Y-1)^{-3/2}\).

*Proof.* Two applications of the Lemma A pattern. First, with
\(f(t) = (Y-t)^{1/2}\) on \([0,\theta_2]\), Taylor with Lagrange
remainder gives \(v^{1/2} = Y^{1/2} - \tfrac12\theta_2 Y^{-1/2} -
E_2\), \(E_2 = \tfrac18(Y-\xi)^{-3/2}\theta_2^2 \in [0,
\tfrac18(Y-1)^{-3/2}]\), and \(Y^{1/2} = m^{3/4}\),
\(Y^{-1/2} = m^{-3/4}\). Second, with \(f(t) = (X-t)^{3/4}\) on
\([0,\theta]\): \(m^{3/4} = X^{3/4} - \tfrac34\theta X^{-1/4} - E_3\),
\(E_3 = \tfrac3{32}(X-\xi')^{-5/4}\theta^2 \in [0,
\tfrac3{32}(X-1)^{-5/4}]\), and \(X^{3/4} = n^{9/8}\),
\(\theta X^{-1/4} = \theta n^{-3/8}\). Combine; every term is
nonnegative, and \(\tfrac12 m^{-3/4} + E_3 + E_2 \le n^{-9/8}\) for
\(n \ge 3\) (the three subdominant amplitudes are \(\asymp
\tfrac12 n^{-9/8}, n^{-15/8}, n^{-27/8}\)). \(\square\)

The decisive feature: unlike the depth-2 layer, *every* non-smooth
term now has decaying amplitude. The cumulative phase cost of
replacing \(\tfrac k2 v^{1/2}\) by the smooth \(\tfrac k2 n^{9/8}\)
over a dyadic block \(n \sim P\) is
\(\ll k \sum_{n \sim P} n^{-3/8} \ll k P^{5/8}\), which for
\(k \le P^{1/24}\) is \(\ll P^{2/3}\), negligible against the target
\(P^{23/24}\). Exact validation (`fourth_letter_scan`, scaled-integer
arithmetic at \(10^{30}\)): the two-sided bound holds on all odd
\(n \le 4001\) and at \(n = 10^6{+}1, 10^7{+}3, 10^9{+}1,
10^{12}{+}1\), worst ratio \(|D|/\text{bound} = 0.9970\), consistent
with the supremum \(1\) approached as \(\theta \to 1^-\).

### Theorem E (triple parity discrepancy) — EXACT — HUMAN PROOF

For every \(\varepsilon > 0\) and every
\((a,b,c) \in \{0,1\}^3 \setminus \{(0,0,0)\}\),

\[
\Bigl|\sum_{n \le N,\ n \text{ odd}}
\psi(n^{3/2})^{a}\,\psi(m^{3/2})^{b}\,\psi(v^{1/2})^{c}\Bigr|
\;\ll_\varepsilon\; N^{23/24+\varepsilon}.
\]

Consequently each of the eight sign classes of
\((\psi_1, \psi_2, \psi_3)\) on odd \(n \le N\) has cardinality
\(\tfrac N{16} + O(N^{23/24+\varepsilon})\).

*Proof.* The \(c = 0\) cases are Theorem C and Theorem 5.1. For
\(c = 1\), wave-expand all present sign factors as in Step 1 of
Theorem C (Vaaler modes and majorants; mode coefficients
\(\mu, \nu, \rho \in \tfrac12\mathbb Z\), truncations
\(J_1 = J_2 = J_3 = P^{1/24}\); double and triple majorant products
are again nonnegative trigonometric polynomials whose mode sums fall
into the same families). Writing \(i = 2\mu\), \(j = 2\nu\),
\(k = 2\rho\), it suffices to bound, uniformly for \(|i| \le 2J_1\),
\(|j| \le 2J_2\), \(1 \le |k| \le 2J_3\),

\[
S_{i,j,k}(P) = \sum_{n \in (P,2P],\ n \text{ odd}}
e\bigl(\tfrac i2 n^{3/2} + \tfrac j2 m^{3/2} + \tfrac k2 v^{1/2}\bigr).
\]

**Smoothing the fourth letter.** By Lemma D, replacing
\(\tfrac k2 v^{1/2}\) by \(\tfrac k2 n^{9/8}\) changes \(S_{i,j,k}\)
by at most \(2\pi\tfrac{|k|}2 \sum_{n \sim P}\bigl(\tfrac34 n^{-3/8}
+ n^{-9/8}\bigr) \ll |k| P^{5/8} \le P^{2/3}\).

**Case \(j = 0\) (pure fourth-letter modes).** The remaining sum is a
single smooth exponential sum with phase \(\varphi(n) = \tfrac i2
n^{3/2} + \tfrac k2 n^{9/8}\) (the odd-\(n\) restriction adds only a
linear phase \(n/2\), invisible to derivative tests). Both curvature
terms are positive for \(i, k > 0\):
\(\varphi'' = \tfrac{3i}8 n^{-1/2} + \tfrac{9k}{128} n^{-7/8}\)
(conjugate for negative modes; for mixed signs with \(|i| \ge 1\) the
first term dominates the second by \(\gg P^{3/8 - 1/24}\), so the sign
is still fixed). Van der Corput II on the block: for \(i = 0\),
\(\lambda \asymp |k| P^{-7/8}\) gives \(\ll |k|^{1/2} P^{9/16} +
|k|^{-1/2} P^{7/16} \ll P^{5/8}\); for \(|i| \ge 1\),
\(\lambda \asymp |i| P^{-1/2}\) gives \(\ll |i|^{1/2} P^{3/4} +
P^{1/4} \ll P^{3/4 + 1/48}\). Both are \(\ll P^{23/24}\).

**Case \(j \ne 0\) (mixed modes).** After the smoothing step the
phase is exactly the Theorem C phase plus the smooth passenger
\(\tfrac k2 n^{9/8}\). Run Steps 2–6 of Theorem C verbatim; the
passenger only modifies the smooth part \(A_h\) of the differenced
phase by \(\tfrac k2[(n{+}2h)^{9/8} - n^{9/8}]\), whose second
derivative is \(\ll |k| h P^{-15/8}\) — smaller than the retained cell
curvature \(jhP^{-3/4}\) by \(P^{-9/8}|k/j| \ll 1\) and than the
\(r\)-mode curvature \(|r|P^{-1/2}\) by more. Every sign-dominance
and ratio check of Theorem C holds with these margins, so
\(|S_{i,j,k}| \ll P^{23/24}\) uniformly.

Summing mode weights (\(O(\log^3 P)\)), majorant families, and dyadic
blocks gives the theorem. \(\square\)

### Corollary F (four-step descent density 13/16) — EXACT — HUMAN PROOF

\[
\#\{n \le N: n \text{ odd},\ \text{itinerary } OOEE\}
= \tfrac N{16} + O(N^{23/24+\varepsilon}),
\]

and the class of starts with a certified descent within four steps —
evens (one step), \(OE\) (two steps), \(OOEE\) (four steps) — has
cardinality

\[
\tfrac N2 + \tfrac N4 + \tfrac N{16} + O(N^{23/24+\varepsilon})
= \tfrac{13N}{16} + O(N^{23/24+\varepsilon}).
\]

*Proof.* By branch consistency,
\(\#OOEE = \tfrac18\sum_{n \le N \text{ odd}}
(1-\psi_1)(1+\psi_2)(1+\psi_3)\); expanding gives the main term
\(\tfrac18 \cdot \tfrac N2\) and seven sign sums bounded by
Theorem E. Every \(OOEE\) start descends within four steps by the
power envelope: the itinerary \(OOEE\) has \(3^2 < 2^4\), so the
Lean-verified contraction (`J-power-envelope-contraction`) applies.
The even class and the \(OE\) class carry their existing one- and
two-step certificates (Theorem 5.1 machinery,
`floorPower_odd_even_two_step_lt`). The three classes are disjoint: the
parity of \(n\) separates the evens, and the second letter separates
\(OE\) from \(OOEE\). \(\square\)

Census cross-check: at \(N = 10^7\) the observed OOEE fraction of odd
starts is \(0.125039\) (pinned in `test_two_step_parity.py`),
i.e. \(N/16\) overall, matching the theorem's main term.

### Review record (Phase 3)

Same adversarial standard as the Phase-2 review; the new surface is
small because Theorem C's machinery is reused unchanged.

- **Lemma D remainder chain**: both Taylor steps re-derived with
  Lagrange form; all four terms of \(D(n)\) are nonpositive, so the
  two-sided bound is exact, and the validator's worst ratio
  \(0.9970\) approaches the theoretical supremum \(1\).
- **Cumulative absorption**: the fourth letter is smoothed *before*
  any differencing, at cost \(kP^{5/8}\); no \(\theta\)- or
  \(\theta_2\)-dependence survives into the van der Corput stage.
  This is the structural reason depth 4 is easier than depth 2: the
  amplitude \(n^{-3/8}\) decays, whereas the depth-2 layer carried
  the growing amplitude \(n^{3/4}\) that forced Lemma A.
- **Pure-\(k\) curvature**: \(\varphi'' > 0\) termwise for positive
  modes; for mixed-sign \((i,k)\) the \(i\)-term dominates by
  \(P^{9/24}\)-margins, so van der Corput II applies with an absolute
  constant on each dyadic block.
- **Mixed-mode dominance**: the passenger curvature
  \(|k|hP^{-15/8}\) is checked against *both* retained scales
  (\(jhP^{-3/4}\) cells, \(|r|P^{-1/2}\) modes); margins \(\ge
  P^{9/8}/|k| \ge P^{9/8 - 1/24}\).
- **Branch consistency**: verified exactly on a window
  (`ooee_indicator_identity_check`), and structurally: the
  \((1+\psi_2)\) factor annihilates the odd-\(v\) terms where the
  unconditional \(\psi_3\) would misreport the fourth letter.
- **Float sanity** (not a verdict): \(|S_{0,0,1}(P)|/\#\{n\} =
  0.0002,\ 0.007,\ 0.00001\) at \(P = 10^4, 10^5, 10^6\), well below
  the proven \(P^{-7/16}\)-scale envelope.

No step failed. The exponent \(23/24\) is inherited from Theorem C
and remains deliberately unoptimized.

## Part III: beyond depth 4 — tier structure and the density-one program

Part III is the Phase-4 record: what generalizes for free, what the
exact ceiling of the current machinery is, the proved algebraic
bricks for the next tier, two recorded route obstructions, and the
conditional density-one theorem. The tier-2 discrepancy bound itself
is **not claimed**.

**Layer bookkeeping.** Along an itinerary, the \((t{+}1)\)-th letter is the
parity of \(\lfloor x_t^{3/2}\rfloor\) (odd branch) or
\(\lfloor x_t^{1/2}\rfloor\) (even branch), with \(x_t \asymp
n^{\gamma_t}\), \(\gamma_t = \prod_{s\le t} e_s\), \(e_s \in
\{3/2, 1/2\}\). Linearizing the new floor leaves a non-smooth layer of
amplitude \(\asymp x_t^{e-1}\): **growing** (\(x_t^{1/2} =
n^{\gamma_t/2}\)) on an odd branch, **decaying** (\(x_t^{-1/2}\)) on
an even branch. Parts I–II carry exactly one growing layer (the
\(m^{3/2}\) layer serving letters 2 and 3) plus any number of decaying
ones.

### Proposition I (one-growing-layer ceiling) — EXACT — HUMAN PROOF

Within the machinery of Parts I–II, the certifiable contracting
prefixes are exactly \(E\), \(OE\), and \(OOEE\), and the certified
descent density \(13/16\) of Corollary F is the exact ceiling of the
method. Any further certified density requires a second growing
layer.

*Proof.* An itinerary is contracting at length \(\ell\) with \(o\) odd
letters iff \(3^o < 2^\ell\). The method proves letters at positions
1–3 of any itinerary (one growing layer) and further letters only along
even branches (decaying layers). Hence the analyzable words have all
odd letters at positions \(\le 2\): the contracting minimal ones are
\(E\) (\(3^0 < 2\)), \(OE\) (\(3 < 4\)), and \(OOE^k\) with
\(9 < 2^{k+2}\), minimal at \(k = 2\), i.e. \(OOEE\). Extensions of a
contracting itinerary certify no new starts. Densities: \(\tfrac12 +
\tfrac14 + \tfrac1{16} = \tfrac{13}{16}\). Any other contracting itinerary
has an odd letter at a position \(\ge 3\), whose parity needs the
\(x_t^{3/2}\) layer with growing amplitude \(n^{\gamma_t/2}\) —
a second growing layer. \(\square\)

### Lemma G (second-order exact linearization) — EXACT — HUMAN PROOF

For odd \(n \ge 5\), with \(X = n^{3/2}\), \(m = \lfloor X\rfloor\),
\(\theta = X - m\):

\[
m^{3/4} = \tfrac5{32}n^{9/8} + \tfrac{15}{16}m\,n^{-3/8}
- \tfrac3{32}m^2 n^{-15/8} - R_3,
\qquad 0 \le R_3 \le \tfrac5{128}(X-1)^{-9/4},
\]

\[
m^{9/4} = \tfrac5{32}n^{27/8} - \tfrac9{16}m\,n^{15/8}
+ \tfrac{45}{32}m^2 n^{3/8} + R_4,
\qquad -\tfrac{15}{128}(X-1)^{-3/4} \le R_4 \le 0 .
\]

*Proof.* Taylor to third order with Lagrange remainder for
\(f(t) = (X-t)^{3/4}\) resp. \((X-t)^{9/4}\) at \(t = \theta\), then
the exact substitution \(\theta = X - m\) in **both** the linear and
the quadratic terms. For \(m^{3/4}\): \(f = X^{3/4} -
\tfrac34\theta X^{-1/4} - \tfrac3{32}\theta^2 X^{-5/4} -
\tfrac5{128}\theta^3 (X-\xi)^{-9/4}\); substituting turns the three
polynomial terms into \(\tfrac5{32}X^{3/4} + \tfrac{15}{16}mX^{-1/4}
- \tfrac3{32}m^2X^{-5/4}\) (coefficient check at \(m = X\):
\(\tfrac5{32} + \tfrac{30}{32} - \tfrac3{32} = 1\)). For
\(m^{9/4}\): \(f = X^{9/4} - \tfrac94\theta X^{5/4} +
\tfrac{45}{32}\theta^2 X^{1/4} - \tfrac{15}{128}\theta^3
(X-\xi)^{-3/4}\), and substitution gives the stated form (check:
\(\tfrac5{32} - \tfrac{18}{32} + \tfrac{45}{32} = 1\)). \(\square\)

The novelty over Lemma A: the integer \(m\) now enters
*quadratically* with smooth coefficients, and the remainders decay
(\(n^{-27/8}\) and \(n^{-9/8}\) scales). Exact validation
(`second_order_scan`, scale \(10^{60}\) — needed because the
identities cancel to \(n^{-9/8}\) out of \(n^{27/8}\)-size terms):
all odd \(5 \le n \le 2001\) and \(n = 10^6{+}1, 10^7{+}3, 10^9{+}1,
10^{12}{+}1\).

### Proposition H (polynomial phase for the OOO\* layer) — EXACT — HUMAN PROOF

For odd \(n \ge 5\), with \(v = \lfloor m^{3/2}\rfloor\):

\[
v^{3/2} = -\tfrac5{64}n^{27/8} + \tfrac9{32}m\,n^{15/8}
- \tfrac{45}{64}m^2 n^{3/8} + \tfrac{15}{64}v\,n^{9/8}
+ \tfrac{45}{32}vm\,n^{-3/8} - \tfrac9{64}vm^2 n^{-15/8}
+ \mathrm{err}(n),
\qquad |\mathrm{err}| \le \tfrac34 n^{-9/8}.
\]

*Proof.* Lemma A at \(Y = m^{3/2}\) gives \(v^{3/2} =
\tfrac32 v\,m^{3/4} - \tfrac12 m^{9/4} + E_5\), \(0 \le E_5 \le
\tfrac38(Y-1)^{-1/2}\); insert both Lemma G identities. The error
collects \(E_5 - \tfrac32 vR_3 - \tfrac12 R_4\), bounded by
\((\tfrac38 + \tfrac{15}{256} + \tfrac{15}{256})n^{-9/8}(1+o(1)) <
\tfrac34 n^{-9/8}\) for \(n \ge 5\) (using \(v \le X^{3/2}\), so
\(vX^{-9/4} \le X^{-3/4}\)). Coefficient sanity at the nominal point
\((m, v) = (X, X^{3/2})\): \((-5 + 18 - 45 + 15 + 90 - 9)/64 = 1\),
recovering \(v^{3/2} = n^{27/8}\). \(\square\)

So the OOO\* mode phase \(\tfrac k2 v^{3/2}\) is, up to absorbable
errors, a *polynomial of degree \((2,1)\) in the integer pair
\((m, v)\)* with smooth coefficients — the analogue of the linear
structure that made Theorem C possible. Validated exactly through
\(n = 10^{12}\) (`second_order_scan`, identity `v32`). The branch
algebra also mirrors Corollary F exactly: `itinerary_word(n,4) ==
"OOOE"` iff \(((-1)^m, (-1)^v, (-1)^{\lfloor v^{3/2}\rfloor}) =
(-1, -1, +1)\), machine-checked (`ooo_indicator_identity_check`);
the \((1-\psi_2)\) factor vanishes exactly where \(J^3\) would take
the even branch.

### Two route obstructions (negative knowledge)

**Composed cells fail.** On a Lemma-B cell (where \(g_1 = m(n{+}2h) -
m(n)\) is constant) the second-level gap \(g_2 = v(n{+}2h) - v(n)\)
takes a new value at essentially every point: \(\Delta Y =
(m{+}G)^{3/2} - m^{3/2}\) varies by \(\asymp h P^{3/4}\) across the
cell, so the sub-cells of constant \(g_2\) have sub-unit length.
Validated (`second_gap_collision_check` at \(n \sim 10^6\),
\(h \in \{1,3\}\)): distinct-value ratio \(1.0000\). The naive
two-level composition of Lemma B is dead; do not retry it.

**The fiber transform loses to sparsity.** Reindexing by \(m\) (each
\(m\) has at most one odd \(n\)-preimage, present iff
\(\lceil m^{2/3}\rceil < (m{+}1)^{2/3}\) with the right parity)
strips one nesting level: \(\psi_1\) becomes the *linear* phase
\((-1)^m\), \(\psi_2\) a single-layer and \(\psi_4\) a double-layer
(Theorem-C shaped) object in \(m\). But the fiber indicator has
density \(\asymp \tfrac23 m^{-1/3}\) on the range \(Q = N^{3/2}\):
its sawtooth part produces full-length mode sums
\(\sum_m e(rm^{2/3} + \cdots)\) that must beat the sparsity exponent
\(1/3\), while the engine saves only \(1/24\); already the \(r = 1\)
mode is fatal (van der Corput II gives exactly \(Q^{2/3}\), the
trivial target, with zero margin). Route parked, recorded.

### The viable route (program, not a claim)

Difference the Proposition-H polynomial phase once in \(n\)
(A-process, Lemma-B cells): the quadratic terms leave \(\theta\)- and
\(m\)-linear structures with coefficients of size \(\asymp
khn^{7/8}\) — genuinely growing sawtooth amplitudes, unlike Part I
where they decayed. These require shifted-window Vaaler expansions
(modes concentrated near the amplitude), after which the phases are
\(rn^{3/2}\)-type with \(r \lesssim khP^{7/8}\); third-derivative
tests give per-mode savings \(\asymp P^{5/48}\), and a second
differencing handles the \(g_2\)-content via the *smooth-in-\(m\)*
expansion \(e(r'[(m{+}G)^{3/2} - m^{3/2}])\), which linearizes by
Lemma A again. Expected outcome: the OOO\* discrepancy at
\(O(N^{1-\delta_2})\) with \(\delta_2\) of order \(10^{-2}\). Status:
**CONJECTURE** (route sketch with proved bricks; the float sanity
\(|S_{v^{3/2}}|/\#\{n\} = 0.009, 0.003, 0.001\) at \(P = 10^4, 10^5,
10^6\) shows the target sum cancels strongly).

### Proposition J (equidistribution implies density-one descent) — EXACT — HUMAN PROOF

Let \(d \ge 1\) and suppose that for every itinerary word \(w\) of
length \(d\) (over all starts, first letter = parity of \(n\)),

\[
\bigl|\#\{n \le N : \mathrm{word}_d(n) = w\} - 2^{-d}N\bigr|
\;\le\; E_d(N).
\]

Let \(N_d\) be the number of length-\(d\) words with no contracting
prefix. Then the starts with **no** contracting prefix of length
\(\le d\) number at most

\[
\frac{N_d}{2^{d}}\,N \;+\; N_d\,E_d(N),
\qquad
N_d \;\le\; 2^{d}e^{-cd},
\qquad
c \;=\; 2\Bigl(\tfrac{\log 2}{\log 3} - \tfrac12\Bigr)^2
\;>\; 0.0342 .
\]

Every other start \(n \ge 2\) satisfies \(T^t(n) < n\) for some
\(t \le d\) with a uniform power-envelope certificate
(`J-power-envelope-contraction`). Consequently, if \(E_d(N) =
O_d(N^{1-\delta_d})\) with \(\delta_d > 0\) for every \(d\), the set
of starts admitting a finite descent certificate has natural density
\(1\).

*Proof.* An itinerary \(w\) of length \(d\) has a contracting prefix iff
\(3^{o_t} < 2^t\) for some \(t \le d\), where \(o_t\) counts odd
letters among the first \(t\). So the words to be counted are those
whose lattice path \((t, o_t)\) satisfies \(3^{o_t} \ge 2^{t}\)
throughout, a condition depending on nothing but \((t, o_t)\); hence
\(N_d\) is a dynamic program over the triangle \(0 \le o \le t \le d\),
exact in integers. Each word class has at most \(2^{-d}N + E_d(N)\)
members; summing over the \(N_d\) non-contracting itineraries gives the
count. The density-one statement follows by letting \(d \to \infty\)
slowly with \(N\) (e.g. any \(d(N) \to \infty\) with
\(N_dE_d(N)/N \to 0\)). \(\square\)

*The closed form, and what it costs.* Keep only \(t = d\): then \(3^{o_d} \ge 2^d\),
i.e. \(o_d \ge \beta d\) with \(\beta = \log 2/\log 3 = 0.6309\ldots\),
and the number of such words is
\(2^d\,\Pr[\mathrm{Bin}(d, \tfrac12) \ge \beta d] \le 2^d
e^{-2(\beta - 1/2)^2 d}\) by Hoeffding. The two words *in particular*
are where the sharpness goes: dropping the prefix constraint costs a
factor \(1.5\) at \(d = 5\) and \(4.4\) at \(d = 24\), and the
exponential form costs the rest, for \(6.7\) at \(d = 5\) and \(43.6\)
at \(d = 40\). Neither loss is in the rate --- the sharp value is
\(-\log\rho = 0.034688\) against Hoeffding's \(0.034285\) --- but in a
polynomial factor, \(N_d/2^d \sim C\rho^{d}d^{-3/2}\) with
\(C \approx 11\). See Paper B Proposition 7.1 and
`paper_b_prefix_count.py`.

This is the Juggler analogue of the Terras program for Collatz:
all-depth parity equidistribution (Conjecture K below) implies that
almost every start descends below itself. The implication is
unconditional; only the hypothesis is open beyond the proved cases
(\(d \le 3\) fully — Theorems 5.1/C plus Proposition L of Part IV,
which closed a gap in an earlier phrasing of this remark; at
\(d = 4\), every itinerary except OOO\* via Theorems E and Q of Part V).

### Census gate at depth 6 — COMPUTATIONALLY VERIFIED

Exact census of all 32 depth-6 words on odd \(n \le 2\cdot10^6\):
every itinerary is realized, and the deviations obey the two-regime
minimal-scale envelope

\[
|D_w| \;\le\; C\,\max\bigl((N/2)\,N^{-\gamma_{\min}(w)},\
N^{2/3}\bigr),
\qquad
\gamma_{\min}(w) = \min_t \gamma_t,
\]

with \(C = 0.61\) (and \(C = 0.40, 1.02\) at \(N = 10^5, 5\cdot
10^5\)). E-heavy words (e.g. \(OEEEE\ast\), whose deepest value is
\(\asymp N^{3/32} \approx 4\)) are boundary-dominated and *cannot*
look equidistributed at feasible \(N\); words whose scales stay
\(\ge N^{3/8}\) deviate by \(\le 14\%\) of their expectation. No
structural bias beyond the boundary effect. This also predicts the
word-dependent exponents any proof must produce: \(\delta_w\)
degrades as \(\gamma_{\min}(w)\) shrinks.

### Conjecture K (all-depth equidistribution)

For every fixed itinerary word \(w\): \(\#\{n \le N:
\mathrm{word}(n) \text{ has prefix } w\} = 2^{-|w|}N +
O(N^{1-\delta_w})\), \(\delta_w > 0\). Proved for \(|w| \le 3\)
(Theorems 5.1/C, Proposition L) and for every itinerary at \(|w| = 4\)
except OOO\* (Theorems E and Q). With Proposition J this implies
density-one finite descent. The only remaining depth-4 case is
tier 2, the OOO\* split, whose precise obstruction — the kernel
\(K_c\) — is isolated in Part IV.

Import of Theorems C/E and Corollary F into the finite-dynamics note
is done (note Theorems 5.4/5.7, Corollary 5.9; consolidation phase).

## Part IV: depth-3 completion and the tier-2 kernel (Phase 5)

### Correction note

Earlier phrasings of the Proposition J remark and Conjecture K said
"proved for depth \(\le 3\)". That was ahead of the facts: Theorem C
proves the depth-3 split only on the OO branch (third letter = parity
of \(\lfloor m^{3/2}\rfloor\), weighted on odd \(m\)), and Theorem E
proves *sign classes* of \((\psi_1, \psi_2, \psi_3)\), which are word
classes only along OOE\*. The OE-branch third letter — the OEO/OEE
split, governed by \(\psi(m^{1/2})\) on even \(m\) — had not been
stated or proved. Proposition L below closes it; the remark and
Conjecture K are now accurate as written.

### Proposition L (OE-branch third letter) — EXACT — HUMAN PROOF

For \(a \in \{0,1\}\),

\[
\Bigl|\sum_{n \le N,\ n \ \mathrm{odd}} \bigl((-1)^m\bigr)^a\,
\psi\bigl(m^{1/2}\bigr)\Bigr| \;\ll_\varepsilon\; N^{7/8+\varepsilon},
\qquad m = \lfloor n^{3/2}\rfloor,
\]

and consequently \(\#\mathrm{OEO}(N),\ \#\mathrm{OEE}(N) = N/8 +
O(N^{7/8+\varepsilon})\).

*Proof.* Exact smoothing (validated, `m12_smoothing_check`, \(n\) to
\(10^{12}\)): with \(X = n^{3/2}\), \(\theta = X - m\),

\[
m^{1/2} = n^{3/4} + D_1(n),
\qquad
-\tfrac12 X^{-1/2} - \tfrac18 (X-1)^{-3/2} \;\le\; D_1 \;\le\; 0,
\]

the Taylor expansion of \((X-\theta)^{1/2}\) with both correction
terms one-signed. \(D_1\) is *decaying*, so replacing
\(\tfrac l2 m^{1/2}\) by \(\tfrac l2 n^{3/4}\) inside a Vaaler mode
costs \(\ll l \sum_{n \sim P} n^{-3/4} \ll l P^{1/4}\), absorbable at
\(l \le 2J = 2P^{1/24}\). The mode sums are then pure:
\(\sum_{n \sim P} e\bigl(\tfrac i2 n^{3/2} + \tfrac l2 n^{3/4}\bigr)\)
with \(l \ne 0\). For \(i \ne 0\): \(\varphi'' = \tfrac{3i}{8}
n^{-1/2}\bigl(1 + O(l P^{-3/4}/i)\bigr)\) is single-signed and
\(\asymp |i| P^{-1/2}\), so van der Corput II gives \(\ll i^{1/2}
P^{3/4} + i^{-1/2} P^{1/4}\). For \(i = 0\): \(\varphi'' \asymp
l P^{-5/4}\), giving \(\ll l^{1/2} P^{3/8} + l^{-1/2} P^{5/8}\). The
odd-\(n\) restriction, Vaaler majorants, truncation tails, and dyadic
assembly are verbatim from Theorem C, and every bound is
\(\ll P^{7/8}\) after summing mode weights. Branch consistency: the
\((1 + (-1)^m)/2\) factor vanishes exactly on odd \(m\), where
\(J^2\) would take the \(3/2\)-power branch, so the unconditional
\(\psi(m^{1/2})\) is only ever weighted where it computes the true
third letter — machine-checked (`oe_indicator_identity_check`,
`itinerary_word(n,3) == "OEE"` iff \(m\) and
\(\lfloor\sqrt m\rfloor\) even, all odd \(n \le 20001\)).
\(\square\)

Depth 3 is now complete: OOO, OOE (Theorem C), OEO, OEE
(Proposition L), each \(N/8 + O(N^{1-\delta})\).

### Lemma M (second-order forms, plain and shifted) — EXACT — HUMAN PROOF

Let \(n \ge 5\) be odd, \(X = n^{3/2}\), \(m = \lfloor X\rfloor\),
\(\theta = X - m\), \(G \ge 0\) an integer, \(Z = X + G\). Then

\[
m^{3/2} = -\tfrac18 X^{3/2} + \tfrac34 m X^{1/2}
+ \tfrac38 m^2 X^{-1/2} + R_5,
\qquad 0 \le R_5 \le \tfrac1{16}(X-1)^{-3/2},
\]

\[
(m+G)^{3/2} = Z^{3/2} - \tfrac32 X Z^{1/2} + \tfrac38 X^2 Z^{-1/2}
+ m\bigl(\tfrac32 Z^{1/2} - \tfrac34 X Z^{-1/2}\bigr)
+ \tfrac38 m^2 Z^{-1/2} + R_6,
\]

with \(0 \le R_6 \le \tfrac1{16}(Z-1)^{-3/2}\).

*Proof.* Both are the second-order Taylor expansion of \(t \mapsto
(B - t)^{3/2}\) at \(t = 0\) (base \(B = X\) resp. \(Z\)) evaluated at
\(t = \theta\), with \(\theta = X - m\) substituted *exactly* so that
\(\theta\) and \(\theta^2\) become polynomials in \(m\) with smooth
coefficients. The remainder \(\tfrac16 f'''(\xi)\theta^3 =
\tfrac1{16}(B-\xi)^{-3/2}\theta^3\), \(\xi \in (0, \theta)\), is
positive since \(f''' > 0\), and at most \(\tfrac1{16}(B-1)^{-3/2}\).
Coefficient sanity at \(m = X\), \(G = 0\): \(-\tfrac18 + \tfrac34 +
\tfrac38 = 1\). Validated exactly (`lemma_m_scan`) for \(n\) up to
\(10^{12}\) with realized gaps \(G = m(n{+}2h) - m(n)\), \(h \in
\{1, 2, 5\}\); the observed defect at \(n = 5\) is \(9.87\cdot
10^{-6}\), matching \(\theta^3 X^{-3/2}/16 = 0.98\cdot10^{-5}\).
\(\square\)

The point of the shifted form: on a Lemma-B cell (constant
\(g_1 = G\)) the level-2 increment \(\Delta Y = (m{+}G)^{3/2} -
m^{3/2}\) becomes a quadratic in \(m\) with smooth coefficients and
remainder \(\ll P^{-9/4}\) — absorbable even against the tier-2
weight \(W \asymp k P^{9/8}\).

### Lemma N (level-2 gap identity) — EXACT — HUMAN PROOF

With \(Y = m^{3/2}\), \(v = \lfloor Y\rfloor\), \(\theta_2 =
\{Y\}\), and \(Y_+ = Y(n + 2h)\), \(\Delta Y = Y_+ - Y \ge 0\):

\[
g_2 \;=\; v(n{+}2h) - v(n)
\;=\; \lfloor \Delta Y \rfloor + \kappa_2,
\qquad
\kappa_2 = \mathbb 1\bigl[\theta_2 \ge 1 - \{\Delta Y\}\bigr]
\in \{0, 1\}.
\]

*Proof.* Identical to Lemma B with \(X \to Y\), \(\delta \to \Delta
Y\): \(\lfloor Y + \Delta Y\rfloor = \lfloor Y\rfloor + \lfloor
\Delta Y\rfloor + \lfloor \{Y\} + \{\Delta Y\}\rfloor\), and the last
floor is the stated indicator. \(\square\) Validated on realized
orbit data (`level2_gap_check`): 800/800 at \(n \sim 10^6\) for
\(h \in \{1, 3\}\), 2995 matches and 5 guard-band skips on a wide
window at \(n \sim 10^3\).

### The kernel isolation (negative knowledge with an exact core)

Differencing the Proposition-H polynomial phase (A-process, step
\(2h\)) splits the \(v\)-block exactly as \(\Delta(vW) = g_2 W_+ +
v\,\Delta W\), where \(W = \partial\Phi_3/\partial v \asymp
\tfrac{3k}4 n^{9/8}\) is the smooth \(v\)-weight.

- \(v\,\Delta W\) is *tame*: \(\Delta W \asymp khP^{1/8}\), and the
  shifted-window Vaaler expansion of its \(\theta_2\)-content has
  window drift \(< 1\) per cell (\(\Delta W\) varies by \(\asymp
  kP^{-3/8}\) across a cell), so its mode mass is logarithmic.
- \(g_2 W_+\) is *the wall*. The exact no-floor form \(g_2 = \Delta Y
  + \theta_2 - \theta_2^+\) leaves \(\Delta Y\,W_+\) (quadratic in
  \(m\) by Lemma M — handled) plus \((\theta_2 - \theta_2^+)W_+\): a
  unit-amplitude sawtooth times a smooth coefficient of size \(\asymp
  kP^{9/8}\) whose derivative \(\asymp kP^{1/8} \gg 1\) crosses
  integers *within single steps of \(n\)*, so no cell of any usable
  length freezes its Fourier window.

Every reorganization tried funnels into the same object:
splitting \(g_2\) by Lemma N instead leaves \(\{\Delta Y\}\,W_+\)
(window drift \(kP^{5/8}/h\) per cell — same wall); the exact swap
\(e(c\,\theta_2) = e(cY)\,e(-\{c\}v)\) (valid because
\(\lfloor c\rfloor v\) is an integer) trades it for the fast sawtooth
\(\{c(n)\}\) times the huge integer \(v \asymp P^{9/4}\) — symmetric
and equally wild; a second A-process transfers the difference either
to \(v\) (reproducing gap terms carrying the *full-size* \(W\)) or to
\(W\) (already exhausted at \(\Delta W\)); and differencing the raw
phase \(\tfrac k2 v^{3/2}\) without Proposition H reproduces
\(c(n)\,g_2\) with \(c \asymp \tfrac{3k}4 v^{1/2}\). By contrast the
\(\kappa_2\)-content is harmless: \(e(\kappa_2 W_+) = 1 +
\kappa_2\,(e(W_+) - 1)\) splits into a 0/1 *indicator weight* —
Vaaler-expandable in \(Y\)-modes with the exact endpoint identity
\(e(r\{\Delta Y\}) = e(r\,\Delta Y)\) for integer \(r\) — times a
factor whose largeness sits harmlessly in the smooth phase.

**Kernel (definition).** For smooth \(c\) with \(c \asymp k P^{9/8}\)
and \(c' \asymp k P^{1/8}\) on \(n \sim P\) (the \(W\)-shaped
family),

\[
K_c(P) \;=\; \sum_{\substack{n \sim P \\ n\ \mathrm{odd}}}
e\bigl(c(n)\,\{\lfloor n^{3/2}\rfloor^{3/2}\}\bigr).
\]

### Conjecture O (kernel cancellation) — *proved: see Theorem R, Part VI*

\(K_c(P) \ll P^{1-\delta}\) for some \(\delta > 0\), uniformly over
the \(W\)-shaped family. Float probe with exact scaled phase
arithmetic (`kernel_probe`, \(c = \tfrac34 n^{9/8}\)): \(|K| = 51.9,\
124.4,\ 1017.5\) on \(5\cdot10^3,\ 5\cdot10^4,\ 5\cdot10^5\) terms —
square-root cancellation. Bounding \(K_c\) was the *precise*
remaining obstacle to the OOO\* split, hence to any depth-4 statement
beyond \(13/16\) through this program. The object is a bilinear
correlation between the fractional parts of one Piatetski–Shapiro
layer and a smooth weight at the scale of the next layer; we found no
treatment of it in the nested-floor literature. Proved in Phases 8–9
with \(\delta = 1/64\) (bounded \(k\)) and \(\delta = 1/72\) for
\(k \le P^{1/24}\): Theorem R.

### Remark (the OEO\* tier is easier — next target)

At depth 4 after OE, the fourth letter on the OEO branch is the
parity of \(\lfloor w^{3/2}\rfloor\) with \(w = \lfloor
m^{1/2}\rfloor \asymp n^{3/4}\). The growing layer here rides the
*slow* variable \(w\), which increments only once every \(\asymp
n^{1/4}\) values of \(n\): its gap variable has long constancy cells,
i.e. the Theorem-C pattern with the roles shifted one level down.
This split (and the easy decaying OEE\* one) looks closable by the
existing engine without meeting the kernel, and would settle depth 4
entirely except OOO\*. *(Done: Part V, Theorem Q.)*

## Part V: the OE\*\* splits — depth 4 complete except OOO\* (Phase 6)

Throughout: \(n\) odd, \(X = n^{3/2}\), \(m = \lfloor X\rfloor\),
\(\theta = X - m\); on the OE branch \(m\) is even and \(J^2(n) = w =
\lfloor U\rfloor\) with \(U = m^{1/2}\), \(\theta_w = U - w\). On the
OEO branch (\(w\) odd) the fourth letter is the parity of \(\lfloor
w^{3/2}\rfloor\); on the OEE branch (\(w\) even), of \(\lfloor
w^{1/2}\rfloor\).

### Lemma A′ (w-level linearization) — EXACT — HUMAN PROOF

For odd \(n \ge 5\):

\[
w^{3/2} \;=\; -\tfrac12 m^{3/4} + \tfrac32 w\, m^{1/4} + E,
\qquad 0 \le E \le \tfrac38 (U-1)^{-1/2},
\]

and since \(U m^{1/4} = m^{3/4}\) *exactly*, equivalently

\[
w^{3/2} \;=\; m^{3/4} \;-\; \tfrac32\, m^{1/4}\,\theta_w \;+\; E .
\]

*Proof.* Lemma A verbatim with base \(U\) in place of \(X\):
\(w^{3/2} = (U - \theta_w)^{3/2} = U^{3/2} - \tfrac32\theta_w U^{1/2}
+ \tfrac38\theta_w^2(U-\xi)^{-1/2}\), substitute \(\theta_w = U - w\)
exactly in the linear term, and note \(U^{3/2} = m^{3/4}\),
\(U^{1/2} = m^{1/4}\). \(\square\) Validated exactly
(`lemma_a_prime_scan`) through \(n = 10^{12}\).

**Corollary (full smoothing).** With \(d_2 = w^{3/2} - n^{9/8} +
\tfrac32 m^{1/4}\theta_w\):

\[
-\tfrac34 n^{-3/8} - \tfrac3{32}(X-1)^{-5/4}
\;\le\; d_2 \;\le\; \tfrac38 (U-1)^{-1/2},
\]

because \(m^{3/4} - X^{3/4} = -\tfrac34\theta X^{-1/4} -
\tfrac3{32}\theta^2(X-\xi')^{-5/4}\) (Taylor of \((X-\theta)^{3/4}\),
both correction terms one-signed) and \(X^{3/4} = n^{9/8}\). All
error terms decay like \(n^{-3/8}\), so for a Vaaler mode \(k\):

\[
\tfrac k2 w^{3/2} \;=\; \tfrac k2 n^{9/8}
\;-\; B(n)\,\theta_w(n) \;+\; O\bigl(k\,n^{-3/8}\bigr),
\qquad
B(n) = \tfrac{3k}4\, m^{1/4} = \tfrac{3k}4 n^{3/8}\bigl(1 +
O(n^{-3/2})\bigr),
\]

with cumulative substitution cost \(O(kP^{5/8})\) on a block
\(n \sim P\). Validated exactly (`oeo_smoothing_scan`) through
\(n = 10^{12}\). *One growing sawtooth remains* — amplitude
\(\asymp k n^{3/8}\) — riding \(\theta_w = \{m^{1/2}\}\), whose
underlying variable increments once every \(\asymp \tfrac43 n^{1/4}\)
steps.

### Theorem Q (the OE\*\* splits) — EXACT — HUMAN PROOF

\[
\#\mathrm{OEOE}(N),\ \#\mathrm{OEOO}(N) = \tfrac N{16} +
O\bigl(N^{7/8+\varepsilon}\bigr),
\qquad
\#\mathrm{OEEE}(N),\ \#\mathrm{OEEO}(N) = \tfrac N{16} +
O\bigl(N^{13/16+\varepsilon}\bigr).
\]

Together with Theorems C/E this proves every depth-4 itinerary word
class except OOO\*.

*Proof.* Indicator algebra: \(\mathrm{OEO}\ast\) is
\(\tfrac18(1+\psi_1)(1-\psi_w)(1\pm\psi(w^{3/2}))\) with \(\psi_1 =
(-1)^m\), \(\psi_w = (-1)^w\); branch-consistent because
\((1+\psi_1)\) vanishes on odd \(m\) (where \(J^2\) takes the odd
branch) and \((1-\psi_w)\) on even \(w\) (where \(J^3\) would take
the even branch) — machine-checked for all four words
(`oeo_indicator_identity_check`). Vaaler-expand the three waves with
truncations \(J_1 = J_2 = J_3 = P^{1/8}\) (majorant errors
\(3P^{7/8}\)); \(\psi_w\)-modes smooth to \(e(\tfrac j2 n^{3/4})\) by
the Proposition L brick. The nontrivial modes are \(k \ne 0\):

**Step 1 (smoothing).** By the Corollary, the mode phase is
\(\varphi_1(n) - B(n)\theta_w(n)\) up to absorbable errors, with
\(\varphi_1 = \tfrac i2 n^{3/2} + \tfrac j2 n^{3/4} + \tfrac k2
n^{9/8}\) and \(B = \tfrac{3k}4 n^{3/8}\) (replacing \(m^{1/4}\) by
\(X^{1/4}\) costs \((3k/16)\theta X^{-3/4}\,\theta_w \ll
kn^{-9/8}\)).

**Step 2 (drift-1 intervals).** \(B' \asymp k n^{-5/8}\), so \(B\)
drifts by at most \(1\) on intervals \(I\) of length \(L_0 =
P^{5/8}/k\); there are \(\asymp k P^{3/8}\) of them. On \(I\), expand
\(e(-B\{U\}) = \sum_r a_r(B)\,e(rU)\) (Fourier in \(U\), Vaaler
truncation \(|r + B| \le T = P^{5/16}\), majorant error \(\ll L_0/T\)
per interval, \(P/T = P^{11/16}\) total). Coefficients:
\(|a_r(B)| \le \min(1, |r+B|^{-1})\), window mass \(O(\log T)\); the
\(n\)-dependence through \(B(n)\) has total variation
\(\sum_r \sup_I |a_r'|\,|B'|\,L_0 \ll \sum_r |r+B|^{-2} = O(1)\),
removed by partial summation once per mode.

**Step 3 (mode sums).** Each mode is \(\sum_{n\in I}
e(\varphi_1(n) + rU(n))\); smoothing \(rU \to r n^{3/4}\) costs
\(\tfrac r2\theta X^{-1/2}\) pointwise, \(\ll |r| P^{-3/4}\cdot L_0
\ll P^{1/4}\) per interval, \(kP^{5/8}\) total. Writing \(r = -B_0 +
t\), \(|t| \le T\):

\[
\varphi'' = \tfrac{27k}{128} n^{-7/8}
- \tfrac3{16}\bigl(t + \tfrac j2\bigr) n^{-5/4}
+ \tfrac{3i}8\, n^{-1/2}.
\]

For \(i \ne 0\) the first-listed scale is dominated: \(\lambda_2
\asymp |i| P^{-1/2}\), single-signed since \(|i|P^{-1/2} \ge
P^{-1/2}\) while the others are \(\le kP^{-7/8} + TP^{-5/4} \ll
P^{-3/4}\); van der Corput II over \(I\) and summation over intervals
give \(\ll i^{1/2}P^{3/4} + i^{-1/2}kP^{5/8}\). For \(i = 0\): the
\(t\)-term satisfies \(|t + j/2|\,P^{-5/4} \le (T + J_2)P^{-5/4} \ll
kP^{-7/8}\) because \(T = P^{5/16} \ll kP^{3/8}\) for every
\(k \ge 1\); hence \(\lambda_2 \asymp k n^{-7/8}\), single-signed.
Van der Corput II per interval: \(L_0\lambda_2^{1/2} +
\lambda_2^{-1/2} \ll k^{-1/2}(P^{3/16} + P^{7/16})\); times
\(kP^{3/8}\) intervals and \(O(\log)\) mode mass:

\[
S_k \;\ll\; k^{1/2} P^{13/16+\varepsilon} .
\]

**Assembly.** With Vaaler weights \(1/k\),
\(\sum_{k\le J_3} \tfrac1k\, k^{1/2} P^{13/16} = J_3^{1/2} P^{13/16}
= P^{7/8}\), balanced against the truncation error \(P/J_3 =
P^{7/8}\) at \(J_3 = P^{1/8}\). The \(i\)- and \(j\)-weighted sums
are smaller (\(\ll P^{3/4+\varepsilon}\)); absorbable inventory:
\(kP^{5/8} \le P^{3/4}\), \(P/T = P^{11/16}\), partial-summation
factors \(O(\log)\). Total \(\ll P^{7/8+\varepsilon}\); dyadic blocks
sum to \(N^{7/8+\varepsilon}\).

**OEE branch.** The fourth letter needs \(\psi(w^{1/2})\):
\(w^{1/2} = (U - \theta_w)^{1/2} = U^{1/2} - \tfrac12\theta_w
U^{-1/2} - \tfrac18\theta_w^2(U-\xi)^{-3/2}\) — *decaying* amplitudes
only, and \(U^{1/2} = m^{1/4} \to n^{3/8}\) likewise. Pure modes
\(e(\tfrac l2 n^{3/8})\): \(\lambda_2 \asymp l P^{-13/8}\), van der
Corput II gives \(l^{1/2}P^{3/16} + l^{-1/2}P^{13/16}\); the mixed
\(i, j\) cases sit in the dominance hierarchy \(iP^{-1/2} \gg
jP^{-5/4} \gg lP^{-13/8}\) with all three second derivatives of the
same sign (no cancellation). Total \(\ll N^{13/16+\varepsilon}\).
\(\square\)

Float sanity (`oeo_mode_probe`, exact scaled phases): \(|S| = 84.8,\
1361.0,\ 6142.3\) on \(5\cdot10^3, 5\cdot10^4, 5\cdot10^5\) terms —
tracking the *coherent-cell random-walk scale* \(P^{5/8}\) (\(1333,\
5623\) predicted at the two larger sizes), far below the proven
\(P^{7/8}\): the phase is constant on each \(w\)-cell of length
\(\asymp \tfrac43 P^{1/4}\), and the \(\asymp P^{3/4}\) cell phases
equidistribute.

### Remark (why the kernel does not appear)

The differencing-free route works because the sawtooth variable
\(\theta_w = \{m^{1/2}\}\) and its coefficient \(B \asymp kn^{3/8}\)
are *both slow*: \(B\) crosses integers every \(\asymp P^{5/8}/k\)
steps, so drift-1 intervals are long enough for the shifted-window
expansion, and the mode frequencies \(r \asymp kP^{3/8}\) keep the
curvature \(rP^{-5/4} \ll\) the main scale. In the OOO\* kernel the
coefficient \(W \asymp kn^{9/8}\) crosses integers *within single
steps* (\(W' \asymp kn^{1/8} \gg 1\)) — no drift-1 interval exists.
The boundary between the two regimes is exactly \(c' \asymp 1\),
i.e. coefficient scale \(n\): itinerary letters whose phase
coefficients grow slower than \(n\) are reachable by this engine;
OOO\* sits above the line.

### Remark (Proposition J needs only O-rooted words)

The itinerary classes in Proposition J range over all starts, but every
E-rooted word has a contracting prefix at length 1 (\(3^0 < 2\)), so
E-rooted classes never enter the exceptional set: the hypothesis only
ever consumes O-rooted class bounds, which are exactly what Theorems
5.1/C/E/L/Q prove. No further gap.

## Part VI: the kernel — a double-differencing attack (Phase 8)

**Status: reviewed.** Drafted in Phase 8 and re-derived
adversarially in Phase 9 (review record after Theorem R). The review
found two defects — one organizational, one a real error in the
draft's Step 5 — and repaired both with the part's own exact
mechanisms; the final exponents are unchanged. Theorem R and its
depth-4 corollary (Theorem S) are `EXACT — HUMAN PROOF`
(ledger rows `J-kernel-cancellation`, `J-depth4-complete`). The
finite-dynamics note is *not* yet updated: its Conjecture 6.2
paragraph is superseded by this part and awaits an editorial
consolidation phase.

Notation: \(n\) odd, \(X = n^{3/2}\), \(m = \lfloor X\rfloor\),
\(\theta = X - m\), \(Y = m^{3/2}\), \(v = \lfloor Y\rfloor\),
\(\theta_2 = Y - v\). Shifts \(d_i = 2h_i\); corner values
\(f_{ab} = f(n + a d_1 + b d_2)\) for \(a, b \in \{0, 1\}\);
\(\Delta_1 f = f_{10} - f_{00}\), \(\Delta_2 f = f_{01} - f_{00}\),
\(\Delta\Delta f = f_{11} - f_{10} - f_{01} + f_{00}\). Gap
variables: \(g_1(n) = m(n{+}d_1) - m(n)\), \(g_2(n) = v(n{+}d_1) -
v(n)\), \(W(n) = \Delta_1 Y(n)\), \(j_1(n) = \Delta_2 g_1(n) =
\Delta\Delta m(n)\).

### Why Phase 5's wall does not block this route

Phase 5 recorded: *"a second A-process transfers the difference
either to \(v\) (reproducing gap terms carrying the full-size \(W\))
or to \(W\) (already exhausted at \(\Delta W\))."* Both recorded
failures difference a **sub-organization** of the OOO\* phase (the
\(vW\)-block of Proposition H). The attack below differences the
**whole kernel phase** \(c\,\theta_2\) twice and only then
decomposes. Three exact mechanisms, none available to the
sub-organized routes, then eliminate every full-size sawtooth
coefficient:

1. **integer annihilation** — whenever an integer-valued quantity
   \(g\) multiplies \(c\), the split \(e(cg) = e(\{c\}g)\) is never
   used; instead \(g\) is reduced (by the exact identities below) to
   *bounded* or *frozen* integers \(J\), and \(e(cJ)\) is a smooth
   phase — no fractional part of \(c\) ever enters;
2. **the level-2 numerology** \(Y'' \asymp P^{1/4} \gg 1 > P^{-3/4}
   \asymp Y'''\): one differencing leaves the level-2 gap content
   unfrozen, but a second freezes it — one extra differencing per
   unit of derivative growth;
3. **the branch split**: the level-1 second gap \(j_1\) is bounded
   and its flicker is carried by indicator weights (Vaaler modes with
   \(O(1)\) coefficients), never by the phase.

### Lemma R1 (kernel reformulation) — EXACT — HUMAN PROOF

For odd \(n \ge 5\),

\[
\tfrac12\bigl(m^{9/4} - v^{3/2}\bigr)
- \tfrac34\, v^{1/2}\theta_2 \;=\; R,
\qquad 0 \le R \le \tfrac3{16}\, v^{-1/2}.
\]

Consequently the central kernel phase \(c\,\theta_2\) with \(c =
\tfrac{3k}4 v^{1/2}\) equals \(\tfrac k2\bigl(Y^{3/2} - \lfloor
Y\rfloor^{3/2}\bigr)\) up to \(kR \ll kP^{-9/8}\): **the kernel is
the exponential sum of the level-2 local floor defect**, the
second-level analog of the note's local remainder calculus. (With
Lemma D, \(v^{1/2} = n^{9/8} + O(n^{-3/8})\), so the \(n^{9/8}\)- and
\(v^{1/2}\)-normalizations of the family differ by an absorbable
phase \(\ll kP^{-3/8}\) pointwise.)

*Proof.* Taylor of \((v + \theta_2)^{3/2}\) at \(v\): \(Y^{3/2} =
v^{3/2} + \tfrac32 v^{1/2}\theta_2 + \tfrac38 (v+\xi)^{-1/2}
\theta_2^2\) with \(\xi \in (0, \theta_2)\), and \(Y^{3/2} =
m^{9/4}\). \(\square\) Validated in exact scaled integers
(`kernel_reformulation_scan`): 1003/1003 odd samples through
\(n = 10^{12}+1\), remainder one-signed in the stated envelope.

### Lemma R2 (double-gap identity) — EXACT — HUMAN PROOF

For all \(n, h_1, h_2\),

\[
\Delta_2 g_2 \;=\; \bigl\lfloor \Delta\Delta Y \bigr\rfloor
+ \kappa''
+ \Delta_2 \kappa_2,
\]

where \(\kappa'' = \mathbb 1\bigl[\{W\} \ge 1 - \{\Delta\Delta
Y\}\bigr]\) and \(\kappa_2 = \mathbb 1\bigl[\theta_2 \ge 1 -
\{W\}\bigr]\) is Lemma N's carry. Every carry is a difference of
unit sawtooths: \(\mathbb 1[\{A\} + \{B\} \ge 1] = \lfloor A +
B\rfloor - \lfloor A\rfloor - \lfloor B\rfloor = \{A\} + \{B\} -
\{A + B\}\).

*Proof.* Lemma N twice: \(g_2 = \lfloor W\rfloor + \kappa_2\), and
the gap identity applied to the real sequence \(n \mapsto W(n)\)
with shift \(d_2\) gives \(\lfloor W_{01}\rfloor - \lfloor
W_{00}\rfloor = \lfloor \Delta_2 W\rfloor + \kappa''\) with
\(\Delta_2 W = \Delta\Delta Y\). The sawtooth form of the carry is
the Lean-verified `floor_add_eq_add_carry` rearranged. \(\square\)
Lean: `seq_floor_gap_second` in `GapCells.lean` (two instances of
`seq_floor_gap` composed). Validated on orbit data
(`double_gap_identity_check`): 400/400 at \(n \sim 10^6\) for
\((h_1, h_2) \in \{(1,1), (1,3), (2,5)\}\), 2980 matches + 20
guard-band skips on a wide window at \(n \sim 10^3\).

### Lemma R3 (branch decomposition and freeze) — EXACT — HUMAN PROOF

*(Restated by the Phase-9 review; see the review record.)* Write
\(b_1 = \lfloor\Delta_1X\rfloor\), \(b_2 = \lfloor\Delta_2X\rfloor\),
\(b_{12} = \lfloor\Delta_{12}X\rfloor\) (shift \(d_1 + d_2\)) — each
constant on runs of length \(\asymp P^{1/2}/h\) — and let
\(\boldsymbol\kappa = (\kappa_1, \kappa_2, \kappa_{12}) \in
\{0,1\}^3\) be the corresponding level-1 carries, so that \(m_{10} =
m + b_1 + \kappa_1\), \(m_{01} = m + b_2 + \kappa_2\), \(m_{11} = m +
b_{12} + \kappa_{12}\). Then on each \(b\)-run intersection and each
carry branch \(\boldsymbol\kappa\),

\[
\Delta\Delta Y \;=\; F_{\boldsymbol\kappa}(m), \qquad
F_{\boldsymbol\kappa}(m) = (m + b_{12} + \kappa_{12})^{3/2}
- (m + b_1 + \kappa_1)^{3/2} - (m + b_2 + \kappa_2)^{3/2} + m^{3/2}
\]

**exactly** (no error term). The net offset \(j = (b_{12} +
\kappa_{12}) - (b_1 + \kappa_1) - (b_2 + \kappa_2)\) is bounded
(\(|j| \le 3\) for \(h_1 h_2 \le P^{1/2}/3\)), and

\[
F_{\boldsymbol\kappa} \;\asymp\; \tfrac32 |j|\, P^{3/4}
+ h_1 h_2 P^{1/4},
\qquad
F_{\boldsymbol\kappa}'(m) \;\asymp\; |j|\, P^{-3/4}
+ h_1 h_2 P^{-5/4} \;<\; 1 .
\]

Hence on each branch the floor \(\lfloor
F_{\boldsymbol\kappa}(X(n))\rfloor\) is constant on runs of length
\(\asymp \min\bigl(P^{1/4}/|j|,\; P^{3/4}/(h_1 h_2)\bigr)\), and the
\(\theta\)-correction \(F(m) = F(X) - F'(\xi)\theta\) has sub-unit
amplitude. The branch indicator \([\boldsymbol\kappa = \cdot]\) is a
finite union of arcs in the single variable \(\theta\) with slowly
moving endpoints \(1 - \{\Delta_1X\}\), \(1 - \{\Delta_2X\}\), \(1 -
\{\Delta_{12}X\}\) (drifts \(\asymp hP^{-1/2} < 1\)): exactly
Theorem C's moving-endpoint expansion.

*Proof.* The corner identities are Lemma B at the three shifts. The
bound on \(j\): \(b_{12} - b_1 - b_2 \in \{0, 1\}\) up to
\(\lfloor\Delta\Delta X\rfloor\)-corrections with \(|\Delta\Delta X|
\le 4h_1h_2\sup|X''| = 3h_1h_2P^{-1/2}\). The derivative: MVT on the
second difference of \(\tfrac32 m^{1/2}\) plus \(\tfrac34 j
(m+\xi)^{-1/2}\). \(\square\) Validated (`branch_freeze_scan`):
distinct branch-floor counts match the drift prediction at \(P =
10^6, 10^8\) (e.g. at \(P = 10^8\), \((h_1,h_2)=(1,1)\): 2 distinct
values per cell against 2.8 predicted for offset \(\pm1\), exactly 1
for offset 0).

### Negative knowledge: the raw second gap is NOT frozen

\(\lfloor \Delta\Delta Y\rfloor\) itself has mean run length
\(1.5\) and jumps of size \(\tfrac32 P^{3/4} \approx 47\,900\) at
\(P = 10^6\) (`frozen`-scan falsifier, this phase): the level-1
flicker \(j_1\) shifts \(\Delta\Delta Y\) by \(\tfrac32 j_1 m^{1/2}\)
at essentially every step. A freeze argument ignoring the branch
split is dead on arrival; the branch organization of Lemma R3 is
forced, with the flicker carried by the \([j_1 = j]\) indicator —
level-1 carries, i.e. unit sawtooths of \(X\)-forms via Lemma R2's
sawtooth identity.

### Theorem R (kernel cancellation) — EXACT — HUMAN PROOF

Let \(c\) be smooth on \((P, 2P]\) with \(c^{(r)} \asymp k
P^{9/8 - r}\) for \(r = 0, 1, 2, 3, 4\), derivative signs following
the monomial pattern (the \(W\)-shaped family; e.g. \(c = \tfrac{3k}4
n^{9/8}\)). Then

\[
K_c(P) \;\ll\; P^{1 - \delta + \varepsilon},
\qquad
\delta = \tfrac1{64} \text{ for } k \ll P^{\varepsilon},
\qquad
\delta = \tfrac1{72} \text{ uniformly for } k \le P^{1/24}.
\]

*Proof (draft).*

**Step 1 (double Weyl differencing).** With \(H_1 = P^{a}\), \(H_2 =
P^{b}\) (chosen in Step 6),

\[
|K_c|^2 \ll \frac{P^2}{H_1} + \frac P{H_1}\sum_{h_1 \le H_1}
|T_1(h_1)|,
\qquad
|T_1|^2 \ll \frac{P^2}{H_2} + \frac P{H_2}\sum_{h_2 \le H_2}
|T_2(h_1, h_2)|,
\]

\(T_2 = \sum_n e(\varphi_2)\), \(\varphi_2 = \Delta\Delta(c\,
\theta_2) = \Delta\Delta(cY) - \Delta\Delta(cv)\) — the exact split
into a real-analytic block and an integer block.

**Step 2 (exact product rule).** For both blocks,

\[
\Delta\Delta(cf) \;=\; c_{11}\,\Delta\Delta f
+ (\Delta_2 c)(n{+}d_1)\,\Delta_1 f
+ (\Delta_1 c)(n{+}d_2)\,\Delta_2 f
+ (\Delta\Delta c)\, f .
\]

Scales: \(\Delta_i c \asymp k h_i P^{1/8}\), \(\Delta\Delta c
\asymp k h_1 h_2 P^{-7/8}\).

**Step 3 (the \(Y\)-block).** Work on cell intersections (count
\(O((h_1 + h_2) P^{1/2})\) cells). Within a cell every shifted
\(Y\)-value is a smooth function of the single variable \(m = X -
\theta\) (Lemma M and its shifted form), so no \(\Delta\theta\)
cross-terms arise:

- \((\Delta\Delta c)\,Y\): smooth part curvature \(\asymp
  k h_1 h_2 P^{-5/8}\); \(\theta\)-coefficient \(\tfrac32
  \Delta\Delta c\, X^{1/2} \asymp k h_1 h_2 P^{-1/8} < 1\)
  (constraint C1: \(k h_1 h_2 \le P^{1/8}\)) — expanded in Fourier
  modes of \(\theta\) at multiplicative mode-mass cost, not
  absorbed.
- \((\Delta_2 c)\,\Delta_1 Y\) and its mirror: \(\Delta_1 Y =
  (m{+}G_1)^{3/2} - m^{3/2}\) on the cell; \(\theta\)-coefficient
  \(\asymp \Delta_2 c \cdot G_1 X^{-1/2} \asymp k h_1 h_2 P^{-1/8} <
  1\); smooth curvature \(\asymp k h_1 h_2 P^{-5/8}\).
- \(c_{11}\,\Delta\Delta Y\): Lemma R3 branches. Per branch with
  net offset \(j\): smooth part \(c\,F_{\boldsymbol\kappa}(X)\) with
  curvature \(\asymp k|j| P^{-1/8} + k h_1 h_2 P^{-5/8} < 1\),
  combined per run with Step 4's frozen floor (Step 5(i));
  \(\theta\)-content \(c\,F'\,\theta\) with coefficient \(\asymp
  k|j| P^{3/8} + k h_1 h_2 P^{-1/8}\) and window drift \((c F')'
  \asymp k|j| P^{-5/8} < 1\): shifted-window expansion, then
  \(X\)-modes \(s \asymp k|j| P^{3/8}\) with curvature \(s X''
  \asymp k|j| P^{-1/8} < 1\), van der Corput II.

**Step 4 (the \(v\)-block).** \(v\) is an integer: no fractional
part of \(c\) is ever split off.

- \((\Delta\Delta c)\,v = (\Delta\Delta c)(Y - \theta_2)\): the
  \(Y\)-part as in Step 3; the \(\theta_2\)-part has coefficient
  \(\asymp k h_1 h_2 P^{-7/8} < 1\).
- \((\Delta_2 c)\,\Delta_1 v = \Delta_2 c\,(\lfloor W\rfloor +
  \kappa_2 - \kappa_2) = \Delta_2 c\,(W - \{W\})\) plus the Lemma-N
  carry: \(\Delta_2 c \cdot W\) is smooth-in-\(m\) per cell
  (curvature \(\asymp k h_1 h_2 P^{-5/8}\), \(\theta\)-coefficient
  \(\asymp k h_1 h_2 P^{-1/8}\)); \(-\Delta_2 c\,\{W\}\) has window
  drift \((\Delta_2 c)' \asymp k h_2 P^{-7/8} < 1\): \(W\)-modes
  \(r\) with \(|r| \lesssim k h_2 P^{1/8}\), each \(rW\) again
  smooth-in-\(m\) per cell (\(\theta\)-coefficient \(\asymp r h_1
  P^{-1/4} \le k h_1 h_2 P^{-1/8} < 1\), curvature \(\asymp k h_1
  h_2 P^{-5/8}\)). Carry factors \(e(\Delta_2 c\,\kappa_2) = 1 +
  \kappa_2 (e(\Delta_2 c) - 1)\): indicator weight times a smooth
  factor; \(\kappa_2 = \{Y\} + \{W\} - \{Y{+}W\}\) (Lemma R2's
  sawtooth identity) expands into unit sawtooths of \(Y\), \(W\),
  \(Y_{10}\) with \(O(1)\) coefficients — Vaaler windows \(|r| \le
  R\), \(R = P^{\rho}\), majorant error \(P/R\) per layer; the
  \(Y\)-modes linearize (Lemma M) to \(X\)-modes \(s \asymp R
  P^{3/4}\), curvature \(sX'' \asymp R P^{1/4} \gg 1\): pieces
  without a frozen-\(J\) factor take the **third**-derivative test
  over full ranges (\(\lambda_3 = s X''' \asymp R P^{-3/4} < 1\),
  saving \(P^{1/8}/R^{1/6}\)); pieces riding a frozen-\(J\) factor
  are the mixed class, Step 5(iii).
- \(c_{11}\,\Delta\Delta v = c_{11}\,\Delta_2 g_2\): Lemma R2. The
  factor \(e(-c \lfloor \Delta\Delta Y\rfloor)\) splits over Lemma
  R3 branches: per branch the frozen integer \(J = \lfloor
  F_{\boldsymbol\kappa}(X(n))\rfloor\) (boundary toggles are
  slow-sawtooth indicators in \(\{F(X)\}\) and \(\theta\)) combines
  with the \(c_{11}\Delta\Delta Y\)-content into the smooth per-run
  phase \(c(F - J)\), curvature \(\asymp k|j| P^{-1/8} + k h_1 h_2
  P^{-5/8} < 1\), single-signed per branch (Step 5(i)); van der
  Corput II per frozen run and summation over runs give \(\ll
  (k|j|)^{1/2} P^{15/16} + |j|^{3/2} k^{-1/2} P^{13/16}\) for \(j
  \ne 0\) and \(\ll (k h_1 h_2)^{1/2} P^{11/16} + (h_1 h_2 /
  k)^{1/2} P^{9/16}\) for \(j = 0\). The carries \(\kappa''\)
  (\(W\)-, \(\Delta W\)-content only: slow modes, Step 5(ii)) and
  \(\Delta_2\kappa_2\) (\(\theta_2\)-content: Step 5(iii)/(iv)) are
  indicator weights times \(e(\mp c)\) (curvature \(c'' \asymp k
  P^{-7/8}\), smooth).

**Step 5 (dominance and mode assembly — as repaired by the review).**
Final pieces fall into four classes.

- **(i) Pure smooth pieces**, \(\lambda_2 \asymp k h_1 h_2 P^{-5/8}\)
  or \(k|j| P^{-1/8}\) — van der Corput II; the leading curvature in
  each group is a genuine double difference of a single smooth
  function per run/branch (the \(c_{11}\Delta\Delta Y\)- and
  \(-c\lfloor\Delta\Delta Y\rfloor\)-contents combine per run to the
  smooth \(c\,(F_{\boldsymbol\kappa} - J)\)), so the double MVT gives
  a single-signed \(\lambda_2\): for the monomial-pattern family the
  composite sign check is \(\alpha(\alpha{-}1)(\alpha{+}\beta{-}2)
  (\alpha{+}\beta{-}3) > 0\) at \(\alpha = \tfrac98\) with \(\beta =
  \tfrac34\) (offset branches, \(cF \asymp k\,\mathrm{off}\,
  n^{15/8}\)) and \(\beta = \tfrac14\)-composites (zero-offset,
  \(cF \asymp kh_1h_2 n^{11/8}\)) — exponents \(\tfrac{15}8,
  \tfrac{11}8 \notin \{0,1,2\}\), no vanishing. Per-run van der
  Corput II is legitimate here because \(\lambda_2^{-1/2} \asymp
  P^{1/16} \ll P^{1/4} \asymp\) run length. Saving \(\ge
  P^{1/16}/(k|j|)^{1/2}\).
- **(ii) Slow-mode pieces** (\(W\)-, \(\Delta W\)-, \(F\)-, small
  \(u\)-modes, no \(\theta_2\)-content): van der Corput II over full
  ranges at the dominant scale; dominance is clean because the
  colliding scale \(s^* \asymp kP^{3/8}\) lies outside every window
  (centers \(\ge\) width by construction; \(u \le R' = P^{1/16} \ll
  kP^{3/8}\); the Theorem-Q separation check).
- **(iii) Mixed pieces** — a frozen-\(J\) factor times a large
  \(X\)-mode \(s \asymp rP^{3/4}\) spawned by the
  \(\theta_2\)-carries (\(\kappa_2\), \(\Delta_2\kappa_2\)): here
  van der Corput II fails (\(\lambda_2 \asymp rP^{1/4} \gg 1\)) and
  per-run III gives nothing (see the review record). Repair: one
  **targeted third Weyl differencing** (shift \(2h_3\), \(h_3 \le
  H_3\)) of the piece, then the split \(J = F - \{F\}\): the
  differenced coefficient \(\Delta_3 c \asymp k h_3 P^{1/8}\) has
  window drift \(\asymp k h_3 P^{-7/8} < 1\) against the *slow*
  sawtooth \(\{F(X)\}\) (drift \(\asymp P^{-1/4}\)), so the
  shifted-window expansion applies with no run segmentation;
  \(\Delta_3\lfloor F\rfloor = \lfloor\Delta_3F\rfloor + \text{carry}
  \in \{-1,0,1\} + \text{carry}\) is bounded (gap identity on \(F\),
  \(|\Delta_3F| \asymp h_3P^{-1/4}\cdot P^{1/2}\)-drift \(< 1\)) and
  its indicators are slow; and the differenced mode curvature
  \(s(\Delta_3X)'' \asymp r h_3 P^{-3/4} < 1\) is single-signed
  (\(X''' < 0\), \(s\)-sign fixed per window) and dominant
  (\(rP^{3/8} \gg k\)): van der Corput II over full ranges gives
  \((rh_3)^{1/2}P^{5/8}\), and balancing \(H_3 = r^{-1/3}P^{1/4}\)
  yields the piece bound \(r^{1/6}P^{1-1/8}\) — the same class-(iv)
  saving as below, so nothing is lost.
- **(iv) Carry-mode pieces without frozen-\(J\)**: \(X\)-modes
  \(|s| \le RP^{3/4}\), third-derivative test over full ranges,
  \(\lambda_3 = sX''' \asymp rP^{-3/4}\), saving
  \(P^{1/8}/r^{1/6}\).

Sub-unit sawtooths cost multiplicative mode-mass \(O(\log)\) only;
mode masses multiply over at most four expansion layers plus the
targeted differencing: \(P^{\varepsilon}\). Majorant truncations
\(P/R\). With \(R = P^{\rho}\), \(\rho = 1/16\): savings
\(P^{1/16}/(k|j|)^{1/2}\), \(P^{1/8 - \rho/6}\), and truncation
\(P^{-\rho}\) balance at

\[
|T_2| \;\ll\; P^{1 - 1/16 + \varepsilon}
\quad\text{under C1: } k h_1 h_2 \le P^{1/8},
\quad h_1 h_2 \le P^{1/2}/3 .
\]

**Step 6 (assembly).** \(\eta = 1/16\). With \(k \le P^{\kappa_0}\)
and \(a + b \le \tfrac18 - \kappa_0\) (C1): \(|K_c| \ll P\,
(P^{-a/2} + P^{-b/4} + P^{-\eta/4})\). For \(\kappa_0 =
\varepsilon\): \(a = \tfrac1{32}\), \(b = \tfrac1{16}\), \(\delta =
\tfrac1{64}\). For \(\kappa_0 = \tfrac1{24}\): \(a = \tfrac1{36}\),
\(b = \tfrac1{18}\), \(\delta = \tfrac1{72}\). Exponents
deliberately unoptimized. \(\square\)

Float support (`differenced_kernel_probe`, exact scaled phases):
\(|T_1| = 267{-}288\), \(|T_2| = 70{-}158\) on \(2.5\cdot10^4\)
terms and \(|T_1| = 300{-}567\), \(|T_2| = 436{-}686\) on
\(2.5\cdot10^5\) terms across \((h_1, h_2) \in \{(1,1), (1,2),
(2,3), (5,7)\}\); triple differences \(|T_3| = 132{-}164\) and
\(213{-}369\) at the same sizes across \((h_1,h_2,h_3) \in \{(1,1,1),
(1,2,3), (2,3,5)\}\) — square-root scale throughout, consistent with
every differenced level of the argument including the targeted third
differencing.

### Review record (Phase 9)

Every step re-derived adversarially. Two defects found; both
repaired with the part's own exact mechanisms; final exponents
unchanged.

1. **Organizational (Lemma R3 as drafted).** The draft conditioned
   on "cells with fixed \((G_1, G_2)\)". But the level-1 gaps are
   *two-valued* on each \(b\)-run — the carry \(\kappa_1(\theta)\)
   toggles at essentially every step — so those "cells" are wild
   sets and the branch indicator would not have admitted the
   moving-endpoint expansion. Repaired by restating R3 over
   \(b\)-run intersections and the carry vector \(\boldsymbol\kappa
   \in \{0,1\}^3\): the eight branch indicators are arcs in \(\theta\)
   with slow endpoints (Theorem C's Step-4 pattern). The exact
   identity, offset bounds, and freeze scales are unchanged; the
   Phase-8 validator already measured the sub-runs of the repaired
   organization.
2. **Real error (Step 5 as drafted).** For mixed pieces (frozen-\(J\)
   factor × large \(X\)-mode \(s \asymp rP^{3/4}\)) the draft
   implicitly used the third-derivative test per \(J\)-run of length
   \(P^{1/4}\). That fails: the test's second term \(M^{1/2}
   \lambda_3^{-1/6}\) summed over \(P^{3/4}\) runs is \(\asymp
   r^{-1/6}P\) — the trivial bound. Repaired by the targeted third
   Weyl differencing of Step 5(iii): after \(\Delta_3\), the
   \(J\)-content splits as \(J = F - \{F\}\) with the *slow* sawtooth
   \(\{F(X)\}\) (drift \(P^{-1/4}\)) against the *small* coefficient
   \(\Delta_3c\) (window drift \(kh_3P^{-7/8} < 1\)): shifted-window
   expansion with no run segmentation, full-range van der Corput II,
   and the class-(iv) saving \(P^{1/8}/r^{1/6}\) is recovered after
   balancing \(H_3\). Float support: the \(T_3\) probes above.

Also verified in the review: the collision inventory (the crossover
scale \(s^* \asymp kP^{3/8}\) lies outside every mode window; small
\(u\)-modes never reach it since \(R' = P^{1/16}\)); single-signed
leading curvatures per branch via the monomial exponent products
\(\tfrac{15}8, \tfrac{11}8 \notin \{0,1,2\}\); the family hypothesis
extended to \(r \le 4\) (used by the double MVT on \((cF)''\));
window drifts of all shifted expansions; the odd-\(n\)
reparameterization; \(k\)-uniformity of all constants; and the
boundary/majorant inventory (\(P/R\)-losses at \(\rho = 1/16\), run
and cell boundary counts \(\ll P^{3/4+\varepsilon}\)).

### Theorem S (the OOO\* splits — depth 4 complete) — EXACT — HUMAN PROOF

For \(w \in \{\mathrm{OOOE}, \mathrm{OOOO}\}\),

\[
\#\{\text{odd } n \le N : \text{word}_4(n) = w\}
= \tfrac N{16} + O\bigl(N^{1 - 1/72 + \varepsilon}\bigr),
\]

and hence **every** depth-\(\le4\) itinerary word class satisfies
\(\#\{n \le N\} = 2^{-|w|}N + O(N^{1-\delta_w})\) with explicit
\(\delta_w > 0\): depth-4 equidistribution is complete.

*Proof.* The class indicator expands (Vaaler, truncation \(J_3 =
P^{1/24}\), error \(P/J_3 = P^{1-1/24}\)) into mode sums \(S_{ijk} =
\sum_n e\bigl(\tfrac i2 X + \tfrac j2 Y + \tfrac k2 v^{3/2}\bigr)\)
over dyadic blocks. Proposition H rewrites \(\tfrac k2 v^{3/2}\) as a
polynomial in \((m, v)\) with smooth coefficients plus an absorbable
error. Its \(v\)-linear part is \(vW\) with \(W \asymp \tfrac{3k}4
n^{9/8}\) in the Theorem-R family; the \(vm\)- and \(vm^2\)-cross
terms reduce to the same family by \(\xi v m = \xi X\,v - \xi\theta
v\) and \(\xi_2 v m^2 = \xi_2X^2\,v - 2\xi_2X\theta\,v +
\xi_2\theta^2 v\), where \(\xi \asymp kn^{-3/8}\), \(\xi_2 \asymp
kn^{-15/8}\) make every \(\theta\)-cross coefficient sub-unit
(\(\xi X \asymp kP^{-3/8}\cdot P^{3/2}\cdot P^{-3/2}\theta\)-scale
\(< 1\)) and every smooth \(v\)-coefficient a family member
(\(\xi X, \xi_2X^2 \asymp kP^{9/8}\) with monomial-pattern
derivatives). Writing \(v = Y - \theta_2\) splits each family term
into a smooth-in-\(m\) part (Lemma M) and a kernel factor
\(e(-c\,\theta_2)\). The double differencing of Theorem R applied to
the whole mode phase carries the passengers along: the pure-\(m\)
polynomial phases difference into the Step-3 classes
(\((\Delta\Delta\mu)m\)-content sub-unit under C1, crosses smooth per
cell, \(\mu\,\Delta\Delta m\) = bounded-offset branch phases with
curvature \(\asymp k|j|P^{-1/8}\), single-signed by the same
monomial-exponent check); the \(\tfrac i2X\)- and \(\tfrac
j2Y\)-passenger phases difference to \(\tfrac i2\Delta\Delta X\)
(curvature \(\ll ih_1h_2P^{-5/2}\), subdominant) and \(\tfrac
j2F_{\boldsymbol\kappa}(m)\) (real-valued, no floor: smooth plus
sub-unit \(\theta\), curvature \(\asymp jP^{-5/4}\), subdominant in
the established hierarchy); and the kernel factor is handled by
Steps 2–5 verbatim. Assembly as in Theorem R and summation over
\(k \le J_3\) with \(1/k\)-weights give \(\sum_k \tfrac1k
P^{1-1/72} + P^{1-1/24} \ll P^{1-1/72+\varepsilon}\); dyadic blocks
sum to \(N^{1-1/72+\varepsilon}\). The \(i\)- and \(j\)-weighted
sums are no larger. \(\square\)

### Consequences

1. **Conjecture O / note Conjecture 6.2 is settled** (Theorem R) for
   the \(W\)-shaped family — the exact object every Phase-5
   reorganization funnels into — and the OOO\* splits close
   (Theorem S): Conjecture K holds unconditionally at every depth
   \(\le 4\), so the base cases \(d \le 4\) of Proposition J's
   hypothesis are theorems.
2. **The certified-descent density stays \(13/16\)** at four steps:
   the OOO\*-classes are non-contracting at depth 4 (\(3^3 > 2^4\)).
   What opens is depth \(\ge 5\), where OOO-prefixed contracting
   words (e.g. OOOEE, \(3^3 < 2^5\)) live: their closure needs the
   fifth-letter machinery, not attempted here.
3. **A tier ladder.** The engine used one differencing per unit of
   derivative growth (\(Y'' \gg 1 > Y'''\)). Deeper growing layers
   need one more differencing each, with \(\delta\) roughly halving
   per level and the same exact identities — the natural attack on
   depth-5 words, not attempted here.
4. **Editorial debt.** The finite-dynamics note still states
   Conjecture 6.2 as open with the \(13/16\)/OOO\*-kernel frontier
   figure; Sections 5–6 and the figure await a consolidation phase.

### Phase-8/9 decision

Phase 8: **PROMOTE** — draft written; falsifier fired once
(raw-freeze failure, recorded above) and was met by an exact
reorganization; validators and probes all passed.

Phase 9 (review): **PROMOTE** — every step re-derived; two defects
found and repaired (review record above); Theorem R and Theorem S
tagged `EXACT — HUMAN PROOF` (ledger rows `J-kernel-cancellation`
retagged, `J-depth4-complete` added); `kernel_bound_proved` and
`depth4_complete_proved` flipped. Depth 5 is taken up in Part VII.

## Part VII: the length-5 contracting splits — density \(7/8\) (Phase 10)

Scope: the two words that raise the certified-descent density above
\(13/16\). Neither is a third growing layer of kernel type.

- **OOOEE** (\(3^3<2^5\)): fifth letter even after OOOE. Decaying
  nestings plus one slow sawtooth of coefficient \(n^{3/16}<n\),
  carried as a tame passenger on Theorem S.
- **OOEOE** (\(3^3<2^5\)): fifth letter odd after OOEO. Lemma A′ at
  \(w=\lfloor v^{1/2}\rfloor\asymp n^{9/8}\) leaves a sawtooth of
  coefficient \(n^{9/16}<n\) — engine side of the Phase-6 line.
  No kernel.

The expanding siblings OOOEO and OOEOO come free with the same
splits. OOOO\* (fifth letter odd after four odds) has coefficient
\(\asymp n^{27/16}>n\) and is **not** attempted: that is a new
supercritical kernel, not this phase.

### Lemma T1 (OOOE\* fifth-letter smoothing) — EXACT — HUMAN PROOF

Let \(z=\lfloor v^{3/2}\rfloor\). For odd \(n\ge5\),

\[
z^{1/2}
= n^{27/16}-\tfrac98 n^{3/16}\,\theta+D_5,
\qquad
|D_5|\le\tfrac34 m^{-3/8}+\tfrac12 v^{-3/4}+\tfrac9{128}n^{-7/16}.
\]

*Proof.* Three one-signed Taylor steps:
\(z^{1/2}=(v^{3/2}-\theta_z)^{1/2}=v^{3/4}-\tfrac12\theta_z v^{-3/4}
+O(v^{-9/4})\);
\(v^{3/4}=(m^{3/2}-\theta_2)^{3/4}=m^{9/8}-\tfrac34\theta_2 m^{-3/8}
+O(m^{-15/8})\);
\(m^{9/8}=(X-\theta)^{9/8}=n^{27/16}-\tfrac98\theta n^{3/16}
+\tfrac9{128}\theta^2(X-\xi)^{-7/8}\).
The \(\theta_z\) and \(\theta_2\) amplitudes decay
(\(v^{-3/4}\asymp n^{-27/32}\), \(m^{-3/8}\asymp n^{-9/16}\)).
\(\square\) Validated (`oooee_smoothing_scan`) through
\(n=10^{12}\). The remaining sawtooth has coefficient
\(\asymp kn^{3/16}<n\), derivative \(\asymp kn^{-13/16}\ll1\), so
drift-1 intervals of length \(\asymp P^{13/16}/k\) exist.

### Lemma T2 (OOEO\* fifth-letter linearization) — EXACT — HUMAN PROOF

Let \(w=\lfloor v^{1/2}\rfloor\), \(\theta_w=\{v^{1/2}\}\). For odd
\(n\ge5\),

\[
w^{3/2}
= n^{27/16}-\tfrac98 n^{3/16}\,\theta
-\tfrac32 v^{1/4}\,\theta_w+D_5',
\]

with \(D_5'\) decaying (\(|D_5'|\le\tfrac34 m^{-3/8}
+\tfrac38(U-1)^{-1/2}\), \(U=v^{1/2}\)).

*Proof.* Lemma A′ at base \(U\): \(w^{3/2}=v^{3/4}
-\tfrac32 v^{1/4}\theta_w+E\), \(0\le E\le\tfrac38(U-1)^{-1/2}\).
The \(v^{3/4}\to n^{27/16}\) chain is Lemma T1's second and third
steps. \(\square\) Validated (`ooeoe_smoothing_scan`) through
\(n=10^{12}\). Two engine sawtooths: coefficient \(n^{3/16}\) on
\(\theta\) and \(n^{9/16}\) on \(\theta_w\); both grow slower than
\(n\).

### Theorem T (the length-5 contracting splits) — ROUTE (withdrawn Phase 26)

\[
\#\mathrm{OOOEE}(N),\;\#\mathrm{OOOEO}(N)
=\tfrac N{32}+O\bigl(N^{1-1/72+\varepsilon}\bigr),
\qquad
\#\mathrm{OOEOE}(N),\;\#\mathrm{OOEOO}(N)
=\tfrac N{32}+O\bigl(N^{43/48+\varepsilon}\bigr).
\]

*Proof.*

**OOOE\*.** Indicator algebra: OOOE\(*\) is the Theorem-S class
indicator times \(\tfrac12(1\pm\psi(z^{1/2}))\), branch-consistent
because after OOOE the image \(z=J^3(n)\) is even, so the fifth
letter is the even-branch value \(\lfloor\sqrt z\rfloor\) —
machine-checked (`oooee_indicator_identity_check`). Vaaler-expand
the fifth wave at truncation \(J_5=P^{1/24}\). Lemma T1 replaces
\(\tfrac l2 z^{1/2}\) by \(\tfrac l2 n^{27/16}
-\tfrac{9l}{16}n^{3/16}\theta\) at absorbable decaying cost.
The \(\theta\)-sawtooth has coefficient \(C\asymp l P^{3/16}<P\);
its shifted-window expansion (drift-1 length \(P^{13/16}/l\),
window \(T=P^{1/8}\ll l P^{3/16}\) for every \(l\ge1\)) produces
\(X\)-modes of size \(\asymp l P^{3/16}\), which are ordinary
first-letter passengers of Theorem S (strictly smaller than the
\(i\le P^{1/24}\) budget already carried). The smooth chirp
\(e(\tfrac l2 n^{27/16})\) has curvature \(\asymp l P^{-5/16}\),
subdominant to every retained Theorem-S scale. Theorem S therefore
applies verbatim and gives \(N/32+O(N^{1-1/72+\varepsilon})\).

**OOEO\*.** Indicator: \(\mathrm{OOEO}\ast
=\tfrac1{16}(1-\psi(m))(1+\psi(v))(1-\psi(w))
(1\pm\psi(w^{3/2}))\), branch-consistent on the OOEO cylinder
(`ooeoe_indicator_identity_check`). Vaaler-expand the four waves.
The \(k=0\) cases are Theorem E. For \(k\ne0\), Lemma T2 writes
the fifth-letter phase as \(\tfrac k2 n^{27/16}-C\theta-B\theta_w\)
with \(B=\tfrac{3k}4 v^{1/4}\asymp k n^{9/16}\) and
\(C=\tfrac{9k}{16}n^{3/16}\).

Expand \(e(-B\theta_w)=e(-B\{v^{1/2}\})\) on drift-1 intervals of
length \(L_B=P^{7/16}/k\) (there are \(\asymp k P^{9/16}\) of
them; \(B'\asymp k n^{-7/16}\)). Window \(T_w=P^{1/4}\ll
k P^{9/16}\) for every \(k\ge1\); majorant \(P/T_w=P^{3/4}\).
At frequency \(\ell=-B+t\), \(|t|\le T_w\), the combined phase
is \(-\tfrac k4 v^{3/4}+t\,v^{1/2}\) plus passengers. Linearizing
\(v^{3/4}\) and \(v^{1/2}\) by Lemmas T1/T2, the \(\theta\)
coefficients from the two expansions cancel at the window centre
up to a residual \(C_{\mathrm{net}}\asymp k n^{3/16}\). One slow
\(\theta\)-sawtooth remains.

Expand \(e(-C_{\mathrm{net}}\theta)\) on the same intervals
(\(C_{\mathrm{net}}\) drifts by \(P^{-3/8}\ll1\) on each \(I\);
window \(T_\theta=P^{1/8}\ll k P^{3/16}\); majorant \(P^{7/8}\)).
The resulting smooth phase has curvature
\[
\lambda_2
=\Bigl(-\tfrac{297k}{1024}+\tfrac{27k}{128}+O(T_w P^{-7/8})
+O(JP^{-1/2})\Bigr)n^{-5/16}
\asymp k\,n^{-5/16},
\]
single-signed: the two leading coefficients are
\(-0.290k+0.211k=-0.079k\neq0\), and the \(t\)- and \(i\)-errors
are \(O(P^{-5/8})\) and \(O(P^{-3/8})\). Van der Corput II on
each \(I\): \(L_B\lambda_2^{1/2}+\lambda_2^{-1/2}
\ll k^{-1/2}P^{21/32}\). Times \(k P^{3/16}\) intervals:
\(S_k\ll k^{1/2}P^{27/32+\varepsilon}\). Balance
\(J_5^{1/2}P^{27/32}=P/J_5\) at \(J_5=P^{5/48}\) gives
\(P^{43/48}\). Dyadic blocks sum to
\(N^{43/48+\varepsilon}\). \(\square\)

Float sanity: `oooee_mode_probe` / `ooeoe_mode_probe` at
\(P=10^4\) give \(|S|=16.3\) on \(636\) OOOE terms and
\(|S|=32.5\) on \(618\) OOEO terms — far below the cylinder
size. Depth-5 census at \(N=10^5\): the four classes lie in
\([3138,3181]\) against \(3125\).

### Corollary U (certified-descent density \(7/8\)) — ROUTE (withdrawn Phase 26)

The class of starts carrying a uniform power-envelope descent
certificate of length at most five — evens, OE, OOEE, OOOEE,
OOEOE — has natural density \(7/8\). Each of OOOEE and OOEOE
has cardinality \(N/32+O(N^{43/48+\varepsilon})\), and
\(3^3<2^5\) forces \(J^5(n)<n\) on both words for \(n\ge2\).

*Proof.* Densities \(\tfrac12+\tfrac14+\tfrac1{16}+\tfrac1{32}
+\tfrac1{32}=\tfrac78\). The new cylinders are Theorem T. The
contraction is Corollary 2.3 of the finite-dynamics note
(\(3^3=27<32=2^5\)). \(\square\)

This is the first increment past the one-growing-layer ceiling of
Proposition I. The leftover \(1/8\) is the expanding length-5
tree OOEOO \(\cup\) OOOEO \(\cup\) OOOO\*. Of those, OOEOO and
OOOEO are now *counted* (Theorem T) and still do not contract;
OOOO\* is uncounted and supercritical.

### Phase-10 decision

**PROMOTE.** Both contracting length-5 words close under the
existing engine: OOOEE is a tame passenger on Theorem S, OOEOE
is a Theorem-Q argument at coefficient \(n^{9/16}\). Certified
density moves \(13/16\to7/8\). No new kernel, no note import,
no all-depth claim. The next mathematical question is whether
the OOOO\* fifth letter (coefficient \(n^{27/16}>n\)) admits a
scale-invariant extension of Theorem R, which is the first
rung of a Terras induction; that is a different phase.

## Part VIII: the OOOO\* kernel — isolation (Phase 11)

Scope: name the supercritical fifth-letter object and decide
whether Theorem R's numerology iterates. No bound, no density
claim, no triple-differencing draft.

Notation as in Part VI, plus \(Z = v^{3/2}\), \(z = \lfloor Z\rfloor\),
\(\theta_3 = Z - z\). After four odds the fifth letter is the
parity of \(\lfloor z^{3/2}\rfloor\). Branch consistency is
machine-checked (`oooo_indicator_identity_check`).

### Lemma V1 (level-3 kernel reformulation) — EXACT — HUMAN PROOF

For odd \(n \ge 5\),

\[
\tfrac12\bigl(v^{9/4} - z^{3/2}\bigr)
- \tfrac34\, z^{1/2}\theta_3 \;=\; R_3,
\qquad
0 \le R_3 \le \tfrac3{16}\, z^{-1/2}.
\]

Consequently the central kernel phase \(c\,\theta_3\) with
\(c = \tfrac{3k}4 z^{1/2}\) equals \(\tfrac k2\bigl(Z^{3/2} -
\lfloor Z\rfloor^{3/2}\bigr)\) up to \(k R_3 \ll k n^{-27/16}\):
**the OOOO\* kernel is the exponential sum of the level-3 local
floor defect**, Lemma R1 with \((m,v)\) replaced by \((v,z)\).
Since \(z \asymp n^{27/8}\), the coefficient is
\(c \asymp k n^{27/16} > n\).

*Proof.* Taylor of \((z + \theta_3)^{3/2}\) at \(z\):
\(Z^{3/2} = z^{3/2} + \tfrac32 z^{1/2}\theta_3 +
\tfrac38 (z+\xi)^{-1/2}\theta_3^2\) with \(\xi \in (0,\theta_3)\),
and \(Z^{3/2} = v^{9/4}\). \(\square\) Validated in exact scaled
integers (`level3_reformulation_scan`): odd samples through
\(n = 10^{12}+1\), remainder one-signed in the stated envelope.

### Kernel (definition)

For smooth \(c\) with \(c \asymp k P^{27/16}\) and
\(c' \asymp k P^{11/16}\) on \(n \sim P\) (the \(z^{1/2}\)-shaped
family),

\[
K_3(P) \;=\; \sum_{\substack{n \sim P \\ n\ \mathrm{odd}}}
e\bigl(c(n)\,\{\lfloor\lfloor n^{3/2}\rfloor^{3/2}\rfloor^{3/2}\}
\bigr).
\]

This is the \(W\)-family of Theorem R with one extra nesting:
coefficient \(\alpha = 27/16\) in place of \(9/8\).

### Smooth numerology iterates

The smooth model \(G(n) = n^{27/8}\) (replacing every floor by
the real power) has

\[
G''' \asymp P^{3/8} \gg 1 > P^{-5/8} \asymp G^{(4)}.
\]

Theorem R used \(Y'' \asymp P^{1/4} \gg 1 > P^{-3/4} \asymp Y'''\)
and two Weyl steps. The same "one extra differencing per unit of
derivative growth" therefore predicts **three** Weyl steps here.
This is the scale-invariant pattern *of the smooth model*, not
of the nested floors. Phase 12 (Part IX) shows the prediction
does not descend: there are no \(v\)-level \(b\)-runs, and the
forced inner linearization produces a \(W\)-family at
\(\alpha = 45/16 > 9/4\).

Closed form only; the derivatives are elementary. A float check
of \(n^{27/8}\) at \(P = 10^4\) matches \(G'''\) and \(G^{(4)}\)
to relative error \(< 1\%\).

### Negative knowledge: raw \(\Delta^4 Z\) is not frozen

The discrete \(Z = v^{3/2}\) inherits jumps from both inner
floors. At \(P = 10^4, 10^5, 10^6\), the mean
\(|\Delta^3 Z|\) is \(10^4\)–\(10^7\) times the smooth
\(G'''\), and \(|\Delta^4 Z|\) is \(10^8\)–\(10^{11}\) rather
than \(\ll 1\) (`level3_raw_gap_wildness`). A freeze argument
that ignores the nested carry lattice — level-1 carries of
\(m = \lfloor n^{3/2}\rfloor\) and level-2 carries of
\(v = \lfloor m^{3/2}\rfloor\) — is dead on arrival. This is
the Phase-8 raw-freeze falsifier one layer up, recorded now so
it is not rediscovered as a "new" obstruction.

The branch set is a *product* of two Lemma-R3 lattices, not a
copy of Lemma R3. The inner variable \(v\) jumps by
\(\asymp n^{5/4}\) per step of \(n\). Inherited Phase-5 dead
routes (composed Lemma-B cells, the swap
\(e(c\theta_3) = e(cZ)\,e(-\{c\}z)\), a second A-process on
\(z^{3/2}\), fibre + van der Corput II, shifted-window Vaaler
on a full-size sawtooth) remain dead; they were not retested.

### Float support

Exact scaled phases (`level3_kernel_probe`,
\(c = \tfrac34 z^{1/2}\)): \(|K_3| = 30.1,\ 59.5,\ 423.7\) on
\(2.5\cdot10^3,\ 2.5\cdot10^4,\ 10^5\) terms — square-root
scale (predicted \(\sqrt N = 50,\ 158,\ 316\)). On the OOOO
cylinder at \(P = 10^5\): \(|K_3| = 59.1\) on \(6207\) terms
(\(\sqrt N = 79\)). Differenced probes at \(P = 2\cdot10^4\):
\(|T_1| = 182\), \(|T_2| = 47\), \(|T_3| = 62\) on \(10^4\)
terms (\(\sqrt N = 100\)).

### What a bound would *not* do

Even a power-saving bound on \(K_3\) at depth 5 only *counts*
OOOOE and OOOOO. Neither contracts:
\(3^4 = 81 > 32 = 2^5\). Certified descent stays \(7/8\).
The first OOOO-prefixed contractor is OOOOEEE
(\(81 < 128 = 2^7\)), a length-7 itinerary, not this phase.

A saving \(\delta\) that halves per extra nesting
(\(1/72 \to 1/144 \to \cdots\)) does **not** feed the
Hoeffding argument of Proposition J at all depths. Terras
still needs \(\delta\) uniform in the depth or at least
\(\ge c/d^2\). Isolation of \(K_3\) is the first rung of
that program, not the program.

### Conjecture V (level-3 kernel cancellation)

\(K_3(P) \ll P^{1-\delta}\) for some \(\delta > 0\), uniformly
over the \(z^{1/2}\)-shaped family \(c \asymp k P^{27/16}\),
\(k \le P^{\varepsilon}\). Supported by the probe; not claimed.

### Phase-11 decision

**PROMOTE** the isolation. Lemma V1 is exact; the object is
named; the smooth numerology iterates; the probe cancels; the
raw-freeze route is recorded dead; no new unnamed wild sum
appeared. The bound is a different phase: it must show that
the *product* of the two carry lattices still kills every
full-size sawtooth coefficient, or exhibit a new wall.

`depth5_kernel_isolated` flipped; `depth5_kernel_bound_proved`
and `density_one_claimed` stay `False`. No ledger row (no
bound, no density increment). No note import. The
scale-invariant copy is taken up — and refuted — in Part IX.

## Part IX: the \(v\)-level wall (Phase 12)

Scope: the Phase-11 question — does the product of the two
carry lattices still kill every full-size sawtooth in \(K_3\),
or is there a new wall at the \(v\)-level? Answer: a new wall.
No bound draft.

### Lemma V2 (forced inner linearization) — EXACT — HUMAN PROOF

For odd \(n \ge 5\),

\[
v^{3/2}
= m^{9/4} - \tfrac32 m^{3/4}\,\theta_2 + E_2,
\qquad
0 \le E_2 \le \tfrac38\, v^{-1/2}.
\]

*Proof.* Taylor of \((Y - \theta_2)^{3/2}\) at \(Y\):
\(v^{3/2} = Y^{3/2} - \tfrac32 Y^{1/2}\theta_2 +
\tfrac38 (Y-\xi)^{-1/2}\theta_2^2\) with \(\xi \in (0,\theta_2)\),
\(Y^{3/2} = m^{9/4}\), \(Y^{1/2} = m^{3/4}\), and
\(Y - \xi \ge v\). \(\square\) Validated
(`level3_inner_linearization_scan`) through \(n = 10^{12}+1\).

Restoring the outer coefficient \(c \asymp k z^{1/2}
\asymp k n^{27/16}\) of Lemma V1, the phase \(c\,v^{3/2}\)
splits as a smooth chirp \(c\,m^{9/4}\) minus the \(W\)-family
phase \(C\,\theta_2\) with

\[
C = \tfrac{3c}2 m^{3/4} \asymp k n^{45/16},
\]

plus a remainder phase \(c E_2 \asymp k n^{9/16}\theta_2^2\)
(engine-side: coefficient \(< n\), derivative
\(\asymp n^{-7/16} < 1\)). The remainder is not the wall.
The main term is.

This linearization is forced if \(Z = v^{3/2}\) is to become
smooth in \(m\). Not linearizing leaves \(Z\) as a function of
the integer \(v = \lfloor Y\rfloor\), which is the other dead
route below.

### Proposition W (no \(v\)-level cells; \(\alpha = 45/16\) past the engine line) — EXACT — HUMAN PROOF / REFUTED method

Two independent deaths of "copy Theorem R one nesting up."

**(i) No \(b\)-runs.** Theorem R segments on runs where
\(\lfloor\Delta X\rfloor\) is constant, of length
\(\asymp P^{1/2}/h\). The \(v\)-level analogue is runs of
\(\lfloor\Delta Y\rfloor\) or of \(\Delta v\). But
\(Y' \asymp P^{5/4}\) and \(Y'' \asymp P^{1/4} \gg 1\), so
\(\lfloor\Delta Y\rfloor\) changes at every step of \(n\).
Measured (`v_level_cell_scan`): mean and max run length \(1\)
at \(P = 10^4, 10^5, 10^6\), both for \(\lfloor\Delta Y\rfloor\)
and for \(\Delta v\). Lemma R3 cannot be restated at the
\(v\)-level: its cells have length \(1\).

**(ii) The forced \(W\)-family is past the engine line.**
For a \(W\)-family \(e(C\theta_2)\) with \(C \asymp k P^{\alpha}\),
Theorem R's Step-3 \(\theta\)-coefficient of \((\Delta\Delta C)\,Y\)
is \(\asymp k h_1 h_2 P^{\alpha - 5/4}\). This is

- sub-unit (R's constraint C1) iff \(\alpha \le 5/4\),
- engine-treatable (coefficient \(< P\) and derivative \(< 1\))
  iff \(\alpha < 9/4\).

Lemma V2 produces \(\alpha = 45/16 = 2.8125 > 9/4\). The spawned
\(\theta\)-sawtooth then has coefficient
\(\asymp k h_1 h_2 P^{25/16} > P\) and derivative
\(\asymp k h_1 h_2 P^{9/16} \gg 1\): a unit sawtooth whose
coefficient exceeds \(n\) and which crosses integers within
single steps. That is the Phase-5 wall, at a larger scale.

The two Phase-11 routes therefore die by recorded mechanisms,
not by a new unnamed sum:

- copy R with \((X,m,Y,v)\mapsto(Y,v,Z,z)\): dies by (i);
- linearize through the inner floor, then invoke R: dies by (ii).

Inherited Phase-5 dead routes (composed Lemma-B cells, the
swap \(e(c\theta_3)=e(cZ)\,e(-\{c\}z)\), a second A-process
on \(z^{3/2}\)) remain dead and were not retested.

### What this does *not* refute

Conjecture V — that \(K_3\) itself cancels — is untouched.
The Phase-11 probe still shows square-root cancellation.
What is refuted is the *method*: a scale-invariant copy of
Theorem R with \(\delta(\alpha)\) read off from the smooth
model \(G(n)=n^{27/8}\). The smooth numerology of Part VIII
is correct as a statement about \(n^{27/8}\) and false as a
statement about \(\{\lfloor Y\rfloor^{3/2}\}\).

A bound on \(K_3\) would still not raise certified descent
at depth 5, and a \(\delta\) that halves per nesting would
still not give Terras. The new information is sharper:
the engine/kernel line of the \(W\)-family is \(\alpha = 9/4\)
for R's own Step-3 bookkeeping, and the first supercritical
OOOO\* coefficient already overshoots it.

### Phase-12 decision

**PROMOTE** the obstruction. Lemma V2 is exact; the missing
\(v\)-level cells are measured; the \(\alpha = 45/16\) wall
is the Phase-5 object at a named larger scale. The
scale-invariant R-extension is **REFUTED** (ledger row
`J-scale-invariant-R-extension`). Conjecture V stays a
conjecture; `depth5_kernel_bound_proved` and
`density_one_claimed` stay `False`.
`scale_invariant_R_extension_refuted` flipped. No note
import, no density claim, no rescue draft. The Terras
increment that does *not* need \(K_3\) is taken up in Part X.

## Part X: the length-7 engine contractors — density \(57/64\) (Phase 13)

Scope: the two leftover itineraries that contract at length 7
*without* meeting \(K_3\). The third length-7 contractor
OOOOEEE still needs the OOOO\* split and is not attempted.

- **OOEOOEE** (\(3^4<2^7\)): sixth letter after the Theorem-T
  class OOEOO. The naive \(\theta_w\)-coefficient
  \(n^{45/32}>n\) rearranges (Lemma X1, the A′ pattern) into
  an integer-\(w\) block whose first gap freezes on runs of
  length \(\asymp P^{7/8}\), plus a \(W\)-family at
  \(\alpha=33/32<9/8\) (Corollary R′) and engine sawtooths.
- **OOOEOEE** (\(3^4<2^7\)): Lemma A′ at
  \(s=\lfloor z^{1/2}\rfloor\), same coefficient budget.

### Corollary R′ (\(W\)-family for \(\alpha\le 9/8\)) — ROUTE (withdrawn Phase 26)

Theorem R's bound \(K_c(P)\ll P^{1-1/72+\varepsilon}\) holds
for every monomial family \(c^{(r)}\asymp k P^{\alpha-r}\)
with \(0<\alpha\le 9/8\) and the same sign pattern, uniformly
for \(k\le P^{1/24}\).

*Proof.* Every constraint in the Phase-9 proof of Theorem R
is monotone in \(\alpha\) on \((0,9/8]\): C1 becomes
\(k h_1 h_2\le P^{5/4-\alpha}\), which is weaker than
\(P^{1/8}\) as \(\alpha\) drops; every curvature and window
drift shrinks; the mixed-piece third differencing has smaller
modes. Sign-dominance
\(\alpha(\alpha-1)(\alpha+\beta-2)(\alpha+\beta-3)>0\) holds
at \(\beta\in\{1/4,3/4\}\) throughout the interval (both
factors \(\alpha+\beta-2\) and \(\alpha+\beta-3\) stay
negative, the first two stay positive). The assembly
exponents of Step 6 only improve. The case \(\alpha=33/32\)
used below is an instance. \(\square\)

### Lemma X1 (OOEOO\* sixth-letter rearrangement) — EXACT — HUMAN PROOF

Let \(w=\lfloor v^{1/2}\rfloor\), \(p=\lfloor w^{3/2}\rfloor\),
\(\theta_p=\{w^{3/2}\}\). For odd \(n\ge5\),

\[
p^{3/2}
= -\tfrac54 v^{9/8} + \tfrac94 w\, v^{5/8}
- \tfrac32 w^{3/4}\,\theta_p + E_X,
\]

with \(0\le E_X\le \tfrac38 p^{-1/2} + \tfrac{45}{32} v^{1/8}\).

*Proof.* Taylor of \((w^{3/2}-\theta_p)^{3/2}\) at \(w^{3/2}\)
gives \(p^{3/2}=w^{9/4}-\tfrac32 w^{3/4}\theta_p+E_p\). Taylor
of \((v^{1/2}-\theta_w)^{9/4}\) at \(v^{1/2}\) gives
\(w^{9/4}=v^{9/8}-\tfrac94 v^{5/8}\theta_w+E_w\). The identity
\(\theta_w=v^{1/2}-w\) rearranges the middle term:
\(v^{9/8}-\tfrac94 v^{5/8}(v^{1/2}-w)
=-\tfrac54 v^{9/8}+\tfrac94 w\,v^{5/8}\). \(\square\)
Validated (`sixth_ooeoo_scan`) through \(n=10^{12}+1\).

The naive coefficient \(\tfrac94 v^{5/8}\asymp n^{45/32}>n\)
of \(\theta_w\) is gone. Remaining sawtooth \(\theta_p\) has
coefficient \(n^{27/32}<n\), derivative \(n^{-5/32}<1\).

### Lemma X2 (OOOEO\* sixth-letter A′) — EXACT — HUMAN PROOF

Let \(z=\lfloor v^{3/2}\rfloor\), \(s=\lfloor z^{1/2}\rfloor\).
For odd \(n\ge5\),

\[
s^{3/2}
= -\tfrac12 z^{3/4} + \tfrac32 s\, z^{1/4} + E,
\qquad
0\le E\le\tfrac38(U-1)^{-1/2},\quad U=z^{1/2}.
\]

*Proof.* Lemma A′ at base \(U=z^{1/2}\). \(\square\)
Validated (`sixth_oooeo_scan`) through \(n=10^{12}+1\).

### Lemma X3 (\(w\)-gap freeze) — EXACT — HUMAN PROOF

On the OOEO cylinder, \(U=v^{1/2}\) has
\(U''\asymp P^{-7/8}<1\), so \(\lfloor\Delta U\rfloor\) is
constant on runs of length \(\asymp P^{7/8}/h\). The integer
gap \(\Delta w=\lfloor\Delta U\rfloor+\kappa_w\) is a frozen
floor plus a 0/1 carry. Measured (`w_gap_freeze_scan`): a
single run covers a window of \(400\) OOEO terms at
\(P=10^4,10^5,10^6\).

### Theorem X (the length-7 engine splits) — ROUTE (withdrawn Phase 26)

\[
\#\mathrm{OOEOOEE}(N),\;\#\mathrm{OOEOOEO}(N),\;
\#\mathrm{OOEOOOE}(N),\;\#\mathrm{OOEOOOO}(N)
=\tfrac N{128}+O\bigl(N^{43/48+\varepsilon}\bigr),
\]
and the same bound for the four OOOEO\*\* words.

*Proof.*

**OOEOO\*\*.** Indicator: the Theorem-T class OOEOO times
\(\tfrac12(1\pm\psi(p^{3/2}))\tfrac12(1\pm\psi(q^{1/2}))\),
branch-consistent (`ooeooee_indicator_identity_check`).
Vaaler-expand the new waves. Lemma X1 writes the sixth-letter
phase as a smooth function of \((v,w)\) minus an engine
\(\theta_p\)-sawtooth. Expand \(v^{9/8}\) and \(v^{5/8}\) by
Lemma A/M:

- first-letter content of \(m^{27/16}\) is a chirp
  \(e(C n^{3/2})e(-C m)\) with \(C\asymp n^{33/32}\),
  curvature \(\asymp n^{17/32}\), van der Corput II;
- \(\theta_2\)-content of \(w\,m^{-1/16}\) has coefficient
  \(\asymp n^{33/32}\), a \(W\)-family with
  \(\alpha=33/32<9/8\), Corollary R′;
- remaining \(\theta_2\)-amplitudes are \(O(n^{9/32})\),
  engine;
- the integer block \(e(\xi w)\) with
  \(\xi\asymp n^{45/32}\) is handled on the frozen
  \(\lfloor\Delta U\rfloor\)-runs of Lemma X3: per run
  \(\Delta w=J+\kappa_w\) with \(J\) frozen, \(e(\xi J)\) a
  smooth chirp, \(\kappa_w\) an indicator weight (Theorem Q
  / R3 pattern at the \(w\)-level);
- \(\theta_p\) expands on drift-1 intervals of length
  \(P^{5/32}\), window \(T\ll P^{27/32}\), producing
  \(X\)-modes smaller than Theorem T's budget.

The seventh letter is the even-branch square root of
\(q=\lfloor p^{3/2}\rfloor\): decaying amplitudes (Lemma D
one level up). Theorem T therefore applies as a passenger
theorem and gives \(N/128+O(N^{43/48+\varepsilon})\).

**OOOEO\*\*.** Lemma X2 plus the \(z^{3/4}\to n^{81/32}\)
chain of Lemma T1 (raised to the \(3/2\)): the same four
classes of terms (chirp, \(W\)-family at \(33/32\), engine
sawtooths, integer-\(s\) block with
\(\lfloor\Delta z^{1/2}\rfloor\)-runs of length
\(\asymp P^{5/16}\)). Same exponent. \(\square\)

Depth-7 census at \(N=10^5\): OOEOOEE \(792\), OOOEOEE
\(787\) against \(391\) — within the
\(\max(N^{2/3},\,\cdot)\) envelope of the depth-6 test
(deviation \(400\ll 1.5\cdot N^{2/3}\)). Every start in
either class with \(n\le 10^5\) satisfied \(J^7(n)<n\).

### Corollary Y (certified-descent density \(57/64\)) — ROUTE (withdrawn Phase 26)

The class of starts carrying a uniform power-envelope descent
certificate of length at most seven — the Corollary-U class
together with OOEOOEE and OOOEOEE — has natural density
\(57/64\). Both new words have cardinality
\(N/128+O(N^{43/48+\varepsilon})\), and \(3^4<2^7\) forces
\(J^7(n)<n\) for \(n\ge2\).

*Proof.* Densities \(\tfrac78+\tfrac1{128}+\tfrac1{128}
=\tfrac{56}{64}+\tfrac{1}{64}=\tfrac{57}{64}\). The new
cylinders are Theorem X. The contraction is
\(81<128\). \(\square\)

The leftover \(\tfrac7{64}\) is the OOOO\* tree (still
uncounted, blocked by Phase 12 and Phase 14) together with
the expanding length-7 siblings of OOEOO\*\* and OOOEO\*\*
(now counted). The next contractor in the leftover is
OOOOEEE, which requires \(K_3\).

### Phase-13 decision

**PROMOTE.** The two length-7 contractors that avoid
OOOO\* close under the existing engine plus Corollary R′.
Certified density moves \(7/8\to 57/64\). This is the first
Terras increment that does not need a new kernel, and it
shows the leftover \(1/8\) was not a single obstruction:
two-thirds of its first contracting layer is engine. OOOOEEE
and Conjecture V remain open. No note import, no
density-one claim. `depth7_engine_contracting_proved`
flipped. The increment-first attack on \(K_3\) is taken up
— and refuted — in Part XI.

## Part XI: increment-first dies on the \(X\)-cells (Phase 14)

Scope: the remaining method that is not a copy of Theorem R
and not V2-first — difference the whole phase
\(c\,\theta_3\) on \(X\)-cell \(b\)-runs, then Taylor the
increment \(F_J(v)=(v+J)^{3/2}-v^{3/2}\) in the single
variable \(\theta_2\) at a frozen \(J=\lfloor\Delta Y\rfloor\).
If \(J\) froze, the leftover would be a \(W\)-family at
\(\alpha=29/16<2<9/4\), inside Theorem R's Weyl and engine
lines. It does not freeze. No bound draft.

### Lemma Z1 (increment linearization) — EXACT — HUMAN PROOF

Let \(J=\Delta v\) at step \(2\) (\(J\ge 1\)) and
\(F_J(y)=(y+J)^{3/2}-y^{3/2}\). For odd \(n\ge 5\),

\[
F_J(v)
= F_J(Y) - F_J'(Y)\,\theta_2 + R_J,
\qquad
-\tfrac38\, v^{-1/2} \le R_J \le 0,
\]

where \(F_J'(Y)=\tfrac32\bigl((Y+J)^{1/2}-Y^{1/2}\bigr)\).

*Proof.* Taylor of \(F_J(Y-\theta_2)\) at \(Y\):
\(F_J''<0\) and \(\xi\ge v\) give the one-sided remainder
\(\tfrac12 F_J''(\xi)\theta_2^2\), bounded by
\(\tfrac38 v^{-1/2}\). \(\square\) Validated
(`increment_linearization_scan`) through \(n=10^{12}+1\).

Restoring \(c\asymp k z^{1/2}\asymp k n^{27/16}\), the
leftover \(c F_J'(Y)\) is a \(W\)-family of size
\(\asymp k n^{29/16}\) at the identity-step gap (since
\(F_J'(Y)\asymp J Y^{-1/2}\asymp n^{1/8}\)). The remainder
\(c R_J\asymp k n^{9/16}\) is engine-side. The identity is
not the wall. Frozen \(J\) is.

### Proposition Z (no \(J\)-runs on \(X\)-cells; \(\partial F/\partial J\) is \(45/16\)) — EXACT — HUMAN PROOF / REFUTED method

Two independent deaths of "difference first, then
increment-linearize on \(X\)-cells."

**(i) No \(J\)-runs.** Theorem R's \(X\)-cells are
\(b\)-runs of \(\lfloor\Delta_h X\rfloor\), length
\(\asymp P^{1/2}/h\). On those cells \(m\) advances by
\(b\asymp h P^{1/2}\) per step. The increment
\(F(m)=(m+b)^{3/2}-m^{3/2}\) has \(F'(m)\asymp P^{-1/4}<1\),
so its floor would freeze for \(\Delta m\asymp P^{1/4}\).
Each cell step is \(\Delta m\asymp P^{1/2}>P^{1/4}\): the
\(n\)-orbit jumps past the \(m\)-freeze in a single step.
Measured (`x_cell_increment_scan`) at
\(P=10^4,10^5,10^6\), on genuine \(\lfloor\Delta X\rfloor\)
\(b\)-runs of mean length \(33,80,200\):

- raw \(\lfloor\Delta Y\rfloor\) and \(\Delta v\) have mean
  and max run length \(1\), with mean
  \(|\Delta\lfloor\Delta Y\rfloor|\asymp P^{3/4}\) (the
  level-1 carry flicker of \(Y\), the Phase-8 raw-freeze
  phenomenon one layer up);
- the \(\kappa\)-fixed branch increment
  \(\lfloor(m+b+\kappa)^{3/2}-m^{3/2}\rfloor\) also has max
  run length \(1\) (per-step change \(\asymp P^{1/4}\gg 1\)).

Restricting to \(X\)-cells does not create \(v\)-level
cells. Lemma R3 cannot be restated for the first
difference of \(Y\).

**(ii) The \(J\)-derivative is the \(45/16\) family.**
\(\partial F_J/\partial J=\tfrac32(v+J)^{1/2}\). Changing
the frozen integer by \(1\) changes the increment phase by

\[
c\cdot\tfrac32(v+J)^{1/2}\asymp k n^{45/16}.
\]

Measured (`increment_j_derivative_scan`):
\(c\bigl(F_{J+1}(v)-F_J(v)\bigr)\big/\bigl(\tfrac98 n^{45/16}\bigr)\to 1\)
through \(n=10^{10}+1\). This is Lemma V2's leftover
(Proposition W(ii)) read as a derivative in \(J\). Replacing
frozen \(J\) by \(J=\Delta Y-\{\Delta Y\}+\kappa\) expands
\(e\bigl(c F_J\{\Delta Y\}\bigr)\) as a full-size sawtooth
of the slow form \(\Delta Y\) — the recorded Phase-5 dead
route (shifted-window Vaaler on a coefficient \(>n\) with
derivative \(\gg 1\)).

The two Phase-14 ingredients therefore die by recorded
mechanisms, not by a new unnamed sum:

- frozen-\(J\) increment on \(X\)-cells: dies by (i);
- unfrozen \(J\) (or \(\{\Delta Y\}\) expansion): dies by
  (ii), which is the Phase-12 wall.

Inherited dead routes (composed Lemma-B cells, the swap
\(e(c\theta_3)=e(cZ)\,e(-\{c\}z)\), a second A-process on
\(z^{3/2}\), fibre + van der Corput II, copy of R one
nesting up, V2 then invoke R) remain dead and were not
retested.

### What this does *not* refute

Conjecture V — that \(K_3\) itself cancels — is untouched.
The Phase-11 probe still shows square-root cancellation.
What is refuted is the *method*: difference-first plus
increment linearization on \(X\)-cells. The leftover
\(\alpha=29/16\) is real as an algebraic coefficient and
unreachable as a Weyl input, because the runs on which the
Taylor is legitimate have length \(1\).

A bound on \(K_3\) would still not raise certified descent
at depth 5 (\(3^4>2^5\)), and a \(\delta\) that halves per
nesting would still not give Terras. The new information is
sharper: every route that needs a frozen first difference
of \(Y\), whether as a \(v\)-level \(b\)-run or as an
\(X\)-cell increment, is the same missing cell.

### Phase-14 decision

**PROMOTE** the obstruction. Lemma Z1 is exact; the missing
\(J\)-runs on \(X\)-cells are measured; the \(J\)-derivative
is the named \(45/16\) wall. The increment-first attack is
**REFUTED** (ledger row `J-increment-first-K3`). Conjecture V
stays a conjecture; `depth5_kernel_bound_proved` and
`density_one_claimed` stay `False`.
`increment_first_k3_refuted` flipped. No note import, no
density claim, no rescue draft. The X1-absorption attack
that would land on a freezing integer is taken up — and
refuted — in Part XII.

## Part XII: X1 cannot land on a freezing integer (Phase 15)

Scope: the most promising remaining attack — absorb the
\(W\)-family leftover \(C\theta_2\), \(C\asymp n^{45/16}\),
by the Lemma-X1 substitution into an integer whose first
gap freezes, leaving only engine sawtooths. No bound draft.

The integers whose real analogs have \(F''<1\) (so
\(\lfloor\Delta F\rfloor\) freezes) are \(n\), \(m\) (on
\(X\)-cells), \(w=\lfloor v^{1/2}\rfloor\),
\(w_m=\lfloor m^{1/2}\rfloor\), and \(s=\lfloor z^{1/2}\rfloor\).
The integer \(v=\lfloor Y\rfloor\) is not on that list.

### Lemma Z3 (X1 landing criterion) — EXACT — HUMAN PROOF

The substitution \(C\{F\}=CF-C\lfloor F\rfloor\) produces a
usable frozen-gap integer \(I=\lfloor F\rfloor\) if and only
if \(\lfloor\Delta F\rfloor\) is constant on long runs. For
unit steps this requires \(F''<1\).

*Proof.* \(\Delta I=\lfloor\Delta F\rfloor+\kappa\) with
\(\kappa\in\{0,1\}\). The floor of the real gap freezes on
runs of length \(\asymp 1/|F''|\) precisely when
\(|F''|<1\); the carry is then an indicator weight (the
Lemma-X3 / Theorem-Q pattern). If \(|F''|>1\) the real gap
changes by \(\gg 1\) at every step and there are no
\(I\)-runs. \(\square\)

Instances, measured (`x1_landing_gap_scan`) at
\(P=10^4,10^5,10^6\) on a window of \(400\) odd steps:

- \(F=v^{1/2}\) (\(F''\asymp n^{-7/8}<1\)) and
  \(F=m^{1/2}\) (\(F''\asymp n^{-5/4}<1\)):
  \(\lfloor\Delta F\rfloor\) is constant on the whole
  window (mean run \(\ge 8\));
- \(F=Y=m^{3/2}\) (\(Y''\asymp n^{1/4}>1\)):
  \(\lfloor\Delta Y\rfloor\) and \(\Delta v\) have mean
  and max run length \(1\).

This is why Lemma X1 could land on \(w\) (the dangerous
sawtooth was \(\{v^{1/2}\}\), a slow variable) and why the
same move cannot land on \(v\).

### Proposition AA (no freezing landing for the \(K_3\) leftover) — EXACT — HUMAN PROOF / REFUTED method

The V2 leftover is \(C\theta_2=C\{Y\}\). The X1 substitution
is uniquely \(\theta_2=Y-v\) and lands on \(v\). Lemma Z3
then says \(v\) has no \(J\)-runs.

Rewriting \(v=P+Q\) with \(P\) a polynomial in the freezing
integers does not help: \(\Delta P=o(\Delta v)\) or else
\(\Delta P\asymp\Delta v\), and in either case \(Q=v-P\)
inherits a first difference of size \(\asymp n^{5/4}\).
Measured, each of

\[
v-w_m^3,\qquad v-m\,w_m,\qquad v-w^2
\]

has mean and max run length \(1\) at
\(P=10^4,10^5,10^6\).

Cubing Lemma T1 after absorbing the first-letter
\(\theta\) into \(m\) produces the same leftover: the
\(\theta_2\)-amplitude \(m^{-3/8}\) of \(z^{1/2}\),
multiplied by \(3(n^{27/16})^2\), is
\(3n^{27/8}m^{-3/8}\asymp 3n^{45/16}\). Cubing a decaying
nesting does not evade V2.

Therefore X1-absorption of \(K_3\) into a freezing integer
is impossible. The attack dies by Lemma Z3, not by a new
unnamed sum. Inherited dead routes (copy of R, V2 then
invoke R, increment-first, composed Lemma-B cells, the
swap \(e(c\theta_3)=e(cZ)\,e(-\{c\}z)\), a second
A-process on \(z^{3/2}\), fibre + van der Corput II,
shifted-window Vaaler on a full-size sawtooth) remain dead
and were not retested.

### What this does *not* refute

Conjecture V is untouched. The Phase-11 probe still
cancels. What is refuted is the method: X1-absorption
applied to a *fast* fractional part. The criterion is
sharp — the same move remains available for every
sawtooth of a variable with \(F''<1\), which is why
depth \(\le 4\) and the engine contractors closed.

A bound on \(K_3\) would still not raise certified descent
at depth 5, and a \(\delta\) that halves per nesting would
still not give Terras. The new information is the landing
rule: X1 can only swallow a sawtooth whose floor already
has cells.

### Phase-15 decision

**PROMOTE** the obstruction. Lemma Z3 is exact; the hybrid
gaps are measured; cubing T1 is V2 in disguise. X1-absorption
of \(K_3\) is **REFUTED** (ledger row `J-x1-absorption-K3`).
Conjecture V stays a conjecture;
`depth5_kernel_bound_proved` and `density_one_claimed` stay
`False`. `x1_absorption_k3_refuted` flipped. No note import,
no density claim, no rescue draft. The two remaining
candidate attacks — extend R past \(9/4\), or replace
nested floors by a smooth model — are taken up and closed
in Part XIII.

## Part XIII: the toolkit obstruction (Phase 16)

Scope: decide whether either leftover attack bounds
\(K_3\). Neither does. The bound program is parked.

```text
Mathematical target     Does extending R past 9/4, or a
                        smooth nested-floor comparison,
                        bound K3?
Novelty hypothesis      45/16 might still be Weyl-accessible,
                        or the floor defect might be a
                        remainder against van der Corput
                        on n^{27/8}.
Falsifier               C' >> 1 at α = 45/16, or the defect
                        equals the W-family leftover.
Existing machinery      Theorem R C1; Lemmas V1/V2; Z3.
Maximum Phase-0 scope   Measure C(n+2)-C(n); identify the
                        defect with V1/V2; write the
                        unification. No new kernel draft.
Promotion criterion     A bound, or a named exhaustion of
                        the toolkit.
Stop criterion          Both leftover attacks die by
                        recorded mechanisms.
```

### The amplitude is not slowly varying

The V2 leftover coefficient is
\(C=\tfrac98 z^{1/2}m^{3/4}\asymp n^{45/16}\). Then

\[
C(n+2)-C(n)
\sim \tfrac{405}{64}\, n^{29/16}\gg 1.
\]

Measured (`v2_amplitude_drift_scan`): the ratio tends to
\(6.328125\) at \(n=10^4,10^6,10^8\). Theorem R's
shifted-window and C1 bookkeeping treat \(C\) as
quasi-static on the Weyl gaps. That hypothesis fails
here: \(C\) jumps by \(\gg 1\) at every odd step. Extending
the engine line from \(9/4\) toward \(2\) would not
repair it. The spawned Step-3 coefficient at
\(\alpha=45/16\) is \(\asymp kh_1h_2 n^{25/16}>n\) already
at \(h_1=h_2=1\) (Proposition W(ii)).

### Smooth comparison is circular

Replacing a nested floor by the corresponding real power
has pointwise phase defect equal to the leftover of
Lemma V1 or V2, not an absorbable remainder:

- \(Y^{3/2}-v^{3/2}=\tfrac32 m^{3/4}\theta_2-E_2\)
  (Lemma V2), coefficient \(n^{45/16}\) after restoring
  \(c\);
- \(v^{9/4}-z^{3/2}\) is the \(K_3\) phase itself
  (Lemma V1).

A van der Corput bound on \(\sum e(\alpha n^{27/8})\)
therefore differs from the nested-floor sum by a
\(W\)-family we cannot estimate. Bounding the error is
bounding \(K_3\). This is **REFUTED** as a method
(`J-nested-floor-without-W-family`).

### Proposition BB (toolkit obstruction) — EXACT — HUMAN PROOF

Every method in the laboratory toolkit for \(K_3\) dies
by one of two mechanisms.

**(I) Missing \(Y\)-cells.** The method needs a frozen
first difference of \(Y=m^{3/2}\). \(Y''\asymp n^{1/4}>1\),
so there are no such cells. This kills the scale-invariant
copy of Theorem R, increment-first on \(X\)-cells, and
X1-absorption into \(v\) or a \(v\)-hybrid
(Propositions W, Z, AA).

**(II) A \(W\)-family past the engine line, with a
fast amplitude.** The method produces
\(e(C\theta_2)\) with \(C\asymp n^{45/16}>n^{9/4}\) and
\(C'\asymp n^{29/16}\gg 1\). This kills V2-then-R and
every smooth-model replacement (Proposition W(ii) and
the paragraph above).

Inherited Phase-5 dead routes remain dead and were not
retested. Conjecture V is not refuted: the Phase-11
probe still cancels at square-root scale. What is
exhausted is the *toolkit*, not the cancellation.

A bound on \(K_3\) would still not raise certified
descent at depth 5, and a \(\delta\) that halves per
nesting would still not give Terras. Further progress
needs a theory that is not a repair of R, X1, or
increment-first.

### Phase-16 decision

**PARK** the \(K_3\) bound. Proposition BB is exact;
both leftover attacks die by recorded mechanisms; the
amplitude drift is measured. Rows
`J-nested-floor-without-W-family` (REFUTED) and
`J-k3-toolkit-obstruction` (EXACT). Conjecture V stays
a conjecture; `depth5_kernel_bound_proved` and
`density_one_claimed` stay `False`.
`k3_toolkit_parked` flipped. No note import, no density
claim, no rescue draft. The two-step-parity theorems
through Corollary Y are untouched. The next density
step is still OOOOEEE, and it still needs a method
that does not exist in this toolkit.

## Part XIV: Phase-0 falsifiers for the two post-BB theories (Phase 17)

Scope: Proposition BB admits exactly two theory families that are
not repairs of R, X1 or increment-first — they change what is
*averaged* (L² transport of distributions) or what is *counted*
(bilinear dispersion / double large sieve on the \(k\)-family).
Before any theory phase, each gets its cheapest falsifier. No
theory drafts, no kernel bounds, no density claims.

### Falsifier (a): pair statistics of the dispersion amplitude

The dispersion route never bounds a single \(K_3(k)\): it treats
\(\sum_k k^{-1}|K_3(k)|\) by squaring and swapping, which converts
the problem into counting near-coincidences of the amplitude

\[
u(n) = \tfrac34\, z^{1/2}\theta_3 \bmod 1
\qquad (\text{the } K_3 \text{ phase at } k = 1,\ \text{family
phase} = k\,u).
\]

It needs (i) near-Poissonian pair counts at scale \(1/J\) —
\(\#\{\|u_i - u_j\| < 1/J\} \approx N^2/J\) — and (ii) no
short-lag rigidity: \(u(n+2h) - u(n)\) equidistributed, since no
sieve decouples nearby terms. Probe
(`dispersion_spacing_census`, \(u\) exact to \(\sim10^{-13}\) via
\(\theta_3\) at scale \(10^{24}\); two-pointer circular
coincidence count):

| \(P\) | \(N\) | ratio \(J{=}16\) | \(J{=}32\) | \(J{=}64\) | \(\max_h R_h\), \(h \le 4\) | noise floor |
| --- | --- | --- | --- | --- | --- | --- |
| \(10^5\) | 49000 | 1.0000 | 1.0000 | 0.9999 | 0.0043 | 0.0045 |
| \(10^6\) | 100000 | 1.0000 | 1.0000 | 1.0000 | 0.0051 | 0.0032 |

Poissonian to four digits at every scale; lag concentration at or
below the \(N^{-1/2}\) noise floor. **The falsifier did not
fire.** (The \(h{=}4\) value at \(P = 10^6\) is \(1.6\times\) the
floor — within ordinary fluctuation for four trials; recorded, not
alarming.)

### Falsifier (b): block randomness of level-3 defects

The transport route never forms a nested Weyl sum: it propagates
the *conditional distribution* of the level-3 data one nesting at
a time and pays in a variance over blocks, tolerating exceptional
blocks — admissible for density-one (Terras) conclusions though
not for exact class counts. It needs level-3 defects to be
block-random: for consecutive blocks \(B\) of odd \(n\),
\(\mathbb E_B\,|\sum_{n\in B} e(r\theta_3)|^2 \approx |B|\), the
fifth letter \(\varepsilon_5 = \psi(z^{3/2})\) at block variance
\(\approx |B|\), and no short-lag autocorrelation. Probe
(`transport_block_variance`):

| \(P\) | \(L\) | blocks | mode ratios \(r \in \{1,2,4,8\}\) | letter ratio | \(\max_h |A(h)|\) | noise floor |
| --- | --- | --- | --- | --- | --- | --- |
| \(10^5\) | 256 | 195 | 0.94–1.05 | 1.09 | 0.0051 | 0.0045 |
| \(10^5\) | 1024 | 48 | 0.94–1.29 | 1.11 | 0.0046 | 0.0045 |
| \(10^6\) | 256 | 200 | 0.90–1.02 | 1.08 | 0.0046 | 0.0044 |
| \(10^6\) | 1024 | 200 | 0.91–1.07 | 1.05 | 0.0038 | 0.0022 |

All variance ratios inside the \(\chi^2\) fluctuation band for the
block counts; autocorrelations at noise. **The falsifier did not
fire.** (Letter ratios sit \(5\)–\(11\%\) above 1 across all four
configurations — within \(1\sigma\) of the \(\chi^2\) spread at
these block counts, but consistent in sign; the transport phase
should re-measure at more blocks before leaning on exact
constants.)

### What Phase 0 does and does not say

Both statistics are **OBSERVATION**. They say the two theories'
*minimal empirical prerequisites* hold — the structure each method
would exploit is present in the data. They do not touch the actual
work: for dispersion, proving a spacing bound for nested-floor
amplitudes (the B–I spacing lemmas lean on rational structure of
smooth monomial phases); for transport, proving approximate
block-independence of level-3 data from level-2 inputs (the
composed-cell obstruction shows the naive conditioning fails; the
transport must condition on the carry lattice, not on a smooth
model). Conjecture V is untouched. No BB mechanism is contradicted:
both routes live outside the toolkit that Proposition BB exhausted.

### Phase-17 decision

**PROMOTE** both theories past Phase 0; neither falsifier fired.
Ranking for the theory phases: transport first (it aims at the
Terras statement itself, where exceptional sets are affordable),
dispersion second (tactical, aims at \(K_3\) proper). Flags
`dispersion_phase0_alive`, `transport_phase0_alive` set
(OBSERVATION); `depth5_kernel_bound_proved` and
`density_one_claimed` stay `False`. No ledger rows (no theorem, no
refutation — census-gate precedent). No note import, no commit.

## Part XV: the transport inductive step — statement, substrate, and the dispersion verdict (Phase 18)

Scope: state the transport inductive step precisely and determine
whether its proof obligations reduce to proven machinery or to
recorded walls; settle the dispersion route's status as a
completion method at the same time. No \(K_3\) bound, no density
move, no note import.

### Proposition CC (dispersion cannot complete the count). REFUTED as a completion route

**Statement.** No family-averaging method (double large sieve,
dispersion, large-sieve amplification over the mode index \(k\))
can, by itself, bound the depth-5 class count \(\#OOOO{*}(N)\).

**Proof.** The fifth-letter count is accessed through
\(\psi(z^{3/2})\), and every Fourier-type expansion of the bounded
function \(\psi\) (Vaaler or otherwise) places weight
\(\asymp 1/k\) on the \(k\)-th harmonic; the count error is
controlled only if \(|K_3(k)| = o(N)\) *for each bounded* \(k\) —
the \(k = 1\) term alone carries weight one. A dispersion bound
controls \(k\)-averages such as \(\sum_{k \le J}|K_3(k)|^2\);
since the family phase is exactly \(k\,u(n)\), the family members
are Fourier coefficients of the distribution of \(u\), and no
average over \(k \le J\) constrains the \(k = 1\) coefficient
individually. There is also no amplification family: the phase
\(u(n)\) has no auxiliary bilinear parameter. Finally, the one
analytic obligation dispersion does generate — an upper bound on
the near-coincidence pair count at scale \(1/J\) — is circular:
the Selberg-majorant expansion of that count is
\(\sum_{|t| \le J}\hat s_t\,|\sum_n e(t\,u(n))|^2\), the kernel
family itself. \(\square\)

The Phase-17 spacing statistics stand as OBSERVATION; the route is
closed as a way to finish the count. (For the record, the same
argument shows the transport route *must* deliver per-\(k\) bounds
at bounded \(k\); it aims to, via per-block bounds.)

Two more negatives, recorded because they eliminate the naive
transport forms: (i) the plain block variance
\(\sum_B |S_B|^2\) expands into the \(h\)-averaged once-differenced
level-3 kernel — the \(T_1^{(3)}\)-family, dead by both BB
mechanisms, so the variance cannot be paid against level-3 pair
statistics; (ii) the fiber transform to the \(m\)- or \(v\)-variable
is exact (the fifth letter is a function of \(v\) alone, and the
Piatetski–Shapiro image weights are slow \(m^{2/3}\)-modes), but
the image is sparse: the needed saving at the \(k\)-th fiber level
is \(1 - (2/3)^k \ge 1/3\), against the engine's \(1/72\). The
sparsity wall of the Phase-5 record is quantitative and permanent.

### Lemma DD (block carry models). EXACT — HUMAN PROOF

Let \(P \le n_0 < 2P\) be odd, \(L = \lfloor P^{1/4}\rfloor\), and
write \(X_0 = n_0^{3/2}\), \(D = (n_0+2)^{3/2} - n_0^{3/2}\). For
\(0 \le t < L\):

**(i) (affine \(m\)-model).**
\(m(n_0 + 2t) = \lfloor X_0 + D\,t \rfloor + O(1)\).
*Proof.* The second difference of \(X = n^{3/2}\) over step 2 is
\(4X'' + O(P^{-3/2}) = 3n^{-1/2} + O(P^{-3/2})\), so the
accumulated quadratic drift is at most
\(\tfrac32 t^2 P^{-1/2} \le \tfrac32\) for \(t \le P^{1/4}\); the
floor moves by at most \(2\). \(\square\)

**(ii) (amplified \(v\)-model).** Let \(A = m(n_0+2) - m(n_0)\),
\(\mu(t) = m_0 + A\,t\), and \(s(t) = m(t) - \mu(t)\) (the realized
carry sequence; \(0 \le s \le \{D\}t + O(1)\), and by (i)
\(s(t) = \lfloor \{X_0\} + \gamma t\rfloor + O(1)\) with
\(\gamma = D - A \in [0,1)\) — a one-dimensional rotation carry).
Then

\[
v(n_0+2t)
 = \Bigl\lfloor \mu(t)^{3/2}
   + \tfrac32\,\mu(t)^{1/2}\, s(t) \Bigr\rfloor + O(1).
\]

*Proof.* Taylor at \(\mu(t)\):
\((\mu + s)^{3/2} = \mu^{3/2} + \tfrac32\mu^{1/2}s
+ \tfrac38\xi^{-1/2}s^2\) with \(\xi \in (\mu, \mu+s)\); the
remainder is at most
\(\tfrac38 P^{-3/4}(L+2)^2 \asymp P^{-1/4} < 1\). \(\square\)

Validators `block_m_affine_model_check` and
`block_v_amplified_model_check` (exact scaled integers, 50 blocks
per scale): the measured defect of (i) is \(\le 2\) at every
\(P \in \{10^4, 10^6, 10^8, 10^{10}\}\), and of (ii) is \(0\) for
\(P \le 10^8\) and \(1\) at \(P = 10^{10}\).

**What the lemma buys.** On \(P^{1/4}\)-blocks the nested level-2
data collapses, with \(O(1)\) exactness, to a *bounded-complexity
system*: a smooth function of an integer-affine base, plus the
carry orbit of a single circle rotation \(t \mapsto \{\gamma t +
\theta_0\}\), amplified by \(W(t) = \tfrac32\mu(t)^{1/2} \asymp
P^{3/4}\). The nesting has been traded for block parameters
\((\theta_0, \gamma, m_0, A)\) whose joint distribution across
blocks is a level-\(\le 2\) statistic — inside the proven engine.
Two supporting facts: the cross-block pair terms carry
\(\theta_2\)-sawtooths with coefficients \(\asymp P^{1/8}|t-t'|
\le P^{3/8}\), far below the engine line \(P^{9/4}\); and the
pair-decay multiplier \(\beta = \{c\,((v+1)^{3/2} - v^{3/2})\}\)
equidistributes at the noise floor (`carry_multiplier_probe`:
\(|{\rm mean}\ e(\beta)| = 0.004\)–\(0.017\) at floor
\(0.007\)–\(0.014\); OBSERVATION).

### Conjecture EE (the transport inductive step)

There exist \(\delta, \delta' > 0\) such that for every bounded
\(k \ge 1\), all but \(O(P^{3/4 - \delta'})\) of the
\(P^{3/4}\)-many blocks satisfy

\[
|S_k(B)| \;=\;
\Bigl| \sum_{t=0}^{L-1} e\bigl(k\,u(n_0 + 2t)\bigr) \Bigr|
\;\le\; L^{1-\delta},
\]

where, by Lemma DD(ii), the phase on \(B\) is an explicit function
of \((t, s(t))\) — a smooth amplification of the rotation orbit —
up to \(O(1)\) floor defects, themselves indicator content in the
rotation and in one further DD-type model at level 3. Summing over
blocks, Conjecture EE implies \(|K_3(k)| \ll P^{1-\delta''}\) for
each bounded \(k\), hence the OOOO\(*\) splits and (with Theorem S
and Proposition J) the density-one program.

**Obligations, each named.** (α) *In-block*: cancellation in
exponential sums over rotation orbits with smooth
\(P^{3/4}\)-amplified weights — Ostrowski/continued-fraction
territory (Denjoy–Koksma-type bounds; the quality of \(\gamma\)'s
continued fraction enters, with bad-\(\gamma\) blocks controlled
by measure). (β) *Cross-block*: equidistribution of the block data
\((\theta_0, \gamma, W\text{-fractions})\) — level-\(\le 2\),
proven machinery (Theorems C/R). (γ) *Level-3 carries*: a DD-type
model one level up (\(z\) on blocks: amplification
\(\asymp P^{9/8}\) of the level-2 carry orbit), plus the
multiplier non-degeneracy already observed.

**Why this is outside Proposition BB.** No frozen \(\lfloor
\Delta Y\rfloor\) is required — the model *tracks* the
\(P^{1/4}\)-scale gap jumps exactly through \(s(t)\) (BB mechanism
I is bypassed, not repaired). No \(\theta_2\)-linearization is
performed — \(v\) enters as an exact integer model, so no
\(W\)-family at \(\alpha = 45/16\) is spawned (mechanism II never
engages). The randomness source is a classical rotation, not a
nested sawtooth.

### Phase-18 decision

**CLOSE** the dispersion branch as a completion route
(Proposition CC; ledger row `J-dispersion-count-route`, REFUTED).
**PROMOTE** the transport branch to its analytic phase with
Conjecture EE as the target and Lemma DD as its proven substrate
(ledger row `J-block-carry-models`, EXACT — HUMAN PROOF). Flags
`dispersion_count_route_refuted` and `transport_substrate_exact`
flipped; `depth5_kernel_bound_proved` and `density_one_claimed`
stay `False`. Conjecture V is open; Conjecture EE is a conjecture.
No note import, no commit.

## Part XVI: the level-3 block phase model and the in-block census (Phase 19)

Scope: obligation (γ) of Conjecture EE — the level-3 analogue of
Lemma DD — plus the census gate for the in-block cancellation
target. Two preliminary analytic findings are recorded first;
no proof of Conjecture EE is attempted, no \(K_3\) bound, no
density move.

### Two findings that shape the analytic phase

**Denjoy–Koksma does not apply naively.** In rotation coordinates
(\(s = \gamma t + \beta_0 - \omega\), \(\omega\) the orbit of the
base rotation), the level-3 phase is a quadratic polynomial in
\(\omega\) with multipliers \(a_1 \asymp P^{15/8}\),
\(a_2 \asymp P^{3/8}\), plus a \((3/2)\mu^{3/4} \asymp
P^{9/8}\)-amplified second fractional layer. The observable's
total variation on the circle is \(\asymp a_1 \gg L = P^{1/4}\),
so the Denjoy–Koksma inequality is vacuous. The correct route is
harmonic: \(e(A\{x\})\) has Fourier mass concentrated in an
\(\ell^1\)-summable window around the harmonic \(j \approx A\),
so a two-layer Fourier cascade (the \(\rho\)-layer at
\(j \approx P^{9/8}\), each harmonic spawning an \(\omega\)-layer
at \(j' \approx jW + a_1 \approx P^{15/8}\)) reduces the block
sum to harmonically-weighted linear-rotation sums with smooth
carriers, at a total mass cost of only polylog — unlike Weyl
differencing, which loses square roots. The smooth carriers
satisfy a sixth-derivative ladder inside blocks
(\(g^{(6)} \asymp P^{-15/16} < 1\)), so van der Corput
high-derivative tests apply there; the linear parts leave
Diophantine conditions on *amplified* block frequencies, to be
handled by measure plus the proven cross-block equidistribution.

**The product form sets the precision budget.** The kernel phase
\(u = \tfrac34 z^{1/2}\theta_3 \bmod 1\) multiplies any
\(\theta_3\)-model error by \(z^{1/2} \asymp P^{27/16}\).
A model of \(\theta_3\) accurate to its natural sub-unit scale is
therefore useless for \(u\): the expansion must be carried to
precision \(P^{-27/16}\), three Taylor orders deeper than
sub-unit. This is a hard constraint the cascade must respect.

### Lemma FF (level-3 block phase model). EXACT — HUMAN PROOF

On DD-blocks, with \(F = \mu^{3/2} + \tfrac32\mu^{1/2}s\),
\(v = \lfloor F\rfloor + d\), \(e = d - \{F\}\):

\[
\theta_3 = \Bigl\{ \mu^{9/4} + \tfrac94\mu^{5/4}s
 + \tfrac{27}{32}\mu^{1/4}s^2 - \tfrac{27}{128}\mu^{-3/4}s^3
 + \tfrac{243}{2048}\mu^{-7/4}s^4
 + \bigl(\tfrac32\mu^{3/4} + \tfrac98\mu^{-1/4}s
    - \tfrac{27}{64}\mu^{-5/4}s^2\bigr)\,e
 + \tfrac38\mu^{-3/4}e^2 \Bigr\} + O(P^{-19/16}),
\]

and \(\tfrac34 z^{1/2} = \tfrac34\bigl(\mu^{9/8}
+ \tfrac98\mu^{1/8}s - \tfrac{27}{128}\mu^{-7/8}s^2\bigr)
+ \tfrac34\cdot\tfrac34 F^{-1/4}e + O(P^{-13/16})\), giving a
model of \(u\) to \(\sim P^{-15/16}\). *Proof.* Taylor expansion
of \((F + e)^{3/2}\) about \(F\) and of \(F^{p}\) about
\(\mu^{3/2}\) (\(p = \tfrac32, \tfrac34\)), with every term above
\(P^{-27/16}\) retained: the dropped terms are \(O(\mu^{-11/4}s^5
+ \mu^{-9/4}s^3|e| + \mu^{-7/4}s\,e^2 + F^{-3/2}|e|^3)
= O(P^{-23/8})\) for \(\theta_3\) — comfortably inside the
\(P^{-27/16}\) budget — and \(O(P^{-13/16})\) for the coefficient,
which multiplies \(\theta_3 < 1\). \(\square\)

Validator `level3_block_model_check` (exact integers at scale
\(10^{48}\); the earlier \(10^{24}\) run exposed how the
\(z^{1/2}\)-amplification magnifies even isqrt rounding):
worst \(\theta_3\)-error \(5\cdot10^{-11}\) at \(P = 10^4\)
falling to \(4\cdot10^{-25}\) at \(P = 10^{10}\); worst
\(u\)-error \(2\cdot10^{-4}\) falling to \(2\cdot10^{-8}\) —
below the predicted scales at every tested \(P\).

**Meaning.** The level-3 kernel phase on a block is now an
explicit closed-form function of four observables: the affine
base \(\mu(t)\), the rotation carry \(s(t)\), the level-2
fractional orbit \(\{F(t)\}\), and the \(O(1)\) defect \(d(t)\).
Obligation (γ) of Conjecture EE is discharged: no further
nesting remains to be modelled.

### The census gate (OBSERVATION)

`block_kernel_sum_census`: \(R_k(B) = |S_k(B)|^2/L\) over
consecutive blocks, \(u\) exact, \(k \in \{1,2,3\}\):

| \(P\) | \(L\) | blocks | mean \(R\) | median \(R\) | max \(R\) | frac \(R>4\) | resonant-decile mean |
| --- | --- | --- | --- | --- | --- | --- | --- |
| \(10^6\) | 31 | 300 | 0.94–1.05 | 0.64–0.72 | 5.8–6.0 | 2.3–3.3% | 0.78–1.13 |
| \(10^8\) | 100 | 200 | 0.93–0.99 | 0.62–0.65 | 5.1–8.4 | 2.0–3.5% | 0.95–1.04 |
| \(10^{10}\) | 316 | 100 | 0.88–1.04 | 0.63–0.76 | 4.0–6.5 | 1.0–2.0% | 0.77–0.80 |

This is a textbook \(\mathrm{Exp}(1)\) profile (median
\(\ln 2 \approx 0.69\), \(\mathbb P(R>4) = e^{-4} \approx 1.8\%\),
max \(\approx \ln(\#\text{blocks})\)): the in-block sums sit at
the *square-root* scale \(|S_k(B)| \asymp L^{1/2}\), far stronger
than the \(L^{1-\delta}\) Conjecture EE needs. Two consequences:
the census gate passes decisively, and \(\gamma\)-rational
resonance does **not** predict bad blocks (resonant-decile means
indistinguishable from the bulk) — the Diophantine conditions of
the cascade live at the amplified frequencies
(\(\{a_1\gamma\}\)-type), not at \(\gamma\) itself, which tells
the analytic phase where its exceptional-set argument must work.

### Phase-19 decision

**PROMOTE** the cascade phase. Obligation (γ) of Conjecture EE is
closed by Lemma FF (ledger row `J-level3-block-phase-model`,
EXACT — HUMAN PROOF); the cancellation target is empirically at
the random-phase scale (OBSERVATION, census-gate precedent — no
ledger row). Flags `level3_block_model_exact`,
`in_block_cancellation_observed` flipped;
`depth5_kernel_bound_proved` and `density_one_claimed` stay
`False`. Conjectures V and EE stay open. No note import, no
commit. The remaining analytic work is obligation (α) in cascade
form: bound the harmonically-weighted linear-rotation sums for
all blocks outside an exceptional set controlled by measure and
the proven level-\(\le 2\) equidistribution.

## Part XVII: the intra-block obstruction and the pure model (Phase 20)

Scope: run the cascade — obligation (α) — to its proof
obligations, adversarially. Outcome: the cascade dies, in a
scale-free way that closes the whole intra-block harmonic
program; the phase records the obstruction (Proposition GG),
distills the minimal open model problem (Conjecture HH), and
validates the model's cancellation empirically. No \(K_3\)
bound, no density move, no note import.

### Proposition GG (the intra-block obstruction). EXACT — HUMAN PROOF

**Statement.** No intra-block harmonic method in the laboratory
toolkit bounds the kernel block sums
\(S_k(B) = \sum_{t<L} e(kC(t)\{\Theta(t)\})\)
(\(C \asymp P^{27/16}\), \(\Theta\) the Lemma-FF phase), at any
block length \(L \le P\). Two mechanisms:

**(GG-I) Window drift.** Any character expansion of
\(e(kC\{\Theta\})\) in the \(\Theta\)-direction has Fourier mass
concentrated in an \(O(\log)\)-window centered at the harmonic
\(j \approx kC(t)\). The center drifts by
\(kC' \asymp kP^{11/16}\) *per step* (about \(3.3\cdot10^4\)
harmonics per step at \(P = 10^6\)), so a fixed harmonic is
active for less than one step: the expansion's inner sums have
length \(< 1\) and the interchange is vacuous. The drift is
per-step in \(n\), hence independent of block length —
higher-degree polynomial models extend DD-blocks to
\(L = P^{(r-1/2)/(r+1)} \to P\), and the mechanism is unmoved.

**(GG-II) Amplitude transfer.** Every algebraic re-form moves
the \(P^{27/16}\) amplitude; none destroys it:
(a) *floor-splitting*: \(e(k\lfloor C\rfloor\{\Theta\})
= e(k\lfloor C\rfloor\Theta)\) is exact (integer multiplier),
but the residual factor \(e(k\{C\}\{\Theta\})\), double-Fourier
expanded (coefficients \(\ell^1\)-summable since \(k\) is
bounded), collapses by \(e(p\{C\}) = e(pC)\),
\(e(q\{\Theta\}) = e(q\Theta)\) back onto the moving-integer
phase \((k\lfloor C\rfloor + q)\Theta\) — whose only reductions
are \(C - \{C\}\) (transferring the amplitude to
\(\{C\}\Theta\), now \(\Theta \asymp P^{27/8}\) on \(\{C\}\)) or
GG-I;
(b) *the pure-phase identity*
\(C\theta_3 = \tfrac34(z^{1/2}v^{3/2} - z^{3/2})\) (exact, since
\(\theta_3 = v^{3/2} - z\)): the floor expansions of the pure
phases spawn \(v^{9/4}\)-terms whose \((9/4)F^{5/4}e\)-content is
the \(\alpha = 45/16\) W-family (Lemma V2), with intra-block
numerology worse than global;
(c) *differencing*, at any order, in \(t\) or across blocks,
preserves the full amplitude on \(\theta_3\)-difference terms
(\(\bar C\,\Delta\theta_3\) with \(|\bar C| \asymp P^{27/16}\));
the cross-block variance is the \(T_1^{(3)}\)-family, dead by
Proposition BB;
(d) *interval-splitting* of \(\{\Theta\}\) into \(R\) cells
needs \(R \gtrsim kC \asymp P^{27/16}\) for the per-cell
freezing error, and its \(\ell^1\)-mass is \(R\) — the mass
equals the amplitude, and refactoring the cell sums merely
rederives the moving window. \(\square\)

The obstruction covers the carry-free case: even for blocks with
\(s \equiv 0\), where everything is an explicit smooth monomial,
mechanisms I and II apply verbatim. This matches the Phase-19
census: resonant (carry-regular) blocks cancel like the bulk, so
the cancellation mechanism in the data was never rotation
entropy — it is fine self-equidistribution of the monomial
against its own amplitude window, which no tool reaches.

### Conjecture HH (the pure amplitude-product model)

Let \(A(t), B(t)\) be smooth monomial-type functions on
\([0, L]\) with \(1 \ll A' \ll A\) (in the Juggler instance
\(A = \tfrac34 k\mu^{9/8}\), \(B = \mu^{9/4}\), \(\mu\) affine;
\(A \asymp P^{27/16}\), \(A' \asymp P^{11/16}\)). Then

\[
\Bigl|\sum_{t \le L} e\bigl(A(t)\,\{B(t)\}\bigr)\Bigr|
\;\le\; L^{1-\delta}.
\]

This is the minimal crystal of the whole \(K_3\) program: every
Juggler-specific structure (carries, defects, nesting) has been
stripped, and what remains is the amplitude-product exponential
sum. The boundary of the known is exactly \(A' \asymp 1\): for
\(A' \ll 1\) partial summation factors the amplitude out (the
"tame passenger" regime the engine and the Piatetski–Shapiro
literature use); for \(A' \gg 1\) nothing in the toolkit or the
literature applies (Beatty/bilinear results treat bounded
amplitudes on the sawtooth terms). Census
(`pure_model_census`, exact scaled integers, OBSERVATION):

| \(P\) | \(L\) | blocks | mean \(R\) | median \(R\) | frac \(R>4\) |
| --- | --- | --- | --- | --- | --- |
| \(10^6\) | 31 | 300 | 0.99–1.01 | 0.67–0.76 | 1.7–3.3% |
| \(10^8\) | 100 | 300 | 0.86–1.08 | 0.60–0.80 | 0.3–2.0% |
| \(10^{10}\) | 316 | 120 | 1.01–1.06 | 0.63–0.82 | 1.7–2.5% |

A textbook \(\mathrm{Exp}(1)\) profile at \(k = 1, 2\): the
model cancels at the square-root scale. Conjecture HH is
empirically comfortable and analytically untouched.

### Phase-20 decision

**PARK** the intra-block harmonic program (Proposition GG,
ledger row `J-intra-block-harmonic-obstruction`). With
Proposition BB (global toolkit) and GG (intra-block program),
both known proof routes to \(K_3\) are now closed by named,
mechanism-level obstructions; Conjectures V, EE and HH stay
open, all with strong empirical support. The transport
reformulation retains its value — Lemmas DD/FF are exact and
reduced the problem to its crystal — but the analytic frontier
is now precisely Conjecture HH, a self-contained exponential-sum
problem (ledger row `J-pure-model-amplitude-product`,
CONJECTURE). The unconditional harvest of the branch (Theorems
C/E/L/Q/R/S/T/X, Corollaries U/Y: every depth-\(\le 4\) class,
the depth-5 and length-7 contracting splits, certified descent
\(57/64\), the conditional density-one theorem) is final for
this program unless HH moves. Flags
`intra_block_harmonic_parked`,
`pure_model_cancellation_observed`;
`depth5_kernel_bound_proved` and `density_one_claimed` stay
`False`. No note import, no commit.

## Part XVIII: Conjecture HH outside the harmonic toolkit — the shift average and the de-randomization gap (Phase 21)

Scope: attack Conjecture HH by non-harmonic methods. Outcome:
one genuine non-harmonic theorem (Lemma II), which explains the
Exp(1) censuses quantitatively; and a three-prong obstruction
(Proposition JJ) showing that closing the remaining gap — the
single point \(\lambda = 0\) — is outside every tool the
laboratory has. No deterministic HH claim, no \(K_3\) bound.

### Lemma II (shift-averaged square-root cancellation). EXACT — HUMAN PROOF

**Statement.** Let \(A_1 < \dots < A_L\) be reals with
\(|A_t - A_{t'}| \ge A'_{\min}|t - t'|\) for some
\(A'_{\min} \ge 1\), and let \(x_1, \dots, x_L\) be *arbitrary*
reals. For \(S_\lambda = \sum_{t \le L} e(A_t\{x_t + \lambda\})\):

\[
\Bigl|\;\int_0^1 |S_\lambda|^2\,d\lambda \;-\; L\;\Bigr|
\;\le\; \frac{6}{\pi}\,\frac{L}{A'_{\min}}\,(\log L + 1).
\]

In particular \(|S_\lambda| \le \sqrt{L/\varepsilon}\) outside a
shift set of measure \(\varepsilon(1 + o(1))\), and the mean of
\(|S_\lambda|^2/L\) tends to 1 — two-sided: the shifted family
can be neither worse nor systematically better than square-root.

**Proof.** Expand the square; the diagonal gives \(L\). For
\(t \ne t'\), \(\varphi(\lambda) = A_t\{x_t + \lambda\} -
A_{t'}\{x_{t'} + \lambda\}\) is piecewise linear on \([0,1)\)
with *real* slope \(A_t - A_{t'}\) on at most three arcs (jumps
at \(1 - \{x_t\}\), \(1 - \{x_{t'}\}\)); on each arc
\(|\int e(\varphi)| \le 1/(\pi|A_t - A_{t'}|)\). Summing,
\(\sum_{t \ne t'} 3/(\pi A'_{\min}|t - t'|) \le
(6/\pi)(L/A'_{\min})(\log L + 1)\). \(\square\)

No characters are expanded anywhere: the mechanism is amplitude
separation alone — \(A' \gg 1\), the very property that kills
every harmonic method (GG-I), is exactly what makes the shift
average trivial. The hypothesis does not mention \(B\): the
census's \(\mathrm{Exp}(1)\) mean is forced for generic shifts
regardless of the argument sequence. The deterministic content
of Conjecture HH is therefore precisely the single point
\(\lambda = 0\).

Validation (`shift_average_probe`, 64 shifts × 100 blocks):
mean \(R\) over shifts \(= 1.0042\) (\(P = 10^6\)) and
\(0.9961\) (\(P = 10^8\)) against the prediction
\(1 \pm 0.0003\) resp. \(1 \pm 0.00002\), within the sampling
noise \(0.0125\).

### Proposition JJ (the de-randomization obstruction). EXACT — HUMAN PROOF

No tool in the laboratory transfers Lemma II to \(\lambda = 0\):

**(i) No second averaging variable.** Amplitude separation
forces any two sample points with \(|A(p) - A(q)| \le 1\) to
satisfy \(|p - q| \le 1/A'_{\min} < 1\): the only lattice
direction along which the amplitude freezes is the trivial one.
Every family average available in the application (block index,
integer base \(\mu_0\), the \(k\)-family) re-enters the
\(T_1\)-family or the amplitude-product class itself
(Propositions BB, GG, CC).

**(ii) Inverse self-similarity.** Any concentration or
discrepancy inverse for \(x_t = A_t\{B_t\} \bmod 1\) — e.g.
deriving a contradiction from \(|S| \ge L/\log\) via arc
concentration — is a statement about \(\sum_t e(j\,x_t)\),
which is the same class with amplitude \(jA\): the class is
closed under its own inverse theory, so no bootstrapping is
possible.

**(iii) Metric non-transfer.** \(|dS_\lambda/d\lambda| \le
2\pi A_{\max} L\) a.e., so \(S_\lambda\) decorrelates at shift
scale \(1/A_{\max} \asymp P^{-27/16}\) (measured: increments
\(0.06\)–\(0.08\sqrt L\) at \(\delta = 0.1/(2\pi A)\),
\(0.57\)–\(0.74\sqrt L\) at \(1/(2\pi A)\), saturated at ten
times that). An almost-all-\(\lambda\) statement leaves
\(\asymp \varepsilon A_{\max}\) bad cells among
\(\asymp A_{\max}\); no measure-theoretic argument pins
\(\lambda = 0\). \(\square\)

The species of the residual problem is now identified: HH at
\(\lambda = 0\) is a *specific-point-in-metric-theory* problem —
the same gap as "almost every \(\alpha\) is normal" versus "is
\(\sqrt2\) normal". The only known successes in that species use
special arithmetic. The Juggler instance does carry special
arithmetic the crystal forgets — \(A^2 = \tfrac{9}{16}k^2 z\)
with \(z\) integer, and \(A\) is algebraically coupled to the
argument via \(\theta_3 = v^{3/2} - z\) — but its natural
exploitations (the pure-phase identity, quadratic-field
periodicity) re-enter the harmonic toolkit and die by GG-II(b).

### Phase-21 decision

**PARK** the \(K_3\)/HH line at the de-randomization frontier.
The line now ends in a complete, three-layer characterization:
Proposition BB (global toolkit), Proposition GG (intra-block
harmonic program), Proposition JJ (metric-to-deterministic
transfer) — with the generic truth of HH *proven* (Lemma II)
and its deterministic instance open. Ledger rows
`J-shift-average-square-root` (EXACT — HUMAN PROOF) and
`J-derandomization-obstruction` (EXACT — HUMAN PROOF); flags
`pure_model_shift_average_proved`, `hh_derandomization_parked`;
`depth5_kernel_bound_proved` and `density_one_claimed` stay
`False`. Conjectures V, EE, HH stay open. No note import, no
commit. The natural next work is editorial: the finite-dynamics
note still carries the stale \(13/16\) headline and Conjecture
6.2, and the branch's final state (harvest + three obstructions
+ the crystal + Lemma II) deserves consolidation.

## Part XIX: the length-8 engine quartet — breaking the density ceiling without \(K_3\) (Phase 23)

Phase 22 consolidated the branch into the note at certified
density \(57/64\). Phase 23 re-examined the frontier itself and
found two things: an overclaim introduced during consolidation,
and a provable depth-8 ring the \(K_3\) fixation had hidden.

**The overclaim (fixed).** The consolidated note asserted "every
uncounted contracting itinerary passes through \(OOOO*\)". False:
\(OOEOOOEE\) (five odd letters, \(3^5 = 243 < 256 = 2^8\)) is
contracting, contains no \(OOOO\) factor, and was uncounted —
only its length-7 prefix was (Theorem X). The sentence is
corrected in both copies of the note; the fix is subsumed by the
theorem below, which counts that itinerary.

**The observation.** The six counted expanding length-7
cylinders (Theorem X) have exactly four contracting length-8
children — appending \(E\) to the four five-odd words:

\[
OOEOOEOE,\quad OOEOOOEE,\quad OOOEOEOE,\quad OOOEOOEE
\]

(the two six-odd words \(OOEOOOO\), \(OOOEOOO\) need length
\(\ge 10\)). Each has \(3^5 = 243 < 256\): a uniform eight-step
descent certificate. The eighth letter is the parity of
\(x_8 = J^7(n)\), and the itineraries interleave enough even
letters that the full seven-level linearization chain of its
phase argument stays **subcritical** — no letter of the quartet
sees a kernel.

### Lemma AA1 (the four eighth-letter chains). EXACT — HUMAN PROOF

Write \(x_1 = n\), \(x_{t+1} = \lfloor x_t^{3/2}\rfloor\) on odd
letters, \(x_{t+1} = \lfloor x_t^{1/2}\rfloor\) on even letters,
following each word; let \(X_7\) be the real number with
\(x_8 = \lfloor X_7 \rfloor\) (so \(X_7 = x_7^{3/2}\) when the
seventh letter is \(O\), \(x_7^{1/2}\) when it is \(E\)). Then
for each quartet parent, expanding every level by the two-term
Taylor identity with one-signed second-order remainder
(\(|E| < 1\) for \(n \ge 51\)),

\[
X_7 \;=\; n^{243/128} \;-\; \sum_{i} B_i(n)\,\theta_i \;+\; E,
\]

where each \(\theta_i \in [0,1)\) is the floor defect at level
\(i\) and every coefficient \(B_i\) is **subcritical**: the
complete inventory of growing coefficients is

| parent | growing coefficients \(B_i\) |
| --- | --- |
| \(OOEOOEO\) | \(\tfrac{27}{16}x_3^{11/32} \asymp n^{99/128}\), \(\tfrac32 x_6^{1/4} \asymp n^{81/128}\), \(\tfrac{81}{64}n^{51/128}\), \(\tfrac98 x_4^{3/16} \asymp n^{27/128}\) |
| \(OOEOOOE\) | \(\tfrac{27}{16}x_3^{11/32} \asymp n^{99/128}\), \(\tfrac{81}{64}n^{51/128}\), \(\tfrac98 x_4^{3/16} \asymp n^{27/128}\) |
| \(OOOEOEO\) | \(\tfrac32 x_6^{1/4} \asymp n^{81/128}\), \(\tfrac{81}{64}n^{51/128}\), \(\tfrac98 x_4^{1/16} \asymp n^{27/128}\) |
| \(OOOEOOE\) | \(\tfrac{81}{64}n^{51/128}\), \(\tfrac98 x_4^{1/16} \asymp n^{27/128}\) |

(all remaining coefficients decay in \(n\)). The largest
coefficient anywhere is \(\asymp n^{99/128}\), with drift
\(\asymp n^{-29/128} < 1\): every sawtooth admits drift-one
windows of length \(\ge n^{29/128}\).

*Proof.* Word-by-word composition of the two-term Taylor
identities \((Y-\theta)^p = Y^p - pY^{p-1}\theta + E_p\) at the
exponents \(p \in \{\tfrac{81}{64}, \tfrac{27}{32},
\tfrac{27}{16}, \tfrac98, \tfrac{9}{16}, \tfrac34, \tfrac32,
\tfrac12\}\) dictated by the letters, with
\(E_p = \tfrac{p(p-1)}2 \xi^{p-2}\theta^2\) one-signed
(positive for \(p > 1\), negative for \(p < 1\)) and bounded by
the stated envelopes. The key structural fact is that the even
letters interpose square roots that keep every intermediate
exponent below \(2\) — no state on these itineraries reaches the
\(\lfloor \cdot^{3/2}\rfloor\)-map at scale \(> n^{9/4}\), so no
coefficient reaches \(n\), in contrast to \(OOOO*\) where the
fifth-letter coefficient is \(n^{27/16}\cdot k\) (Lemma V1).
\(\square\)

Validation: `eighth_letter_chain_check` verifies the hardest
composite identity (\(OOEOOEO\), six levels, scale \(10^{30}\))
exactly, residual inside the one-signed envelope on 46 samples
through \(n = 3\cdot10^7 + 1\), measured coefficient exponents
all \(< 1\) (max \(0.91\) at small \(n\), decreasing toward
\(99/128 = 0.773\)).

### Theorem AA (the length-8 engine quartet). ROUTE (withdrawn Phase 26)

For each \(w\) in the quartet,
\(\#\{n \le N : n \in C_w\} = 2^{-8}N + O(N^{1-1/48+\varepsilon})\).

*Proof sketch (Theorem Q/T/X pattern).* The class indicator is
the product of the eight half-wave factors; letters one through
seven are the counted Theorem-X classes. The eighth wave
expands in Vaaler modes \(e((k/2)X_7)\), \(k \le J_8\). By
Lemma AA1 the mode phase is a fixed chirp
\((k/2)n^{243/128}\) minus subcritical sawtooth terms. On each
sawtooth, split into drift-one windows (length \(\ge
n^{29/128}\)), expand the product against the frozen window
centre; the centre value recombines with the chirp, and the
residual modes carry curvature \(\le T\cdot n^{-7/8}\) with
window budget \(T = P^{1/16}\), subdominant to the chirp
curvature \(\lambda \asymp k n^{-13/128}\). Intersecting the
(at most four) window systems leaves intervals of length
\(L_0 \ge n^{29/128} \gg \lambda^{-1/2}\); van der Corput II
gives \(L_0\lambda^{1/2} + \lambda^{-1/2} \ll
k^{1/2}n^{45/256}\) per interval — summed over the
\(\asymp P^{99/128}\) intervals,
\(|S_k| \ll k^{1/2} P^{243/256}\). Truncating at
\(J_8 = P^{13/384}\) balances the majorant \(P/J_8\):
total \(O(P^{1-13/384+\varepsilon})\), stated as
\(O(N^{1-1/48+\varepsilon})\) without optimization. The
passenger waves (letters two through seven) carry the budgets
already established in Theorems S/T/X; every new cross term is
subcritical by Lemma AA1. \(\square\)

Validation: `depth8_quartet_census` (\(N = 2\cdot10^5\) and
\(10^6\)): all four classes within \(1.8\) normalized deviations
of \(N_{\mathrm{odd}}/128\), zero descent violations.
`depth8_mode_probe` (\(k = 1, 2, 3\)): eighth-wave mode sums on
all four parents at ratio \(0.002\)–\(0.045\) of cylinder size
at \(N = 2\cdot10^5\), shrinking to \(0.006\)–\(0.011\) at
\(N = 10^6\) — square-root scale.

### Corollary AB (certified descent density 29/32). ROUTE (withdrawn Phase 26)

The quartet words each carry the uniform certificate
\(J^8(n) < n\) (\(3^5 < 2^8\), Corollary 2.3). Adding their
densities \(4 \cdot 2^{-8} = 1/64\) to Corollary Y:

\[
\frac{57}{64} + \frac1{64} \;=\; \frac{29}{32}
\]

of all starts admit a descent certificate of length at most
eight. The leftover \(3/32\) is: the \(OOOO*\) tree (\(1/16\),
blocked at its root by \(K_3\)), the expanding \(O\)-children of
the quartet splits (\(4/256\)), and the two six-odd trees
\(OOEOOOO*\), \(OOOEOOO*\) (\(4/256\)).

### The structural law exposed

The quartet is not an accident. An odd letter applied at state
scale \(n^\sigma\) produces a kernel coefficient \(\asymp
n^{\sigma/2}\); the engine plus Theorem R′ covers
\(\sigma/2 \le 9/8\), i.e. \(\sigma \le 9/4\). Even letters
halve \(\sigma\), odd letters multiply it by \(3/2\): the
blocked roots are exactly the \(O\)-heavy prefixes that push an
odd state past \(n^{9/4}\) — \(OOOO\) (state \(n^{27/8}\),
coefficient \(n^{27/16}\): Lemma V1) and its deeper analogues —
while every \(E\)-interleaved word stays countable. The
non-\(OOOO\) leftover therefore thins at every depth
(a geometric tail of engine theorems), whereas the \(OOOO\) tree
(\(1/16\)) is monolithically blocked by \(K_3\). The certified
density can be pushed beyond \(29/32\) by more engine work with
strictly diminishing increments, but never past
\(1 - 1/16 - (\text{deeper blocked roots})\) without \(K_3\).

### Phase-23 decision

**PROMOTE.** Theorem AA and Corollary AB enter the note as
Theorem 5.16 and the extended Corollary 5.17 (certified-descent
densities \(7/8\), \(57/64\), \(29/32\)); the overclaim sentence
is replaced by the exact leftover decomposition. Ledger rows
`J-depth8-engine-quartet` and `J-eight-step-descent-density`
(both EXACT — HUMAN PROOF); flags
`depth8_engine_quartet_proved`, `depth8_chains_subcritical`.
`depth5_kernel_bound_proved` and `density_one_claimed` stay
`False`: nothing here touches \(K_3\), and the structural law
says the \(OOOO\) tree is where the remaining \(1/16\) lives.

## Part XII: length-5 passenger repair (Phase 27)

Scope: close the two named Phase-26 holes in Theorem T against the
Phase-26 kernel (Paper B Lemma 5.2 and Theorem 6.1). Not a Paper B
edit. Not \(K_3\). Not length 7/8. Not Corollary R′.

### Slot classification (OOOE\*)

The Phase-24 draft called the fifth-letter \(X\)-modes “ordinary
first-letter passengers of Theorem S, strictly smaller than the
\(i\le P^{1/24}\) budget.” After Phase 26 that comparison is the
wrong slot: Theorem 6.1 budgets \(|i|\le 2P^{1/96}\), and
Lemma 5.2(ii) budgets decorations \(|q'|\le P^{1/16}\). The modes
are neither.

Lemma T1 writes the fifth-letter phase as the smooth chirp
\(\tfrac l2 n^{27/16}\) minus the sawtooth \(C\theta\),
\(C=\tfrac{9l}{16}n^{3/16}\). Lemma 3.7 expands \(e(-C\{X\})\) into
modes \(e(uX)\). Those are first-letter monomials, i.e. the
\(r\)-modes of Lemma 5.2 Stage 2 (families \(e(r\nu^{3/2})\) with
truncation \(R_0=P^{1/4}\)), not (D1) \(Y\)-wave decorations.

Truncate the fifth letter at \(J_5=2P^{1/96}\) (the Theorem 6.1
layer). Then \(l\le 2P^{1/96}\) and
\[
|C|\le\tfrac98\cdot 2\,P^{1/96+3/16}=O\bigl(P^{19/96}\bigr).
\]
Lemma 3.7 with \(T=R_0=P^{1/4}\) satisfies
\(T\ge 8(1+|C|)\): \(8P^{19/96}/P^{24/96}=8P^{-5/96}\to 0\). The
produced modes have \(|u|\le P^{1/4}\), exactly Stage 2’s existing
budget. The draft’s \(T=P^{1/8}\) violated Lemma 3.7
(\(P^{1/8}\ll P^{3/16}\)); that choice is discarded.

The \(|q'|\le P^{1/16}\) cap is the kernel’s own \(Y\)-wave range
(\(J_2=P^{1/24}\) after differencing), not a structural obstruction
for \(X\)-modes. Shrinking \(J_5\) cannot fit \(lP^{3/16}\) into
that cap (\(l_{\max}P^{3/16}\le P^{1/16}\) forces \(l<1\)); the
repair is the correct slot, not an enlarged decoration.

### Theorem 6.1 Steps D–E at the enlarged \(i\)-range

Write \(I_{\mathrm{tot}}\) for the combined first-letter index:
Theorem 6.1’s own \(|i|\le 2P^{1/96}\) plus the fifth-letter
\(|u|\le P^{1/4}\). The combined range is \(|I_{\mathrm{tot}}|\le P^{1/4}\).

- *Step D, \(i\)-passenger.* \(\Delta\Delta(\tfrac i2 X)\) has
  second derivative \(\le 2.3\,|i|h_1h_2P^{-5/2}\). At
  \(|i|\le P^{1/4}\) and \(h_1h_2=P^{1/16}\) this is
  \(O(P^{1/4+1/16-5/2})=O(P^{-35/16})\), inside class (D3)
  (\(|\varphi''|\le 3kh_1h_2P^{-5/8}\)) by
  \(P^{-35/16}/P^{1/16-5/8}=P^{-2}\). The fifth-letter chirp
  \(\tfrac l2 n^{27/16}\), after the same double difference, is
  likewise (D3):
  \(h_1h_2\cdot l\cdot P^{27/16-4}=O(P^{1/16+1/96-37/16})\).
- *Step D, \(j\)-passenger and \(q_d\).* The fifth letter does not
  enlarge \(j\) or the \(Y\)-wave frequencies. The written bound
  \(|q_d|\le 3P^{1/24}+P^{1/96}\le P^{1/16}\) is unchanged.
- *Step E, composites.* An \(X\)-mode is smooth. It does not enter
  the kernel \(\theta\)-coefficient \(B\). The offset composite
  \(405/512\) (ratio \(7:4\)) and the zero-offset curvature
  \(8.27\,kh_1h_2\nu^{-5/8}\) are therefore the Phase-26 values.
  The (D3) curvature of the new modes is dominated at the same
  Stage-E ratios already displayed (\(\le P^{-1/4}\) against
  \(\lambda_a'\ge 0.72P^{-1/8}\)).
- *Lemma 5.2 Stage 5.* Modes with \(|u|\le P^{1/4}\) are a subset
  of the Stage-2 family already bounded by \(3R_0^{1/2}P^{3/4}\log P
  =3P^{7/8}\log P\). Collision-band mass stays \(O(\log P)\).
- *Flat cost of Lemma 3.7.* Per point
  \(8(1+|C|)/T=O(P^{19/96-1/4})=O(P^{-5/96})\); over a block
  \(O(P^{1-5/96})\), inside Theorem 6.1’s \(P^{1-1/96}\) budget.
  Fifth-letter Vaaler majorant \(4P/J_5=O(P^{1-1/96})\).

Theorem 6.1 therefore applies to every fifth-letter decorated
\(OOOE*\) mode sum, uniformly in \(|l|\le 2P^{1/96}\). Hence
\[
\#\mathrm{OOOEE}(N),\;\#\mathrm{OOOEO}(N)
=\tfrac N{32}+O\bigl(N^{1-1/96+\varepsilon}\bigr).
\]

### OOEO\*: \(\lambda_2\) after Lemma 3.10

The Phase-24 curvature
\[
\lambda_2
=\Bigl(-\tfrac{297k}{1024}+\tfrac{27k}{128}+O(T_wP^{-7/8})
+O(JP^{-1/2})\Bigr)n^{-5/16}
\]
has leading combination \(-297/1024+216/1024=-81/1024=-0.079k\neq 0\).
Lemma 3.10(a): under \(n=2r+1\), every derivative scales by the
same power of \(2\), so curvature *ratios* and *signs* are
invariant. The single-sign check and the dominance of the
\(T_w\)- and \(J\)-errors (\(O(P^{-5/8})\), \(O(P^{-3/8})\) against
\(kn^{-5/16}\)) survive without adjustment. Lemma 3.10(b): the
\(n\)-variable van der Corput display
\(L_B\lambda_2^{1/2}+\lambda_2^{-1/2}\) dominates the reindexed
bound. The window-centre cancellation of the two \(\theta\)
coefficients is algebraic (Lemmas T1/T2) and is not a Jacobian
statement.

The rest of the Phase-10 OOEO\* argument is unchanged: it never
used Lemma 5.2 decorations. Hence
\[
\#\mathrm{OOEOE}(N),\;\#\mathrm{OOEOO}(N)
=\tfrac N{32}+O\bigl(N^{43/48+\varepsilon}\bigr).
\]

### Theorem T (repaired) — EXACT — HUMAN PROOF

The two displays above. Indicator identities and the decaying
remainders of Lemmas T1/T2 are the Phase-10 exact statements
(`oooee_indicator_identity_check`, `ooeoe_indicator_identity_check`,
`oooee_smoothing_scan`, `ooeoe_smoothing_scan`).

### Corollary U (repaired) — EXACT — HUMAN PROOF

The class of starts carrying a uniform power-envelope descent
certificate of length at most five — evens, OE, OOEE, OOOEE,
OOEOE — has natural density \(7/8\). Densities
\(\tfrac12+\tfrac14+\tfrac1{16}+\tfrac1{32}+\tfrac1{32}=\tfrac78\).
The cylinders are Theorem T. The contraction \(3^3<2^5\) is
`J-power-envelope-contraction`. Not a density of starts that reach
\(1\). Imported into Paper B as Corollary 6.4.

### Phase-27 decision

**PROMOTE** the length-5 repair. Ledger rows `J-depth5-contracting`
and `J-five-step-descent-density` retagged `EXACT — HUMAN PROOF`.
Flag `depth5_contracting_proved` flipped `True`. Length 7/8 and
Corollary R′ stay `CONJECTURE`. No Paper B edit. No \(K_3\).
The single next question is Corollary R′ at one concrete
\(\alpha\neq 9/8\) (the intended consumer was \(\alpha=33/32\)).

## Part XIII: Theorem R at \(\alpha=33/32\) (Phase 28)

Scope: rerun Paper B Theorem 5.3 at the single monomial family
\(\alpha=33/32\), against the Phase-25/26 kernel (Lemmas 3.8–3.10
and 5.1–5.2 as printed). Not the full Corollary R′ interval. Not
length 7/8. Not a Paper B edit. Not a bound for \(\alpha>9/8\)
(`J-scale-invariant-R-extension` remains **REFUTED**).

The Phase-24 slogan (“every constraint is monotone in \(\alpha\)”)
is discarded. Every standing estimate, window drift, and dominance
margin is re-derived below. The only new analytic cost is the
exponent pair \(\bigl(\tfrac54,\tfrac{41}{32}\bigr)\), which sits
at distance \(1/32\): Lemma 3.8’s \(c_6\) is \(1/55\), still
positive, and is absorbed by the existing ineffective \(P_0\).

Write \(c=\tfrac{3k}4 n^{33/32}\) on a dyadic block \(n\sim P\),
odd, with \(1\le k\le P^{1/24}\). The same \(H_1=P^{1/48}\),
\(H_2=P^{1/24}\) as Theorem 5.3. Then
\(kh_1h_2\le P^{5/48}\). Signs follow the monomial pattern
(\(c>0\), \(c'>0\), \(c''>0\)).

### Standing estimates at \(\alpha=33/32\)

\[
\begin{aligned}
c'&=\tfrac{99k}{128}\,n^{1/32},&
c''&=\tfrac{99k}{4096}\,n^{-31/32},\\
\Delta_ic&=2h_ic'(\xi)\in(1.54,\,1.59)\,kh_iP^{1/32},\\
\Delta\Delta c&=4h_1h_2c''(\xi)\in(0.049,\,0.097)\,kh_1h_2P^{-31/32}.
\end{aligned}
\]
Call these (E3)\(^\dagger\)–(E4)\(^\dagger\). The printed (C1)
\(kh_1h_2\le P^{1/8}\) still holds, with slack
\(P^{5/48}/P^{1/8}=P^{-1/48}\); the \(\alpha\)-accurate sufficient
condition is the weaker \(kh_1h_2\le P^{7/32}\). Lemma 5.1 and
(E1)–(E2), (E5) are independent of \(c\). The printed Lemma 5.2
applies *a fortiori*: its (D2)–(D3) Stage-6 dominances are upper
bounds on \(|c|\), \(|c'|\), \(|c''|\), and each of those is
strictly smaller than the \(\alpha=9/8\) size used to prove the
lemma (\(33/32<9/8\), \(1/32<1/8\), \(-31/32<-7/8\)). The main
curvature of Lemma 5.2 is a \(Y\)-wave, independent of \(c\).

Sign product of (E6), at \(\beta\in\{1/4,3/4\}\):
\[
\alpha(\alpha-1)(\alpha+\beta-2)(\alpha+\beta-3)
=\tfrac{33}{32}\cdot\tfrac{1}{32}\cdot(\tfrac{33}{32}+\beta-2)
\cdot(\tfrac{33}{32}+\beta-3).
\]
Both last factors stay negative (\(\alpha+\tfrac14-2=-23/32\),
\(\alpha+\tfrac34-2=-7/32\)), the first two stay positive, and
no factor vanishes (\(\alpha\neq1\), \(\alpha\neq 2-\beta\),
\(\alpha\neq 3-\beta\)). Product positive, same pattern as
\(\alpha=9/8\).

### Steps 1–4

*Step 1.* Unchanged: \(|K_c|^2\le 2P^2/H_1+(4P/H_1)\sum|T_1|\)
and likewise for \(T_1\), and it is enough to prove
\(|T_2|\ll P^{23/24+\varepsilon}\).

*Step 2.* \(|M_1|\le 0.10\,kh_1h_2P^{-31/32}\), so deleting
\(M_1\) costs \(\ll kh_1h_2P^{1/32}\le P^{13/96}\), inside
\(P^{23/24}\).

*Step 3a.* \(B=\Delta_2c(n{+}d_1)\in(1.54,1.59)\,kh_2P^{1/32}\),
with \(|B'|\le 0.10\,kh_2P^{-31/32}\). Freeze on windows where
\(B\) moves by \(\le P^{-1/8}\) (the printed residual): at most
\(2kh_2P^{5/32}{+}1\) windows, residual
\(\sum|e((B{-}B_0)\{W\})-1|\le 6.3P^{7/8}\). Lemma 3.7 at
\(T=P^{1/2}/(2h_1)\), \(J=P^{1/4}\):
\(|B|\le P^{11/96}\) and
\(T\ge\tfrac12 P^{23/48}\ge 8(1+|B|)\) for \(P\ge P_0\).
Flat cost \(\le 16h_1P^{1/2}+16\,kh_1h_2P^{1/2+1/32}
\le 16P^{25/48}+16P^{61/96}\). Modes satisfy
\(uh_1\le P^{13/96}+P^{1/2}/2\le P^{1/2}\), so every mode is a
Lemma 5.2(i) object. Window boundaries cost
\(\le 2kh_2P^{5/32}\cdot 3.4P^{3/8}\le 7P^{17/32+1/12}
=7P^{59/96}\).

*Steps 3b–3e.* \(|(\Delta_2c)''|\le 0.05\,kh_2P^{-63/32}\) sits
inside the printed (D3) box \(3kh_1h_2P^{-5/8}\) (ratio
\(\le P^{-11/32}/h_1\)). Likewise \(|c''|\ll kP^{-31/32}\) is
strictly inside (D3). The expansion inventory, mode species, and
anchor-present-in-every-piece organization are those of
Theorem 5.3.

*Step 4.* Independent of \(\alpha\): wave pieces
\(\ll P^{23/24+\varepsilon}\). Resonant \(t=0\) remnants are
(D1) decorations of Step 5.

### Step 5a (offset branches)

On an offset branch, \(cF=\tfrac98\,kj\,\nu^{57/32}(1+O(P^{-1/4}))\).
The smooth second derivative is
\(\tfrac{12825}{8192}\,kj\,\nu^{-7/32}\). The window-centre
coefficient is \(B=\tfrac9{16}kj\,\nu^{9/32}(1+O(P^{-1/4}))\),
so \(uX''=-\tfrac{27}{64}\,kj\,\nu^{-7/32}\). Composite
\[
\lambda_a=\tfrac{9369}{8192}\,k|j|\,n^{-7/32}\,(1+O(P^{-1/4}))
\in[0.8,\,1.4]\,k|j|P^{-7/32}
\]
for \(P\ge P_0\). The two terms have ratio
\(12825:3456=3.711\), single-signed (the printed \(9/8\) ratio
was \(4.375\)). Competitors against
\(\lambda_a\ge 0.8\,P^{-7/32}\):

- differenced-wave \(\le 0.51P^{-1/4}\), ratio
  \(\le 0.64\,P^{-1/32}\);
- resonant (D1) \(\le 6P^{-19/16}\), ratio
  \(\le 8P^{-31/32}\);
- slow modes \(\le 3P^{1/24}P^{-5/4}\), ratio
  \(\le 4P^{-95/96}\);
- (D3) \(\le 3P^{1/16}P^{-1/2}\), ratio
  \(\le 4P^{-7/32}\).

All \(\to 0\). The \(\theta\)-sawtooth has coefficient
\(\tfrac9{16}k|j|P^{9/32}\)-scale: at most
\(1.2k|j|P^{9/32}{+}1\) windows. Collision band: Lemma 3.8 at
the pair \(\bigl(\tfrac{57}{32},\tfrac32\bigr)\) (distinct;
zeros of the affine test at \(s=1\) and \(s=7/16\neq 1\)),
scale \(M\asymp k|j|P^{-7/32}\). Band total
\(\ll (k|j|)^{1/2}P^{57/64}\log P\). Main estimate Lemma 3.3
per frozen run: run lengths \(\ge\tfrac1{22}P^{1/4}/(|j|{+}1)\)
and \(\lambda_a^{-1/2}\ll P^{7/64}\) is shorter than a run
(\(7/64<16/64\)). Assembly
\[
\sum_{\mathrm{runs}}\bigl(\ell\lambda_a^{1/2}+\lambda_a^{-1/2}\bigr)
\le 1.3\,(k|j|)^{1/2}P^{57/64}
+O\bigl(k^{-1/2}P^{55/64}\bigr).
\]
At \(k\le P^{1/24}\):
\((k)^{1/2}P^{57/64}\le P^{175/192}<P^{23/24}=P^{184/192}\).
The printed \(9/8\) bottleneck \((k)^{1/2}P^{15/16}=P^{23/24}\)
is slack here.

### Step 5b (zero-offset)

\(cF_{\mathrm{sm}}=\tfrac{81k}{16}h_1h_2\nu^{41/32}(1+O(hP^{-1}))\),
and
\[
2c'F_{\mathrm{sm}}'+c\,F_{\mathrm{sm}}''
=\tfrac{1701}{1024}\,kh_1h_2\,\nu^{-23/32}(1+O(hP^{-1})).
\]
Thus \(\lambda_0\in[0.8,\,4]\,kh_1h_2P^{-23/32}\). The
\(\theta\)-coefficient at \(j=0\) is
\(|B|\le 1.2\,kh_1h_2P^{-7/32}\le 1.2P^{-11/96}<1\): still
sub-unit. Three regimes as printed, with the comparisons
reset to \(\lambda_0\asymp kh_1h_2P^{-23/32}\).

- *Anchor-dominant* (\(60\mu\le\lambda_0\)): Lemma 3.3 per run.
  \(\sum\ell\lambda_0^{1/2}\le (kh_1h_2)^{1/2}P^{41/64}
  \le P^{133/192}\).
- *Mode-dominant* (\(\mu\ge 60\lambda_0\), i.e.
  \(uh_1\ge 60\,kh_2P^{1/32}\)): Lemma 5.2(i) with the
  undifferenced anchor as decoration. The threshold
  \(P^{1/32}\) is *lower* than the printed \(P^{1/8}\), so
  more of the range is mode-dominant. Anchor run-boundary
  cost \(\le 75P^{11/16}\) as printed.
- *Middle band.* The interpolant is the printed construction
  with the new \(c\). Leading monomials
  \[
  \Phi(\nu)=a\,\nu^{5/4}+b\,\nu^{41/32}+w\,\nu^{3/2},
  \]
  exponents
  \(\bigl\{\tfrac54,\tfrac{41}{32},\tfrac32\bigr\}
  =\bigl\{\tfrac{40}{32},\tfrac{41}{32},\tfrac{48}{32}\bigr\}\)
  pairwise distinct. Extend the printed set to
  \(E^\dagger=E\cup\bigl\{\tfrac{41}{32},\tfrac{57}{32}\bigr\}\).
  Lemmas 3.8–3.9 apply to any finite set of pairwise distinct
  exponents away from \(2\); their proofs never use the
  specific list except through \(c_6(E)\) and \(c_7(E)\).

  For the close pair \(\bigl(\tfrac54,\tfrac{41}{32}\bigr)\):
  the affine zeros are \(s=1\) and
  \(s=\tfrac{24}{23}\). The intersection computation gives
  \(c_6=1/55>0\). The third-derivative zero \(s=24/23\)
  lies outside the transition
  \(s\in\bigl(\tfrac{54}{55},\tfrac{56}{55}\bigr)\), so
  \(|nf'''|\ge c_6|A|\) throughout that transition. The
  three-term Vandermonde on
  \(\bigl\{-\tfrac34,-\tfrac{23}{32},-\tfrac12\bigr\}\) is
  invertible, hence \(c_7(E^\dagger)>0\). Both constants
  are smaller than the printed \(c_6(E)\), \(c_7(E)\); the
  paper already takes \(P_0\) ineffective, and
  \(\rho_0(E^\dagger)\le\min(c_6,c_7)/8\) still absorbs the
  \(O(P^{-1/4})\) interpolant errors for \(P\ge P_0\).

  On a dyadic block the ratio \(n^{-1/32}\) varies by only
  \(2^{-1/32}\), so the Lemma 3.8 region \(I_0\) may be the
  whole block. That does not kill the estimate: \(\Omega_V\)
  is still measured by Lemma 3.9. Interpolant error
  \(|f''-\Lambda|\ll kP^{-31/32}\) (the printed
  \(P^{-9/8}\) replacement is \(P^{-39/32}\) here). Scale
  \[
  S=\max\bigl(|uh_1{+}u'h_2|P^{-3/4},\,
  kh_1h_2P^{-23/32},\,|w|P^{-1/2}\bigr),
  \]
  and the middle-band constraints give
  \(S\ge cP^{-23/32}\) whenever \(kh_1h_2\ge 1\), with
  \(S\le CP^{-23/32}\) on the collision band (or the
  conservative printed ceiling \(300P^{-1/2}\)). The same
  choice \(V=3S^{1/2}P^{-11/24}\) satisfies
  \(V\ge 10|f''-\Lambda|\) and \(V\le c_7S/2\) for
  \(P\ge P_0\). Then \(V/S\ll P^{-19/192}\), so
  \[
  |\Omega_V|\ll P(V/S)+P(V/S)^{1/2}
  \ll P^{173/192}+P^{365/384},
  \]
  and \(365/384<23/24=368/384\). Piece-boundary and
  Lemma 3.3 costs are at most this large. The middle band
  totals \(\ll P^{365/384+\varepsilon}\ll P^{23/24}\).

### Step 6 and the instance

Additive costs improve or match the printed list (\(M_1\)
deletion is \(P^{13/96}\) instead of \(P^{1/4}\); window
residuals still \(P^{7/8}\); majorants unchanged). Piece
totals: Step 4 as printed; Step 5a at \(P^{175/192}\);
Step 5b at \(P^{365/384}\). Hence
\(|T_2|\ll P^{23/24+\varepsilon}\) and
\(|K_c|\ll P^{1-1/96+\varepsilon}\), uniformly in
\(k\le P^{1/24}\).

### Theorem R at \(\alpha=33/32\) — EXACT — HUMAN PROOF

Let \(c\) be smooth on \((P,2P]\) with
\(c^{(r)}\asymp kP^{33/32-r}\) for \(r=0,\ldots,4\),
derivative signs following the monomial pattern
(e.g. \(c=\tfrac{3k}4 n^{33/32}\)), and
\(1\le k\le P^{1/24}\). Then
\[
K_c(P)\ll P^{1-1/96+\varepsilon},
\]
uniformly in \(k\).

This is the intended consumer of the withdrawn Corollary R′.
The family-for-all-\(\alpha\) claim
(`J-w-family-below-nine-eighths`) stays `CONJECTURE`: each
other target \(\alpha\) needs its own exponent set and its
own \(c_6\). Length 7 still has the growing remainder
\(\tfrac{45}{32}v^{1/8}\asymp n^{9/32}\).

### Phase-28 decision

**PROMOTE** the \(\alpha=33/32\) instance. Ledger row
`J-w-family-thirty-three-thirty-seconds` tagged
`EXACT — HUMAN PROOF`. Flag `w_family_alpha_33_32_proved`
flipped `True`. The Corollary R′ family, length 7/8, and
Paper B stay as they were. No \(K_3\). The single next
question is the length-7 remainder: can \(kE\) with
\(E\asymp v^{1/8}\) be kept as a subcritical extra phase
and estimated, now that the \(\alpha=33/32\) \(W\)-family
is a theorem?

## Part XIV: the length-7 remainder is an engine (Phase 29)

Scope: keep \(kE_X\) in the phase and estimate it. Not
Theorem X. Not the passenger inventory. Not length 8. Not a
Paper B edit.

On the OO prefix, \(v=\lfloor m^{3/2}\rfloor\) with
\(m=\lfloor n^{3/2}\rfloor\), so \(v\asymp n^{9/4}\) and
\(v^{1/8}\asymp n^{9/32}\). Lemma X1 splits
\[
E_X=E_p+E_w,\qquad
E_p=\tfrac38\xi_p^{-1/2}\theta_p^2\le\tfrac38 p^{-1/2},
\qquad
E_w=\tfrac{45}{32}\xi_w^{1/4}\theta_w^2\le\tfrac{45}{32}v^{1/8}.
\]
\(E_p\asymp n^{-27/32}\) decays: discarding \(kE_p\) costs
\(\ll kP^{5/32}\). The growing piece is \(E_w\), and
\(\xi_w=v^{1/2}+O(1)\) gives
\(E_w=\tfrac{45}{32}v^{1/8}\theta_w^2+O(n^{-27/32})\).
The OOOEO remainder of Lemma X2 is already
\(\le\tfrac38 U^{-1/2}\asymp n^{-9/16}\) and is not this hole.

### Reduction to a smooth argument

\[
v=n^{9/4}-\tfrac32 n^{3/4}\theta_2+O(n^{-3/4}),
\]
hence
\[
v^{1/2}=n^{9/8}-\tfrac34 n^{-3/8}\theta_2+O(n^{-9/8}),
\qquad
v^{1/8}=n^{9/32}+O(n^{-39/32}).
\]
Thus \(\theta_w=\{v^{1/2}\}=\{n^{9/8}+\varepsilon\}\) with
\(\varepsilon\ll n^{-3/8}\). Off the \(O(n^{-3/8})\)-neighbourhood
of the integers (density \(O(n^{-3/8})\), trivial cost
\(P^{5/8}\)),
\[
\theta_w=\{n^{9/8}\}-\tfrac34 n^{-3/8}\theta_2+O(n^{-9/8}),
\]
and the cross term in \(\theta_w^2\) produces, after multiplying
by \(k n^{9/32}\), a discarded cost \(\ll kP^{29/32}\le P^{91/96}\)
at \(k\le P^{1/24}\). Seal: `x1_remainder_reduction_scan`.

The extra phase is therefore
\[
kE_X=A\,\{n^{9/8}\}^2+\text{decaying},\qquad
A=\tfrac{45}{32}k\,n^{9/32}(1+O(n^{-3/2})).
\]
It is *not* a (D3) decoration: \(\lvert(A\{n^{9/8}\}^2)''\rvert\)
is not \(O(kh_1h_2P^{-5/8})\). It is *not* a reason to discard
(\(\lvert e(kE)-1\rvert P\asymp kP^{1+9/32}\) is worse than
trivial). It *is* an engine of amplitude \(A\ll n\) in a smooth
argument of exponent \(9/8\), with
\((n^{9/8})'\asymp n^{1/8}\gg1\) and
\((n^{9/8})''\asymp n^{-7/8}<1\).

### Lemma X4 (quadratic-sawtooth engine) — EXACT — HUMAN PROOF

Let \(1\le\lvert k\rvert\le P^{1/24}\) and let \(A\) be as
above. Write \(F(x)=e(A\{x\}^2)\). Then \(F\) is \(1\)-periodic,
\(\lvert F\rvert=1\), and the jump at the integers is
\(1-e(A)\), of size \(\le2\). The Fourier coefficients satisfy
\[
\lvert\hat F(u)\rvert\ll\lvert A\rvert^{-1/2}+\lvert u\rvert^{-1}
\qquad(u\neq0)
\]
by the Fresnel / van der Corput bound on
\(\int_0^1 e(Ax^2-ux)\,dx\) (second derivative \(2A\),
stationary point in \((0,1)\) iff \(u\in(0,2A)\)). Consequently,
for odd \(n\sim P\),
\[
\Bigl\lvert\sum_n e(kE_X(n))\Bigr\rvert
\ll P^{27/32+\varepsilon}.
\]

*Proof.* Expand \(F(n^{9/8})=\sum_u\hat F(u)\,e(un^{9/8})\).
Lemma 3.3 at curvature \(u\cdot\tfrac9{64}n^{-7/8}\) gives
\[
\Bigl\lvert\sum_n e(un^{9/8})\Bigr\rvert
\ll\lvert u\rvert^{1/2}P^{9/16}+\lvert u\rvert^{-1/2}P^{7/16}.
\]
Truncate at \(U_\ast\asymp\lvert A\rvert\asymp kP^{9/32}\)
(beyond this, \(\lvert\hat F(u)\rvert\ll\lvert u\rvert^{-1}\)
and the tail is a majorant of cost \(\ll P/U_\ast\)). The
two leading sums are
\[
\lvert A\rvert^{-1/2}\cdot\lvert A\rvert^{3/2}P^{9/16}
=\lvert A\rvert P^{9/16}\ll kP^{27/32},
\]
\[
P^{9/16}\lvert A\rvert^{1/2}\ll k^{1/2}P^{45/64}.
\]
At \(k\le P^{1/24}\) both are
\(\le P^{85/96}\) and \(\le P^{139/192}\), inside
\(P^{23/24}=P^{184/192}\). Lemma 3.10 does not change the
margins. \(\square\)

As a factor in an ambient sum the same expansion attaches
only engine modes \(e(un^{9/8})\) with
\(\lvert u\rvert\ll kP^{9/32}+T\). Each is Lemma 3.3 at
\(\ll P^{13/16}\) after the usual Lemma-3.7 window
\(T=P^{1/2}\) (hypothesis \(T\ge8(1+\lvert A\rvert)\):
\(\lvert A\rvert\le P^{31/96}<P^{1/2}\)). This is the class
the Phase-13 draft already named (“remaining
\(\theta_2\)-amplitudes are \(O(n^{9/32})\), engine”),
except the argument is the *smooth* \(n^{9/8}\), not a
nested floor.

Whether every host in the Theorem X inventory absorbs the
extra frequency \(\lvert u\rvert\le P^{31/96}\) is a
passenger rerun, not this hole.

### Phase-29 decision

**PROMOTE** the remainder estimate. Ledger row
`J-length7-remainder-engine` tagged `EXACT — HUMAN PROOF`.
Flag `length7_remainder_engine_proved` flipped `True`.
`J-depth7-engine-contracting` stays `CONJECTURE` (passenger
inventory not rerun). No density \(57/64\). No Paper B.
No \(K_3\). The single next question is the length-7
passenger rerun: do the sixth-letter \(X\)-modes and the
new \(n^{9/8}\)-frequencies sit in Lemma 5.2 / Theorem T’s
existing budgets?

## Part XIX: length-7 passengers miss Stage 2 (Phase 34)

Scope: rerun the Phase-13 slogan “Theorem T applies as a
passenger theorem” against the Phase-26/27 slots (Lemma 5.2
Stage 2, \(R_0=P^{1/4}\); Theorem 6.1 / Part XII
\(\lvert I_{\mathrm{tot}}\rvert\le P^{1/4}\); (D1)
\(\lvert q'\rvert\le P^{1/16}\); (D3)
\(\lvert\varphi''\rvert\le 3kh_1h_2P^{-5/8}\)). Not a new
estimate. Not length 8. Not a Paper B edit. Not \(K_3\).

The two named species, and the first-letter chirp that the
same slogan also absorbs, are classified below. Every
comparison is at \(1\le\lvert k\rvert\le P^{1/24}\).

### \(\theta_p\) is not an \(X\)-mode

Lemma X1 leaves the sawtooth
\(-\tfrac32 kw^{3/4}\theta_p\) with
\(\theta_p=\{w^{3/2}\}\) and \(w\asymp n^{9/8}\). The
coefficient is
\[
B\asymp k n^{27/32}\le P^{1/24+27/32}=P^{85/96}.
\]
Already at \(k=1\), \(\lvert B\rvert\asymp P^{27/32}>P^{1/4}\).
Lemma 3.7 requires \(T\ge 8(1+\lvert B\rvert)\asymp P^{27/32}\);
the Phase-13 window \(T\ll P^{27/32}\) is the length-5
\(T=P^{1/8}\) error at a new scale. The produced modes have
\(\lvert u\rvert\le\lvert B\rvert+T\asymp P^{27/32}\), which
exceeds Stage 2’s \(R_0=P^{1/4}\) by \(P^{19/32}\).

The argument is \(w^{3/2}\). On the OO prefix,
\(w^{3/2}=v^{3/4}+O(v^{1/4})=n^{27/16}+O(n^{9/16})\), not
\(X=n^{3/2}\). These are \(n^{27/16}\)-chirps, not
Lemma 5.2 Stage-2 families \(e(r\nu^{3/2})\). They are not
(D1) \(Y\)-waves (\(27/16\neq 9/4\)). Lemma 3.3 at
curvature \(u\cdot n^{-5/16}\) costs
\(u^{1/2}P^{27/32}\ge P^{81/64}>P\) at the natural
\(\lvert u\rvert\asymp P^{27/32}\): the existing
second-derivative test is worse than trivial.

### The Phase-29 frequencies are not Stage 2 either

Lemma X4 attaches engine modes \(e(un^{9/8})\) with
\(\lvert u\rvert\ll kP^{9/32}\le P^{31/96}\). Now
\(P^{31/96}>P^{1/4}=P^{24/96}\), and \(9/8\neq 3/2\).
Against (D3),
\(\lvert(un^{9/8})''\rvert\asymp uP^{-7/8}\le P^{-53/96}\),
while the printed box at \(h_1h_2=1\) is
\(P^{-5/8}=P^{-60/96}\). The modes sit outside every
Phase-27 slot. (The isolated sum \(\sum e(kE_X)\) remains
Lemma X4; the failure is the *passenger* citation.)

### The first-letter chirp is the same mismatch

Lemma A/M on \(v^{9/8}\) produces the smooth chirp
\(e(Cn^{3/2})\) with \(C\asymp kn^{33/32}\le P^{1/24+33/32}=P^{103/96}\).
This is an \(X\)-type phase whose coefficient already
exceeds \(R_0\). Lemma 3.3 at curvature \(CP^{-1/2}\asymp
P^{17/32}\) costs \(C^{1/2}P^{3/4}=P^{81/64}>P\). The
Phase-13 “van der Corput II” is not Lemma 3.3 and is not
in the Phase-27 budget.

The \(\alpha=33/32\) \(W\)-family piece sits
(`J-w-family-thirty-three-thirty-seconds`). The OOOEO
remainder of Lemma X2 still decays. Neither saves the
slogan.

### Proposition X-pass (no Theorem-T passenger) — REFUTED method

The claim that the length-7 sixth letter is a tame
passenger of Theorem T / Lemma 5.2 Stage 2 is **REFUTED**.
The Phase-13 comparisons (“\(X\)-modes smaller than
Theorem T’s budget”, “Theorem T therefore applies”) are
the same wrong-slot slogan Phase 27 discarded at length 5,
at larger exponents. The counts are not refuted.

### Phase-34 decision

**PARK** Theorem X. Ledger row
`J-length7-passenger-theorem-t` tagged `REFUTED`. Flag
`length7_passenger_theorem_t_refuted` flipped `True`.
`J-depth7-engine-contracting` stays `CONJECTURE`. No
density \(57/64\). No vdC-III campaign. No Paper B.
No \(K_3\). The single next question is whether a
third-derivative van der Corput on the two chirps
\(e(un^{27/16})\) and \(e(Cn^{3/2})\) closes them inside
\(P^{23/24}\) without a new decoration class.

## Part XX: isolated length-7 chirps by one A-process (Phase 35)

Scope: the two isolated monomials named in Phase 34, plus a
decoration check. Not Theorem X. Not a new decoration class
(no Lemma 3.11). Not length 8. Not a Paper B edit. Not
\(K_3\). Not the Phase-1 third-derivative test on
\(\theta\)-frozen short cells, and not the Phase-9 per-run
third-derivative on mixed frozen-floor \(\times\) \(X\)-mode
pieces (those summed to the trivial bound).

The tool is the Paper B \(A\)-process already displayed after
Lemma 3.3, followed by Lemma 3.3 itself. No third-derivative
black box is imported.

### The derived third-derivative bound

Let \(f\) be \(C^3\) on a dyadic block of odd integers of
length \(\asymp P\), with \(f'''\) of constant sign and
\(\lambda\le\lvert f'''\rvert\le\alpha\lambda\) for an
absolute \(\alpha\). The Paper B \(A\)-process at even
shifts \(2h\), \(1\le H\le P\), produces inner phases
\(g(n)=f(n+2h)-f(n)\) with
\(\lvert g''\rvert\asymp h\lambda\). Lemma 3.3 then gives
\[
\lvert S\rvert^2
\ll\frac{P^2}H+P^2(H\lambda)^{1/2}+P(H\lambda)^{-1/2}.
\]
Balancing the first two terms at \(H=\lambda^{-1/3}\)
(admissible on both ranges below) yields
\[
\lvert S\rvert
\ll P\lambda^{1/6}+P^{1/2}\lambda^{-1/6}.
\]
The second term is the square-root of the third; it is
strictly smaller than the first on both chirps.

### The two isolated sums

All comparisons are at \(1\le\lvert k\rvert\le P^{1/24}\),
sums over odd \(n\sim P\).

**Lemma X5 (isolated sixth-letter chirps) — EXACT — HUMAN PROOF.**

(i) If \(\lvert u\rvert\le P^{85/96}\), then
\[
\Bigl\lvert\sum e\bigl(u n^{27/16}\bigr)\Bigr\rvert
\ll P^{535/576}.
\]
At the natural size \(\lvert u\rvert\asymp P^{27/32}\) the
same argument gives \(P^{177/192}\).

(ii) If \(\lvert C\rvert\le P^{103/96}\), then
\[
\Bigl\lvert\sum e\bigl(C n^{3/2}\bigr)\Bigr\rvert
\ll P^{535/576}.
\]
At the natural size \(C\asymp P^{33/32}\) the bound is
again \(P^{177/192}\).

Both are strictly inside \(P^{23/24}=P^{184/192}=P^{552/576}\).

*Proof of (i).* Write \(f(n)=u n^{27/16}\). Then
\(f'''(n)=u\cdot\tfrac{27}{16}\cdot\tfrac{11}{16}\cdot\bigl(-\tfrac{5}{16}\bigr)n^{-21/16}\)
is single-signed, and on \((P,2P]\) the ratio
\(\sup\lvert f'''\rvert/\inf\lvert f'''\rvert=2^{21/16}\)
is absolute. Thus \(\lambda\asymp\lvert u\rvert P^{-21/16}\).
The window \(H=\lvert u\rvert^{-1/3}P^{7/16}\) satisfies
\(1\le H\le P\) throughout \(\lvert u\rvert\le P^{85/96}\)
(since \(85/96<21/16\)). The main term is
\[
P\lambda^{1/6}
=\lvert u\rvert^{1/6}P^{25/32}.
\]
At \(\lvert u\rvert=P^{27/32}\) this is \(P^{177/192}\); at
\(\lvert u\rvert=P^{85/96}\) it is \(P^{535/576}\). The
inverse term is \(P^{111/192}\) and \(P^{329/576}\)
respectively. Lemma 3.10 does not change the display: the
\(A\)-process is already the odd-\(n\), even-shift form.

*Proof of (ii).* Now \(f(n)=C n^{3/2}\) and
\(f'''(n)=-\tfrac38 C n^{-3/2}\), ratio \(2^{3/2}\) on the
block. Thus \(\lambda\asymp\lvert C\rvert P^{-3/2}\) and
\(H=\lvert C\rvert^{-1/3}P^{1/2}\), admissible up to
\(\lvert C\rvert\le P^{103/96}<P^{3/2}\). The main term is
\(\lvert C\rvert^{1/6}P^{3/4}\), the same two exponents as
in (i). \(\square\)

The two natural sizes are the same leading phase
\(n^{81/32}\): \(u n^{27/16}\) at \(\lvert u\rvert\asymp
n^{27/32}\), and \(C n^{3/2}\) at \(C\asymp n^{33/32}\).

### The reduction is not a decoration

On the OO prefix,
\[
w^{3/2}
=v^{3/4}+O(v^{1/4}),
\qquad
v=n^{9/4}-\tfrac32 n^{3/4}\theta_2+O(n^{-3/4}),
\]
so
\[
v^{3/4}
=n^{27/16}-\tfrac98 n^{3/16}\theta_2+O(n^{-21/16}).
\]
The leftover amplitude after writing
\(e(u w^{3/2})=e(u n^{27/16})e(\psi)\) is
\(\lvert u\rvert n^{3/16}\). At \(\lvert u\rvert\asymp
P^{27/32}\) this is \(P^{33/32}>n\); at the uniform end
\(P^{85/96}\) it is \(P^{103/96}>n\). The spawned
coefficient has derivative
\(\lvert u\rvert n^{-13/16}\asymp P^{1/32}\to\infty\).
This is the Phase-5 wall (coefficient \(>n\), derivative
\(\gg 1\)). It is not (D1) (\(\lvert q'\rvert\le P^{1/16}\))
and not (D3) (\(\lvert\varphi''\rvert\le 3kh_1h_2 P^{-5/8}\)).
A hypothesis \(\lvert\varphi'''\rvert\ll\lvert f'''\rvert\)
would be a new decoration class; it is not written.

The first-letter chirp \(e(C n^{3/2})\) is already smooth
in \(n\). Its companions in the Lemma A/M expansion of
\(v^{9/8}\) (the \(\alpha=33/32\) \(W\)-family, the
\(O(n^{9/32})\) engine, the integer-\(w\) block, the
seventh letter) are separate species, not decorations of
this chirp. Keeping them in the same exponential would
again require a new class.

### Affine \(w^{3/2}\) on X3-runs is not this theorem

Lemma X3 freezes \(\lfloor\Delta U\rfloor\) on runs of
length \(\asymp P^{7/8}\). On each such run,
\(w=w_0+Jt+\kappa_w\) with \(J\) frozen and
\(\kappa_w\in\{0,1\}\). The isolated affine phase
\(u(w_0+Jt)^{3/2}\) has the same third-derivative size as
\(u n^{27/16}\). One \(A\)-process per run (the window
\(H=P^{5/32}\) at \(k=1\) is \(\ll P^{7/8}\)) plus a
triangle over \(\ll P^{1/8}\) runs recovers the same
exponents \(P^{177/192}\) and \(P^{535/576}\). The
\(0\)-\(1\) carry is not (D1) or (D3): a carry jumps the
phase by \(\lvert u\rvert w^{1/2}\asymp P^{45/32}\). That
object is the existing Theorem Q / R3 pattern at the
\(w\)-level, not a decoration of Lemma X5, and is not
estimated here. Isolated \(\sum e(u n^{27/16})\) is
therefore not the \(\theta_p\) inventory sum
\(\sum e(u w^{3/2})\).

### Phase-35 decision

**PROMOTE** the isolated chirp bounds. Ledger row
`J-length7-vdc3-chirps` tagged `EXACT — HUMAN PROOF`.
Flag `length7_vdc3_chirps_proved` flipped `True`.
`J-depth7-engine-contracting` stays `CONJECTURE`: the
actual \(\theta_p\) sum is \(e(u w^{3/2})\), the reduction
is not an existing decoration, and the integer-\(w\)
block, seventh letter, and assembly are unrerun. No
density \(57/64\). No Lemma 3.11. No Paper B. No \(K_3\).
The single next question is whether \(e(u w^{3/2})\) on
Lemma X3 runs, with the \(0\)-\(1\) carry treated by the
Theorem Q / R3 pattern, closes inside \(P^{23/24}\)
without a new decoration class.

## Part XXI: X3-runs plus the Q/R3 carry miss \(e(uw^{3/2})\) (Phase 37)

Scope: the actual \(\theta_p\) inventory sum
\(\sum e(u w^{3/2})\), on Lemma X3 runs, with \(\kappa_w\)
read as a Theorem Q / R3 indicator. Not Theorem X. Not a
new decoration class. Not length 8. Not a Paper B edit.
Not \(K_3\). Isolated Lemma X5 stands.

All comparisons at \(1\le\lvert k\rvert\le P^{1/24}\),
\(\lvert u\rvert\asymp P^{27/32}\) up to \(P^{85/96}\).

### Three readings of “Q/R3 at the \(w\)-level”

Lemma X3 freezes \(J=\lfloor\Delta U\rfloor\) on runs of
length \(\asymp P^{7/8}\). It does not freeze
\(\kappa_w=\Delta w-J\in\{0,1\}\). On the OO prefix,
\(U=v^{1/2}\asymp n^{9/8}\) has \(U'\asymp P^{1/8}\gg 1\),
so \(\{U\}\) rotates by \(\{\Delta U\}\) each odd step and
\(\kappa_w=[\{\,U\,\}\ge 1-\{\Delta U\}]\) is a mechanical
word. Seal: `w_carry_run_scan` at \(P=10^4,10^5,10^6\)
gives \(J\)-runs covering the whole window of \(400\)
OOEO terms, \(\kappa\in\{0,1\}\), and mean \(\kappa\)-run
\(2.26\), \(1.64\), \(1.88\).

**Affine interpolant on \(\kappa\)-constant sub-runs.**
The Phase-35 \(A\)-process window is
\(H=\lvert u\rvert^{-1/3}P^{7/16}\), hence
\(H\asymp P^{5/32}\) at \(k=1\). A \(C^3\) interpolant
with frozen slope \(J+\kappa\) needs \(\kappa\)-constant
length \(\ge H\). Mean length \(O(1)\) does not grow with
\(P^{5/32}\). Long \(\kappa\)-runs occur only when
\(\{\Delta U\}\) is small, which is the wrap of \(\Delta U\)
— exactly where \(J\) itself thaws. This is the Phase-1
short-cell third-derivative failure and the Phase-9
per-run collapse, at a new letter.

**Indicator weight / moving-endpoint (Theorem C, Lemma R3).**
Vaaler-expand \(\kappa_w\) as an arc in \(\{U\}\). The
modes are \(e(rU)\asymp e(r n^{9/8})\). Rewriting
\(w=\lfloor U\rfloor=U-\theta_U\) puts
\[
e(u w^{3/2})
=e(u U^{3/2})\,e(-B\theta_U)\,e(E),
\qquad
B=\tfrac{3u}2 U^{1/2}\asymp\lvert u\rvert n^{9/16}.
\]
At \(\lvert u\rvert\asymp P^{27/32}\) one has
\(B\asymp P^{45/32}>n\) and
\(B'\asymp\lvert u\rvert n^{-7/16}\asymp P^{13/32}\gg 1\).
Lemma 3.7 needs \(T\ge 8(1+\lvert B\rvert)\asymp P^{45/32}>P\).
This is the Phase-5 wall (Theorem Q’s own engine line
\(c'\asymp 1\)). Conditioning on the carry *sequence* in
an \(A\)-process window produces \(2^H\) branches.

**Discard the accumulated carry on an X3-run.**
Write \(w=w_0+Jt+K(t)\) with \(K\asymp t/2\asymp P^{7/8}\).
The phase error is
\(\lvert u\rvert w^{1/2}K\asymp P^{73/32}\). After one
\(A\)-process, \(K_h\le H\) still costs
\(\lvert u\rvert w^{1/2}H\asymp P^{25/16}\). Neither is
a (D1) or (D3) decoration.

### Proposition X-carry (no Q/R3 carry for \(\theta_p\)) — REFUTED method

The claim that \(\sum e(u w^{3/2})\) closes inside
\(P^{23/24}\) by Lemma X3 plus the Theorem Q / R3 carry
pattern, without a new decoration class, is **REFUTED**.
Isolated Lemma X5 is not this sum. A hypothesis
\(\lvert\varphi'''\rvert\ll\lvert f'''\rvert\) would be
a new class; it is not written. The counts are not
refuted.

### Phase-37 decision

**PARK** Theorem X. Ledger row
`J-length7-x3-qr3-carry` tagged `REFUTED`. Flag
`length7_x3_qr3_carry_refuted` flipped `True`.
`J-length7-vdc3-chirps` stays `EXACT — HUMAN PROOF`.
`J-depth7-engine-contracting` stays `CONJECTURE`. No
density \(57/64\). No Lemma 3.11. No Paper B. No
\(K_3\). The existing-toolkit route for the \(\theta_p\)
inventory is closed. The single next question is whether
the Phase-13 integer-\(w\) block \(e(\xi w)\) with
\(\xi\asymp n^{45/32}\) independently sits below the
engine line on X3-runs, or is the same Phase-5 wall.

## Part XXII: the integer-\(w\) block is the Phase-5 wall (Phase 38)

Scope: the Phase-13 integer block \(e(\xi w)\) with
\(\xi\asymp n^{45/32}\), independently of
\(e(uw^{3/2})\). Not Theorem X. Not another rewriting of
\(\theta_p\). Not length 8. Not a Paper B edit. Not
\(K_3\). Isolated Lemma X5 stands.

Lemma X1 writes
\[
p^{3/2}
=-\tfrac54 v^{9/8}+\tfrac94 w\,v^{5/8}
-\tfrac32 w^{3/4}\theta_p+E_X.
\]
The integer coefficient is
\(\xi=\tfrac{9k}4 v^{5/8}\asymp kn^{45/32}\), already
\(>n\) at \(k=1\). Lemma X1’s own remark is that the
*naive* \(\theta_w\) coefficient
\(\tfrac94 v^{5/8}\asymp n^{45/32}>n\) is gone after
the rearrangement. Splitting \(e(\xi w)\) off from
\(-\tfrac54 kv^{9/8}\) reinstates that coefficient.

### Three independent readings, one wall

All comparisons at \(1\le\lvert k\rvert\le P^{1/24}\).

**Sawtooth \(e(-\xi\{U\})\).** Write \(w=\lfloor U\rfloor
=U-\theta_U\). Then
\(e(\xi w)=e(\xi U)\,e(-\xi\theta_U)\). The sawtooth
has coefficient \(\xi\asymp P^{45/32}>n\) and
derivative \(\xi'\asymp P^{13/32}\gg 1\). Lemma 3.7
needs \(T\ge 8(1+\lvert\xi\rvert)\asymp P^{45/32}>P\).
This is Theorem Q’s engine line (the Phase-5 wall), at
the same exponent Phase 37 recorded for
\(B=\tfrac{3u}2 U^{1/2}\).

**Dual sawtooth \(e(w\{\xi\})\).** Since \(w\in\mathbb Z\),
\(e(\xi w)=e(w\{\xi\})\). The coefficient is now
\(w\asymp n^{9/8}>n\), with \(w'\asymp n^{1/8}\gg 1\).
Same wall, dual variables.

**X3-run plus Q/R3.** On a run of length
\(\asymp P^{7/8}\), \(\xi\) itself drifts by
\(\xi'P^{7/8}\asymp P^{41/32}\gg 1\): the frequency is
not frozen. The slogan “\(e(\xi J)\) a smooth chirp”
fails before the carry. The carry \(\kappa_w\) is still
the Phase-37 mechanical word of mean run \(O(1)\).
Discarding \(K\asymp P^{7/8}\) costs phase
\(\xi K\asymp P^{73/32}\).

The smooth interpolant \(e(\xi U)\) is
\(e\bigl(k v^{9/8}\bigr)\), of size \(n^{81/32}\). That
is the first-letter chirp already estimated as an
isolated monomial by Lemma X5, and already worse than
trivial for Lemma 3.3 (\(P^{81/64}\)). It is not a new
species and it is not the integer block.

### Proposition X-int (no engine-line integer-\(w\)) — REFUTED method

The claim that \(e(\xi w)\) with \(\xi\asymp n^{45/32}\)
sits below the engine line on Lemma X3 runs is
**REFUTED**. It is the naive \(\theta_w\) coefficient
Lemma X1 eliminated, independently of \(e(uw^{3/2})\).
The counts are not refuted.

The OOOEO sibling \(e(\eta s)\) with
\(\eta\asymp n^{27/32}<n\) is *not* this hole: after a
Theorem Q expansion it produces the same
\(n^{27/16}\)-chirps at \(\lvert u\rvert\asymp P^{27/32}\)
already treated in Parts XIX–XXI. It is not an escape
and is not opened here.

### Phase-38 decision

**PARK** Theorem X. Ledger row
`J-length7-integer-w-block` tagged `REFUTED`. Flag
`length7_integer_w_engine_line_refuted` flipped `True`.
`J-depth7-engine-contracting` stays `CONJECTURE`. No
density \(57/64\). No Lemma 3.11. No Paper B. No
\(K_3\). Do not reopen \(e(uw^{3/2})\) and do not
rewrite the \(45/32\) coefficient. The existing-toolkit
route for the OOEOO sixth letter is closed. The single
next question is the length-8 \(E'\) hole, a different
door.

## Part XXIII: the length-8 remainder decays — discard is legal (Phase 40)

Scope: \(E\) and \(E'\) on the four length-8 quartet
parents. Not Theorem AA. Not Theorem X. Not a Paper B
edit. Not \(K_3\). Not another rewriting of
\(e(uw^{3/2})\). Isolated Lemma AA1 stands.

Lemma AA1 writes
\[
X_7=n^{243/128}-\sum_i B_i(n)\,\theta_i+E,
\]
with \(|E|<1\) for \(n\ge 51\). Phase 26 discarded \(E\)
at that crude size: Vaaler cost \(J_8P=P^{1+13/384}\)
wipes the eighth-letter saving. Keeping \(e(kE)\) at the
same crude size needs \(E'\), which was not written.
The AA1 proof already names one-signed second-order
envelopes. Phase 40 records the rate and the discard
cost.

### The six Taylor remainders on \(OOEOOEO\)

Write \(x_1=n\) and follow the letters \(OOEOOEO\). The
floor identities \(x_{t+1}=Y_t-\theta_t\) are exact; the
only remainders are the Taylor tails
\(E_p=\tfrac{p(p-1)}{2}\xi^{p-2}\theta^2\) of the power
maps that reassemble \(X_7=x_7^{3/2}\). Expanding the
main monomial level by level:

\[
\begin{align*}
E^{(6)}
&=\tfrac38\xi_7^{-1/2}\theta_6^2
\ll x_7^{-1/2}\asymp n^{-81/128},\\
E^{(5)}
&=\tfrac{3}{32}\xi_6^{-5/4}\theta_5^2
\ll x_6^{-5/4}\asymp n^{-405/128},\\
E^{(4)}
&=\tfrac{9}{128}\xi_5^{-7/8}\theta_4^2
\ll x_5^{-7/8}\asymp n^{-189/128},\\
E^{(3)}
&=\tfrac{297}{512}\xi_4^{-5/16}\theta_3^2
\ll x_4^{-5/16}\asymp n^{-45/128},\\
E^{(2)}
&=\tfrac{135}{2048}\xi_3^{-37/32}\theta_2^2
\ll x_3^{-37/32}\asymp n^{-333/128},\\
E^{(1)}
&=\tfrac{1377}{8192}\xi_2^{-47/64}\theta_1^2
\ll x_2^{-47/64}\asymp n^{-141/128}.
\end{align*}
\]

These are the six envelopes already in
`eighth_letter_chain_check`. The leading term is
\(E^{(3)}\), from
\((x_3^{1/2}-\theta_3)^{27/16}\). Every other tail is
strictly smaller.

Bilinear cross terms from expanding a coefficient
\(B_i\) through an earlier floor are of the form
\((\partial B_i/\partial x_j)\theta_i\theta_j\). The
largest is
\(\tfrac{27}{16}\cdot\tfrac{11}{32}x_3^{-21/32}
\asymp n^{-189/128}\), below the leading tail. There is
no extra floor remainder to amplify: \(x_{t+1}=Y_t-\theta_t\)
exactly.

### The other three parents

\(OOEOOOE\) shares the prefix \(OOEOO\) and the main
monomial \(x_4^{27/16}\). Its last step is a square root
(\(X_7=x_7^{1/2}\)), whose tail is
\(\ll n^{-567/128}\). The leading remainder is again
\(E^{(3)}\asymp n^{-45/128}\).

\(OOOEOEO\) and \(OOOEOOE\) apply the third letter as
\(O\), so \(x_4=x_3^{3/2}\). Their largest written tails
are the last-step \(n^{-81/128}\) and the first-step
\(n^{-141/128}\), both smaller than \(n^{-45/128}\).

Thus on every quartet parent
\[
\lvert E\rvert\ll n^{-45/128}.
\]
The crude bound \(\lvert E\rvert<1\) for \(n\ge 51\) is
the corollary \(51^{-45/128}<1\) plus a constant.

### Drift

The leading term is \(C(n)\theta_3^2\) with
\(C\asymp n^{-45/128}\) and
\(\theta_3=\{x_3^{1/2}\}\), so
\(\theta_3'\asymp n^{1/8}\). Hence
\[
\lvert E'\rvert\ll n^{-45/128+1/8}=n^{-29/128}<1.
\]
Floor jumps change \(E\) by at most the envelope
\(n^{-45/128}\), which is finer than this scale. The
other tails give strictly smaller formal derivatives
(worst sibling: last-step \(n^{-47/128}\)).

### Discard is legal; crude discard stays dead

On the Phase-23 range \(1\le\lvert k\rvert\le J_8=P^{13/384}\),
\[
k\lvert E\rvert\ll P^{13/384-45/128}=P^{-61/192}\to 0.
\]
So \(e(kE)=1+O(kE)\). The Vaaler cost of replacing
\(e(kE)\) by \(1\) is
\[
\sum_{k\le J_8}\frac1k\cdot k\lvert E\rvert P
=J_8\lvert E\rvert P\ll P^{131/192}.
\]
This sits strictly inside the eighth-letter majorant
\(P^{243/256}\) and the engine line \(P^{23/24}\). The
same range has \(k\lvert E'\rvert\to 0\), so even a keep
reading is a decaying phase — discard is the right
description.

The crude size \(\lvert E\rvert<1\) still costs
\(J_8P=P^{1+13/384}\), worse than trivial. The slogan
“\(\lvert E\rvert<1\) is enough” remains a dead method.
The hole was the missing rate, not a missing \(E'\)
class.

Validation: `eighth_remainder_rate_scan` on the
\(OOEOOEO\) formal chain. Residuals lie inside the
one-sided envelopes with **no slack** on every odd
\(n\in[51,299]\) and at \(n=10^4+1\), \(10^6+1\), and
through a 200-term window at \(10^6\) (max
\(\lvert E\rvert n^{45/128}=0.57\), max
\(\lvert\Delta E/2\rvert n^{29/128}=0.03\)); spot checks
through \(n=3\cdot 10^7+1\) stay inside.

### Lemma AA2 (remainder rate) — EXACT — HUMAN PROOF

On each quartet parent, \(\lvert E\rvert\ll n^{-45/128}\)
and \(\lvert E'\rvert\ll n^{-29/128}<1\). Discarding
\(e(kE)-1\) on \(k\le P^{13/384}\) costs
\(\ll P^{131/192}\). The Phase-26 \(E'\) hole is closed
as a method hole. The counts are not promoted.

### Phase-40 decision

**PROMOTE** Lemma AA2. Ledger row
`J-length8-remainder-discard` tagged
`EXACT — HUMAN PROOF`. Flag
`length8_remainder_discard_proved` flipped `True`.
`J-depth8-engine-quartet` stays `CONJECTURE` (inherits
Theorem X). No density \(29/32\). No Paper B. No
\(K_3\). Do not reopen \(E'\) and do not reopen the
length-7 sixth-letter rewrites. The length-8 remainder
door is closed. Theorem AA is blocked only by Theorem X,
whose existing-toolkit route is closed.

## Part XXIV: the harvest counting program is terminal (Phase 41)

Scope: whether any attack on the Theorem X leftover
\(\sum e(u w^{3/2})\) sits outside the killed toolkit, or
whether the harvest counting program is terminal. Not a
new estimate. Not a rewriting of \(45/32\). Not Theorem X.
Not Theorem AA. Not a Paper B edit. Not \(K_3\). Isolated
Lemmas X4, X5, AA2 stand.

The leftover is one object. Lemma X1 leaves the sawtooth
\(-\tfrac32 k w^{3/4}\theta_p\) with
\(\theta_p=\{w^{3/2}\}\) and \(w\asymp n^{9/8}\). After
Vaaler, the inventory sum is
\(\sum e(u w^{3/2})\) at
\(1\le\lvert u\rvert\le P^{85/96}\) (natural size
\(P^{27/32}\)).

### Finite laboratory vocabulary

Every reading that the harvest has named is listed once.

| Reading | Row / part | Why it is not a door |
| --- | --- | --- |
| Stage 2 / Theorem T passenger | `J-length7-passenger-theorem-t` | \(\lvert u\rvert\asymp P^{27/32}>P^{1/4}\); argument \(n^{27/16}\neq X\) |
| Remainder modes as Stage 2 / (D3) | Part XIX | \(\lvert u\rvert\asymp P^{31/96}>P^{1/4}\); \(9/8\neq 3/2\) |
| Isolated \(e(un^{27/16})\), \(e(Cn^{3/2})\) | `J-length7-vdc3-chirps` | estimated; not the inventory |
| Reduction \(w^{3/2}=n^{27/16}+O(n^{3/16}\theta_2)\) as (D1)/(D3) | Part XX | spawned amplitude \(P^{33/32}>n\); Phase-5 wall |
| Affine \(u(w_0+Jt)^{3/2}\) on X3-runs | Part XX | same third derivative as the isolated chirp; omits the carry |
| X3 plus Q/R3 carry | `J-length7-x3-qr3-carry` | \(\kappa_w\) has mean run \(O(1)\); \(B\asymp P^{45/32}>n\) |
| Integer-\(w\) block \(e(\xi w)\) | `J-length7-integer-w-block` | naive \(\theta_w\) coefficient; \(\xi>n\) |
| Dual \(e(w\{\xi\})\) | Part XXII | coefficient \(w\asymp n^{9/8}>n\) |
| A different X1 rearrangement | Part XXII | reinstates \(45/32\) |
| New decoration \(\lvert\varphi'''\rvert\ll\lvert f'''\rvert\) | Part XX | not written; leftover already exceeds \(n\) |
| \(K_3\) / BB/GG/JJ | toolkit PARK | wrong object (\(OOOO*\)) |
| Corollary R′ family | family CONJECTURE | \(W\)-family, not \(\theta_p\) |
| Length-8 eighth wave | `J-length8-remainder-discard` | consumes Theorem X as a passenger |

A nearby reformulation of any row in this table is not a
new door. In particular: a different carry treatment on
X3-runs is Phase 37; a different splitting of
\(e(\xi w)\) is Phase 38; a different decoration name for
the spawned \(n^{3/16}\theta_2\) term is Phase 35.

### What “outside-toolkit” would have to be

The readings that are *not* already named as killed are
exactly three slogans:

1. van der Corput III, or an exponent pair, on the
   *nested* sum \(e(u w^{3/2})\) itself (not the isolated
   monomials of Lemma X5);
2. a new Paper B decoration class that permits
   coefficient \(>n\);
3. a new linearization of \(p^{3/2}\) that avoids both
   \(\theta_p\) and the naive \(n^{45/32}\) coefficient.

(1) is a Hardy-of-floor / nested-floor exponential sum.
The laboratory has already exported that species and
forbidden wrapping it as a Juggler construction
(`docs/theory/exponent_pair_two_monomial.md`; the closed
floor-Hardy reformulations
`juggler_v94_rate_free`, `juggler_v94_hardy_lift`,
`juggler_nil_pet_reentry`, `juggler_rate_free_floor_hardy`).
(2) is Paper B infrastructure for one leftover, and the
leftover already sits above the engine line. (3) is the
rewrite Phase 38 forbade.

None of these is a Juggler Phase-0. The executable
laboratory vocabulary for \(\sum e(u w^{3/2})\) is empty.

### Proposition X-term (no outside-toolkit Juggler door) — REFUTED method

The claim that an outside-toolkit *Juggler* attack on
\(\sum e(u w^{3/2})\) remains, so that Theorems X and AA
are not laboratory-terminal, is **REFUTED** as a method
slogan. The leftover is real. The counts are not
refuted. The densities \(57/64\) and \(29/32\) stay
**CONJECTURE**. The laboratory door is empty.

### Phase-41 decision

**CLOSE** the harvest counting program. Ledger row
`J-harvest-counting-terminal` tagged `REFUTED` (the
outside-toolkit slogan). Flag
`harvest_counting_terminal` flipped `True`.
`J-depth7-engine-contracting` and
`J-depth8-engine-quartet` stay `CONJECTURE`. No density
move. No Paper B. No \(K_3\). Do not reopen
\(e(uw^{3/2})\), do not rewrite \(45/32\), do not reopen
\(E'\), and do not wrap a nested-floor bound as a
Juggler branch. The single next question is the
already-exported exponent-pair leftover, which is not a
harvest door.




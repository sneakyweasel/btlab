# Arb audit of the papers

Run date: 23 September 2026. Scope: Papers A–E and the active Beatty
first-passage companion. The audit made **1,973 actual MCP calls** through
fresh stdio connections to [the Arb service](../architecture/arb_mcp.md).
Every certified transcendental evaluation used the service; enumeration and
interval bookkeeping used exact Python integers and rationals. Paper D also
uses floating-point estimates solely to order its search for witnesses.

The finite checks are **COMPUTATIONALLY VERIFIED**. The consequences below
use the specified existing mathematical arguments. They are not new Lean
proofs. Manuscripts, publication kits and deposited versions were not revised.

## Findings

| Paper | Certified scope | Progress |
|---|---|---|
| A | Four complete finite period screens; monotone upper-cell bound | At the existing first surviving count pair, a primitive cubic-band cycle must have minimum below **487,011,720**, improving the manuscript's 520,000,000 cutoff |
| B | Seven printed constants and two conditional density examples | Confirms the constants; no change to 7/8, 127/128 or the open FD premise |
| C | Twelve production roots, OOEE slack, sixteen rate-boundary checks | Confirms the previously recorded sharper conditional examples, including depths 16 and 34 |
| D | All Rhin ceilings and admissible lengths for 1–62 minima at the assumed floor 2^51 | Certifies every exclusion through 61; the same length survives at 62 |
| E | Growth exponent, exact integer comparison, fixed-grid endpoint and five derivative constants | The existing certificate supports the stronger eventual ancestor exponent **423/500 = 0.846**, instead of 21/25 = 0.84 |
| Beatty companion | First 256 exact atoms, complete remaining mass, full two-thirds moment and content | Certified Minkowski content lies in **[2.95207917, 3.07760004]** |

These are refinements of existing arguments. No new termination result,
general cycle exclusion, harmonic-mass divergence or Hausdorff lower bound
follows from this audit.

## A: sharpen the existing minimum cutoff

The [Paper A source](../theory/juggler_finite_dynamics_note.md), Proposition
6.3b, gives the upper-cell inequality for a primitive actual Juggler cycle
with minimum m > 1 and maximum M < m^3. At the fixed counts
(L,o,e) = (780239,492276,287963), put

\[
\Lambda=o\log3-L\log2,\qquad
A(m)=(\log m)e^{-(1-1/L)\Lambda},\qquad
U(m)=\frac{e^{-A(m)}}{A(m)}
       \left(1+\frac{L}{\log3\,(A(m)+1)}\right).
\]

Such a cycle requires Lambda < U(m). The existing monotonicity theorem
makes U strictly decreasing. Arb certifies

\[
U(487011720)<\Lambda<U(487011719).
\]

Consequently, under the same descent input as Corollary 6.3c,

\[
350000000<m<487011720.
\]

This is the least excluded integer for this scalar bound. It does not say
the preceding integer is realizable, exclude period 780239, raise the
descent floor, or cover cycles outside the cubic-band hypothesis. The
monotonicity and cutoff interface already exist as
`CubicGrid.closedGeometricChargeBound_strictAntiOn_minimum` and
`CubicGrid.FullUpperCellChargeBounds.closedGeometric_cutoff_excludes`;
this run does not supply a new Lean proof of the numerical comparison.

Independently, certified logarithms and exact rational screening cover
every length through each listed frontier. The remaining parity and
walk-charge comparisons use MCP enclosures. The continued-fraction
denominators used by the walk bound are checked from an interval as well.

| Assumed descent floor | First length not excluded | Crude exclusions | Parity exclusions | Walk exclusions |
|---:|---:|---:|---:|---:|
| 1,000,000 | 25,781 | 25,756 | 24 | 0 |
| 26,254,995 | 176,251 | 176,222 | 14 | 14 |
| 162,849,448 | 478,245 | 478,212 | 17 | 15 |
| 350,000,000 | 780,239 | 780,193 | 30 | 15 |

The descent campaigns themselves were not rerun.

## B and C: confirmed finite constants

For [Paper B](../theory/juggler_parity_discrepancy_note.md), all seven
displayed rounding intervals contain the certified values: the sharp and
convenient KL rates, rho, eta, oscillation envelope, ladder mean and first
jump. The examples at fixed depths 100 and 1000 enclose the logarithm of
the exceptional-density bound **conditional on FD at that depth**. They do
not establish FD.

For [Paper C](../theory/juggler_fate_almost_all_note.md), all twelve
production roots and the positive fixed OOEE slack at 5/8 are certified.
For q = 1/2, 11/20, 3/5, 31/50, the respective Chernoff boundaries are
16, 34, 168, 1135 and the Azuma boundaries are 16, 34, 175, 1201.
This MCP run checks each boundary and its predecessor. Minimality over
all integer depths comes from the separate
[canonical Paper C audit](../architecture/certified_numerics.md), which
checks every preceding depth. Production, cylinder, pressure and
admissible-error hypotheses remain separate mathematical inputs.

## D: exhaustive enclosure audit through 61 minima

The [Paper D source](../theory/collatz_3n_minus_1_m_cycles_note.md) uses
the assumed descent floor X0 = 2^51 and Rhin's external logarithmic bound.
This run checks every ceiling K3(m), for 1 <= m <= 62, by opposite signs
at consecutive integers and a positive derivative on the increasing
branch. The defining function has positive second derivative, so the
derivative check extends to all larger lengths. The decimal 13.3 is
supplied exactly.

The length enumeration uses an exact rational rotation sieve, with an
explicit completeness bound. Let beta = log(2)/log(3), S = 2^256, and
certify beta in [a/S,(a+1)/S] using a 512-bit MCP evaluation. Let
N = K3(62)-1, epsilon = 62/((X0-1)log(3)), and choose

\[
E=\lceil S\epsilon_{\rm upper}\rceil+N.
\]

For 1 <= K <= N, every genuine upper-window hit
0 < ceil(K beta)-K beta < epsilon satisfies
(K a mod S) >= S-E. Indeed the rational approximation lies below K beta
by at most K/S; widening by N/S covers that error, including an integer
crossing. The exact number of rational hits through n is

\[
\sum_{k=0}^{n}\left\lfloor\frac{ka+E}{S}\right\rfloor
-\sum_{k=0}^{n}\left\lfloor\frac{ka}{S}\right\rfloor.
\]

Euclidean floor sums and recursive interval splitting enumerate every
hit. This may add candidates but cannot miss one. Arb then certifies
the odd count, positive logarithmic surplus and admissibility of each.
All 62 ceilings and counts agree with the recorded table.

Every admissible length for m <= 61 has a negative chaining margin or a
negative valley margin at an exact rational threshold. For a valley
branch, the chosen threshold lies strictly below its certified breakpoint
and above log2(X0-1), so it is a valid finite witness for the paper's
inequality. Floating-point estimates only order the search for witnesses;
they do not establish an exclusion.

At m = 61, the closest margin is approximately **-0.11754776878822766
bits**, at length 83,130,157,078,217. At m = 62, the same single length
survives the optimized tests among 120 admissible lengths; all 62 valley
branches are accounted for. Its simple Lemma 2 killing-floor logarithm
is approximately 55.25168590196912. This is a diagnostic value, not a
certified descent campaign. No exclusion through 62 is claimed, and
higher-floor tables were outside this run.

## E: a stronger rational exponent from the same certificate

The [Paper E source](../theory/juggler_signed_collatz_note.md), Lemmas
5.3–5.4, supplies a fixed positive prefactor and growth rate
mu = 5059/5000. Arb encloses

\[
\gamma=50\log_2(5059/5000)=0.846207212891068226\ldots
>\frac{423}{500}.
\]

An independent exact integer check gives

\[
5059^{25000}>2^{423}5000^{25000}.
\]

**Written consequence with computational arithmetic evidence.** For every
positive target a with 3 not dividing a, for all sufficiently large
integer X, the paper's capped positive 3n-1 ancestor count satisfies

\[
X^{423}\le N(a,X)^{500}\le\bigl(\pi^-_a(X)\bigr)^{500}.
\]

To see this, repeat Theorem 5.1's interpolation proof. At cutoffs
10000 r 2^j, the count is at least K mu^(50j) for fixed K > 0.
Between successive cutoffs, monotonicity loses only a fixed factor.
The strict inequality mu^50 > 2^(423/500) eventually absorbs both
factors. This proves the stated eventual exponent without changing the
177,147-row certificate. No explicit new onset X0(a) is supplied.

The existing Lean theorem still states 21/25. The independent canonical
`check_paper_e.py` audit also passed all 177,147 exact rows and its 59
recorded Lean declaration checks; it was not a fresh Lean compilation.

The fixed-grid endpoint 5069/5000 has certified exponent approximately
0.9886534520013553, and its averaged obstruction is strictly below one.
The five audited derivative constants in Appendix C pass. The grid
ceiling limits this certificate method; it is not an upper bound on
actual ancestor counts. No reciprocal-mass divergence or termination
claim follows from exponent 423/500.

## Beatty companion: the entire profile tail is computable

The [working note](../theory/juggler_beatty_first_passage_note.md),
Sections 1 and 13, proves positivity and the exact total mass

\[
F(t)=1+\sum_{\delta_r<t}w_r,\qquad
\sum_{r\ge1}w_r=\frac1{\alpha-1},\qquad \alpha=\log_2 3.
\]

For the first R = 256 atoms, integer dynamic programming counts the
surviving words through depth 406. Each prefix test is exactly
3^(number of ones) > 2^(prefix length), and
m_r = floor(alpha r) is obtained from the bit length of 3^r. Thus the
counts do not depend on rounded logarithms. MCP calls certify every
phase, weight and phase ordering.

Write F_R for the finite profile and
tau = 1/(alpha-1)-sum_(r<=R) w_r. The proved mass identity gives
0 <= F-F_R <= tau everywhere. Since F_R >= 1 and the derivative of
x^(2/3) is at most 2/3 for x >= 1,

\[
0\le\int_0^1 F(t)^{2/3}\,dt-\int_0^1 F_R(t)^{2/3}\,dt
\le\frac23\tau.
\]

Integrating over all finite jump cells and propagating outward endpoints
gives these decimal intervals, rounded outward for display:

| Quantity | Certified enclosure |
|---|---|
| First 256 weights' mass | [1.61988167, 1.61988168] |
| Entire remaining mass tau | [0.08962961, 0.08962962] |
| Integral of F_R^(2/3) | [1.40531077, 1.40531078] |
| Integral of F^(2/3) | [1.40531077, 1.46506386] |
| Minkowski content | [2.95207917, 3.07760004] |

For the last row use Section 17's proved formula, with
beta = 1/alpha and kappa = beta/sqrt(2 pi (1-beta)):

\[
\mathcal M^{2/3}(K)
=3\,2^{1/3}\kappa^{2/3}\int_0^1F(t)^{2/3}\,dt
=3\left(\frac{\beta^2}{\pi(1-\beta)}\right)^{1/3}
  \int_0^1F(t)^{2/3}\,dt.
\]

The convention is the limit of the tube volume divided by epsilon^(1/3).
This bounds the full infinite-profile quantity using a proved identity;
it is not a fit to a guessed tail. It does not give a convergence rate
for finite-depth counts or tube volumes. It also does not bound the
different survivor-convolution tail discussed in Section 11.

## Reproduction and evidence

```powershell
python -m pip install -e ".[dev]" -r tools/requirements-formalpedia.txt
python tools/check_papers_arb.py
python tools/check_papers_arb.py --paper A E Beatty --output-root .build/arb-review
python tools/lab.py test -- tests/tools/test_arb_paper_audit.py
python tools/check_paper_e.py
python tools/lab.py check --hashes
```

The first audit command deliberately writes canonical reports and manifests;
the second example writes a separate review run. Each run verifies the
checkout binding, rejects unresolved comparisons and checks that inputs
and implementation sources did not change during computation. Actual
backend versions, request precision, source hashes and rational outward
endpoints are preserved. Recorded hashes are provenance, not a signature
or an independent implementation audit.

| Paper | Calls | Report | Run manifest |
|---|---:|---|---|
| A | 429 | [a.json](../../data/research/juggler/arb_paper_audit/a.json) | [a.research.json](../../data/research/juggler/arb_paper_audit/a.research.json) |
| B | 15 | [b.json](../../data/research/juggler/arb_paper_audit/b.json) | [b.research.json](../../data/research/juggler/arb_paper_audit/b.research.json) |
| C | 30 | [c.json](../../data/research/juggler/arb_paper_audit/c.json) | [c.research.json](../../data/research/juggler/arb_paper_audit/c.research.json) |
| D | 715 | [d.json](../../data/research/collatz/arb_paper_audit/d.json) | [d.research.json](../../data/research/collatz/arb_paper_audit/d.research.json) |
| E | 9 | [e.json](../../data/research/collatz/arb_paper_audit/e.json) | [e.research.json](../../data/research/collatz/arb_paper_audit/e.research.json) |
| Beatty | 775 | [beatty.json](../../data/research/juggler/arb_paper_audit/beatty.json) | [beatty.research.json](../../data/research/juggler/arb_paper_audit/beatty.research.json) |

The [runner](../../tools/check_papers_arb.py) uses a small
[audit package](../../tools/arb_paper_audit_core/).
[Tests](../../tests/tools/test_arb_paper_audit.py) independently enumerate
small floor-sum problems and all binary words through depth 12, check
outward bookkeeping, and validate the saved evidence and finite witnesses.
They read evidence; they do not regenerate canonical artifacts.

## Triage and decision

```text
Mathematical target     Do certified finite evaluations sharpen any existing paper conclusion?
Novelty hypothesis      Existing strict inequalities leave usable numerical headroom; proved total mass controls the Beatty tail.
Falsifier               Every improved value needs a new unproved analytic input, or an enclosure overlaps its decision boundary.
Already killed by?      The Diophantine-walls and complete-Collatz-fibres obstructions still rule out inferring general cycle exclusion or harmonic growth. They do not forbid these finite refinements.
Existing machinery      The Arb MCP, exact paper certificates, monotone UC2 bound, positive growth induction, Beatty mass identity and content formula.
Maximum Phase-0 scope   Papers A–E plus 256 Beatty atoms, existing A frontiers, D at floor 2^51 through 62 minima; no new campaign.
Promotion criterion     Reproducible outward comparisons plus an explicit consequence using established hypotheses.
Stop criterion          Unresolved comparisons or missing analytic inputs; do not extend the scope or promote an evidence label to Lean.
```

**PROMOTE** the numerical refinements and reproducible audits recorded here.
No new research branch or publication revision is opened by this decision.

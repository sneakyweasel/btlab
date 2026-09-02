# Juggler multi-step itinerary-parity census

Status: **THEOREM**

Phase-0 gate for iterating the one-step image-parity discrepancy bound
(Theorem 5.1 of the finite-dynamics note, \(|S_O(N)|\ll N^{5/6}\)) to
joint parity itineraries of depth two through four on odd starts. Exact
integer counting only. Not a frequency theorem, not a predictive-state
claim, and not a termination claim.

## Problem

Do the joint parity itineraries \((n, J(n), J^2(n), J^3(n)) \bmod 2\) on odd
starts converge to the product densities, and with what empirical
discrepancy exponent — i.e., is the depth-2 analytic lemma worth
attempting?

## Exact statement

For odd \(n\), let \(w(n)\) be the length-4 itinerary parity itinerary
(first letter always `O`). For each word \(w\) of length
\(d\in\{2,3,4\}\), set

\[
D_w(N) = \#\{\text{odd } n \le N : w(n)\text{ has prefix } w\}
  - \frac{\#\{\text{odd } n \le N\}}{2^{d-1}}.
\]

Phase 0 asks whether every \(D_w(N) = o(N)\) empirically, with a
fitted envelope exponent clearly below 1, on \(N \le 10^7\). It does
not prove any bound.

## Current literature

- Theorem 5.1 (`J-odd-image-discrepancy`): the depth-1 odd-start sign
  sum satisfies \(|S_O(N)|\ll N^{5/6}\) — **EXACT — HUMAN PROOF**. Its
  dossier's recorded best next question was whether the bound
  iterates; this branch is that question's Phase 0.
- Parity discrepancy transfer — **REFUTED** (translation-uniform
  short-interval law). Avoided here: the summation variable stays
  \(n\), never the sparse image set.
- Landing-θ and residue predictive states — **CLOSE**/**REFUTED**.
  Not reopened: densities of itinerary classes are counted, no state is
  claimed to predict the next letter.
- `ooe_cylinder_both_next_parities` — residue classes do not decide
  letter 3. Consistent with (and explains the need for) an
  Archimedean, not 2-adic, approach.
- Piatetski-Shapiro-type nested-floor equidistribution: the depth-2
  parity is the parity of \(\lfloor m^{3/2}\rfloor\) at
  \(m=\lfloor n^{3/2}\rfloor\), a nested floor outside the classical
  single-floor theory. Project relationship: **independent**.

## Branch budget

```text
Mathematical target     Do joint parities (J(n), J^2(n), J^3(n)) mod 2
                        on odd n equidistribute with power-saving
                        discrepancy, empirically, at depth <= 4?
Novelty hypothesis      Depth >= 2 classes have product densities; the
                        contracting OOEE class then carries a uniform
                        4-step certificate, lifting certified density
                        above 3/4 once a depth-2 lemma is proved.
Falsifier               A depth-2/3/4 class not converging to the
                        product density, or envelope exponent ~ 1.
Existing machinery      floor_power; Theorem 5.1; oo-descent census;
                        refuted transfer row (kept closed).
Maximum Phase-0 scope   One exact census module + pinned tests +
                        geometric envelope fit, N <= 10^7, depth <= 4.
                        No analytic proof, no Lean, no CLI, no plots.
Promotion criterion     All depth <= 4 classes converge with fitted
                        exponent clearly < 1.
Stop criterion          Persistent density bias, exponent ~ 1, or
                        machinery gravity.
```

## Balanced-ternary formulation

None required. The map is on ordinary positive integers.

## Why BT may be relevant

It is not required. The 2-adic / BT bridge stays closed.

## Candidate operations / invariants

- Depth-4 itinerary itinerary census over odd \(n \le 10^7\) —
  **COMPUTATIONALLY VERIFIED** (exact isqrt counting)
- All eight depth-4 classes at product density \(1/8\pm0.2\%\) —
  **OBSERVATION**
- Depth-2 envelope \(\max|D_w|=195\) at \(N=10^7\)
  (\(\approx N^{1/3}\) scale, fitted exponent \(0.28\)) —
  **OBSERVATION**
- Depth-3/4 fitted exponents \(0.63\) / \(0.66\) —
  **OBSERVATION**
- OOEE class fraction \(0.125039\) with zero four-step descent
  violations (guard for the exact contraction \(x^{16}\le n^9\)) —
  **COMPUTATIONALLY VERIFIED**
- Depth-2 analytic lemma — proved in Phase 1–2
  (`depth2_analytic_lemma_proved` is `True`)
- Even-branch depth-4 results — proved in Phase 3
  (`depth4_even_branch_proved` is `True`)
- Depth-5 contracting splits OOOEE/OOEOE — drafted in Phase 10,
  withdrawn in Phase 26, repaired in Phase 27
  (`depth5_contracting_proved` is `True`); laboratory and
  Paper B certified density \(7/8\) (Corollary 6.4); the
  four-step class remains \(13/16\)
- OOOO\* kernel isolated — Phase 11 (`depth5_kernel_isolated`
  is `True`); bound not proved
- Scale-invariant copy of Theorem R — **REFUTED** in Phase 12
  (`scale_invariant_R_extension_refuted` is `True`)
- Length-7 engine contractors OOEOOEE/OOOEOEE — drafted in
  Phase 13, withdrawn in Phase 26
  (`depth7_engine_contracting_proved` is `False`);
  \(57/64\) is **CONJECTURE**. The \(\alpha=33/32\)
  \(W\)-family instance is **EXACT — HUMAN PROOF** (Phase 28);
  the remainder \(kE_X\) is an engine (Phase 29,
  `length7_remainder_engine_proved` is `True`); the
  Theorem-T passenger slogan is **REFUTED** (Phase 34,
  `length7_passenger_theorem_t_refuted` is `True`); the
  isolated chirps close (Phase 35,
  `length7_vdc3_chirps_proved` is `True`); the X3 plus
  Q/R3 carry slogan is **REFUTED** (Phase 37,
  `length7_x3_qr3_carry_refuted` is `True`); the
  integer-\(w\) block is the Phase-5 wall (Phase 38,
  `length7_integer_w_engine_line_refuted` is `True`);
  the inventory object \(e(uw^{3/2})\) remains the hole;
  the length-8 remainder decays and discard is legal
  (Phase 40, `length8_remainder_discard_proved` is `True`);
  the harvest counting program is laboratory-terminal
  (Phase 41, `harvest_counting_terminal` is `True`)

- Increment-first \(K_3\) attack — **REFUTED** in Phase 14
  (`increment_first_k3_refuted` is `True`); bound not proved
- X1-absorption of \(K_3\) — **REFUTED** in Phase 15
  (`x1_absorption_k3_refuted` is `True`); bound not proved
- \(K_3\) toolkit — **PARKED** in Phase 16
  (`k3_toolkit_parked` is `True`); Conjecture V open
- Length-8 engine quartet OOEOOEOE/OOEOOOEE/OOOEOEOE/OOOEOOEE —
  drafted in Phase 23, withdrawn in Phase 26
  (`depth8_engine_quartet_proved` is `False`);
  the \(E'\) hole is closed as a method hole (Phase 40);
  the counting door is empty (Phase 41);
  \(29/32\) is **CONJECTURE**
- Global halt — not claimed

## Experiments

- Probe: `research.juggler_sequence.two_step_parity`
- Records: [juggler_two_step_parity.md](../research/juggler_two_step_parity.md),
  [juggler_two_step_parity.json](../research/juggler_two_step_parity.json)
- Tests: `tests/research/juggler_sequence/test_two_step_parity.py`
  (pinned exact counts at \(N=10^5\))
- Sign-critical domain gate: `sign_critical_domain_scan` samples
  the written composites of (E6)/Step 5a, Theorem 6.1, and
  Lemma 5.2 Stage 4/6 over \((n,h_1,h_2,k,j)\) in (C1)–(C3).
  `kernel_margin_scan` remains the one-point algebraic check.

One CPU pass, 26 seconds at \(N=10^7\). No GPU, no Lean change, no
Research Engine modification.

## Conjectures

- **Conjecture V** (level-3 kernel cancellation): \(K_3(P)\ll
  P^{1-\delta}\) for the \(z^{1/2}\)-shaped family
  \(c\asymp k P^{27/16}\). Isolated in Phase 11; bound open.
  The scale-invariant *method* for proving it is **REFUTED**
  (Phase 12); the cancellation statement is untouched.
  Envelope exponents remain observations.

## Counterexamples

- None found on the window: no class bias, no descent violation.
- Prior refutations stand: residue classes do not decide letter 3;
  θ-bins do not predict the next landing; the short-interval transfer
  law is false. None were retested.
- Phase 12: the scale-invariant copy of Theorem R is **REFUTED**
  (no \(v\)-level \(b\)-runs; forced \(\alpha=45/16\) wall).
  Permanent; do not retry as a repair of Theorem R.

## Formalization

None added. The four-step OOEE certificate shape
\(T_w(n)^{16}\le n^9\) is an instance of the existing Lean power
envelope; no new file is warranted before the analytic lemma survives
review.

## Phase 1: the analytic lemma

Working document:
[juggler_two_step_parity_lemma.md](../research/juggler_two_step_parity_lemma.md).

- Literature check (August 2026): nested floor powers
  \(\lfloor\lfloor n^c\rfloor^d\rfloor\) are not covered by the
  Piatetski-Shapiro corpus (single floors, intersections,
  pseudo-polynomials only). Novelty annotation: **independent**.
- **Lemma A (exact linearization)** — **EXACT — HUMAN PROOF**:
  \(m^{3/2} = \tfrac32 m n^{3/4} - \tfrac12 n^{9/4} + E(n)\) with
  \(0 \le E(n) \le \tfrac12 n^{-3/4}\). The nested fractional part is
  eliminated exactly; the integer \(m\) enters the phase linearly.
  Validated by exact scaled-integer arithmetic through
  \(n = 10^{12}+1\); the observed worst ratio \(0.7494\) matches the
  theoretical supremum \(3/4\).
- **Lemma B (gap cells)** — **EXACT — HUMAN PROOF**:
  \(m(n{+}2h) - m(n) = \lfloor\delta(n)\rfloor + [\{n^{3/2}\} \ge
  1 - \{\delta(n)\}]\), giving \(O(hP^{1/2})\) cells of length
  \(\asymp P^{1/2}/h\) per dyadic block on which the gap is constant.
  Validated exactly at \(10^6\) and \(10^9\).
- **Theorem C (nested parity discrepancy)** —
  **EXACT — HUMAN PROOF** (`J-nested-parity-discrepancy`): all four
  joint parity classes of \((m, \lfloor m^{3/2}\rfloor)\) on odd
  \(n \le N\) have cardinality \(N/8 + O(N^{23/24+\varepsilon})\).
  Proof chain: Vaaler waves, Lemma A substitution, one van der Corput
  A-process (\(H = N^{1/12}\)), Lemma B cells with an exactly split
  moving-endpoint expansion, second-derivative test per cell,
  assembly at \(J_1 = J_2 = N^{1/24}\).

## Phase 2: review pass

Adversarial re-derivation of every step (record in the working
document). All estimates re-derived with constants; three
presentational repairs (exact moving-endpoint split replacing
smooth-weight partial summation; majorant-product bookkeeping;
half-integer mode coefficients). The delicate smooth cancellation was
pinned to its exact constant: \(A_h'' \to \tfrac{81}{256} jh^2
n^{-7/4}\), and the scaled-integer validator
`smooth_cancellation_check` returns \(0.3164 = 81/256\) across
\(n = 10^4\) to \(10^8\). No step failed. Ledger rows
`J-nested-parity-linearization` and `J-nested-parity-discrepancy`
added; `depth2_analytic_lemma_proved` flipped to `True`. Ambient
counting only: not an orbit transfer, not a frequency theorem along
trajectories, not a termination claim.

## Phase 3: the depth-4 extension

Same working document, Part II. The structural surprise: depth 4 is
*easier* than depth 2, because after Lemma A's pattern is applied
twice more, every non-smooth term of the fourth-letter phase has
decaying amplitude.

- **Lemma D (fourth-letter linearization)** — **EXACT — HUMAN PROOF**
  (`J-fourth-letter-linearization`): \(v^{1/2} = n^{9/8} + D(n)\) with
  \(-\tfrac34 n^{-3/8} - n^{-9/8} \le D(n) \le 0\), where
  \(v = \lfloor m^{3/2}\rfloor\). Smoothing the fourth letter costs
  only \(O(kN^{5/8})\) cumulatively, so it happens *before* any
  differencing. Validated exactly through \(n = 10^{12}+1\); worst
  ratio \(0.9970\) against supremum \(1\).
- **Theorem E (triple parity discrepancy)** — **EXACT — HUMAN PROOF**
  (`J-triple-parity-discrepancy`): all eight sign classes of
  \(((-1)^m, (-1)^v, (-1)^{\lfloor\sqrt v\rfloor})\) on odd
  \(n \le N\) have cardinality \(N/16 + O(N^{23/24+\varepsilon})\).
  Pure fourth-letter modes reduce to a single smooth exponential sum;
  mixed modes rerun the Theorem C machinery with a smooth passenger
  whose curvature is smaller than every retained scale by
  \(\ge N^{9/8-1/24}\).
- **Corollary F (four-step descent density)** — **EXACT — HUMAN
  PROOF** (`J-four-step-descent-density`):
  \(\#\mathrm{OOEE}(N) = N/16 + O(N^{23/24+\varepsilon})\), and the
  certified \(\le 4\)-step descent class (evens, OE, OOEE) has density
  \(13/16\) — up from the paper's \(3/4\). Branch consistency of the
  indicator algebra \((1-\psi_1)(1+\psi_2)(1+\psi_3)/8\) verified
  exactly (`ooee_indicator_identity_check`).

Review record in the working document (Phase-3 section): Lemma D's
remainder chain re-derived, the absorption order checked (smoothing
precedes differencing, so no \(\theta\)-dependence reaches the van
der Corput stage), curvature sign and dominance margins verified for
both mode cases, float sanity on \(|S_{0,0,1}|\). No step failed.

## Phase 4: beyond depth 4 — tier structure and the density-one program

Same working document, Part III. Scope: what generalizes, what the
ceiling is, the algebraic bricks for tier 2, route obstructions, and
the conditional density-one theorem. The tier-2 bound is not claimed.

- **Proposition I (one-growing-layer ceiling)** — **EXACT — HUMAN
  PROOF**: the machinery of Parts I–II certifies exactly \(E\),
  \(OE\), \(OOEE\) among contracting prefixes; \(13/16\) is the exact
  ceiling of the method. Every further certified start needs a second
  growing nesting layer (an odd letter at position \(\ge 3\)).
- **Lemma G (second-order exact linearization)** — **EXACT — HUMAN
  PROOF** (`J-second-order-linearization`): exact quadratic-in-\(m\)
  forms of \(m^{3/4}\) and \(m^{9/4}\) with decaying remainders, by
  substituting \(\theta = X - m\) into both the linear and quadratic
  Taylor terms. Validated at scale \(10^{60}\) through
  \(n = 10^{12}\).
- **Proposition H (polynomial phase)** — **EXACT — HUMAN PROOF**: the
  OOO\* layer phase \(v^{3/2}\) equals a degree-\((2,1)\) polynomial
  in the integer pair \((m, v)\) with smooth coefficients, up to
  \(\tfrac34 n^{-9/8}\). The tier-2 analogue of Lemma A's linear
  structure. Branch algebra for OOO\* machine-checked.
- **Obstructions recorded**: (i) composed Lemma-B cells fail — the
  second-level gap changes at essentially every point of a cell
  (distinct ratio \(1.0000\)); (ii) the fiber transform to
  \(m\)-space strips one nesting level but loses to the sparsity
  exponent \(1/3 \gg 1/24\); the \(r = 1\) fiber mode is fatal. Both
  routes parked permanently.
- **Proposition J (conditional density-one)** — **EXACT — HUMAN
  PROOF** (`J-equidistribution-implies-density-one`): all-depth
  parity equidistribution with power savings implies density-one
  finite descent (Hoeffding, \(c > 0.0342\)) — the Juggler analogue
  of the Terras program. Implication unconditional; hypothesis open
  beyond depth 3 (closed by Proposition L in Phase 5) and the OOE\*
  splits at depth 4.
- **Census gate (depth 6)** — **COMPUTATIONALLY VERIFIED**: all 32
  words realized at \(N = 2\cdot10^6\); deviations obey the
  two-regime minimal-scale envelope
  \(|D_w| \le 1.1\max((N/2)N^{-\gamma_{\min}}, N^{2/3})\) across
  \(N = 10^5, 5\cdot10^5, 2\cdot10^6\). E-heavy words are
  boundary-dominated (deep values reach single digits), not biased.
- **Conjecture K**: all-depth equidistribution. The concrete next
  case is tier 2 (OOO\* split) via the double-differencing route:
  A-process on the polynomial phase, shifted-window Vaaler for the
  growing sawtooth amplitudes (\(\asymp khn^{7/8}\)),
  third-derivative tests, one more differencing. Expected saving
  \(\delta_2 \sim 10^{-2}\).

## Phase 5: depth-3 completion, tier-2 bricks, and the kernel

Working document, Part IV. Scope: close a discovered gap at depth 3,
prove the level-2 structural lemmas, and drive the tier-2 reduction
until it closes or the obstruction is exact. It did not close; the
obstruction is now a single named object.

- **Correction note**: Phase-4 wording said depth 3 was "proved" —
  but the OE-branch third letter (OEO/OEE split, \(\psi(m^{1/2})\) on
  even \(m\)) had never been stated. Recorded honestly; closed the
  same phase.
- **Proposition L (OE-branch third letter)** — **EXACT — HUMAN
  PROOF** (`J-even-branch-third-letter`): \(\#\mathrm{OEO}(N),
  \#\mathrm{OEE}(N) = N/8 + O(N^{7/8+\varepsilon})\) via the decaying
  smoothing \(m^{1/2} = n^{3/4} + D_1\) and van der Corput II. Depth
  3 is now genuinely complete.
- **Lemma M (plain and shifted second-order forms)** and **Lemma N
  (level-2 gap identity)** — **EXACT — HUMAN PROOF**
  (`J-tier2-gap-and-shifted-forms`): \(m^{3/2}\) and
  \((m{+}G)^{3/2}\) as quadratics in \(m\) with positive
  \(O(X^{-3/2})\) Taylor remainders; \(g_2 = \lfloor\Delta Y\rfloor +
  \kappa_2\), Lemma B one level up. Validated to \(n = 10^{12}\).
- **Kernel isolation** (negative knowledge with an exact core): after
  the A-process, the \(v\)-block term \(g_2 W_+\) leaves a
  unit sawtooth \(\theta_2\) carrying the smooth coefficient
  \(W \asymp k n^{9/8}\) whose derivative \(\asymp k n^{1/8} \gg 1\)
  crosses integers within single steps. Four reorganizations (Lemma-N
  split, the exact swap \(e(c\theta_2) = e(cY)e(-\{c\}v)\), a second
  A-process, raw differencing without Proposition H) all funnel into
  the same object. Only the \(\kappa_2\)-content is harmless (0/1
  indicator weight). **Kernel**: \(K_c(P) = \sum_{n \sim P}
  e(c(n)\{\lfloor n^{3/2}\rfloor^{3/2}\})\), \(c \asymp k P^{9/8}\),
  \(c' \asymp k P^{1/8}\).
- **Conjecture O (kernel cancellation)**: \(K_c \ll P^{1-\delta}\).
  Float probe with exact scaled phases: \(|K| = 51.9, 124.4, 1017.5\)
  on \(5\cdot10^3, 5\cdot10^4, 5\cdot10^5\) terms — square-root
  cancellation. A bilinear correlation between the fractional parts
  of one Piatetski–Shapiro layer and a smooth weight at the next
  layer's scale; no treatment found in the nested-floor literature.
- **OEO\* observation**: at depth 4 after OE, the growing layer rides
  the slow variable \(w = \lfloor m^{1/2}\rfloor\) (increments every
  \(\asymp n^{1/4}\) steps, long constancy cells) — the Theorem-C
  pattern shifted one level down. Likely closable by the existing
  engine *without* meeting the kernel; would settle depth 4 except
  OOO\*.

## Phase 6: the OE\*\* splits — depth 4 complete except OOO\*

Working document, Part V. Scope: the promoted question — does the
engine iterate one level down the scale hierarchy? It does, and the
reduction is *shorter* than Theorem C.

- **Lemma A′ (w-level linearization)** — **EXACT — HUMAN PROOF**:
  since \(U m^{1/4} = m^{3/4}\) exactly (\(U = m^{1/2}\), \(w =
  \lfloor U\rfloor\)), Lemma A collapses to \(w^{3/2} = m^{3/4} -
  \tfrac32 m^{1/4}\theta_w + E\) with \(0 \le E \le \tfrac38
  (U-1)^{-1/2}\). Two exact Taylor steps smooth the whole fourth
  letter to \(n^{9/8}\) minus one growing sawtooth \(B\theta_w\),
  \(B = \tfrac{3k}4 n^{3/8}\). Validated to \(n = 10^{12}\)
  (`lemma_a_prime_scan`, `oeo_smoothing_scan`).
- **Theorem Q (OE\*\* splits)** — **EXACT — HUMAN PROOF**
  (`J-depth4-slow-branch`): \(\#\mathrm{OEOE}, \#\mathrm{OEOO} =
  N/16 + O(N^{7/8+\varepsilon})\); \(\#\mathrm{OEEE}, \#\mathrm{OEEO}
  = N/16 + O(N^{13/16+\varepsilon})\). No differencing: \(B\) drifts
  by \(\le 1\) on intervals of length \(P^{5/8}/k\); shifted-window
  Fourier expansion, sign-collision check (\(T = P^{5/16} \ll
  kP^{3/8}\) for every \(k \ge 1\)), van der Corput II, balance
  \(J = P^{1/8}\). Branch consistency of all four indicators
  machine-checked (`oeo_indicator_identity_check`).
- **Depth 4 is complete except OOO\***: six of eight odd-rooted
  words proved (Theorems E and Q); OOO\* is exactly the kernel
  (Conjecture O). The regime boundary is now sharp: the engine
  reaches letters whose phase coefficients grow slower than \(n\)
  (integer crossings slower than one per step); OOO\* sits above.
- **Proposition J audit**: E-rooted words have a contracting prefix
  at length 1, so the hypothesis only consumes O-rooted class bounds
  — no further hidden gap.
- Float sanity: the OEO mode sum tracks the coherent-cell
  random-walk scale \(P^{5/8}\) (\(1361\) vs \(1333\) predicted at
  \(P = 10^5\); \(6142\) vs \(5623\) at \(10^6\)), far below the
  proven \(P^{7/8}\); the census fitted depth-4 exponent \(0.66\)
  matches.

## Phase 10: length-5 contracting splits — density \(7/8\)

Working document, Part VII. Scope: the two words that move the
certified-descent density. Neither meets a new kernel.

- **Lemma T1** — **EXACT — HUMAN PROOF**: \(z^{1/2}=n^{27/16}
  -\tfrac98 n^{3/16}\theta+D_5\) with \(D_5\) decaying. One slow
  sawtooth of coefficient \(n^{3/16}<n\).
- **Lemma T2** — **EXACT — HUMAN PROOF**: Lemma A′ at
  \(w=\lfloor v^{1/2}\rfloor\), two engine sawtooths
  (\(n^{3/16}\) and \(n^{9/16}\)).
- **Theorem T** (`J-depth5-contracting`) — **EXACT — HUMAN
  PROOF**: OOOEE/OOOEO at \(N/32+O(N^{1-1/72+\varepsilon})\)
  (tame passenger on Theorem S); OOEOE/OOEOO at
  \(N/32+O(N^{43/48+\varepsilon})\) (Theorem-Q argument).
- **Corollary U** (`J-five-step-descent-density`) — **EXACT —
  HUMAN PROOF**: certified \(\le5\)-step class (evens, OE, OOEE,
  OOOEE, OOEOE) has density \(7/8\).
- OOOO\* not claimed (coefficient \(n^{27/16}>n\)).

## Phase 11: OOOO\* kernel isolation

Working document, Part VIII. Scope: name the supercritical
fifth-letter object and test whether Theorem R's numerology
iterates. No bound, no density claim.

- **Lemma V1** — **EXACT — HUMAN PROOF**:
  \(\tfrac12(v^{9/4}-z^{3/2})-\tfrac34 z^{1/2}\theta_3=R_3\)
  one-signed, \(0\le R_3\le\tfrac3{16}z^{-1/2}\). The OOOO\*
  kernel is the level-3 local floor defect. Validated to
  \(n=10^{12}\).
- **Kernel \(K_3\)**: \(\sum e(c(n)\{v^{3/2}\})\),
  \(c\asymp k n^{27/16}\).
- **Smooth numerology iterates**: \(G(n)=n^{27/8}\) has
  \(G'''\asymp P^{3/8}\gg 1>P^{-5/8}\asymp G^{(4)}\) — three
  Weyl steps, the same "one extra differencing per unit of
  derivative growth."
- **Raw \(\Delta^4 Z\) is wild** (negative knowledge):
  \(|\Delta^4 Z|\gg 1\). The branch set is a product of two
  Lemma-R3 lattices, not a copy of R. Inherited Phase-5
  routes remain dead.
- **Probe**: \(|K_3|\) at square-root scale through
  \(10^5\) terms; OOOO-cylinder and differenced probes agree.
- **Conjecture V**: \(K_3\ll P^{1-\delta}\). Not claimed.
- A bound at depth 5 would not raise certified density
  (\(3^4>2^5\)); first OOOO-prefixed contractor is OOOOEEE.
  The "three Weyl steps" prediction is a smooth-model
  statement only; see Phase 12.

## Phase 12: the \(v\)-level wall

Working document, Part IX. Scope: the product of carry
lattices versus a new wall. The wall is real.

- **Lemma V2** — **EXACT — HUMAN PROOF**
  (`J-level3-inner-linearization`):
  \(v^{3/2}=m^{9/4}-\tfrac32 m^{3/4}\theta_2+E_2\),
  \(0\le E_2\le\tfrac38 v^{-1/2}\). Forced if \(Z\) is to
  become smooth in \(m\). Restoring \(c\asymp n^{27/16}\)
  produces a \(W\)-family at \(\alpha=45/16\).
- **Proposition W** — no \(v\)-level \(b\)-runs (mean and
  max run of \(\lfloor\Delta Y\rfloor\) and of \(\Delta v\)
  equal \(1\) at \(P=10^4,10^5,10^6\)); and
  \(\alpha=45/16>9/4\) is past Theorem R's engine line for
  Step-3 \(\theta\)-coefficients (spawned sawtooth has
  coefficient \(>n\) and derivative \(\gg 1\)).
- **Scale-invariant R-extension** — **REFUTED**
  (`J-scale-invariant-R-extension`). Both copy-routes die
  by recorded mechanisms. Conjecture V (cancellation of
  \(K_3\)) is not refuted.

## Phase 13: length-7 engine contractors — density \(57/64\)

Working document, Part X. Scope: the two leftover itineraries that
contract at length 7 without \(K_3\).

- **Corollary R′** — **EXACT — HUMAN PROOF**
  (`J-w-family-below-nine-eighths`): Theorem R holds for
  every monomial \(W\)-family with \(0<\alpha\le 9/8\).
- **Lemma X1** — **EXACT — HUMAN PROOF**: the naive
  \(n^{45/32}\) \(\theta_w\) coefficient rearranges into
  an integer-\(w\) block.
- **Lemma X3**: \(\lfloor\Delta v^{1/2}\rfloor\) freezes on
  runs of length \(\asymp P^{7/8}\) on the OOEO cylinder.
- **Theorem X** (`J-depth7-engine-contracting`): all eight
  OOEOO\*\* and OOOEO\*\* words at \(N/128+O(N^{43/48+\varepsilon})\).
- **Corollary Y** (`J-seven-step-descent-density`): certified
  \(\le7\)-step class has density \(57/64\).
- OOOOEEE not claimed (needs \(K_3\)).

## Phase 14: increment-first dies on the \(X\)-cells

Working document, Part XI. Scope: difference \(c\,\theta_3\)
first on \(X\)-cell \(b\)-runs, then increment-linearize at
a frozen \(J=\lfloor\Delta Y\rfloor\). The leftover would be
\(\alpha=29/16\), inside Theorem R. \(J\) does not freeze.

- **Lemma Z1** — **EXACT — HUMAN PROOF**
  (`J-increment-linearization`):
  \(F_J(v)=F_J(Y)-F_J'(Y)\theta_2+R_J\),
  \(-\tfrac38 v^{-1/2}\le R_J\le 0\). Algebraic leftover
  \(c F_J'\asymp n^{29/16}\). Validated to \(n=10^{12}\).
- **Proposition Z** — no \(J\)-runs on genuine
  \(\lfloor\Delta X\rfloor\) \(b\)-runs (raw
  \(\lfloor\Delta Y\rfloor\), \(\Delta v\), and the
  \(\kappa\)-fixed branch increment all have max run
  length \(1\) at \(P=10^4,10^5,10^6\), while the
  \(b\)-runs themselves have length \(\asymp P^{1/2}\));
  and \(\partial F_J/\partial J\) reintroduces
  \(\alpha=45/16\) (\(c(F_{J+1}-F_J)/(\tfrac98 n^{45/16})\to 1\)).
- **Increment-first \(K_3\)** — **REFUTED**
  (`J-increment-first-K3`). Both ingredients die by
  recorded mechanisms (missing \(v\)-level cells; the
  Phase-12 wall; Phase-5 full-size sawtooth). Conjecture V
  is not refuted.

```text
Mathematical target     Does differencing K3 first on X-cell
                        b-runs, then increment-linearizing at
                        frozen J = floor(ΔY), bound K3?
Novelty hypothesis      Frozen J makes the leftover α = 29/16,
                        inside Theorem R's Weyl and engine lines,
                        evading the V2-first wall at 45/16.
Falsifier               J has run length 1 on those cells, or
                        unfreezing J reintroduces α ≥ 9/4.
Existing machinery      Theorem R; Lemmas V1/V2; X-cell b-runs;
                        increment identity (Z1).
Maximum Phase-0 scope   Validate Z1; measure J-runs on genuine
                        floor(ΔX) b-runs; measure the J-derivative
                        scale. Bound only if both inputs hold.
Promotion criterion     A power-saving bound on K3, or a named
                        obstruction that kills the method.
Stop criterion          Either falsifier, or machinery gravity.
```

## Phase 15: X1 cannot land on a freezing integer

Working document, Part XII. Scope: absorb \(C\theta_2\),
\(C\asymp n^{45/16}\), by the Lemma-X1 substitution into
an integer whose gap freezes. The landing is uniquely \(v\),
which does not freeze.

- **Lemma Z3** — **EXACT — HUMAN PROOF**
  (`J-x1-landing-criterion`): X1 lands on \(\lfloor F\rfloor\);
  this has cells iff \(F''<1\). Slow square-roots freeze on
  a window of \(400\) steps; \(Y''\asymp n^{1/4}>1\) does not.
- **Proposition AA** — hybrids \(v-w_m^3\), \(v-m w_m\),
  \(v-w^2\) have run length \(1\); cubing T1 reproduces
  \(3n^{45/16}\theta_2\).
- **X1-absorption of \(K_3\)** — **REFUTED**
  (`J-x1-absorption-K3`). Conjecture V is not refuted.

```text
Mathematical target     Can X1 absorb the 45/16 leftover into
                        an integer whose first gap freezes?
Novelty hypothesis      The same move that killed n^{45/32} on
                        OOEOO lands on w, w_m, m, or s here.
Falsifier               The landing is v (or a v-hybrid) and
                        that integer has run length 1.
Existing machinery      Lemma X1; Lemma Z3; V2; T1; freeze scans.
Maximum Phase-0 scope   State the landing criterion; measure
                        slow floors vs Y vs v-hybrids; check
                        T1-cube remainder scale.
Promotion criterion     An engine leftover, or a named
                        obstruction that kills the method.
Stop criterion          The landing has no cells.
```

## Phase 16: the toolkit obstruction — PARK

Working document, Part XIII. Scope: the two leftover
attacks. Both die. The bound program is parked.

- **Amplitude drift** — \(C=\tfrac98 z^{1/2}m^{3/4}\)
  satisfies \(C(n+2)-C(n)\sim\tfrac{405}{64}n^{29/16}\gg 1\)
  (`v2_amplitude_drift_scan`). R-windows cannot run at
  \(\alpha=45/16\).
- **Smooth comparison** — **REFUTED**
  (`J-nested-floor-without-W-family`): the pointwise
  defect *is* Lemmas V1/V2.
- **Proposition BB** (`J-k3-toolkit-obstruction`) —
  **EXACT — HUMAN PROOF**: every toolkit method dies by
  missing \(Y\)-cells or a \(W\)-family past \(9/4\) with
  fast amplitude.
- **PARK** the \(K_3\) bound (`k3_toolkit_parked`).
  Conjecture V stays a conjecture.

## Results

At \(N=10^7\) (4,999,999 odd starts):

| depth | max \(|D_w|\) | \(\max|D|/N^{1/2}\) | fitted exponent |
| --- | --- | --- | --- |
| 2 | 195.0 | 0.062 | 0.28 |
| 3 | 1156.5 | 0.366 | 0.63 |
| 4 | 3020.75 | 0.955 | 0.66 |

All eight depth-4 counts lie in \([623915, 625551]\) against the
product value \(625000\). The OOEE class holds \(12.504\%\) of odd
starts (product density \(12.5\%\)) and every OOEE start satisfied
\(T^4(n)<n\). The depth-2 envelope is on the same \(N^{1/3}\) scale
as the proven depth-1 case. Labels: **COMPUTATIONALLY VERIFIED**
counts, **OBSERVATION** exponents.

Sign-critical composites on (C1)–(C3) (**OBSERVATION** gate,
1 Sep 2026): no offset or zero-offset composite loses sign on
\(P\in\{10^4,\dots,10^{12}\}\). Worst ratios: (E6) \(3.931\) at
\(P=10^4\) (printed \(4.375\)); Theorem 6.1 offset \(1.572\)
(printed \(1.75\)); zero-offset \(0.9993\) against \(8.27\);
Stage 4 agreement \(0.9984\), all samples inside
\([0.30,1.35]\,uhP^{-3/4}\). Stage 6 (D2) printed bound exceeds
\(1\) at \(P=10^4\) only (ratio \(2.30\)); first clean \(P\) on
the grid is \(10^5\). Not a large-\(P\) hole; Paper B already
takes \(P\ge P_0\) ineffective. No ledger row.

## Open questions

One mathematical, now located to a single point: Conjecture HH
at shift \(\lambda = 0\). Phase 21 *proved* the generic case —
Lemma II gives two-sided square-root cancellation of
\(\sum_{t \le L} e(A_t\{x_t + \lambda\})\) for almost every
shift \(\lambda\), for arbitrary \(x_t\), by direct integration
(no characters) — so the deterministic instance is a
specific-point-in-metric-theory problem (the "is \(\sqrt2\)
normal" species), and Proposition JJ shows the laboratory has
no de-randomization tool: no second averaging variable, a
self-similar inverse theory, and a \(1/A \asymp P^{-27/16}\)
shift-correlation scale that measure arguments cannot resolve.
The \(K_3\) line ends in three named obstruction layers
(BB global, GG intra-block, JJ metric-transfer); Conjectures V,
EE, HH stay open with strong empirical support. The editorial
debt is discharged: the second consolidation phase imported
Theorems R/S/T/X, Corollaries U/Y, Lemma II, and the obstruction
ladder into the finite-dynamics note (its old Conjecture 6.2 and
\(13/16\) headline are superseded; the note's open items are now
Conjectures 6.3 and 6.5).

## Decision

**PROMOTE** (Phase 0, census gate): every depth \(\le 4\) class
converges to the product density with envelope exponents
\(0.28\)–\(0.66\); the falsifier did not fire.

**PROMOTE** (Phase 1, analytic lemma): the growing-amplitude
obstruction dissolved under the exact linearization (Lemma A), the
supporting cell structure is exact (Lemma B), and a complete draft
proof of the depth-2 power saving \(N^{23/24+\varepsilon}\)
(Theorem C) was written with explicit exponent bookkeeping.

**PROMOTE** (Phase 2, review pass): every step of Theorem C
re-derived adversarially; the one delicate cancellation confirmed to
its exact constant \(81/256\); three presentational repairs applied;
ledger rows added and the module flag flipped. The theorem is
settled at project standard.

**PROMOTE** (Phase 3, depth-4 extension): Lemma D closed the fourth
letter with decaying amplitudes, Theorem E extended the discrepancy
bound to all eight triple-parity classes at the same exponent
\(23/24\), and Corollary F lifted the certified \(\le 4\)-step
descent class to density \(13/16\). Three ledger rows added;
`depth4_even_branch_proved` flipped to `True`.

**PROMOTE** (Phase 4, beyond depth 4): the generalization question
was answered structurally. Proposition I fixes \(13/16\) as the exact
ceiling of the one-growing-layer method; Lemma G and Proposition H
provide the proved algebraic bricks for the second growing layer;
two tempting shortcut routes were refuted and recorded; Proposition J
turns all-depth equidistribution into density-one finite descent
(the Juggler Terras program), unconditionally as an implication. Two
ledger rows added. The tier-2 analytic bound is the promoted open
frontier, not a claim.

**PROMOTE** (Phase 5, kernel isolation): a real gap at depth 3 was
found and closed the same phase (Proposition L); the tier-2 bricks
(Lemmas M/N) are proved and validated to \(10^{12}\); and the tier-2
reduction was driven to a single irreducible obstruction, the kernel
\(K_c\), with four dead reorganizations recorded as negative
knowledge and a float probe showing square-root cancellation
(Conjecture O). Two ledger rows added; the Proposition-J row
corrected. The kernel bound is the promoted frontier, not a claim.

**PROMOTE** (Phase 6, OE\*\* splits): the engine iterates down the
scale hierarchy exactly as conjectured — Lemma A′ collapsed the
reduction to two Taylor steps, Theorem Q closed all four OE\*\*
classes at \(N^{7/8+\varepsilon}\)/\(N^{13/16+\varepsilon}\) with no
differencing, and depth 4 is complete except OOO\*. The
engine/kernel regime boundary is now sharp (coefficient growth
\(n^{1}\)). One ledger row added; Proposition-J row and Conjecture-K
texts updated.

**PROMOTE** (Phase 7, consolidation): the branch is imported into the
finite-dynamics note at publication quality. Lemmas A/B/D/A′ and
Theorems C/E/L/Q enter as note Lemma 5.3, Theorem 5.4,
Proposition 5.5, Lemma 5.6, Theorems 5.7–5.8; Corollary F and the
Proposition-I ceiling as Corollary 5.9; Proposition J as
Proposition 6.1; Conjecture O as Conjecture 6.2, with the two
analytic route obstructions recorded in the note's Section 6
negative-knowledge paragraph. The exact floor reductions (parity
bridge, Lemma B/N gap identity) are now Lean-verified in
`formal/Problems/Juggler/GapCells.lean`
(`floor_odd_iff_half_le_fract_half`, `floor_add_eq_add_carry`,
`floor_gap_eq_carry`, `seq_floor_gap`), imported by both barrels.
Reviewer packet, formalization map, frontier figure, ledger
(`J-kernel-cancellation` added; lean fields on the gap rows), and the
review bundle are synchronized; PDFs rebuilt.

**PROMOTE** (Phase 8, kernel attack): a complete double-differencing
draft proof of Conjecture O was written (Theorem R, working doc Part
VI): two Weyl differencings exploit the level-2 numerology \(Y''
\asymp P^{1/4} \gg 1 > P^{-3/4} \asymp Y'''\), the exact double-gap
identity (Lemma R2, Lean `seq_floor_gap_second`) reduces the integer
content to bounded/frozen values, and the branch decomposition
(Lemma R3) carries the level-1 flicker in indicator weights — no
full-size sawtooth coefficient survives, evading both recorded
Phase-5 walls, which differenced sub-organizations rather than the
full phase. Draft exponent: \(\delta = 1/64\) for bounded \(k\),
\(1/72\) uniformly for \(k \le P^{1/24}\). The falsifier fired once
(raw \(\lfloor\Delta\Delta Y\rfloor\) is *not* frozen — mean run
1.5, jumps \(\tfrac32 P^{3/4}\)) and was met by the exact branch
reorganization, recorded as negative knowledge. New validators:
`kernel_reformulation_scan` (Lemma R1, kernel = level-2 local floor
defect sum, exact to \(10^{12}\)), `double_gap_identity_check`,
`branch_freeze_scan`, `differenced_kernel_probe` (\(|T_1|, |T_2|\)
at square-root scale). No ledger retag, no note import, no density
claim: `kernel_bound_proved` stays `False`;
`kernel_double_differencing_draft` flipped to `True`.

**PROMOTE** (Phase 9, review pass): every step of Theorem R
re-derived adversarially. Two defects found and repaired with the
part's own exact mechanisms, final exponents unchanged: (1) the
draft's "constant-gap cells" are wild sets (the level-1 carry
toggles every step); Lemma R3 restated over \(b\)-run intersections
and the carry vector \((\kappa_1,\kappa_2,\kappa_{12})\), whose
branch indicators are \(\theta\)-arcs with slow endpoints. (2) The
draft's per-run third-derivative test on mixed pieces (frozen floor
× large \(X\)-mode) is worthless — its second term sums to the
trivial bound; repaired by a targeted third Weyl differencing plus
the split \(J = F - \{F\}\), where the differenced coefficient's
sub-unit window drift \((\Delta_3c)' \asymp kh_3P^{-7/8}\) lets the
slow sawtooth \(\{F(X)\}\) expand with no run segmentation,
recovering the \(P^{1/8}/r^{1/6}\) saving. Collision inventory,
sign-dominance (monomial exponents \(15/8, 11/8 \notin \{0,1,2\}\)),
\(k\)-uniformity and majorant bookkeeping verified; the triple
difference \(T_3\) probes cancel at square-root scale. Theorem R
upgraded to `EXACT — HUMAN PROOF` (row `J-kernel-cancellation`
retagged), and Theorem S closes the OOO\* splits at
\(N^{1-1/72+\varepsilon}\): depth-4 equidistribution is complete
(new row `J-depth4-complete`); Conjecture K holds at every depth
\(\le 4\) and Proposition J's base cases \(d \le 4\) are theorems.
`kernel_bound_proved`, `tier2_analytic_lemma_proved`,
`depth4_complete_proved` flipped. The certified-descent density
stays \(13/16\) (OOO\* classes are non-contracting at depth 4); no
density-one claim.

**PROMOTE** (Phase 10, length-5 contracting splits): Lemma T1
smooths the OOOE\* fifth letter to a slow sawtooth of coefficient
\(n^{3/16}<n\), a tame passenger on Theorem S; Lemma T2 is
Lemma A′ at \(w=\lfloor v^{1/2}\rfloor\), coefficient
\(n^{9/16}<n\), and a Theorem-Q argument closes OOEO\* at
\(N^{43/48+\varepsilon}\). Theorem T counts all four words;
Corollary U lifts the certified \(\le5\)-step descent class to
density \(7/8\). Two ledger rows added;
`depth5_contracting_proved` flipped. OOOO\* (coefficient
\(n^{27/16}>n\)) is not claimed. No density-one claim.

**PROMOTE** (Phase 11, OOOO\* isolation): Lemma V1 identifies
the fifth letter as the level-3 floor defect \(K_3\); the
smooth numerology iterates (three Weyl steps); the probe
cancels at square-root scale; raw \(\Delta^4 Z\) is recorded
wild. Conjecture V is the bound, not a claim.
`depth5_kernel_isolated` flipped; no ledger row, no density
move, no note import.

**PROMOTE** (Phase 12, \(v\)-level wall): Lemma V2 forces the
inner linearization; there are no \(v\)-level \(b\)-runs;
the resulting \(W\)-family has \(\alpha=45/16>9/4\). The
scale-invariant copy of Theorem R is **REFUTED**. Conjecture
V stays a conjecture. Two ledger rows added;
`scale_invariant_R_extension_refuted` flipped. No bound, no
density move, no rescue draft, no note import.

**PROMOTE** (Phase 13, length-7 engine contractors): Lemma X1
absorbs the naive \(n^{45/32}\) \(\theta_w\) coefficient into
the integer \(w\); Lemma X3 freezes \(\lfloor\Delta v^{1/2}\rfloor\)
on runs of length \(\asymp P^{7/8}\); Corollary R′ extends
Theorem R down to \(\alpha\le 9/8\). Theorem X counts all
eight OOEOO\*\* and OOOEO\*\* words; Corollary Y lifts
certified descent to \(57/64\). Three ledger rows added;
`depth7_engine_contracting_proved` flipped. OOOOEEE still
needs \(K_3\). No density-one claim, no note import.

**PROMOTE** (Phase 14, increment-first obstruction): Lemma Z1
is the exact increment Taylor (leftover \(\alpha=29/16\));
\(X\)-cell \(b\)-runs do not freeze \(J\); the \(J\)-derivative
is the named \(45/16\) wall. The increment-first attack is
**REFUTED**. Two ledger rows added;
`increment_first_k3_refuted` flipped. Conjecture V stays a
conjecture. No bound, no density move, no rescue draft, no
note import.

**PROMOTE** (Phase 15, X1-absorption obstruction): Lemma Z3
is the landing criterion (\(F''<1\)); the \(K_3\) leftover
lands on \(v\); hybrids and cubing T1 stay at \(45/16\).
X1-absorption of \(K_3\) is **REFUTED**. Two ledger rows
added; `x1_absorption_k3_refuted` flipped. Conjecture V
stays a conjecture. No bound, no density move, no rescue
draft, no note import.

**PARK** (Phase 16, toolkit obstruction): \(C'\gg 1\) at
\(\alpha=45/16\); smooth comparison is V1/V2; Proposition BB
unifies every toolkit death. Two ledger rows added;
`k3_toolkit_parked` flipped. Conjecture V stays a
conjecture. No bound, no density move, no rescue draft,
no note import.

**PROMOTE** (Phase 17, post-BB Phase-0 falsifiers): the two
admissible theory families — L² transport of conditional
distributions (Terras-type, tolerates exceptional blocks) and
bilinear dispersion on the \(k\)-family (double large sieve,
counts coincidences instead of differencing) — each got its
cheapest falsifier. Neither fired: the dispersion amplitude
\(u=(3/4)z^{1/2}\theta_3\bmod 1\) has Poissonian pair statistics
to four digits at scales \(1/16\)–\(1/64\) and no short-lag
rigidity (\(P=10^5,10^6\); \(u\) exact to \(10^{-13}\)), and
level-3 defects are block-random (mode and fifth-letter block
variances at the random-phase scale, autocorrelation at noise;
blocks of 256 and 1024). Both theories promote to dedicated
phases: transport first (aims at the density-one statement,
where exceptional sets are affordable), dispersion second
(aims at \(K_3\) proper). Working doc Part XIV; probes
`dispersion_spacing_census`, `transport_block_variance`;
flags `dispersion_phase0_alive`, `transport_phase0_alive`
(OBSERVATION). No ledger rows, no bound, no density move,
no note import. Conjecture V stays a conjecture; the
Phase-16 PARK of the *old toolkit* stands — these are new
theories, not repairs.

**CLOSE dispersion / PROMOTE transport** (Phase 18, inductive
step): Proposition CC refutes dispersion as a completion route —
Vaaler weights put weight one on \(k=1\), family averages cannot
constrain any individual bounded-\(k\) coefficient, no
amplification family exists, and the Selberg pair-count route is
circular. The naive transport forms also die (plain block variance
= the \(T_1^{(3)}\)-family, BB-dead; fiber transform = sparsity
wall, needs \(1-(2/3)^k \ge 1/3\) versus the engine's \(1/72\)).
But Lemma DD (EXACT — HUMAN PROOF) collapses the level-2 data on
\(P^{1/4}\)-blocks to an affine base plus one circle-rotation
carry orbit amplified by \(W\asymp P^{3/4}\), with \(O(1)\)
defects (measured \(\le 2\) and \(\le 1\) at
\(P=10^4\)–\(10^{10}\)) — trading nested floors for
bounded-complexity structure with block parameters at proven
levels, bypassing both BB mechanisms rather than repairing them.
Conjecture EE states the inductive step on this substrate with
three named obligations. Two ledger rows
(`J-dispersion-count-route` REFUTED, `J-block-carry-models`
EXACT); probes `block_m_affine_model_check`,
`block_v_amplified_model_check`, `carry_multiplier_probe`; flags
`dispersion_count_route_refuted`, `transport_substrate_exact`.
No \(K_3\) bound, no density move, no note import.

**PROMOTE** (Phase 19, level-3 model and census gate): naive
Denjoy–Koksma is vacuous (observable variation \(P^{15/8} \gg
L\)); the correct route is a two-layer Fourier cascade with
\(\ell^1\)-bounded harmonic mass. Lemma FF (EXACT — HUMAN PROOF,
`J-level3-block-phase-model`) gives the level-3 kernel phase as
an explicit closed form in the four block observables, with the
key discovery that the product form \(u = \tfrac34 z^{1/2}
\theta_3\) forces the \(\theta_3\)-expansion to precision
\(P^{-27/16}\), three orders past sub-unit — the precision
budget of the cascade. Validated at scale \(10^{48}\): errors
\(5\cdot10^{-11}\) down to \(4\cdot10^{-25}\) (\(\theta_3\)),
\(2\cdot10^{-4}\) down to \(2\cdot10^{-8}\) (\(u\)). The census
gate passed: \(R_k(B) = |S_k(B)|^2/L\) has a textbook
\(\mathrm{Exp}(1)\) profile at \(P = 10^6, 10^8, 10^{10}\) for
\(k \le 3\) — square-root cancellation per block, far stronger
than EE needs — with no \(\gamma\)-resonance elevation, locating
the cascade's Diophantine conditions at the amplified
frequencies. Obligation (γ) of Conjecture EE discharged. Probes
`level3_block_model_check`, `block_kernel_sum_census`; flags
`level3_block_model_exact`, `in_block_cancellation_observed`.
No \(K_3\) bound, no density move, no note import.

**PARK** (Phase 20, intra-block obstruction): the cascade dies
at mechanism level. Proposition GG
(`J-intra-block-harmonic-obstruction`, EXACT — HUMAN PROOF):
(I) the kernel product's Fourier window drifts by
\(kC' \asymp P^{11/16}\) per step — about \(3.3\cdot10^4\)
harmonics per step at \(P = 10^6\) — so character expansions
have inner sums shorter than one step at *every* block length;
(II) every algebraic re-form transfers the \(P^{27/16}\)
amplitude instead of destroying it (floor-splitting circles
back through \(e(k\lfloor C\rfloor\{\Theta\}) =
e(k\lfloor C\rfloor\Theta)\); the exact identity
\(C\theta_3 = \tfrac34(z^{1/2}v^{3/2} - z^{3/2})\) regenerates
the \(45/16\) W-family; differencing preserves the amplitude;
interval-splitting's \(\ell^1\)-mass equals the amplitude).
The obstruction covers carry-free blocks, matching the
Phase-19 finding that resonant blocks cancel like the bulk.
Distillate: Conjecture HH (`J-pure-model-amplitude-product`,
CONJECTURE) — the pure amplitude-product sum
\(\sum e(A\{B\})\), monomials, \(1 \ll A' \ll A\); the known
boundary is exactly \(A' \asymp 1\) (tame passengers below,
nothing above). Census: Exp(1) profile at \(P = 10^6\)–\(10^{10}\)
(`pure_model_census`). Flags `intra_block_harmonic_parked`,
`pure_model_cancellation_observed`. The unconditional harvest
(depth-\(\le 4\) completeness, contracting splits, \(57/64\),
conditional density-one) is final for this program unless HH
moves. No \(K_3\) bound, no density move, no note import.

**PARK** (Phase 21, the shift average and the de-randomization
gap): the non-harmonic attack on HH produced one theorem and
one obstruction. Lemma II (`J-shift-average-square-root`,
EXACT — HUMAN PROOF): for amplitudes separated by
\(|A_t - A_{t'}| \ge A'_{\min}|t-t'|\) and *arbitrary* reals
\(x_t\), the shift-averaged second moment satisfies
\(|\,\mathbb{E}_\lambda|S_\lambda|^2 - L\,| \le
(6/\pi)(L/A'_{\min})(\log L + 1)\) — two-sided square-root
cancellation for almost every shift, by direct integration of
piecewise-linear pair phases (no characters); the amplitude
separation that kills every harmonic method is exactly what
trivializes the shift average. Probe: mean \(R\) over
\(64 \times 100\) shift-block samples \(= 1.0042\)
(\(P=10^6\)), \(0.9961\) (\(P=10^8\)) against \(1 \pm 0.0003\).
Proposition JJ (`J-derandomization-obstruction`, EXACT — HUMAN
PROOF): the transfer to \(\lambda = 0\) is out of reach — (i)
no second averaging variable exists and all family averages
re-enter BB/GG/CC-dead classes, (ii) the concentration inverse
is the same class at amplitude \(jA\) (self-similar), (iii) the
shift-correlation scale is \(1/A_{\max} \asymp P^{-27/16}\)
(measured), so almost-all statements cannot pin \(\lambda = 0\).
The \(K_3\)/HH line is **PARKED** at this frontier with the
generic case proven and the deterministic instance identified
as a specific-point-in-metric-theory problem. Flags
`pure_model_shift_average_proved`, `hh_derandomization_parked`.
No \(K_3\) bound, no density move, no note import.

**PROMOTE** (second consolidation, 29 August 2026): the branch's
final state is imported into the finite-dynamics note at
publication quality. New note items: Lemma 5.10 (R1/R2/R3),
Theorem 5.11 (Theorem R, condensed six-step proof), Corollary 5.12
(R′), Theorem 5.13 (S), Theorem 5.14 (T), Theorem 5.15 (X),
Corollary 5.16 (U+Y, densities \(7/8\) and \(57/64\)), Lemma 6.2
(V1), Conjecture 6.3 (V), Theorem 6.4 (Lemma II, full proof),
Conjecture 6.5 (HH), and condensed BB/GG/JJ negative knowledge in
Section 6. Abstract, introduction, verification convention,
Section-5 preamble, frontier figure (57/64, level-3 kernel),
Section 7, and acknowledgments updated; reviewer packet,
formalization map, paper dossier, and bundle synced; PDF rebuilt
(26 pages) and hash-checked across the three copies.

Best next question: external review of the consolidated note, or
any genuinely new idea on Conjecture 6.5 (the pure
amplitude-product model) from outside the parked toolkits.

**PROMOTE** (Phase 23, the length-8 engine quartet, 29 August
2026): re-examining the frontier found a consolidation overclaim
("every uncounted contracting itinerary passes through \(OOOO*\)" —
false: \(OOEOOOEE\) is a counterexample; fixed) and a provable
depth-8 ring. Theorem AA (`J-depth8-engine-quartet`, EXACT —
HUMAN PROOF): the four contracting length-8 words
\(OOEOOEOE\), \(OOEOOOEE\), \(OOOEOEOE\), \(OOOEOOEE\) — exactly
the contracting children of the Theorem-X classes — each have
cardinality \(N/256 + O(N^{1-1/48+\varepsilon})\). Lemma AA1:
their eighth-letter chains are fully subcritical (top coefficient
\(\tfrac{27}{16}x_3^{11/32} \asymp n^{99/128}\), drift
\(n^{-29/128} < 1\)) because the interleaved even letters keep
every state below the \(n^{9/4}\) kernel frontier; validated in
exact scaled integers through \(n = 3\cdot10^7\)
(`eighth_letter_chain_check`), censuses within \(1.8\) normalized
deviations, mode ratios \(0.002\)–\(0.045\)
(`depth8_quartet_census`, `depth8_mode_probe`). Corollary AB
(`J-eight-step-descent-density`): certified descent density
\(57/64 \to 29/32\). Structural law exposed: odd letters at state
scale \(n^\sigma\) cost \(n^{\sigma/2}\), covered iff
\(\sigma \le 9/4\) — the non-\(OOOO\) leftover thins forever by
engine work, the \(OOOO\) tree (\(1/16\)) stays blocked by
\(K_3\). Imported into the note as Theorem 5.16 and Corollary
5.17 (old Corollary 5.16 renumbered); abstract, introduction,
Section-5 preamble, Section-6 opening, leftover decomposition
(\(3/32\), exact), figure, packet, formalization map synced.
Flags `depth8_engine_quartet_proved`, `depth8_chains_subcritical`.
No \(K_3\) claim; `density_one_claimed` stays `False`.

**PROMOTE with correction** (Phase 25, the Graham–Kolesnik
expansion of the kernel, 29 August 2026): the requested full-length
rewrite of Paper B's Section 5 (every \(\ll\) with its own displayed
constant) found one wrong estimate and one undisplayed loss in the
Phase-8/9 record, both now repaired in print. (1) **Correction**:
the mixed pieces are not \(e(sX)\) with a frozen real coefficient
\(s \asymp qP^{3/4}\) — that model silently discards the sawtooth
\(-\tfrac32 qX^{1/2}\theta\) of amplitude \(\asymp qP^{3/4}\) inside
\(qY = q(X-\theta)^{3/2}\). Treated exactly as level-2 waves, the
targeted third differencing survives but yields the honest depth-2
bound \(q^{-1/6}P^{23/24+\varepsilon}\) (new Lemma 5.2(ii)), not
the recorded \(q^{1/6}P^{7/8+\varepsilon}\); the kernel saving drops
from \(\delta = 1/72\) (and \(1/64\) at bounded \(k\)) to
\(\delta = 1/96\), uniformly for \(k \le P^{1/24}\). (2)
**Absorbed loss**: the offset-branch pieces carry a
\((k|j|)^{1/2}P^{15/16}\) factor the old record never displayed; it
meets the new \(P^{23/24}\) bottleneck exactly at \(k = P^{1/24}\),
so the original \(k\)-range survives with no \(k\)-explicit
statement. New machinery in print: the master identity
\(\Delta\Delta(c\,\theta_2)\) decomposed exactly into four bounded
brackets (Lemma 5.1(iv), machine gate `master_identity_check`,
12,000 exact scaled-integer samples over three shift pairs),
standing estimates (E1)–(E6) with displayed constants, sign-margin
gates m1/m2 (`kernel_margin_scan`), and preliminaries 3.7–3.10
(third-derivative test, shifted-window expansion, two- and
three-term monomial tests for curvature collisions). Downstream
exponents synced: Theorems 6.1–6.4 now \(N^{1-1/96+\varepsilon}\)
where the kernel budget binds (the engine's own \(43/48\) is
unaffected); **no density changes** — \(13/16\), \(7/8\),
\(57/64\), \(29/32\) all stand. Ledger rows
`J-kernel-cancellation`, `J-depth4-complete`,
`J-depth5-contracting`, `J-w-family-below-nine-eighths`,
`J-depth7-engine-contracting`, `J-depth8-engine-quartet`,
`J-seven-step-descent-density`, `J-eight-step-descent-density`
corrected. The editorial debt of the assessment below is
discharged.

**PARK the harvest, freeze the claim** (Phase 26, referee-report
response, 29 August 2026): a full referee-style review of Paper B
("do not submit this") found two mathematical errors in print, three
proofs that were reductions by slogan, and a set of framing
overclaims. All are now repaired or withdrawn. **Errors fixed in
print**: (1) Step 5b of Theorem 5.3 summed inverse-power van der
Corput terms per cell as if the phase were smooth on the whole block
(the per-cell third-derivative term sums to \(> P\)); repaired by a
global sublevel-splitting argument — new Lemma 3.9 bounds the measure
of the transition set \(\Omega_V\) where the three-term monomial
model of \(f''\) is small, \(\Omega_V\) gets the trivial bound, good
pieces get Lemma 3.3, total \(\ll P^{15/16+\varepsilon}\). (2) The
old Theorem 7.4 "in particular" was false as quantified: Markov gives
\(\sqrt{L/\varepsilon}\cdot\sqrt{1+O(\log L/A'_{\min})}\) off measure
\(\varepsilon\), i.e. square-root times \(\sqrt{\log L}\) unless
\(A'_{\min}\gg\log L\); restated honestly as Proposition 7.4.
**Withdrawn from Paper B** (retagged `CONJECTURE` in the ledger with
the holes recorded): Theorems 6.2–6.4 and Corollary 6.5 — the
length-7 rearrangement discards a Taylor remainder that *grows* like
\(n^{9/32}\) (cost \(kP^{1+9/32}\), worse than trivial); the length-8
chain has \(|E|<1\) but no control of \(E'\); the length-5 split
rides passenger modes of size \(lP^{3/16}>P^{1/16}\) that were never
rerun against the kernel dominances; Corollary 5.4
(proof-by-monotonicity, never rerun at any specific \(\alpha\)) is
deleted with them. Certified densities \(7/8\), \(57/64\), \(29/32\)
revert to conjectures; the paper's density claim is \(13/16\) only.
**Rewritten as full proofs**: Theorem 4.4 (seven staged steps, every
cost displayed — the skeleton of Lemma 5.2(i)); Theorem 6.1 with a
complete passenger inventory — explicit mode ranges
\(|i|,|j|,|k|\le2P^{1/96}\), corner exactness
\(\theta(n{+}d)=\theta+\delta_d-\beta_d\) with exact
\(\theta^2\)-cancellation in the \((+,-,-,+)\) pattern, and both
sign-critical composites recomputed for the decorated phase (offset:
\(945/512-540/512=405/512\), ratio \(7{:}4\), single-signed;
zero-offset: \(8.27\,kh_1h_2\nu^{-5/8}\), positive). **New
preliminaries**: Lemma 3.8 (two-term test with trivial transition
bound), Lemma 3.9 (three-term sublevel splitting), Lemma 3.10 (parity
reindexing — the factor-4 Jacobian of \(n=2r+1\) made explicit, so
odd-\(n\) sums are no longer treated as consecutive). **Framing**:
machine gates, Lean identifiers, sample counts, and the
laboratory-record confession stripped from the analytic text (checks
stay in the repository and are labelled as such); scope narrowed to
O-rooted itineraries over odd starts everywhere; "exact linearization" and
"carry-branch decomposition" no longer claimed as new — the *package*
is; related work expanded (digital vs. convex outer functions,
Beatty compositions, Bergelson–Leibman and why generalized
polynomials do not apply); Prasad–Prasad citation dropped,
Iwaniec–Kowalski and Lagarias now cited where used;
Müllner–Spiegelhofer added. Ledger rows `J-depth5-contracting`,
`J-five-step-descent-density`, `J-w-family-below-nine-eighths`,
`J-depth7-engine-contracting`, `J-seven-step-descent-density`,
`J-depth8-engine-quartet`, `J-eight-step-descent-density` retagged
`CONJECTURE`; `J-kernel-cancellation`, `J-depth4-complete`,
`J-shift-average-square-root` rewritten. The remaining external
debt is the referee's item 6: one independent human check of
Section 5.

**CLOSE** (sign-critical domain gate, 1 Sep 2026): the four
written composites keep sign on the standing domain for
\(P\ge 10^5\). The only failure is Lemma 5.2 Stage 6 (D2)
at \(P=10^4\) (printed bound ratio \(2.30\)), already
covered by the paper's ineffective \(P_0\). No constant
repair. No new ledger row. Items 1/3/4 of the hypothesis
census are not opened.

## Publication assessment

Status: `THEOREM` for the frozen claim set, **consolidated into the
standalone parity-discrepancy paper** (Paper B,
[juggler_parity_discrepancy_note.md](../theory/juggler_parity_discrepancy_note.md)),
created 29 August 2026 when external review split the former single
note, then **frozen in Phase 26** after a referee-style review. The
paper now claims exactly: exact linearization; depths 1–3; the
\(OE*\) splits; the kernel bound \(K_c\ll P^{1-1/96+\varepsilon}\)
(Theorem 5.3, full-length Section 5); the \(OOO*\) splits with a
complete passenger inventory (Theorem 6.1); certified-descent density
\(13/16\) (Corollary 4.9, the three classes \(E\), \(OE\),
\(OOEE\) only); the conditional density-one implication
(Proposition 7.1, \(O\)-rooted hypothesis) with unconditional
base cases \(d\le4\);
and the level-3 obstruction with the shift-averaged \(L^2\) bound
(Proposition 7.4). Paper B numbering: Theorem R is Theorem 5.3
(mixed-piece repair as Lemma 5.2, Lemmas R1/R2/R3 as Lemma 5.1),
Theorem S is Theorem 6.1, Lemma V1 is Lemma 7.2, Conjecture V is
Conjecture 7.3, Lemma II is Proposition 7.4 (quantification corrected
in Phase 26), Conjecture HH is Conjecture 7.5. The former Theorems
6.2–6.4, Corollaries 6.5 and 5.4 (Theorem T, Theorem X, Theorem AA,
Corollaries U/Y/AB, Corollary R′) are **withdrawn from the paper**
and retagged `CONJECTURE` in the ledger with their holes recorded;
their drafted arguments remain in the laboratory record as routes.
The laboratory retains the full statements: the scale-invariant copy
of Theorem R, the increment-first \(K_3\) attack, and X1-absorption
are laboratory-**REFUTED**; the \(K_3\) toolkit is
laboratory-**PARKED** (Proposition BB); dispersion is
laboratory-**REFUTED** as a completion route (Proposition CC);
transport produced Lemmas DD/FF and Conjecture EE but its
intra-block analytic program is laboratory-**PARKED**
(Proposition GG); the de-randomization of Proposition 7.4 is
laboratory-**PARKED** (Proposition JJ). Remaining external debt
before submission: one independent human check of Section 5 (the
Phase-25 structural error was caught in-house; the Phase-26 Step-5b
error was caught by external review — there is no reason to assume
it was the last).

## Phase 27: length-5 harvest repair

Child dossier
[juggler_engine_harvest.md](juggler_engine_harvest.md). The two
named length-5 holes close against the Phase-26 kernel (lemma
Part XII). Laboratory certified density moves \(13/16\to 7/8\).
Paper B is not edited. Length 7/8 and Corollary R′ stay
`CONJECTURE`. Flag `depth5_contracting_proved` is `True` again.

## Phase 28: Theorem R at \(\alpha=33/32\)

Child dossier
[juggler_w_family_33_32.md](juggler_w_family_33_32.md).
Paper B Theorem 5.3 rerun at the single monomial family
\(\alpha=33/32\). Every displayed margin survives (lemma
Part XIII). Instance row
`J-w-family-thirty-three-thirty-seconds` is
`EXACT — HUMAN PROOF`. Flag `w_family_alpha_33_32_proved`
is `True`. The Corollary R′ family stays `CONJECTURE`.
Length 7/8 stay parked behind the remainder / \(E'\) holes.
Paper B is not edited.

## Phase 29: length-7 remainder engine

Child dossier
[juggler_length7_remainder.md](juggler_length7_remainder.md).
The Lemma X1 remainder \(kE_X\) is an engine
\(A\{n^{9/8}\}^2\) with \(A\asymp kn^{9/32}\) (lemma
Part XIV, `J-length7-remainder-engine`). Flag
`length7_remainder_engine_proved` is `True`. Theorem X
stays `CONJECTURE` (passenger inventory). Paper B is not
edited.

## Phase 30: decoration-and-mode budget census

Child dossier
[juggler_decoration_budget.md](juggler_decoration_budget.md).
Phase-0 inventory of the frozen Theorem 5.3 Step 3 /
Theorem 6.1 Step A pieces at the paper's \((H_1,H_2,k)\).
Four \(P_0\) overflows (\(|t|\le 3J_2\), two-layer
\(|q_d|\le 2J_2\), Y-passenger \(3P^{1/24}+P^{1/96}\),
fixed term count \(9>8\)); all die
(\(3P^{-1/48}\to 0\); named threshold \(P\ge 3^{48}\)).
No Theorem-T witness: \(\max|j|=2\) on sampled orbits;
\(7:4\) composite single-signed. **PARK** as
effectiveness. `J-kernel-cancellation` not retagged.
Paper B is not edited. Do not open a \(P_0\)-effectiveness
campaign. Remaining debt: one independent human check of
Section 5.

## Phase 31: Lemma 3.7 / Lemma 5.2 hypothesis checker

Child dossier
[juggler_kernel_p0_hypotheses.md](juggler_kernel_p0_hypotheses.md).
The five printed Lemma 3.7 / Lemma 5.2 conditions (not
the sums) first hold together at the paper majorants
when \(P=311486\). Full-block inventories at \(P=10^8\)
pass. Not an effectiveness campaign and not a Paper B
edit. Do not reopen these five lines.

## Phase 32: Step 5b interpolant \(P_0\)

Child dossier
[juggler_step5b_p0.md](juggler_step5b_p0.md).
The displayed interpolant-error chain
\(219P^{-25/24}+0.11P^{-5/6}\le 0.1P^{-5/6}\) never
holds (\(0.11>0.1\)). Introductory example first holds
at \(1.30\cdot 10^{13}\); \(V/S\le c_7/2\) at
\(3.92\cdot 10^{24}\). Not a kernel retag and not a
Paper B edit. Do not open another \(P_0\) census.

## Phase 33: Step 5b sublevel geometry vs Lemma 3.9

Child dossier
[juggler_step5b_sublevel.md](juggler_step5b_sublevel.md).
On the printed zero-offset triple, \(\Omega_V\) and the
Vandermonde transition \(T\) have \(O_E(1)\) interval
counts and do not track the cell inventory. Cancellation
fills the dyadic block at every census \(P\), so the
trivial bound costs \(P\): the geometric reading of the
Phase-32 \(V\le c_7S/2\) line, not a new threshold.
`J-kernel-cancellation` not retagged. Paper B is not
edited. Do not open a finer grid.

## Phase 34: length-7 passengers miss Stage 2

Child dossier
[juggler_length7_passenger.md](juggler_length7_passenger.md).
The Phase-13 slogan “Theorem T applies as a passenger”
is **REFUTED** (lemma Part XIX). \(\theta_p\) is an
\(n^{27/16}\)-chirp at \(\lvert u\rvert\asymp P^{27/32}\);
remainder modes are \(n^{9/8}\) at \(\lvert u\rvert\asymp
P^{31/96}\); the first-letter chirp has
\(C\asymp kn^{33/32}\). None sit in Stage 2 / (D1) / (D3).
Lemma 3.3 costs \(P^{81/64}>P\). Flag
`length7_passenger_theorem_t_refuted` is `True`. Theorem X
stays `CONJECTURE`. Paper B is not edited. No vdC-III
campaign.

## Phase 35: isolated length-7 chirps by one A-process

Child dossier
[juggler_length7_vdc3.md](juggler_length7_vdc3.md).
One Paper B \(A\)-process plus Lemma 3.3 closes
\(\sum e(un^{27/16})\) and \(\sum e(Cn^{3/2})\) inside
\(P^{23/24}\) (lemma Part XX, `J-length7-vdc3-chirps`).
The reduction \(w^{3/2}=n^{27/16}+O(n^{3/16}\theta_2)\)
is not a (D1)/(D3) decoration. Flag
`length7_vdc3_chirps_proved` is `True`. Theorem X stays
`CONJECTURE`. Paper B is not edited. No Lemma 3.11.

## Phase 37: X3-runs plus the Q/R3 carry miss \(e(uw^{3/2})\)

Child dossier
[juggler_length7_x3_carry.md](juggler_length7_x3_carry.md).
Lemma X3 freezes \(J\), not \(\kappa_w\). Mean
\(\kappa\)-run is \(O(1)\) on X3-interiors; the sawtooth
form has coefficient \(P^{45/32}>n\) (lemma Part XXI,
`J-length7-x3-qr3-carry`). Flag
`length7_x3_qr3_carry_refuted` is `True`. Isolated
Lemma X5 stands. Theorem X stays `CONJECTURE`. Paper B
is not edited. No Lemma 3.11.

## Phase 38: the integer-\(w\) block is the Phase-5 wall

Child dossier
[juggler_length7_integer_w.md](juggler_length7_integer_w.md).
\(\xi\asymp n^{45/32}\) is the naive \(\theta_w\)
coefficient Lemma X1 eliminated. Independently of
\(e(uw^{3/2})\) it sits above the engine line
(\(\xi>n\), \(\xi'\gg 1\); X3-run drift \(P^{41/32}\)).
Flag `length7_integer_w_engine_line_refuted` is `True`
(lemma Part XXII, `J-length7-integer-w-block`). Isolated
Lemma X5 stands. Theorem X stays `CONJECTURE`. Paper B
is not edited. No Lemma 3.11.

## Phase 39: Paper B harvest import (density \(7/8\))

Paper B now prints the repaired length-5 harvest:
Lemma 6.2, Theorem 6.3, Corollary 6.4 (density \(7/8\)).
Corollary 4.9 remains the four-step class \(13/16\).
Length 7/8 and the densities \(57/64\), \(29/32\) stay
withdrawn. Reviewer bundle and PDFs synced.

## Phase 40: length-8 remainder discard

Child dossier
[juggler_length8_remainder.md](juggler_length8_remainder.md).
The AA1 remainder satisfies
\(\lvert E\rvert\ll n^{-45/128}\) and
\(\lvert E'\rvert\ll n^{-29/128}<1\). Vaaler discard of
\(e(kE)-1\) costs \(\ll P^{131/192}\) (lemma Part XXIII,
`J-length8-remainder-discard`). The crude
\(\lvert E\rvert<1\) discard stays dead. Flag
`length8_remainder_discard_proved` is `True`. Theorem AA
stays `CONJECTURE` (inherits X). Paper B is not edited.

## Phase 41: harvest counting program is terminal

Child dossier
[juggler_harvest_counting.md](juggler_harvest_counting.md).
Every laboratory reading of \(\sum e(u w^{3/2})\) is a
killed route, a nearby reformulation, an isolated
monomial already in Lemma X5, or a nested-floor / new
decoration class that is not a Juggler construction
(lemma Part XXIV, `J-harvest-counting-terminal`). Flag
`harvest_counting_terminal` is `True`. Theorems X and AA
stay `CONJECTURE`. Paper B is not edited.

## Phase 42: exponent-pair leftover is not a laboratory door

The Phase-41 leftover is the already-boxed pair of
[exponent_pair_two_monomial.md](../theory/exponent_pair_two_monomial.md).
That page is external mathematics, not a Phase-0. The
origin branches
[juggler_ps_inversion_barrier.md](juggler_ps_inversion_barrier.md)
and
[juggler_bi_resonance_limit.md](juggler_bi_resonance_limit.md)
stay **CLOSE**. No new dossier, ledger row, or module.
Paper B is not edited.

## Phase 36: Paper B writeup repair (frozen 13/16)

Paper B Section 5 writeup repaired in
[juggler_parity_discrepancy_note.md](../theory/juggler_parity_discrepancy_note.md).
Lemma 5.2 budget \(\lvert q_d\rvert\le 4P^{1/24}\), nine
decorations; Step 5b interpolant keeps the two-term
majorant (no \(0.11\le 0.1\) collapse); \(c_7=1/288\)
displayed; \(P_0\) named. Claim set still \(13/16\).
`J-kernel-cancellation` not retagged. Harvest not
imported. Reviewer bundle and PDFs synced.

# Juggler reviewer packet (three manuscripts)

Author: Philippe Cochin. Date: 3 September 2026.
Status: Paper A is a submission candidate; Paper B is a revised
working draft (2 September 2026; certified density \(7/8\));
Paper C (fate contagion, 3 September 2026) is a first complete draft
— see its claim map below.

The former single note has been split into two manuscripts:

- **Paper A** —
  [juggler_finite_dynamics_note.md](juggler_finite_dynamics_note.md):
  *Cycle Financing and Near-Convergent Diophantine Obstructions
  in the Juggler Map.*
  The contributions are the Juggler-specific finance inequality
  (Theorem 4.4, hence \(L\ge 25781\) at the known \(10^6\)
  floor) and the Section 5 walk-charge envelope: transport to a
  reduced base (Theorem 5.3), hug adversary (Theorem 5.4), word
  identity (Lemma 5.6), Denjoy--Koksma over certified Ostrowski
  blocks (Theorem 5.7), and the census-free window theorem on
  \([50508,301994)\) (Theorem 5.8). The kill table gives
  \(L\ge 176251\) at the laboratory floor \(26254995\)
  (Theorem 5.9); Corollary 5.10 evaluates the same kill
  criterion at the second certified floor \(162849448\) and
  gives \(L\ge 478245\); the main numerical result is
  \(L\ge 780239\) at the third certified floor \(350000000\)
  (Corollary 5.11) — certified evaluations of the same kill
  criterion on the survivors, including lengths beyond the
  census-free window; they are not extensions of Theorem 5.8.
  Theorem 3.22 (\(e\ge 4\)) is the Section 3 structural
  headline. Theorem 4.7 is the supporting run-packing
  refinement. Section 4 opens with the excursion necklace of a
  minimum-based itinerary: organizing prose, not a new theorem.
  Finance-survivor arithmetic is secondary. Lemma 4.4b is the
  odd-count monotonicity used to evaluate the table at
  \(o_{\min}\). The core lemmas are mechanized in Lean 4;
  selected finite classifications, the descent floors
  (Propositions 1.3 and 5.1, Corollaries 5.10 and 5.11), and the
  per-length kill tables are independently certified
  computations. Leftover \(84\) is a laboratory companion, not
  a paper theorem. Peak/run bounds and the closed return-cost
  branch are not paper claims.
- **Paper B** —
  [juggler_parity_discrepancy_note.md](juggler_parity_discrepancy_note.md):
  *Parity equidistribution of nested floor powers, with descent
  applications to the Juggler map.* The exact-linearization
  discrepancy calculus, the kernel theorem, depth-4 completeness over
  odd starts, the length-5 contractors, the certified-descent
  densities \(13/16\) (four steps) and \(7/8\) (five steps), and the
  level-3 frontier. Human proofs; only the exact floor identities
  beneath them are in Lean. Length 7/8 and the densities
  \(57/64\), \(29/32\) remain laboratory conjectures.

Each paper is written to be self-contained. This page is a claim map,
not required reading for the proofs.

**Primary review questions.** For Paper A: are the power-envelope,
census, and finance arguments correct at their stated
quantifiers? (The global-defect identity is Appendix C and is not
an input to Theorem 4.4.) Is Theorem 4.6 scoped as a verified computation,
not a Lean theorem? For Section 5: is the transport recursion of
Theorem 5.3 correct with its stated constants; is the hug
domination chain of Theorem 5.4 complete; is Denjoy--Koksma
applied in the correct coordinate (\(\theta=\alpha/(1+\alpha)\),
§5.5); and are Corollaries 5.10 and 5.11 read as certified
evaluations of the kill criterion beyond the
\([50508,301994)\) window, not as extensions of Theorem 5.8?
For Paper B: are the depth-1–4 estimates (exponents
\(5/6\) to \(23/24\)) sound; is the kernel theorem (Theorem 5.3,
double Weyl differencing over the carry-branch decomposition and
master identity of Lemma 5.1, with the level-2 wave Lemma 5.2,
\(\delta=1/96\), and the Step-5b sublevel splitting of Lemma 3.9) a
complete proof a stranger can check; is Theorem 6.1's passenger
inventory (explicit mode ranges, recomputed composites \(405/512\)
and \(8.27\,kh_1h_2\nu^{-5/8}\)) correctly reduced to it; is Theorem 6.3's length-5 passenger slot (Stage-2 \(X\)-modes, not
(D1) decorations) correctly reduced to Theorem 6.1; and are the
densities (Corollaries 4.2, 4.9, 6.4) kept distinct from existential
descent and \(\operatorname{ReachesOne}\)?

No termination theorem is claimed anywhere. The level-3 kernel bound
(Paper B, Conjecture 7.3) and the pure amplitude-product model
(Conjecture 7.5) are open, and the paper says so; the shift-averaged
\(L^2\) bound (Proposition 7.4) is proved, and is an average-only
statement carrying a \(\sqrt{\log L}\) factor in general.

Large language models were used extensively in drafting. They are not
authors. Lean theorems and named computations certify the
exact-arithmetic claims of Paper A and the floor identities cited by
Paper B; every analytic estimate of Paper B is a human proof.

## What to read

| File | Role |
|---|---|
| [juggler_finite_dynamics_note.md](juggler_finite_dynamics_note.md) | Paper A (review object 1) |
| [juggler_parity_discrepancy_note.md](juggler_parity_discrepancy_note.md) | Paper B (review object 2) |
| this page | claim and falsifier map |
| [juggler_finite_dynamics_formalization.md](juggler_finite_dynamics_formalization.md) | Lean names, optional |
| `formal/Problems/JugglerPaper.lean` | paper Lean barrel (`lake build Problems.JugglerPaper`) |

## Theses

**Paper A.** Every realized finite Juggler word obeys a power
envelope. An exact compositional global defect is recorded in
Appendix C; Theorem 4.4 uses only the envelope's nonnegativity.
One-step-preimage geometry classifies minimum-based itineraries with at
most three evens; the small-cycle censuses and the family
calculations (both Appendix D) assemble
to \(e\ge 4\), hence period at least eleven (Theorem 3.22). The
financing inequality at a cycle minimum (Theorem 4.4,
constant \(1\)), with the convenient statewise bound of
Corollary 4.5 and the certified descent floor of
Proposition 1.3, yields \(L\ge 25781\). Theorem 4.6 certifies
that bound with a conservative \(6/5\) majorant; the cutoff is
not an artifact of that majorant.
Section 5 couples the states through one closed exponent walk:
transport to a reduced base, the hug adversary, the itinerary
identity, and Denjoy--Koksma over certified Ostrowski blocks
give a census-free envelope on \([50508,301994)\); the kill
table yields \(L\ge 176251\) at the laboratory floor, and a
certified evaluation of the same criterion at the second floor
\(162849448\) — beyond the window, not through it — yields
\(L\ge 478245\), and a third certified floor \(350000000\)
yields the main bound \(L\ge 780239\).
Finance-survivor lengths through \(10^5\) and their lattice
are supporting material. Short certificates are a remark in
Section 6. Peak count \(p\) is named there as the next
direction; no peak-count theorem is claimed. The same
defect-financing pattern is noted for other piecewise
floor-power maps and is not taken up.

**Paper B.** An exact-linearization discrepancy calculus with a
kernel theorem for the level-2 floor defect proves every *O-rooted*
itinerary word class of depth at most four (the eight length-4 words
over odd starts) equidistributed with power savings, so the uniform
certificate classes have densities \(3/4\) (two steps), \(13/16\)
(four), and \(7/8\) (five, Corollary 6.4); all-depth equidistribution
would imply density-one finite descent (Proposition 7.1), with the
base cases \(d\le4\) now unconditional, and the precise remaining
obstacle is the level-3 kernel of Conjecture 7.3, whose deterministic
model instance is Conjecture 7.5 (the shift-averaged \(L^2\) bound of
Proposition 7.4 says nothing about the deterministic shift).

## Claim map — Paper A

| Claim | Evidence | Scope |
|---|---|---|
| Power envelope and exponent-gap contraction | **EXACT — LEAN VERIFIED** | conditional on a realized itinerary |
| Global defect identity, vanishing, and composition (Appendix C) | **EXACT — LEAN VERIFIED** | weighted lift, not an additive sum; not a uniform tax; not an input to Theorem 4.4 |
| Odd one-step preimages have at most one integer (Lemma 3.1) | **EXACT — LEAN VERIFIED** | one-step fibers |
| Nontrivial cycle itineraries are formally expanding; min-to-even prefixes are superquadratic (Theorem 3.2) | **EXACT — LEAN VERIFIED** | necessary condition; not an exclusion of all cycles |
| Coarse lower envelope \(C_v\) (Lemma 3.3) | **EXACT — LEAN VERIFIED** | one-step \(n<4\lfloor\sqrt n\rfloor^2\) and composition; used by Lemma 3.5; Lean `lower_growth_word` |
| Next-square thresholds (Lemma 3.4) | **EXACT — LEAN VERIFIED** | \(OO\) at \(q\ge5\), \(OOO\) at \(q\ge3\), odd inheritance, last-even one-step preimage, and \(O^aE\) for \(a\ge3\) |
| Length-six orientations \(OOOEOE\) and \(OOOOEE\) (Lemma 3.5) | **EXACT — LEAN VERIFIED** | the only two leftover even-terminating length-six words; \(n<256\) is a \(254\)-start table, not a census of all words; tail \(n\ge256\) by \(n^{81}>2^{130}(n+1)^{64}\) |
| Small-cycle census: no cycle itinerary of length \(\le6\) (Theorem 3.6) | **EXACT — LEAN VERIFIED** | lengths \(\le6\) only; strengthened by Theorem 3.8 |
| Leftover length-seven orientations \(OOOOEOE\) and \(OOOOOEE\) (Lemma 3.7) | **EXACT — LEAN VERIFIED** | the only two leftover even-terminating length-seven words; \(n<14\) is a \(12\)-start table; tail \(n\ge14\) by \(n^{243}>2^{422}(n+1)^{128}\) |
| Small-cycle census: no cycle itinerary of length \(\le7\) (Theorem 3.8) | **EXACT — LEAN VERIFIED** | lengths \(\le7\) only; strengthened by Theorem 3.22 |
| Trailing even run (Lemma 3.9) | **EXACT — LEAN VERIFIED** | one-step-preimage identity; \(r=1\) is Lemma 3.4(iv) |
| Two-even leftover families (Theorem 3.12) | **EXACT — LEAN VERIFIED** | \(O^{k-2}EE\) and \(O^{k-3}EOE\) for every \(k\ge6\); not a length-8 census |
| First-even transport (Theorem 3.13) | **EXACT — LEAN VERIFIED** | minimum-based starts only; not a `CycleItinerary` theorem at a non-minimum start |
| Bunched families \(O^aEEE\), \(O^aEOEE\), \(O^aEOOEE\), \(O^aEOOOEE\), \(O^aEEOE\), \(O^aEOEOE\), and \(O^aEOOEOE\) (Theorems 3.14--3.20) | **EXACT — LEAN VERIFIED** | seven families only; not a length-8 or length-9 census |
| Gapped leftovers as cycle itineraries (Theorem 3.21) | **EXACT — LEAN VERIFIED** | both gapped families; rotation of already-excluded CycleMins; not first-E at a non-minimum start; not a length-8 or length-9 census |
| Canonical run form (Lemma 3.21b); classification (Lemma 3.21a); even-count assembly (Theorem 3.22); period at least eleven (Corollary 3.23) | **EXACT — LEAN VERIFIED** | minimum-based itineraries are \(O^aEO^bEO^cE\); no cycle itinerary with fewer than four evens; expansion corollary, not a length-9 or length-10 itinerary census |
| Cycle surplus \(\Delta_w(n)=n^{3^{\#O}}-n^{2^{\lvert w\rvert}}\) (Corollary 2.7, Appendix C); per-step slack bound \(x^e<(J(x)+1)^2\) | **EXACT — LEAN VERIFIED** | no uniform per-step tax exists; recorded for future work |
| Excursion necklace (Section 4 opening) | organizing; no new tag | names the circular itinerary of Theorem 3.2, Lemma 3.4, Lemma 3.21b, and the last-even one-step preimage; first peak overshoots, last peak lands in the entry one-step preimage; not a contradiction and not a halt theorem |
| Finance inequality (Theorem 4.4) | **EXACT — LEAN VERIFIED** | `cycleMin_finance`; constant \(1\); conceptual sharp form; not a halt theorem |
| Inv-sum form (Corollary 4.4c) | **EXACT — LEAN VERIFIED** | `cycleMin_finance_inv_sum`; same defects, remainders kept as \(1/x_{i+1}\) |
| Per-length exclusion given a floor (Corollary 4.5) | **EXACT — HUMAN PROOF** | convenient length-only statewise bound; \(n_{\max}\) from the parity charge |
| Verified computation (Theorem 4.6) | **COMPUTATIONALLY VERIFIED** | conservative \(6/5\) certification of Corollary 4.5 at floor \(10^6\); no period \(\le 25780\); \(141\) exceptions through \(10^5\); first length not excluded is \(25781\); the cutoff is not an artifact of \(6/5\) |
| Run-type packing (Theorem 4.7) | **EXACT — HUMAN PROOF** | \(\mathtt{OE}\)-starts lift to \(n^{4/3}\); not Lean |
| Run-type table (Theorem 4.8) | **COMPUTATIONALLY VERIFIED** | \(42\) of the \(141\) die; \(99\) remain; first survivor still \(25781\) |
| Survivor lattice (Proposition 4.9) | **EXACT — LEAN VERIFIED** | unimodular basis and family arithmetic; identification with \(\mathcal E_{\mathrm{run}}\) is Theorem 4.8 |
| Lean leftover \(84\) or \(\ge 85\) | **EXACT — LEAN VERIFIED** | Appendix A companion; formalization lag relative to Theorem 4.6 |
| Laboratory descent floor \(26254995\) (Proposition 5.1); raised cutoff \(50508\) (Theorem 5.2) | **COMPUTATIONALLY VERIFIED** | certified first-passage input plus the Theorem 4.6 table; not Lean |
| Transport to a reduced base (Theorem 5.3) | **EXACT — HUMAN PROOF** | Lean in log form (`cycleMin_transport`); \(n\ge 400\) hypothesis |
| Hug charge domination (Theorem 5.4) | **EXACT — HUMAN PROOF** | maximisation Lean (`hug_charge_maximal`); strict uniqueness human, unused by kills |
| Rotation average \(C_*\) (Proposition 5.5) | **EXACT — HUMAN PROOF** | Laplace bound Lean (`rotationAverage_gap`); ergodic identification classical prose |
| Itinerary identity (Lemma 5.6) | **EXACT — LEAN VERIFIED** | `budgetedWord_eq_hugWord` |
| Denjoy--Koksma block envelope (Theorem 5.7) | **EXACT — HUMAN PROOF** | DK classical, stated in §5.5 with the \(\alpha\to\theta\) coordinate change; per-block hypotheses Lean (`theta_convergent_quality`, `theta_block_permutations`) |
| Census-free window envelope on \([50508,301994)\) (Theorem 5.8) | **EXACT — HUMAN PROOF** | digit caps and scan Lean; valid on the window only — do not read beyond \(301994\) |
| Kill table, period \(\ge 176251\) (Theorem 5.9) | **COMPUTATIONALLY VERIFIED** | kill template Lean (`cycleMin_hug_kill_criterion`); per-length evaluation certified computation |
| Second floor \(162849448\), period \(\ge 478245\) (Corollary 5.10) | **COMPUTATIONALLY VERIFIED** | certified evaluation of the same criterion beyond the window; **not** an extension of Theorem 5.8 |
| Third floor \(350000000\), period \(\ge 780239\) (Corollary 5.11) | **COMPUTATIONALLY VERIFIED** | certified evaluation of the same criterion beyond the window; **not** an extension of Theorem 5.8 |
| Four-block expanding chain \(1999\to\cdots\to887471\) (Section 6) | **EXACT — LEAN VERIFIED** | one certified hard path; not a growth theorem |
| Even and odd-to-even starts have uniform short certificates (Section 6) | **EXACT — LEAN VERIFIED** | not all descent certificates |
| No descent certificate \(\Rightarrow\) odd-to-odd | **EXACT — LEAN VERIFIED** | one direction only; complement of the short-certificate remark |

## Claim map — Paper B

| Claim | Evidence | Scope |
|---|---|---|
| Parity bridge, gap-cell, and double-gap floor identities (Lemmas 3.2, 4.3(ii), 5.1(ii)) | **EXACT — LEAN VERIFIED** | `GapCells.lean`; exact reductions only, no analytic content |
| Branch-consistency identity (Lemma 3.6) | **EXACT — HUMAN PROOF** | exact indicator algebra; replaces any sampled verification |
| \(\lvert S_O(N)\rvert\ll N^{5/6}\) (Theorem 4.1) | **EXACT — HUMAN PROOF** | classical van der Corput; included for completeness |
| \(\lvert\mathrm{OO}(N)-N/4\rvert\ll N^{5/6}\) (Corollary 4.2) | **EXACT — HUMAN PROOF** | short-certificate class density \(3/4\) |
| Nested parity discrepancy \(N^{23/24+\varepsilon}\) (Theorem 4.4) | **EXACT — HUMAN PROOF** | depth 2; exponent deliberately unoptimized |
| OE-branch third letter \(N^{7/8+\varepsilon}\) (Proposition 4.5) | **EXACT — HUMAN PROOF** | completes depth 3 |
| Triple parity discrepancy \(N^{23/24+\varepsilon}\) (Theorem 4.7) | **EXACT — HUMAN PROOF** | OOE\(*\) depth-4 words |
| OE\(**\) splits \(N^{7/8+\varepsilon}\), \(N^{13/16+\varepsilon}\) (Theorem 4.8) | **EXACT — HUMAN PROOF** | depth 4 except OOO\(*\) |
| Certified-descent density \(13/16\) (Corollary 4.9) | **EXACT — HUMAN PROOF** | only the three classes \(E\), \(OE\), \(OOEE\); four-step ceiling; not an \(E\)-rooted census |
| Level-2 wave bound \(q^{-1/6}P^{23/24+\varepsilon}\) (Lemma 5.2) | **EXACT — HUMAN PROOF** | targeted third differencing; standalone statement; coefficient budget \(\lvert q_d\rvert\le 4P^{1/24}\); at most nine decorations |
| Kernel cancellation \(K_c(P)\ll P^{1-1/96+\varepsilon}\) (Theorem 5.3) | **EXACT — HUMAN PROOF** | \(W\)-shaped family at \(\alpha=9/8\), \(k\le P^{1/24}\); Step 5b interpolant two-term majorant \(219P^{-25/24}+0.11P^{-5/6}\) (no collapse to \(0.1\)); \(c_7=1/288\); \(P_0\) named and ineffective |
| OOO\(*\) splits; depth 4 complete over odd starts (Theorem 6.1) | **EXACT — HUMAN PROOF** | eight O-rooted length-4 classes; Step D \(Y\)-passenger inside \(\lvert q_d\rvert\le 4P^{1/24}\); Step E estimates the decorated phase at \(\lambda_a'\) and \(\lambda_0'\), not by slogan |
| Length-5 identities (Lemma 6.2) | **EXACT — HUMAN PROOF** | \(OOOE*\) smoothing and \(OOEO*\) linearization; one-signed remainders |
| Length-5 splits (Theorem 6.3) | **EXACT — HUMAN PROOF** | \(OOOE*\) rides Theorem 6.1 at \(N^{1-1/96+\varepsilon}\); \(OOEO*\) uses the shifted-window method of Theorem 4.8 at the \(v\)-level, error \(N^{43/48+\varepsilon}\); \(X\)-modes sit in the Lemma 5.2(i) budget, not (D1); \(k=0\) on \(OOEO*\) is Theorem 4.7 |
| Certified-descent density \(7/8\) (Corollary 6.4) | **EXACT — HUMAN PROOF** | five classes \(E\), \(OE\), \(OOEE\), \(OOOEE\), \(OOEOE\); total error \(O(N^{1-1/96+\varepsilon})\) (the worse fifth-letter exponent); leftover eighth is \(OOEOO\cup OOOEO\cup OOOO*\) |
| Length-7/8 splits and densities \(57/64\), \(29/32\) (withdrawn) | **CONJECTURE** | not imported; passenger slogan **REFUTED**; inventory and \(E'\) remain |
| Equidistribution \(\Rightarrow\) density-one descent (Proposition 7.1) | **EXACT — HUMAN PROOF** | \(O\)-rooted hypothesis; conclusion unconditional for \(d\le4\); open beyond |
| Level-3 kernel reformulation (Lemma 7.2) | **EXACT — HUMAN PROOF** | exact Taylor identity; validated in scaled integers |
| Level-3 kernel cancellation \(K_3(P)\ll P^{1-\delta}\) (Conjecture 7.3) | **CONJECTURE** | not claimed; square-root cancellation observed in exact probes |
| Shift-averaged \(L^2\) bound (Proposition 7.4) | **EXACT — HUMAN PROOF** | almost-every-shift, square-root times \(\sqrt{\log L}\) in general; no claim at \(\lambda=0\) |
| Pure amplitude-product model (Conjecture 7.5) | **CONJECTURE** | not claimed; Exp(1) censuses at \(P=10^6\)–\(10^{10}\) |

## Claim map — Paper C

Paper C is
[juggler_fate_almost_all_note.md](juggler_fate_almost_all_note.md):
*Fate Contagion in the Juggler Map and the Almost-All Reduction of
Termination* (3 September 2026; revised the same day after a first
external review). It cites Papers A and B and reproves nothing from
them; only its Appendix C depends on a statement of Paper B's type,
imported as the explicit standalone Hypothesis L.

| Claim | Evidence | Scope |
|---|---|---|
| Fate classes closed, trichotomy, exclusion (Lemma 2.1) | **EXACT — LEAN VERIFIED** | `FateContagion.lean` |
| Even block and \(OE\) fiber are exact intervals; cell identity (Lemmas 3.1, 3.2) | **EXACT — LEAN VERIFIED** | `even_block_mem`, `oe_fiber_mem`, `sqrt_sqrt_eq_iff`, `oe_fiber_disjoint` |
| Sweep lemma, fiber parity \(\ge 1/7\), thin bad fibers (Lemmas 4.1–4.3) | **EXACT — HUMAN PROOF** | elementary; constants explicit; \(m\ge 10^6\) |
| Block average \(|U(m')|=\tfrac14|I(m')_{\rm odd}|+O(m'^{11/9}\log m')\) (Proposition 4.4) | **EXACT — HUMAN PROOF** | Vaaler + second-derivative test + Kusmin–Landau; not sharp |
| Recursion lemma (Lemma 5.1) | **EXACT — HUMAN PROOF** | abstract: functional inequality with vanishing errors gives \(g\gg t^{\lambda}\) |
| Log-density of a backward-closed set \(\gg(\log x)^{\lambda}\), \(\lambda<0.4050\) (Theorem 5.3; Theorem 1) | **EXACT — HUMAN PROOF** | the main theorem; excludes no fate |
| Fate contagion, natural density infinitely often (Corollaries 5.4, 5.5) | **EXACT — HUMAN PROOF** | \((\log y)^{\lambda-1}\) on infinitely many dyadic blocks, not all |
| Odd generation; \(F\) is the \(E\)-forest over odd preimages of \(F\cap S\) (Theorem 6.1; Theorem 2) | **EXACT — LEAN VERIFIED** | `odd_mem_iff`, `nonempty_iff_odd_image_mem` |
| Exact first-letter decomposition (6.1); free term \(\psi_F\); \(\psi_F\equiv0\iff F=\emptyset\) (Proposition 6.3) | **EXACT — HUMAN PROOF** | \(S\)-fairness defined (Def. 6.2); the walk argument is Remark 6.4, labelled heuristic, not a theorem |
| Conjecture \(\iff\) log-count \(o((\log x)^\lambda)\) of failures (Corollary 7.1) | **EXACT — HUMAN PROOF** | needs \([1,N_0]\subseteq R\) |
| Tao-type bound with \(e>1-\lambda^{**}\) \(\Rightarrow\) conjecture; equivalence (Theorems 7.2, 7.3; Theorem 3) | **EXACT — HUMAN PROOF** | via contagion and odd generation; Collatz comparison stated as a structural analogy of growth scales |
| Envelope descent into the floor (Lemma 8.1) | **EXACT — LEAN VERIFIED** | `reachesOne_of_itinerary_envelope`; uses Paper A's `power_bound_word` |
| Chernoff count of bad words, odd-start share (Lemma 8.2) | **EXACT — HUMAN PROOF** | \(e(19)=0.527\), \(e(21)=0.621\) |
| \(\mathrm H(C,A)\Rightarrow\) Tao-type bound; \(C\ge 21\) unconditional, \(C\ge 19\) under Appendix C (Theorem 8.3, Corollary 8.4) | **EXACT — HUMAN PROOF** | conditional; fair share \(2^{-(d-1)}y/2\) |
| One-sided form (Theorem 9.1), pressure and no-momentum forms (Theorem 9.2, Proposition 9.3) | **EXACT — HUMAN PROOF** | conditional; Azuma / exponential Markov; stopping at the floor essential |
| What the weakest form does not need; bounded-depth barrier (Section 9.3) | **EXACT — HUMAN PROOF** | fair-to-depth-\(k\)-then-all-\(O\) measure; intermediate forms are **REPARAMETERIZATION** |
| Free term = infinite-depth live mass; duality; critical exponent \(0.5073\) (Proposition 10.1, Corollary 10.2; Theorem 5) | **EXACT — HUMAN PROOF** / **REPARAMETERIZATION** | exact map cannot replace contagion |
| Depth-uniformity budget \(cC<1\) (Proposition 10.3) | **EXACT — HUMAN PROOF** | narrow by design: methods whose only error term decays like \(2^{-cd}\), used through the per-cylinder count |
| Hypothesis L (localized twisted triple discrepancy), Appendix C | **CONJECTURE** (hypothesis) | dyadic untwisted case is Paper B Theorem 4.7; localization and twist not proved; status stated |
| \(OOEEE\) production and \(\lambda^{***}=0.4922\) from Hypothesis L (Lemmas C.1–C.3, Proposition C.4, Theorem C.5) | **EXACT — HUMAN PROOF**, conditional on Hypothesis L | nesting, exceptional set (Erdős–Turán + Kusmin–Landau), Vaaler expansion written out |
| Fiber/block/closure, survival and pressure experiments (Section 11) | **OBSERVATION** / **COMPUTATIONALLY VERIFIED** (closure to \(10^9\)) | prove nothing; one table, one paragraph |

Falsifiers for Paper C: a nonempty backward-closed set with
\(\sum_{n\in A,n\le x}1/n=o((\log x)^{0.40})\); a good fiber
(\(m\ge 10^6\)) with fewer than \(H_m/7\) even images; an even block
\(I(m')\) with \(|U(m')|\) below the main term by more than
\(C_0m'^{11/9}\log m'\); an odd \(n\ge 3\) with
\(n\in F\not\ni\lfloor n^{3/2}\rfloor\); a start whose word reaches
\(u_t\le -L(y)\) without entering \([1,N_0]\); a word measure fair to
depth \(k\) and all-\(O\) afterwards for which the reduction's
argument still yields the bound (would refute Section 9.3(e)); an
odd \(n\ge3\) with \(n^{9/16}-\lfloor\lfloor n^{3/2}\rfloor^{3/2}\rfloor^{1/4}>n^{-15/16}\)
(would refute Lemma C.1).

## Quantifier checks

1. A descent certificate is a realized itinerary with image strictly
   below the start. Paper A's short-certificate remark isolates a
   uniform short subclass. It does not say that odd-to-odd starts
   lack descent.
2. Paper B Corollaries 4.2, 4.9, and 6.4 are densities of uniform
   subclasses (\(3/4\) at two steps, \(13/16\) at four, \(7/8\) at
   five). None is a density of `FiniteProgress` nor of `ReachesOne`.
   The figures \(57/64\) and \(29/32\) remain conjectures, not paper
   claims.
3. Terras–Everett prove almost-all Collatz stopping times. Neither
   paper proves the Juggler analogue; Proposition 7.1 is an
   unconditional *implication* from all-depth equidistribution, whose
   hypothesis is a theorem for \(d\le4\) and open beyond (first open
   case: the depth-5 \(OOOO*\) split, Conjecture 7.3).
4. `power_bound_contracts` requires a realized contracting itinerary.
5. Cycle restrictions do not exclude all cycles. Paper A Theorem 3.6
   is a census for lengths at most six; Theorem 3.8 extends it to
   lengths at most seven. Theorems 3.12--3.21 exclude leftover
   families; Theorem 3.22 assembles them as an even-count
   exclusion (period at least eleven). Section 4 excludes later
   *periods* by financing. A leftover-length cycle remains
   possible as far as the papers prove.
6. The `native_decide` boundary checks cover the `Fin 256` length-six
   leftover tables and \(257^{64}<2\cdot256^{64}\), and the `Fin 14`
   length-seven leftover tables together with
   \(2^{422}15^{128}<14^{243}\).

## What the papers do not claim

- Every positive integer reaches \(1\).
- Three-quarters, \(13/16\), or \(7/8\) of starts reach \(1\).
- Those densities as *complete* certificate inventories: they count
  uniform classes.
- The length-7/8 densities \(57/64\), \(29/32\), as paper claims.
- E-rooted (even-start) word classes at any depth.
- A Collatz theorem, or a transfer of Terras's theorem to \(J\).
- Density-one finite descent (Proposition 7.1 is conditional on
  all-depth equidistribution; only \(d\le4\) is proved).
- The level-3 kernel bound \(K_3(P)\ll P^{1-\delta}\)
  (Conjecture 7.3 is open), or any bound on the pure
  amplitude-product model at the deterministic shift
  (Conjecture 7.5 is open; Theorem 7.4 is almost-every-shift only).
- Every trajectory meets a contracting itinerary.
- Every nontrivial cycle is impossible.
- A state-distribution finance inequality (the maximum of
  \(\sum 1/(x_i\log x_i)\) over realizable cycle geometry).
  Paper A records that program in Section 5; Theorems 4.4--4.7
  are length-only upper bounds on the same sum.
- That the excursion necklace of Section 4, or the missing
  implication from the forced lift plus the necklace plus the
  entry one-step preimage, excludes leftover lengths or proves there is no
  cycle.
- The Juggler map is irreducible or has no finite-state model.
- The \(N^{5/6}\) bound controls trajectories or arbitrary image sets.

## Suggested falsifiers

Reject or revise if:

1. a Lean theorem is quoted with stronger quantifiers than its statement;
2. the \(3/4\), \(13/16\), or \(7/8\) figure is called a Terras
   theorem or a `ReachesOne` density;
3. Paper A's short-certificate remark is read as “odd-to-odd starts have no descent”;
4. any analytic estimate of Paper B is described as Lean-certified;
5. the census of Paper A Theorem 3.6 is read beyond length six, or
   Theorem 3.8 beyond length seven, or Theorem 3.22 is read as a
   length-9 or length-10 itinerary census rather than an even-count
   assembly, or Theorem 3.13 is read
   as a cycle-itinerary exclusion at a non-minimum start, or Theorem
   4.6 is quoted as a Lean theorem, or leftover \(84\) is quoted
   as the printed leftover, or an exclusion of every leftover
   length is attributed to either paper;
6. a discrepancy proof replaces a floor by a single exponential, or
   an exact linearization (Paper B Lemmas 4.3(i), 4.6, 5.1, 6.2,
   7.2) is quoted without its one-signed remainder bounds;
7. an interval bound is applied to a sparse image set without transfer;
8. a finite first-return count is promoted to an infinite theorem;
9. Proposition 7.1 is quoted without its equidistribution hypothesis,
   or Conjecture 7.3 or 7.5 is cited as a theorem;
10. Proposition 7.4 is quoted as a bound at the deterministic shift
    \(\lambda=0\), as pure square-root cancellation without the
    \(\sqrt{\log L}\) caveat, or any numerical probe or repository
    validation is treated as a proof step;
11. a withdrawn pre-Phase-26 claim (old Theorems 6.2–6.4 and
    Corollaries 5.4 or 6.5: length 7/8 and the densities
    \(57/64\), \(29/32\)) is cited as a theorem of Paper B; the
    present Lemma 6.2, Theorem 6.3, and Corollary 6.4 restore
    only the repaired length-5 count and the density \(7/8\);
12. the excursion necklace of Paper A Section 4 is quoted as a
    new theorem, or the first CycleMin peak is identified with
    the last-even entry one-step preimage;
13. Theorem 5.8 is quoted for a length outside
    \([50508,301994)\), or Corollary 5.10 or 5.11 is described as an
    extension of the census-free window rather than a certified
    evaluation of the Theorem 5.9 kill criterion, or the
    \(478245\) or \(780239\) bound is quoted as a Lean theorem.

## Verification

Repository: [https://github.com/sneakyweasel/balanced_ternary/](https://github.com/sneakyweasel/balanced_ternary/).

```text
pip install -e ".[dev]"
python tools/render_theorem_ledger.py --check
python -m pytest tests/unit/test_theorem_ledger.py
python -m pytest tests/research/juggler_sequence/test_oo_descent_density.py
python -m pytest tests/research/juggler_sequence/test_progress_coverage.py
python -m pytest tests/research/juggler_sequence/test_odd_image_discrepancy.py
python -m pytest tests/research/juggler_sequence/test_two_step_parity.py
python -m pytest tests/research/juggler_sequence/test_cycle_leftover_itineraries.py
python -m pytest tests/research/juggler_sequence/test_layer_architecture.py
```

From `formal/`: `lake build Problems.JugglerPaper`.
The laboratory barrel `Problems.Juggler` is not the review object.

# Agent guide

This is the **Balanced Ternary Mathematical Laboratory**: a
problem-independent core (`bt`) plus independent research applications
(`research.*`). The active application is the **Juggler map**
\(T(n)=\lfloor\sqrt n\rfloor\) (\(n\) even), \(\lfloor n\sqrt n\rfloor\)
(\(n\) odd).

```text
cli, visualization          application edges
research.*                  problem-specific mathematics
research_engine             problem-independent experimental dynamics
bt.*                        problem-independent BT mathematics
```

`bt.*` must never import `research.*` or `research_engine`. Architecture:
[docs/architecture/overview.md](docs/architecture/overview.md).

## Juggler reading path

1. [docs/theory/juggler_finite_dynamics_note.md](docs/theory/juggler_finite_dynamics_note.md) — Paper A: cycle-length lower bounds. Full numerical audit 4 Sep 2026 (`research.juggler_sequence.paper_a_audit`, 27 tests): the finance spine reproduces to the digit at all four floors; three printed constants corrected (\(n_{\max}(50508)\) 162848325→162848324, the convergent asymptotic \(/\log^2 n\)→\(/\log n\), \(Lpprox n^{0.64}\)→\(n^{0.59}\)); new §5.8 Proposition 5.12 prices the whole semiconvergent fan \(L_k=176251+301994k\), \(k\le55\), ending on \(q_{14}=16785921\) — next step needs floor \(4.48\cdot10^9\) (12.8×), full fan \(2.20\cdot10^{12}\); walk charge measured worth ×8.09 in floor (Lemma 5.13: margin scales as (N log N)^1.047, predicts kill floors to 0.2%); Corollary 5.14 conditional: floor 5.54e8 (only 1.58× the present) gives period ≥ 1082233, kill table already computed and committed under N554000000_kills (itinerary obstructions + finance + the §5 walk-charge envelope; lab extracts [juggler_walk_charge_note.md](docs/theory/juggler_walk_charge_note.md) and [juggler_cycle_itinerary_structure_note.md](docs/theory/juggler_cycle_itinerary_structure_note.md) — word geometry for termination, cycles, and escape). §6.1 (3 Sep 2026) records the companion context — envelope as Paper C's descent step, floor as its target, cycle basins contagious, cycles at the critical odd share \(\log 2/\log 3\), floor stratifies the failure set — as imports; it proves nothing new about cycles. Paper D draft (not a fourth review object): [juggler_near_convergent_diophantine_note.md](docs/theory/juggler_near_convergent_diophantine_note.md) — family leftover: near-convergents of \(\log 2/\log 3\) past \(780239\), reduced to dangerous-position partial quotients; Baker REFUTED, further \(N_0\) PARK; constrains cycle states, not \(\psi_F\).
2. [docs/theory/juggler_parity_discrepancy_note.md](docs/theory/juggler_parity_discrepancy_note.md) — Paper B: parity discrepancy of nested floor powers (8-section journal form, 4 Sep 2026 referee-safe repair: Theorem 5.3 is the monomial \(c=\tfrac{3k}4 n^{9/8}\); frozen \(B=-\tfrac9{32}k\beta_1\beta_2\nu^{-9/8}\) with \(\lvert B\rvert\le6\); \(\rho_0\) ratios \(O(P^{-1/4})\); Lemma 5.2 reconstructed on the manuscript, author-chain only, now with standing constraint (C4) \(h_1,h_2\le P^{1/24}\); audit ledger moved to [paper_b_audit_ledger.md](docs/theory/paper_b_audit_ledger.md) + `research.juggler_sequence.paper_b_audit`, 114 exponent checks; Lemma 5.2(ii) from (i) is Claims A–H (author-chain Stages 1–5 of (i) remain); §3.5 localized/twisted Theorems 4.11–4.12 and the \(OOEEE\) Corollary 4.13 feeding Paper C; Theorem 5.3 remains dyadic; §8 what the kernel program buys and cannot)
3. [docs/theory/juggler_flight_note.md](docs/theory/juggler_flight_note.md) — laboratory extract: descent-free flights (envelope, dichotomy, anchor-period, divergent structure, shared lattice). Not a paper; the flight program is descriptively terminal.
4. [docs/juggler_branch_ledger.md](docs/juggler_branch_ledger.md) — every branch, decision, and strongest evidence
5. [docs/negative_knowledge.md](docs/negative_knowledge.md) — every recorded failure (`REFUTED` / CLOSE / method wall); search before reopening
6. [docs/theory/juggler_cycle_finance_note.md](docs/theory/juggler_cycle_finance_note.md) and [docs/theory/juggler_run_survivor_lattice_note.md](docs/theory/juggler_run_survivor_lattice_note.md) — the cycle frontier
7. [docs/theory/juggler_fate_contagion_note.md](docs/theory/juggler_fate_contagion_note.md) — fate contagion (the three Moirai: Atropos = reach 1, Lachesis = nontrivial cycle, Clotho = escape): every nonempty backward-closed set (every realized fate class) has \(\sum_{n\le x}1/n\gg(\log x)^{\lambda}\) for \(\lambda<\lambda^{**}=0.4480\) by elementary means and for \(\lambda<\lambda^{***}=0.5392\) with the localized Paper B estimate (§7); the conjecture is equivalent to an almost-all statement with a logarithmic rate (`J-fate-log-density`, `J-fate-contagion-equivalence`; exact layer `FateContagion.lean`). Not a halt theorem; no fate excluded.
8. [docs/theory/juggler_tao_reduction_note.md](docs/theory/juggler_tao_reduction_note.md) — the Tao-type reduction: a bounded-target almost-all theorem with rate \((\log y)^{-e}\), \(e>1-\lambda^{**}=0.552\), implies the conjecture (`J-tao-rate-implies-conjecture`), and it follows from the log-log-depth cylinder bound \(\mathrm H(C,A)\), \(C\ge 19\) with \(\lambda^{***}\) (`J-tao-loglog-depth-bound`, conjecture `juggler_loglog_depth_cylinder_bound`, \(C\ge 20\) elementary / \(C\ge 18\) with \(\lambda^{***}\)), because Juggler descent is by powers. Weakest form (§10, `J-tao-pressure-form`): the live pressure \(\mathrm P_\theta(C)\) — one exponential moment of the odd count on starts still above \(N_0\) — or its no-momentum form (tilted odd share of live starts \(\le q+o(1)\) on average over depths); it needs no fixed-depth control (\(K_3\) is irrelevant to the reduction) and no fixed-depth control can reach it. Conditional; the wall is the bulk of the parity word at depth \(\asymp\log\log y\). Do not read it as evidence for termination.
9. [docs/theory/juggler_fate_almost_all_note.md](docs/theory/juggler_fate_almost_all_note.md) — Paper C: *Fate Contagion in the Juggler Map and the Almost-All Reduction of Termination* — the paper distilled from items 7–8 (Theorem 1 contagion with \(\lambda^{**}\) unconditional, via the abstract recursion lemma 5.1; Theorem 2 odd generation; Theorem 3 the Tao-type equivalence; Theorem 4 the hierarchy of hypotheses down to the pressure form; Theorem 5 the exact decomposition with free term = live mass; \(S\)-fairness defined formally, the walk argument labelled a heuristic; Appendix C conditional on the standalone Hypothesis L, the only import from Paper B). Build: `pandoc -f markdown+tex_math_single_backslash --pdf-engine=xelatex -V geometry:margin=1in --resource-path=docs/theory` into `juggler_review/`; figures by `python docs/theory/figures/render_paper_c_figures.py` (written to `docs/theory/figures/`, mirrored to `juggler_review/figures/`). The notes 7–8 remain the source of the proofs and constants. Revised after a first external review (3 Sep 2026); pairing and consistency pass 4 Sep 2026 (Lemma 4.1′ written in full, \(C_0=250\), review PDF rebuilt).

Claim labels: [docs/README.md](docs/README.md).
Research method: [docs/methodology.md](docs/methodology.md).
BT-core theory (STRUCTURAL, parked): `docs/theory/balanced_ternary_calculus.md`,
`cubic_newton_stratum.md`; the rewrite-calculus note remains ready to send
for external review.

## Juggler state of the problem

- **Cycles:** no nontrivial cycle of period \(<780239\) at the
 laboratory certified descent floor \(N_0=350000000\)
 (`J-residual-floor-three-hundred-fifty-million`,
 `J-cycle-period-seven-hundred-eighty-thousand`): the floor
 certificate is complete (749-chunk extension from \(162849449\),
 two bit-cap leftovers resolved at \(3\cdot 10^9\), peak
 \(1493770145\) bits) and the walk charge kills all \(10\) parity
 leftovers below the blocker \(780239=176251+2\cdot 301994\)
 (\(k=2\) semiconvergent fan, required \(14.46\), walk margin
 \(0.6049\), DK break-even \(5.54\cdot 10^8\) — Diophantine, not
 computational). Lengths \(\le 478244\) carry from the previous
 floor \(N_0=162849448\)
 (`J-residual-floor-one-hundred-sixty-two-million`,
 `J-cycle-period-four-hundred-seventy-eight-thousand`: 547 chunks,
 zero failures, peak \(463362780\) bits; walk killed all \(15\)
 leftovers below \(478245=176251+301994\)).
 Since the 1 Sep 2026 consolidation Paper A prints the
 \(26254995\) floor: parity cutoff \(50507\) (§5.1), then the
 walk-charge envelope — transport, hug adversary, itinerary identity,
 Denjoy–Koksma over certified Ostrowski blocks, window theorem on
 \([50508,301994)\) — gives period \(\ge 176251\) (§5.2–5.7,
 `J-cyclemin-walk-charge-instance`), Corollary 5.10 prints the
 second floor \(162849448\) with period \(\ge 478245\), and
 Corollary 5.11 prints the third floor \(350000000\) with period
 \(\ge 780239\); the
 \(10^6\) base instance and
 the \(99\)-length survivor lattice on \((25781,16266),(1054,665)\)
 (`RunSurvivorLattice.lean`) stay in §4. Discrete word layer,
 quotient arithmetic with the DK block hypotheses
 (\(|\theta-p/q|<1/q^2\) for all certified convergents plus block
 permutations, `theta_convergent_quality`,
 `theta_block_permutations`), general Ostrowski numeration
 (window digit cap \(s(L)\le 47\) structural), the transport
 inequality of Thm 5.3, the defect-to-hug-charge chain
 (§5.2 + Thm 5.4 analytic half), the Prop 5.5 Laplace bound
 (`rotationAverage_gap`, quadratic-majorant FTC, no quadrature),
 the Thm 4.6 certified identity
 (`cycleMin_defect_finance`), and the Thm 5.9 kill template
 (`cycleMin_hug_kill_criterion`) are Lean (`WalkChargeItineraries.lean`,
 `OstrowskiSandwich.lean`, `OstrowskiNumeration.lean`,
 `RotationAverage.lean`, `WalkTransport.lean`, `WalkChargeMax.lean`,
 `DefectFinance.lean`); of the §5 envelope chain only the
 ergodic identification of \(C_*\), DK's
 variation-versus-integral inequality
 (both classical, PARK), and the
 per-length kill evaluations remain analytic prose / verified
 computation. The walk program is terminal: the
 fan-minimum reduction (`juggler_walk_fan_minimum_law`, CONJECTURE)
 ties further asymptotic progress to unbounded partial quotients of
 \(\log 2/\log 3\) — classical OPEN. Killing the
 remaining near-convergents (first \(780239\)) is Diophantine; the
 laboratory-kill slogan is **CLOSE**
 (`juggler_cycle_diophantine_survivors`; Paper D draft
 [juggler_near_convergent_diophantine_note.md](docs/theory/juggler_near_convergent_diophantine_note.md)).
 The direct Baker/SdW transfer is **REFUTED** (`juggler_cycle_gap_baker`),
 the Paper A × Paper B merge is CLOSE (`juggler_cycle_paper_merge`),
 the DK-arch free-kill of \(478245\) is **REFUTED**
 (`juggler_walk_arch_kills_blocker`: any valid tightening of
 \(2s(L)\) sits above the already-computed hug DP, which loses
 at margin \(0.433\) at the previous floor),
 and further \(N_0\) campaigns are PARK (the next useful floor is
 \(5.54\cdot 10^8\); the next *seed* waits at \(4.54\cdot 10^{11}\)).
 Floor-free: the gap transfer
 \(n\log n\cdot\min(o\log 3-L\log 2,1)\le 2L\) (Paper A Thm 4.10,
 `cycleMin_gap_transfer`, `GapTransfer.lean`) with Rhin's measure
 excludes every cycle with \(L^{14.3}\le n\log n/915\) (Cor 4.11,
 `J-cyclemin-short-cycle-rhin`); the no-cycle problem is exactly
 the long regime \(L\approx n^{0.59}\), a per-orbit parity statement
 at depth \(L\) with no mechanism. The mechanical fixed-point band
 of a survivor word has the finance-predicted count and a fair-coin
 realized parity (`juggler_cycle_mechanical_window`, CLOSE). Do not
 reopen as a short-interval Paper B, a two-copy Sturmian rigidity,
 or a longer band scan.
- **Flights:** the descent-free (open-orbit) program is descriptively
  terminal. Extract: [juggler_flight_note.md](docs/theory/juggler_flight_note.md).
  Lean envelope and walk-height law on `AboveAnchor`; every flight has
  unbounded walk (hug-hugging is cycle-exclusive); bounded-walk flights
  from \(n\ge 3.5\cdot 10^8\) have eventual period \(\ge 780239\)
  (the cycle bound at this floor is now unconditional); divergent flights diverge pointwise with
  recurrent hug domination and record jumps quantized to the
  \(\log_2 3\)-lattice (shortest near-return \(19\)).   Do not reopen
  composition (`REPARAMETERIZATION`), odd-tower placement, DK-as-kill,
  \(\{(3/2)^n\}\) as a Juggler successor
  ([juggler_three_halves_mod_one](docs/problems/juggler_three_halves_mod_one.md);
  classical OPEN, flavor only),
  valley-composition exclusion (`CLOSE`: occupancy is the existing
  pigeonhole), or a bounded walk coboundary
  (`juggler_walk_phase_correction`: even-square tower kills every
  bounded \(\psi\); the fan margin is smaller than the collapse). The terminating-side height-law PARK is not an exclusion
  mechanism. Hug-cylinder construction stays PARK
  (`juggler_hug_flow_window`): depth \(1\) is
  `J-hug-flow-window-depth-one`. Interval-ET depth \(2\) is CLOSE
  (`J-hug-flow-image-gap`): the image is \(3\sqrt X\)-separated.
  Mechanical lift, prefix realization, and formal-versus-realized
  do not say hug prefixes cannot be realized. Exclusion of
  divergent orbits is not claimed.
- **Termination:** certified descent density \(7/8\)
  (length-5 repair, `J-five-step-descent-density`, Paper B
  Corollary 6.4). The four-step class remains \(13/16\)
  (Corollary 4.9). Densities \(57/64\) and \(29/32\) remain
  **CONJECTURE** (Phase-26 holes: length-7 chirps miss
  Stage 2, `J-length7-passenger-theorem-t` **REFUTED** as a
  method; isolated \(e(un^{27/16})\) and \(e(Cn^{3/2})\)
  close by one \(A\)-process plus Lemma 3.3,
  `J-length7-vdc3-chirps`, but the inventory object is
  \(e(uw^{3/2})\) and the reduction is not a decoration;
  X3 plus Q/R3 is **REFUTED** (`J-length7-x3-qr3-carry`);
  the integer-\(w\) block at \(\xi\asymp n^{45/32}\) is
  the Phase-5 wall (`J-length7-integer-w-block`);
  the length-8 remainder decays
  (`J-length8-remainder-discard`: \(\lvert E\rvert\ll
  n^{-45/128}\), discard \(\ll P^{131/192}\); crude
  \(\lvert E\rvert<1\) discard stays dead); the growing
  remainder is now an engine,
  `J-length7-remainder-engine`; the harvest counting
  program is laboratory-terminal
  (`J-harvest-counting-terminal`: every reading of
  \(e(uw^{3/2})\) is a killed route or not a Juggler
  construction — do not wrap a nested-floor bound as
  one). Corollary R′ is still a
  family-CONJECTURE, but the instance \(\alpha=33/32\) is
  **EXACT — HUMAN PROOF**,
  `J-w-family-thirty-three-thirty-seconds`). The rated
  pointwise route is parked behind the \(K_3\) obstruction
  ladder BB/GG/JJ. The rate-free line is laboratory-terminal:
  nearby reformulations of the floor-Hardy composition are
  closed (`juggler_v94_rate_free`, `juggler_v94_hardy_lift`,
  `juggler_nil_pet_reentry`, `juggler_rate_free_floor_hardy`).
  The remaining problem is external mathematics, exported at
  [docs/theory/exponent_pair_two_monomial.md](docs/theory/exponent_pair_two_monomial.md):
  prove \(\tfrac54 p+q<\tfrac23\) for an exponent pair
  applicable to \(cm^{9/4}-jm^{2/3}\). It is not a Juggler
  construction and must not be wrapped as one. The conjecture
  `juggler_tower_rate_free_equidistribution` stays ACTIVE; a
  completely different route to the node-wise E-share
  \(\beta>\beta_*=1-\log 2/\log 3\approx 0.36907\) would also
  suffice. The m-variable PS inversion is recorded and closed
  (`juggler_ps_inversion_barrier`): the fixed harmonic
  reduces exactly to those two-monomial sums, needing
  sub-density \(o(M^{2/3})\) versus the known hull minimum
  \(95/112\); main-term saving \(N^{13/16}\) and the
  bias-mass relaxation of Lemma B are recorded there. Do not
  re-run it. The Bombieri–Iwaniec follow-up is also closed
  (`juggler_bi_resonance_limit`): sub-density needs \(p<2/27\)
  on the BI line, while the method's ceiling under perfect
  spacing is \(3/20\) — a factor \(81/40\) short even
  conjecturally-within-method. Do not reopen the composition door, the
  \(\beta\)-fallback as a weaker species, PET, Theorem R,
  \(\lambda=0\), or further literature-name audits. Not
  claimed.
- **Fates (the Moirai):** every realized fate class — Atropos
 (reach 1), Lachesis (a nontrivial cycle's basin), Clotho (escape) —
 is backward-closed and has \(\sum_{n\le x}1/n\gg(\log x)^{\lambda}\)
 for every \(\lambda<\lambda^{**}=0.4480\) (`J-fate-log-density`,
 mechanism: even blocks are intervals, OE fibers of
 \(\lfloor n^{3/4}\rfloor\) carry \(\ge 1/3-O(1/H)\) of each parity of
 \(\lfloor n^{3/2}\rfloor\) and average \(1/2\) over even blocks).
 The rest-average lift \(1/3\to 1/2\) is PARK
 (`juggler_oe_rest_average`): a fixed low-even seed mixes, infinite
 planting does not yield a coefficient. Log-log clock branch (5 Sep
 2026, PARK, [juggler_lachesis_loglog_clock.md](docs/problems/juggler_lachesis_loglog_clock.md),
 Lean `LogLogClock.lean`): the walk mod 1 is the rotation by
 \(\log_2(3/2)\) indexed by the odd count; a cycle basin is not
 lacunary above \(n^{2^{1+u_{\max}}}\), with \(E\)-visible density
 \(\approx\sum_C(1/x)/\ln y\) and \(\sum_C 1/x\) pinned by Lean finance;
 the upper bound on any basin is the free term; a divergent orbit's
 basin gets the same only under slow escape (odd share within
 \(0.004\) of \(q^*\)), never realised; the hug band is the minimal
 invariant band and its word is forced; failures with \(k\) leading
 even steps are \(\ge 261^{2^k}\) (Lean) / \((N_0+1)^{2^k}\). The deep
 census is dominated by a floor raise; do not run it. The gap \(0.448\to 0.4927\)
 is a dynamical averaging problem for the low-even set \(P\), not
 another pointwise fiber bound, and is not opened.
 Hence the conjecture \(\iff\) the failures have log-count
 \(o((\log x)^{\lambda})\) (`J-fate-contagion-equivalence`), and a
 bounded-target Tao-type bound \(\#\{n\text{ odd}\in(y,2y]:n\notin R\}
 \le y(\log y)^{-e}\) with \(e>0.552\) implies the conjecture
 (`J-tao-rate-implies-conjecture`); that bound follows from the
 log-log-depth cylinder conjecture \(\mathrm H(C,A)\), \(C\ge 20\)
 (`J-tao-loglog-depth-bound`, `juggler_loglog_depth_cylinder_bound`),
 and even from its one-sided form: odd-share \(\le q<\log 2/\log 3\)
 on every cylinder of depth \(<C(q)\log_2(\log 2y/\log N_0)\),
 \(C(0.55)=44\) (`J-tao-biased-split-bound`, Azuma). The bad mass sits
 on odd runs \(\ge 4\) (99.99% at \(10^{100}\)): for the uniform form
 the hypothesis is the iterated \(O^t\to O^{t+1}\) split. The weakest
 form is the live pressure / no-momentum hypothesis
 (`J-tao-pressure-form`, Tao note §10): the tilted odd share of live
 starts (weights \(e^{\theta o_t}\)) is \(\le q+o(1)\) on average over
 depths \(<C\log_2\log y\); it is one-sided, aggregated over cylinders,
 free of any \(o(\log\log y)\) initial depths, tolerant of towers biased
 below \(0.84\), and no bounded-depth cylinder statement can reach it
 (fair-to-depth-\(k\)-then-all-\(O\) measure). Almost-all-cylinder and
 pair-correlation forms are `REPARAMETERIZATION`
 (`J-tao-cylinder-forms-reparameterization`); do not re-derive them.
 Pressure census: tilted share \(0.50\pm0.06\) to depth \(40\) at
 \(10^{12}\)–\(10^{50}\) (OBSERVATION). One frontier statement (Tao
 note §11, `J-tao-free-term-is-live-mass`): the free term \(\psi_F\)
 of the exact map is the infinite-depth live mass of the \(OO\)
 cylinder; the two halves of (6.1) are contagion and the
 failure-density upper recursion with the same critical exponent
 \(0.507\) as the Tao threshold; the exact map cannot replace
 contagion; an analytic cylinder method may lose at most a factor
 \(2^{1/C}=1.037\) in saving exponent per depth (Weyl differencing
 excluded regardless of \(K_3\)). Do not open a third formulation.
 Depth-two ceiling of the contagion method is
 \(\lambda=0.4927\); pointwise natural density for all \(x\) does not
 follow (single-seed \(E\)-trees are lacunary). Exact map (note §6,
 `J-fate-odd-generation`, Lean): a two-way closed class is the
 \(E\)-forest over the odd preimages of its intersection with
 \(S=\{\lfloor m^{3/2}\rfloor: m\text{ odd}\}\); the conjecture
 \(\iff F\cap S=\emptyset\iff\) \(S\)-fairness of \(F\); the
 first-letter decomposition (6.1) has one free term (the \(OO\)-type
 share), Paper A bounds the seed of a cycle, Paper B the descending
 branches. Do not reopen: a Tao analogue with a *growing* target does
 not feed contagion; bounded-odd-run control cannot reach the
 hypothesis; the depth-uniform kernel question is PARK behind the
 \(K_3\) program. Done (note §7, `J-fate-ooeee-production`): Paper B's
 Theorems 4.4/4.7 localize to intervals \(\ge P^{1/2}\) with relative
 saving \(P^{-1/24}\); the \(OOEEE\) production on even blocks gives
 \(\lambda^{***}=0.5392\) (Tao threshold \(0.4608\), \(C(1/2)=18\),
 \(C(0.55)=39\)). Kernel-theorem localization (Paper B 5.3/6.1, for
 \(OOOEE\)/\(OOEOE\) on even blocks; orientation \(\lambda=0.5561\),
 \(C=18\)) is **CLOSE** (fate note §7.4, `J-kernel-localize`): the
 fibers have length \(P^{5/32}\), below the triple-parity threshold
 \(P^{1/2}\), and Lemma 3.9's trivial bound is the whole interval
 (\(P^{89/96}\) on a dyadic block; \(\min(Y,P^{89/96})=Y\) on either
 candidate \(Y\)). Do not reopen as a forty-estimate re-derivation
 or a \(V\)-retune. \(\mathrm H(C,A)\)
 uses the odd-start fair share \(2^{-(d-1)}y/2\) (first letter \(O\)).
 The certified floor is the *target*: exact orbits from \(10^{12}\) to
 \(10^{50}\) stay above \(N_0\) at the odd-start fair-coin rate to depth
 \(40\) within \(3\%\) (`tao_census`, OBSERVATION — aggregate evidence
 only). The floor stratifies \(F\) (\(\min F\) is an \(OO\)-start,
 \(F\cap S\subseteq(N_0^{3/2},\infty)\)) and cycles sit exactly at the
 critical odd share \(\log 2/\log 3\) (fate note §8); no threshold is
 crossed by \(N_0\) or \(L\).
- **Local attacks are closed.** Fibres are parity + interval only
  (`even_preimage_iff`, `odd_preimage_unique`, `preimage_same_next_state`): no finite
  local configuration around a hypothetical cycle is contradictory. Seam,
  ancestry, provenance, collision-pair, word-order, error-transport, and
  cycle-lift drops all reduce to Collision Factorization (first meeting iff
  the parent is off-cycle) or the lift identity \(T^L(t)=c\ge n\). The
  integer-edge interface is `Seam.lean` (`SeamData`); it packages that
  factorization and does not reopen the kill. Do not reopen them; the
  ledger, `conjectures/refuted/`, and
  [docs/negative_knowledge.md](docs/negative_knowledge.md) list each kill.
- **Anti-overclaim:** do not treat a finite check, a period floor, a
  density, a leftover census, or any weaker compiled lemma as a halt
  theorem, as "no cycle of any length", or as a Collatz/Juggler
  solution. Finite checks are not proofs. Slogan language ("we solved
  Juggler / Collatz") is forbidden even if a theorem exists: state the
  theorem with its quantifiers, Lean name, and ledger tag. If Lean
  compiles a `sorry`-free statement that matches the English (every
  orbit reaches the trivial cycle, or there is no nontrivial cycle),
  say that statement, tag it `EXACT — LEAN VERIFIED`, and record it.
  Do not refuse to name a matching theorem, and do not hide it under
  "this is not a halt theorem." Until that gate, those phrases are
  overclaim. See [docs/README.md](docs/README.md).

## Juggler file map

| Artifact | Home |
|----------|------|
| Probes / censuses | `src/research/juggler_sequence/<branch>.py` |
| Tests (fast suite) | `tests/research/juggler_sequence/test_<branch>.py` |
| Data artifacts | `data/research/juggler/.../summary.json` |
| Lean (itineraries, cells, CycleMin, finance, lattice, seam) | `formal/Problems/Juggler/` (`WalkChargeItineraries.lean`, `Seam.lean`) |
| Branch dossier | `docs/problems/juggler_<id>.md` (all TEMPLATE headings; enforced by `tests/integration/test_problem_dossiers.py`) |
| Negative knowledge | [docs/negative_knowledge.md](docs/negative_knowledge.md) (completeness: `tests/integration/test_negative_knowledge.py`) |
| Conjecture record | `conjectures/{active,refuted,proved,archived}/<id>.json` |
| Journal entry | `docs/research_journal.md` (consolidations allowed; no auto-milestones) |
| Named theorem metadata | `docs/theory/theorem_ledger.json`, then render |
| External leftover (not a Juggler branch) | [docs/theory/exponent_pair_two_monomial.md](docs/theory/exponent_pair_two_monomial.md); Paper D draft (family leftover, not a review object): [docs/theory/juggler_near_convergent_diophantine_note.md](docs/theory/juggler_near_convergent_diophantine_note.md) |

## How a direction runs

`explore → distill → prove/refute → decide`. Before substantial
implementation, output a triage block:

```text
Mathematical target     one precise question
Novelty hypothesis      what could possibly be new
Falsifier               the observation that kills the idea
Existing machinery      what the platform already provides
Maximum Phase-0 scope   the smallest experiment that answers the target
Promotion criterion     what would justify PROMOTE
Stop criterion          what forces PARK or CLOSE
```

Implement only that scope. Search [docs/negative_knowledge.md](docs/negative_knowledge.md), `conjectures/refuted/`, the branch
ledger, and the `REFUTED` ledger rows before re-testing a hypothesis.

At the end of a phase, report:

```text
What was learned      3–7 concise points
Strongest theorem     one statement
Strongest refutation  one false hypothesis or counterexample, if any
Reusable machinery    what enters the platform
Branch status         PROMOTE | PARK | CLOSE
Why                   one short paragraph
Best next question    exactly one
```

Then stop. Machinery gravity — new structure, new CLI, new visualization,
no new mathematical consequence — means stop implementing, find the
invariant or obstruction, and decide. Every branch ends in `PROMOTE`,
`PARK`, or `CLOSE`; do not auto-open the next one. Do not raise \(N_0\),
reopen finance, or edit Paper A from a Phase-0 branch. Do not
generate nearby reformulations of the floor-Hardy composition.

## Where non-Juggler math goes

Trit / `D` / jets / `≡_k` → `src/bt/calculus/`; cubic strata →
`src/research/residuals/`; Collatz → `src/research/collatz/`; generic Lean
→ `formal/BTCalculus/`. No `bt.calculus` shims, no compatibility packages.
New research area: [docs/problems/TEMPLATE.md](docs/problems/TEMPLATE.md)
plus `src/research/<id>/`.

## Commands

```powershell
python -m pip install -e ".[dev,ui]"
pytest                                              # fast suite
pytest tests/research/juggler_sequence -q           # Juggler only
pytest --runslow
python -m research.juggler_sequence.<branch>        # run a probe
python tools/render_theorem_ledger.py --check
$env:PATH = "$env:USERPROFILE\.elan\bin;$env:PATH"
cd formal; lake build                               # no sorry / admit
```
## Adding a Lean module or a probe (checklist)

1. New Lean file under `formal/Problems/Juggler/` → import it in the
   barrel `formal/Problems/Juggler.lean`, register it in `LAYERS` of
   `src/research/juggler_sequence/lean_paths.py` (imports must point to
   lower-ranked entries), and — if it is a review object of Paper A —
   in `PAPER_MODULES` and `formal/Problems/JugglerPaper.lean`.
   `tests/research/juggler_sequence/test_layer_architecture.py` is a
   plain substring test: the words `sorry`, `admit`, `axiom` may not
   appear anywhere in a registered file, not even in comments.
   `Seam.lean` already owns the name `OnCycle`.
2. Compile one file with `lake env lean <file>` (≈ 40 s) before
   `lake build Problems.Juggler` (≈ 1 min when oleans are cached).
3. New probe → `src/research/juggler_sequence/<branch>.py`, fast test,
   `data/research/juggler/<branch>/summary.json`, dossier with every
   TEMPLATE heading, ledger rows (JSON is `indent=1`, `ensure_ascii=False`;
   re-render), journal entry, branch-ledger row.
4. `tests/integration/test_docs_links.py` treats every `](` as a
   markdown link: do not write `[a − b](1 − c)`-style math in ledger
   statements or notes.

## Environment notes for agents

- Shell is PowerShell: no `head`/`tail`/heredocs (`<<'EOF'` fails);
  use `Select-Object -First/-Last`, `Select-String`, and write
  multi-line scripts to a temp file. `rg` globs like `dir/*.lean`
  fail on Windows paths — use `rg -g "*.lean" dir`; parentheses in
  `rg` patterns must be escaped or avoided.
- **LaTeX and Python strings.** The papers hold 2639 macros across 42
  names that a *non-raw* Python string silently corrupts — `\tfrac`
  (675), `\nu` (199), `\theta` (195), `\beta` (179), `\rfloor` (145),
  `\varepsilon` (144), `\frac` (123), `\text`, `\asymp`, `\alpha`,
  `\rho`, `\to`, `\bigl` … Any macro starting with `a b f n r t v 0 x`
  is an escape: `"\theta"` is TAB + `heta`, `"\nu"` is NEWLINE + `u`,
  `"\approx"` is BEL + `pprox`, `"\frac"` is FF + `rac`. **This is
  Python, not the shell** — a quoted heredoc (`<<'PY'`) passes the text
  through untouched; the damage happens in the string literal on the
  far side, so blaming "heredoc mangling" sends you to the wrong fix.
  Therefore:
  1. To change a file containing LaTeX, use the Edit/Write tools.
     There is no string layer, so there is nothing to escape.
  2. If a script is genuinely needed, write it to a file with Write and
     then run it. Not `python <<'PY'`, not `python -c "…"`.
  3. If a Python string must carry LaTeX, make it raw: `r"\theta"`.
  4. Symptoms: a literal tab or a stray line break inside a `.md`; a
     regex that quietly stops matching; `SyntaxWarning: invalid escape
     sequence`. Three real defects reached the manuscripts this way
     (`\theta` in Paper A §5, `\to` in §3, `\theta(L)` in the reviewer
     packet) and survived several revisions.
  `test_manuscript_consistency.py::test_no_mangled_latex_escapes`
  catches the tab case — no legitimate tab exists in these documents.
  It cannot catch a stray *newline*, so prefer assertions whose target
  string fits on one line.
- Floats: `10.0**1000` overflows; work in `log y`.
- The fast suite (`pytest`, xdist) takes ≈ 3.5 min; the research-control
  tests regenerate `docs/research/*.json` artifacts (harmless
  churn). The working tree may be auto-committed by the host between
  turns; check `git log -1` before assuming files are uncommitted.
- Mathlib names used here: `Nat.eq_sqrt`, `Nat.le_sqrt`, `Nat.sqrt_lt`,
  `Nat.pow_le_pow_iff_left`, `Function.iterate_fixed`,
  `Function.iterate_mul`, `Function.iterate_add_apply`.

## Remarks

If you're Fable don't spend ages fixing tests - focus on the math.

You have access to a Windows 11 machine with an AMD Ryzen 9 3900X (12C/24T), 64 GB RAM, and an RTX 5090 (32 GB VRAM, CUDA 13.3), so don't be afraid to use it.

Persistent policy lives in [.cursor/rules/](.cursor/rules/). Streamlit work uses
[.agents/skills/developing-with-streamlit/SKILL.md](.agents/skills/developing-with-streamlit/SKILL.md).
